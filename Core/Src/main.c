/* USER CODE BEGIN Header */
/**
  ******************************************************************************
  * @file           : main.c
  * @brief          : Main program body
  ******************************************************************************
  * @attention
  *
  * Copyright (c) 2025 STMicroelectronics.
  * All rights reserved.
  *
  * This software is licensed under terms that can be found in the LICENSE file
  * in the root directory of this software component.
  * If no LICENSE file comes with this software, it is provided AS-IS.
  *
		 项目总览
 * 硬件：STM32F103C8T6 + DengFOC(M0通道) + 无刷2208 + AS5600(I2C) + 外部12V
 * 关键引脚（与 CubeMX 一致）：
 *   - TIM2_CH1/2/3 -> 三相PWM输出到驱动板M0（A相/B相/C相）
 *   - PA8 -> 电机使能 Motor_EN（上电后拉高）
 *   - I2C2(PB10=SCL, PB11=SDA) -> AS5600 读角度
 *   - ADC1_IN8(PB0)=O2_CS、ADC1_IN9(PB1)=O1_CS -> 两相电流采样
 *   - USART1(PA9/PA10) -> 上位机串口交互
 *
 * 模式（串口命令 cX 切换）：
 *   c1: 开环速度   -> 目标 t=rad/s，直接积分电角 el_angle 输出Uq
 *   c2: 闭环电流   -> 目标 Iq_ref（代码里先固定0.5A），做 dq 电流PI，输出 Ud/Uq，再SVPWM
 *   c3: 闭环位置   -> 目标 t=rad（机械角），位置PID输出Uq，角度用编码器的电角
 *
 * 其它命令：
 *   a       : 零电角对齐（给 d 轴定向电压，让转子吸附）
 *   z       : 电流偏置校准（ADC零点）
 *   t3.14   : 设置目标（c1=速度rad/s；c3=位置rad）
 *   p5 i200 d0.1 : 设置位置环 PID
 *
 * 时序：
 *   - TIM4 中断（CTRL_HZ=10kHz）：跑 control_step() —— 真正的控制（开环/电流/位置）
 *   - 主循环(1kHz)：读AS5600角度、做“解缠绕”、推导电角（给控制用）；20Hz 打印状态
 *
 * 目前状态：c1、c3 已正常；c2（电流环）需要后续继续整定与采样时序优化。

  ******************************************************************************
  */
/* USER CODE END Header */
/* Includes ------------------------------------------------------------------*/
#include "main.h"
#include "adc.h"
#include "dma.h"
#include "i2c.h"
#include "tim.h"
#include "usart.h"
#include "gpio.h"

/* Private includes ----------------------------------------------------------*/
/* USER CODE BEGIN Includes */
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <math.h>
#include <ctype.h>
/* USER CODE END Includes */

/* Private typedef -----------------------------------------------------------*/
/* USER CODE BEGIN PTD */

/* USER CODE END PTD */

/* Private define ------------------------------------------------------------*/
/* USER CODE BEGIN PD */
#ifndef M_PI
#define M_PI 3.14159265358979323846f
#endif

#ifndef TWO_PI
#define TWO_PI (2.0f * M_PI)
#endif

#ifndef _3PI_2
#define _3PI_2 (1.5f * M_PI)
#endif

#define TX_BUFFER_COUNT 8
#define TX_BUFFER_SIZE  96
/* USER CODE END PD */

/* Private macro -------------------------------------------------------------*/
/* USER CODE BEGIN PM */

/* USER CODE END PM */

/* Private variables ---------------------------------------------------------*/

/* USER CODE BEGIN PV */


/* 控制模式与物理参数 */
typedef enum { MODE_OL_SPEED=1, MODE_CL_CURRENT=2, MODE_CL_POS=3, MODE_CL_SPEED=4 } ctrl_mode_t;
static const int   pole_pairs = 7;     // 2208 7对极
static const int   Dir = 1;            // 相线对调+取正，保持“正速度=角度正增”
static const float Vdc = 12.0f;        // 母线电压（用于电压归一/限幅）
static const float Uq_limit = 4.0f;    // 输出Uq上限（先保守）


/* 运行时的模式与目标量 */
volatile ctrl_mode_t g_mode = MODE_OL_SPEED; // 默认上电开环速度
volatile float g_target = 1.0f;              // c1=rad/s, c3=rad（位置）
volatile float g_kp = 5.0f, g_ki = 0.0f, g_kd = 0.1f; // 位置环PID参数


/* 控制节拍与电角 */
#define CTRL_HZ 10000.0f       // TIM4中断频率（CubeMX里要配一致）
#define Ts (1.0f/CTRL_HZ)      // 控制步长（秒）
static float el_angle = 0.0f;  // 开环速度模式用的“自己积”的电角


/* 电流采样（DMA）与实时电流（安培） */
volatile uint16_t adc_raw[2] = {0,0}, adc_last[2] = {0,0};
volatile float ia_A = 0.0f, ib_A = 0.0f;


/* 串口收发缓冲与简单协议 */
#define RX_MAX 64
static uint8_t rx_ch;
static char rx_line[RX_MAX];
static uint16_t rx_len = 0;
static char tx_buffer[TX_BUFFER_COUNT][TX_BUFFER_SIZE];
static volatile uint8_t tx_head = 0, tx_tail = 0;
volatile uint8_t tx_busy = 0;


/* 角度（机械->电） */
static volatile float g_angle_el_cache = 0.0f;     // 用于控制的电角（由机械角推导）
//static const float ADC_REF = 3.3f;
static const float ADC_K = (3.3f/4095.0f);


/* 电流换算与偏置（板载电阻与运放增益） */
static const float R_SHUNT = 0.01f, AMP_GAIN = 50.0f;
static const float V2A = 1.0f/(R_SHUNT*AMP_GAIN);  // 伏->安
static const float GAIN_A = -V2A, GAIN_B = -V2A;   // 板子接法决定正负（这里负号是我这块板的方向）
static float offset_a_V = 0.0f, offset_b_V = 0.0f; // ADC零偏（上电校准）


/* 机械角与零电角 */
static float zero_elec_angle = 0.0f;               // 对齐得到的零电角
volatile float g_mech_angle = 0.0f;                // 机械累计角（rad）
static float g_last_mech_angle = 0.0f;
//	g_full_rotations = 0.0f; // （当前版本仍保留全圈计数）


/* dq 电流环变量（后续继续整定） */
static float Iq_ref = 0.5f;         // 先固定Iq_ref=0.5A 方便感受吸力
static float Id = 0.0f, Iq = 0.0f;
static float id_integral = 0.0f, iq_integral = 0.0f;
static float id_kp = 1.5f, id_ki = 150.0f;  // d轴 PI
static float iq_kp = 0.2f, iq_ki = 50.0f;  // q轴 PI


/* 位置环PID的内部变量（积分/上次误差） */
static float pi_i = 0.0f, last_e = 0.0f;


/* ---- 诊断/保护 ---- */
static volatile uint8_t sat_flag = 0;      // 电压向量限幅标志（便于串口观察）
static volatile uint8_t fault_latched = 0; // 过流锁存
static const float I_TRIP = 2.0f;          // 过流阈值(A) —— 保守值，见下文说明


/* 可打印的观测量 */
static float Ud_dbg=0, Uq_dbg=0, Uabs_dbg=0;


/* 在线校正开关：相序对调/ q轴翻转/ 电角偏置（度 -> 弧度） */
static int   cfg_swap_ab = 0;          // 0: 正常；1: 交换 ia/ib
static int   cfg_flip_q  = 0;          // 0: 正常；1: 翻转 q 轴符号
static float angle_offset_el = 0.0f;   // 电角额外偏置（弧度）


/* 速度环PID参数与状态 */
static float vel_kp = 0.30f, vel_ki = 5.0f, vel_kd = 0.0f;
static float vel_i = 0.0f, vel_last_e = 0.0f;

/* 速度计算与滤波 */
static float g_mech_velocity = 0.0f;        // 当前机械速度(rad/s)
static float g_last_angle_for_vel = 0.0f;  // 速度微分用的上次角度
static const float vel_lpf_alpha = 0.15f;  // 低通滤波系数(0.1~0.3合适)

/* 串口输出模式切换 */
typedef enum { UART_MODE_TEXT=0, UART_MODE_VOFA=1 } uart_output_mode_t;
static volatile uart_output_mode_t uart_output_mode = UART_MODE_TEXT; // 默认文本模式
/* USER CODE END PV */

/* Private function prototypes -----------------------------------------------*/
void SystemClock_Config(void);
/* USER CODE BEGIN PFP */

static void Align_ZeroElectricalAngle(void);
static void current_offsets_calib(uint16_t rounds);
static inline float pid_step(float kp,float ki,float kd,float e,float out_lim);
static void pid_reset(void);
static void uart_safe_print(const char* s);
/* 声明新的可靠角度读取函数 */
static float get_stable_angle(void);

/* USER CODE END PFP */

/* Private user code ---------------------------------------------------------*/
/* USER CODE BEGIN 0 */
extern TIM_HandleTypeDef htim2; extern TIM_HandleTypeDef htim4;
extern ADC_HandleTypeDef hadc1; extern I2C_HandleTypeDef hi2c2;
extern UART_HandleTypeDef huart1;

// [B2] 通用数学小工具：归一化/饱和 —— 所有控制分支都要用到的基础函数
static inline float sat01(float x){ return x<0?0:(x>1?1:x); }
static inline float norm2pi(float a){ while(a<0.0f)a+=TWO_PI; while(a>=TWO_PI)a-=TWO_PI; return a; }


// [B3] 串口“非阻塞发送”管线：环形缓冲 + Transmit_IT + 发送完成回调链式续发
static void uart_safe_print(const char* s) {
    uint8_t next_head = (tx_head + 1) % TX_BUFFER_COUNT;
    if (next_head == tx_tail) return;
    strncpy(tx_buffer[tx_head], s, TX_BUFFER_SIZE - 1);
    tx_buffer[tx_head][TX_BUFFER_SIZE - 1] = '\0';
    tx_head = next_head;
    __disable_irq();
    if (!tx_busy) {
        tx_busy = 1;
        HAL_UART_Transmit_IT(&huart1, (uint8_t*)tx_buffer[tx_tail], (uint16_t)strlen(tx_buffer[tx_tail]));
    }
    __enable_irq();
}

// [B3] 串口“非阻塞发送”管线：环形缓冲 + Transmit_IT + 发送完成回调链式续发
void HAL_UART_TxCpltCallback(UART_HandleTypeDef *huart) {
    if (huart->Instance == USART1) {
        tx_tail = (tx_tail + 1) % TX_BUFFER_COUNT;
        if (tx_tail != tx_head) {
            HAL_UART_Transmit_IT(&huart1, (uint8_t*)tx_buffer[tx_tail], (uint16_t)strlen(tx_buffer[tx_tail]));
        } else {
            tx_busy = 0;
        }
    }
}


// [B4] 命令解析器：c/t/p/i/d/qr/qi/dr/di/y/v/w/a/z —— 修改模式/目标/参数/在线极性修正/对齐/校准
static void parse_line(char* line) {
	/* 思路（串口小协议）：逐字符解析字母+数值，例如：
 *  c3\n   -> 切到位置闭环
 *  t1.57\n-> 设置目标为1.57rad
 *  p5 i200 d0.1 -> 改位置环 PID
 * 小优化：当切到 c3 时，“就地定点”，可以在切换时加一行：
 *   if (new_mode==MODE_CL_POS) g_target = g_mech_angle;
 */
    char* cursor = line;
    while (*cursor) {
        while (*cursor && !isalpha((unsigned char)*cursor)) { cursor++; }
        if (!*cursor) break;
        char cmd = tolower((unsigned char)*cursor);
        cursor++;
        char* end_ptr;
        float val = strtof(cursor, &end_ptr);
        if (end_ptr == cursor) {
             if (cmd == 'a') Align_ZeroElectricalAngle();
             if (cmd == 'z') current_offsets_calib(500);
        } else {
            switch(cmd) {
                case 'c':
									if ((ctrl_mode_t)val == MODE_CL_POS) { g_target = g_mech_angle; }
											if ((int)val >= MODE_OL_SPEED && (int)val <= MODE_CL_SPEED && (ctrl_mode_t)val != g_mode) {
                        g_mode = (ctrl_mode_t)val;
                        pid_reset();
										    fault_latched = 0; // 切模式时清除过流锁存

                    }
                    break;
                case 't': g_target = val; break;
                case 'p': g_kp = val; break;
                case 'q':  // q0.8 / qr2.0 / qi150
                    if (*cursor=='r') {       // qr2.0 -> q轴 Kp
                        iq_kp = val; cursor++; // 消费 'r'
                    } else if (*cursor=='i') { // qi150 -> q轴 Ki
                        iq_ki = val; cursor++; // 消费 'i'
                    } else {                   // q0.8 -> Iq_ref
                        Iq_ref = val;
                    }
                    break;
                case 'd':  // 兼容已存在的 d(位置D)，但也允许 dr/di 指电流环
                    if (*cursor=='r') { // dr2.0 -> d轴 Kp
                        id_kp = val; cursor++; // 消费 'r'
                    } else if (*cursor=='i') { // di150 -> d轴 Ki
                        id_ki = val; cursor++; // 消费 'i'
                    } else {
                        g_kd = val; // 保持原意：位置环 D
                    }
                    break;
                case 'i':  // 兼容已存在的 i(位置I)，也允许 qi 设置 q轴 Ki（为了对称，也支持 'qr'）
                    if (*cursor=='r') { // qr2.0 -> q轴 Kp（为了对齐 'dr' 也接受 'qr'）
                        iq_kp = val; cursor++;
                    } else if (*cursor=='i') { // qi150 -> q轴 Ki
                        iq_ki = val; cursor++;
                    } else {
                        g_ki = val; // 保持原意：位置环 I
                    }
                    break;
										case 'y': // y1/y0 -> 交换A/B相（Clarke前交换）
                    cfg_swap_ab = (val != 0.0f) ? 1 : 0;
                    break;
                case 'v': // v1/v0 -> 翻转 q 轴（Park后 Iq 与逆变 Uq 同时翻转）
                    cfg_flip_q = (val != 0.0f) ? 1 : 0;
                    break;
                case 'w': // w90/w-90/w0 -> 设置电角偏置(度)
                    angle_offset_el = val * (M_PI/180.0f);
                    break;
								case 's': {  // 速度环PID设置：sp0.3 / si5 / sd0
										char sub = *cursor;
										if (sub=='p' || sub=='i' || sub=='d') {
												cursor++; // 先消费子命令字母
												float v = strtof(cursor, &end_ptr);
												if (sub=='p')      vel_kp = v;
												else if (sub=='i') vel_ki = v;
												else               vel_kd = v;
												cursor = end_ptr;  // 把游标推进到数字末尾
										}
								} break;
								case 'u': // u0/u1 -> 切换串口输出模式
										if ((int)val == 0 || (int)val == 1) {
											uart_output_mode = (uart_output_mode_t)((int)val);
    }
    break;
            }
        }
        cursor = end_ptr;
    }
}


// [B4-ISR] 串口接收中断：逐字拼行，遇 '\n' 调 parse_line() 并回 ACK
void HAL_UART_RxCpltCallback(UART_HandleTypeDef *huart){
  if(huart->Instance==USART1){
    if(rx_ch=='\n' || rx_len>=RX_MAX-1){
        rx_line[rx_len]='\0';
        parse_line(rx_line);
        char ack[64];
        snprintf(ack, sizeof(ack), "ACK: mode=%d, Tgt=%.2f\r\n", (int)g_mode, g_target);
        uart_safe_print(ack);
        rx_len=0;
    }
    else if(rx_ch!='\r'){ rx_line[rx_len++] = (char)rx_ch; }
    HAL_UART_Receive_IT(&huart1, &rx_ch, 1);
  }
}


// [B5-ISR] ADC+DMA 完成回调：将 dma 写入的 adc_raw 快照到 adc_last（控制 ISR 只读 adc_last）
void HAL_ADC_ConvCpltCallback(ADC_HandleTypeDef* hadc){
  if(hadc->Instance == ADC1){ adc_last[0] = adc_raw[0]; adc_last[1] = adc_raw[1]; }
}



// [B6] I2C 总线卡死恢复：清 BUSY/重新初始化，保证 AS5600 读角可靠
static void I2C_ClearBusyFlagErratum(void) {
    HAL_I2C_DeInit(&hi2c2);
    HAL_Delay(2);
    HAL_I2C_Init(&hi2c2);
}

// [B6-1] 角度原始读取（0..2π）：读寄存器 0x0E/0x0F -> 12bit -> 弧度，失败返回负数
static float AS5600_ReadMechRad(void){
  uint8_t reg = 0x0E;
  uint8_t buf[2] = {0};
  // 让I2C读取失败时返回一个无效值(-1)，而不是一个可能被误用的旧值
  if (HAL_I2C_Master_Transmit(&hi2c2, (0x36 << 1), &reg, 1, 50) != HAL_OK) {
      I2C_ClearBusyFlagErratum();
      return -1.0f;
  }
  if (HAL_I2C_Master_Receive(&hi2c2, (0x36 << 1), buf, 2, 50) != HAL_OK) {
      I2C_ClearBusyFlagErratum();
      return -1.0f;
  }
  uint16_t raw = (((uint16_t)buf[0] << 8) | buf[1]) & 0x0FFF;
  return (float)raw * (TWO_PI / 4096.0f);
}

// [B6-2] 稳定角读取：连读多次，连续两次接近才认定可靠，供“对齐零电角”使用
static float get_stable_angle(void) {
    float angle_prev = -1.0f, angle_curr = 0.0f;
    for (int i = 0; i < 20; i++) { // 最多尝试20次
        angle_curr = AS5600_ReadMechRad();
        // 确保读数有效(>0)且连续两次读数非常接近
        if (angle_curr >= 0.0f && angle_prev >= 0.0f && fabsf(angle_curr - angle_prev) < 0.01f) {
            return angle_curr; // 读数稳定，返回
        }
        angle_prev = angle_curr;
        HAL_Delay(5); // 稍作延时，等待总线稳定
    }
    // 如果循环20次还不行，就返回最后一次读到的有效值，或者0
    return (angle_curr >= 0.0f) ? angle_curr : 0.0f;
}

// [B7] 机械角“解缠绕”：0..2π 原始角 -> 折返增量到 [-π,π] -> 连续机械角 g_mech_angle
// [B9] 三相电压合成（电压形式 SVPWM）：dq^-1 -> αβ -> 加共模偏置 -> 写 TIM2 CCR1/2/3
static void set_phase_voltage(float Uq, float angle_el) {
  float sa = sinf(angle_el), ca = cosf(angle_el);
  float Ualpha = -Uq*sa, Ubeta  = Uq*ca;
  float Ua = Ualpha + 0.5f*Vdc, Ub = (1.7320508f*Ubeta - Ualpha)*0.5f + 0.5f*Vdc, Uc = -(Ualpha + 1.7320508f*Ubeta)*0.5f + 0.5f*Vdc;
  uint32_t ARR = __HAL_TIM_GET_AUTORELOAD(&htim2);
  __HAL_TIM_SET_COMPARE(&htim2, TIM_CHANNEL_1, (uint32_t)(sat01(Ua/Vdc)*ARR));
  __HAL_TIM_SET_COMPARE(&htim2, TIM_CHANNEL_2, (uint32_t)(sat01(Ub/Vdc)*ARR));
  __HAL_TIM_SET_COMPARE(&htim2, TIM_CHANNEL_3, (uint32_t)(sat01(Uc/Vdc)*ARR));
}

// [B12-aux] 读缓存电角：主循环按 1kHz 计算并写入，控制 ISR 只读
static inline float electric_angle_from_sensor(void){ return g_angle_el_cache; }


// [B12] 控制核心（10kHz 固定节拍）：c1 开环速度 / c3 位置闭环 / c2 电流闭环（含过流锁存/抗饱和）
static void control_step(void){
	/* 思路（控制主循环，固定频率=CTRL_HZ）：
 * - MODE_OL_SPEED：开环速度 -> 直接对电角积分 el_angle += ω_e*Ts，然后用固定Uq输出；
 * - MODE_CL_POS  ：位置闭环 -> 误差 = (目标rad - 机械累计rad)，位置PID输出Uq，再用“编码器推导的电角”来施加电压；
 * - MODE_CL_CURRENT：电流闭环 -> ADC两相电流 -> Clarke/Park -> dq双PI -> 限幅 -> 逆变换 -> 三相电压 -> SVPWM。
 * 把重活（sinf/sqrtf）放这里，但频率不要太高（当前尝试10kHz；如有卡顿可以先降到2~5kHz再升）。
 */
  switch(g_mode){
    case MODE_OL_SPEED: {
      float omega_e = (float)pole_pairs * (float)Dir * g_target;
      el_angle = norm2pi(el_angle + omega_e * Ts);
      set_phase_voltage(Uq_limit, el_angle);
    } break;
    case MODE_CL_POS: {
      float error = g_target - g_mech_angle;
      float Uq = pid_step(g_kp, g_ki, g_kd, error, Uq_limit);
      set_phase_voltage(Uq, electric_angle_from_sensor());
    } break;
    case MODE_CL_CURRENT: {
        /* 过流锁存：若触发，直接拉零输出，等待你切换模式或重新校准来清除 */
        if (fault_latched) {
            uint32_t ARR = __HAL_TIM_GET_AUTORELOAD(&htim2);
            __HAL_TIM_SET_COMPARE(&htim2, TIM_CHANNEL_1, 0);
            __HAL_TIM_SET_COMPARE(&htim2, TIM_CHANNEL_2, 0);
            __HAL_TIM_SET_COMPARE(&htim2, TIM_CHANNEL_3, 0);
            break;
        }

        /* 1) 读取两相ADC -> 去偏置 -> 换算成电流(A) */
        float va = (float)adc_last[0] * ADC_K - offset_a_V;
        float vb = (float)adc_last[1] * ADC_K - offset_b_V;
        ia_A = va * GAIN_A;  // A相
        ib_A = vb * GAIN_B;  // B相

        /* 过流检测（相电流任一超阈值即保护） */
        if (fabsf(ia_A) > I_TRIP || fabsf(ib_A) > I_TRIP) {
            fault_latched = 1;
            uint32_t ARR = __HAL_TIM_GET_AUTORELOAD(&htim2);
            __HAL_TIM_SET_COMPARE(&htim2, TIM_CHANNEL_1, 0);
            __HAL_TIM_SET_COMPARE(&htim2, TIM_CHANNEL_2, 0);
            __HAL_TIM_SET_COMPARE(&htim2, TIM_CHANNEL_3, 0);
            break;
        }

        /* 2) Clarke 输入（根据开关可交换相） */
        float ia = ia_A, ib = ib_A;
        if (cfg_swap_ab) { float tmp=ia; ia=ib; ib=tmp; }

        float Ialpha = ia;
        float Ibeta  = (ia + 2.0f*ib) * 0.57735027f; // 1/sqrt(3)

        /* 3) Park（角度 = 传感器角 + 可调偏置） */
        float angle_el = electric_angle_from_sensor() + angle_offset_el;
        float sa = sinf(angle_el), ca = cosf(angle_el);
        Id =  ca*Ialpha + sa*Ibeta;
        Iq = -sa*Ialpha + ca*Ibeta;

//        /* 如需 q 轴翻转，先在电流侧翻 */
//        if (cfg_flip_q) Iq = -Iq;

        /* 4) d/q 轴 PI（带积分限幅 + 反算抗饱和） */
        float err_d = 0.0f - Id;
        float err_q = Iq_ref - Iq;
        id_integral += id_ki * err_d * Ts;
        iq_integral += iq_ki * err_q * Ts;

        float Ud_unsat = id_kp * err_d + id_integral;
        float Uq_unsat = iq_kp * err_q + iq_integral;

        float mag = sqrtf(Ud_unsat*Ud_unsat + Uq_unsat*Uq_unsat);
        float Ud = Ud_unsat, Uq = Uq_unsat;
        sat_flag = 0;
        if (mag >= Uq_limit - 1e-3f) {
            float k = Uq_limit / (mag + 1e-6f);
            Ud *= k; Uq *= k; sat_flag = 1;
        }

        /* 反算抗饱和 */
        id_integral += (Ud - Ud_unsat);
        iq_integral += (Uq - Uq_unsat);

        float i_lim = Uq_limit;
        if (id_integral >  i_lim) id_integral =  i_lim;
        if (id_integral < -i_lim) id_integral = -i_lim;
        if (iq_integral >  i_lim) iq_integral =  i_lim;
        if (iq_integral < -i_lim) iq_integral = -i_lim;

        /* 若 q 轴翻转，电压侧也同步翻，保证几何一致 */
        if (cfg_flip_q) Uq = -Uq;

        /* 5) dq -> αβ -> 三相电压，写 CCR */
        float Ualpha =  ca*Ud - sa*Uq;
        float Ubeta  =  sa*Ud + ca*Uq;
        float Ua = Ualpha + 0.5f*Vdc;
        float Ub = (1.7320508f*Ubeta - Ualpha)*0.5f + 0.5f*Vdc;
        float Uc = -(Ualpha + 1.7320508f*Ubeta)*0.5f + 0.5f*Vdc;

        uint32_t ARR = __HAL_TIM_GET_AUTORELOAD(&htim2);
        __HAL_TIM_SET_COMPARE(&htim2, TIM_CHANNEL_1, (uint32_t)(sat01(Ua/Vdc)*ARR));
        __HAL_TIM_SET_COMPARE(&htim2, TIM_CHANNEL_2, (uint32_t)(sat01(Ub/Vdc)*ARR));
        __HAL_TIM_SET_COMPARE(&htim2, TIM_CHANNEL_3, (uint32_t)(sat01(Uc/Vdc)*ARR));

        Ud_dbg = Ud; Uq_dbg = Uq; Uabs_dbg = sqrtf(Ud*Ud + Uq*Uq);
    } break;
		case MODE_CL_SPEED: {
    // 速度误差 = 目标速度(rad/s) - 当前速度(rad/s)
    float error_vel = g_target - g_mech_velocity;
    
    // 速度PID（复用位置环的PID结构，用速度环参数）
    vel_i += vel_ki * 0.5f * Ts * (error_vel + vel_last_e);
    if (vel_i > Uq_limit) vel_i = Uq_limit;
    if (vel_i < -Uq_limit) vel_i = -Uq_limit;
    
    float d_term = vel_kd * (error_vel - vel_last_e) / Ts;
    float Uq = vel_kp * error_vel + vel_i + d_term;
    
    // 输出限幅
    if (Uq > Uq_limit) Uq = Uq_limit;
    if (Uq < -Uq_limit) Uq = -Uq_limit;
    vel_last_e = error_vel;
    
    // 使用编码器电角施加电压（与c3一致）
    set_phase_voltage(Uq, electric_angle_from_sensor());
} break;
  }
}


// [B12-ISR] TIM4 更新中断：每个 Ts 调一次 control_step() —— “固定计算时间”保证
void HAL_TIM_PeriodElapsedCallback(TIM_HandleTypeDef *htim){
  if(htim->Instance == TIM4){ control_step(); }
}


// [B8] 对齐零电角：给定向电压(θ=_3PI_2)吸附→稳读机械角→零电角=mech*pp*Dir→清状态
static void Align_ZeroElectricalAngle(void){
	/* 思路（对齐零电角）：
 * 1) 给 d 轴一个固定电压（用 _3PI_2 方向），让转子自动吸到这个电角方向；
 * 2) 连续稳定读取 AS5600 的机械角（get_stable_angle），记录此刻机械角；
 * 3) 推导“零电角” zero_elec_angle = mech * pole_pairs * Dir（再取 0~2π）
 * 4) 之后的电角都要减掉这个零点，保证控制和传感一致。
 * 注意：这一步必须在使能 PWM 之后、电机不被外力扰动时做。
 */
  uint32_t t0 = HAL_GetTick();
  while(HAL_GetTick()-t0 < 1500){ set_phase_voltage(1.0f, _3PI_2); }
  /* 使用新的可靠函数来获取零点角度 */
  float initial_angle = get_stable_angle();
  zero_elec_angle = norm2pi(initial_angle * pole_pairs * Dir);
  g_angle_el_cache = zero_elec_angle;
  set_phase_voltage(0.0f, 0.0f);
	  sat_flag = 0;          // 状态清干净（避免旧的限幅/故障状态影响对齐后的首个周期）
  fault_latched = 0;     // 
}


// [B10] 位置环 PID（梯形积分+前向差分+输出限幅+积分限幅），输出 Uq
static inline float pid_step(float kp,float ki,float kd,float e,float out_lim){
  pi_i += ki * 0.5f * Ts * (e + last_e);
  if(pi_i > out_lim) pi_i = out_lim; if(pi_i < -out_lim) pi_i = -out_lim;
  float d = kd * (e - last_e) / Ts;
  float u = kp*e + pi_i + d;
  if(u > out_lim) u = out_lim; if(u < -out_lim) u = -out_lim;
  last_e = e;
  return u;
}

// [B10-aux] 位置环重置：切模式/设定点变化时清积分，防突变
static void pid_reset(void) { 
    pi_i = 0.0f; 
    last_e = g_target - g_mech_angle;
    //重置速度环状态
    vel_i = 0.0f;
    vel_last_e = g_target - g_mech_velocity;
}

// [B11] 电流零偏校准：静止采样 N 次求平均 -> offset_a_V / offset_b_V
void current_offsets_calib(uint16_t rounds){
  uint32_t sum_a=0,sum_b=0;
  for(uint16_t i=0;i<rounds;i++){ sum_a+=adc_last[0]; sum_b+=adc_last[1]; HAL_Delay(1); }
  offset_a_V = (float)(sum_a/rounds)*ADC_K; offset_b_V = (float)(sum_b/rounds)*ADC_K;
}

static void update_cumulative_mechanical_angle(void) {
	/* 思路（机械角累计/解缠绕）：
 * - AS5600 原始角0~2π，需要把跨0/2π的“跳变”还原成连续曲线。
 * - 现在版本用 g_full_rotations 记录整圈数：当 Δθ 超过 π，就 ±2π 修正整圈数。
 *   这个写法能工作，但对偶发跳读略敏感。
 * - 稳妥替代（可选）：先把 Δθ 折返到 [-π,π]，再积分到 g_mech_angle（不维护整圈数）。
 *   先保留当前实现，因为现在 c3 已经正常；等把 c2 跑稳后再替换为“折返增量式”。
 */
	
//    // 只有在读取成功时才更新角度
//    float current_mech_angle = AS5600_ReadMechRad();
//    if (current_mech_angle < 0.0f) {
//        return; // 读取失败，直接返回，不更新任何值
//    }
//    
//    float delta_angle = current_mech_angle - g_last_mech_angle;
//    if (fabsf(delta_angle) > M_PI) {
//        if (delta_angle > 0) g_full_rotations -= TWO_PI;
//        else g_full_rotations += TWO_PI;
//    }
//    g_mech_angle = g_full_rotations + current_mech_angle;
//    g_last_mech_angle = current_mech_angle;
//}
// （可选替换）更稳妥的解缠绕

    float curr = AS5600_ReadMechRad();
    if (curr < 0.0f) return;             // 读失败就跳过
    float d = curr - g_last_mech_angle;
    if (d >  M_PI) d -= TWO_PI;
    if (d < -M_PI) d += TWO_PI;
    g_mech_angle += d;
    g_last_mech_angle = curr;
}

// [B7-1] 机械速度计算：数值微分 + 一阶低通滤波
static void update_mechanical_velocity(void) {
    const float dt = 0.001f;  // 主循环1kHz，dt=1ms
    float raw_vel = (g_mech_angle - g_last_angle_for_vel) / dt;
    // 一阶IIR低通滤波：y[n] = α*x[n] + (1-α)*y[n-1]
    g_mech_velocity = vel_lpf_alpha * raw_vel + (1.0f - vel_lpf_alpha) * g_mech_velocity;
    g_last_angle_for_vel = g_mech_angle;
}

// VOFA+ JustFloat 协议发送函数
static void vofa_send_data(void) {
    // 定义要发送的通道数据（最多可以8-10个通道）
    float data[16];
    
    // ===== 通用通道（所有模式都有） =====
    data[0] = g_target;          // CH0: 目标值(速度rad/s 或 位置rad 或 电流A)
    data[1] = g_mech_angle;      // CH1: 机械角度(rad)
    data[2] = g_mech_velocity;   // CH2: 机械速度(rad/s)
    data[3] = (g_mode == MODE_OL_SPEED) ? el_angle : g_angle_el_cache;  // CH3: 电角度(rad)
    
    // ===== 电流相关通道 =====
    data[4] = ia_A;              // CH4: A相电流(A)
    data[5] = ib_A;              // CH5: B相电流(A)
    data[6] = Id;                // CH6: d轴电流(A)
    data[7] = Iq;                // CH7: q轴电流(A)
    
    // ===== 电压相关通道 =====
    data[8] = Ud_dbg;            // CH8: d轴电压(V)
    data[9] = Uq_dbg;            // CH9: q轴电压(V)
    data[10] = Uabs_dbg;         // CH10: 电压幅值(V)
    
    // ===== 状态标志通道 =====
    data[11] = (float)sat_flag;      // CH11: 电压饱和标志
    data[12] = (float)fault_latched; // CH12: 过流保护标志
    data[13] = (float)g_mode;        // CH13: 当前控制模式(1/2/3/4)
    
    // ===== 预留通道（用于后续扩展） =====
    data[14] = 0.0f;             // CH14: 预留
    data[15] = 0.0f;             // CH15: 预留
    
    // JustFloat 协议帧尾：0x00 0x00 0x80 0x7f
    uint8_t tail[4] = {0x00, 0x00, 0x80, 0x7f};
    
    // 发送数据（浮点数组 + 帧尾）
    HAL_UART_Transmit(&huart1, (uint8_t*)data, sizeof(data), 10);
    HAL_UART_Transmit(&huart1, tail, 4, 10);
}




/* USER CODE END 0 */

/**
  * @brief  The application entry point.
  * @retval int
  */
int main(void)
{

  /* USER CODE BEGIN 1 */

  /* USER CODE END 1 */

  /* MCU Configuration--------------------------------------------------------*/

  /* Reset of all peripherals, Initializes the Flash interface and the Systick. */
  HAL_Init();

  /* USER CODE BEGIN Init */

  /* USER CODE END Init */

  /* Configure the system clock */
  SystemClock_Config();

  /* USER CODE BEGIN SysInit */

  /* USER CODE END SysInit */

  /* Initialize all configured peripherals */
  MX_GPIO_Init();
  MX_DMA_Init();
  MX_ADC1_Init();
  MX_I2C2_Init();
  MX_TIM2_Init();
  MX_TIM4_Init();
  MX_USART1_UART_Init();
  /* USER CODE BEGIN 2 */

	// [B13] 上电初始化流程（一次性）：启动 PWM/ADC+DMA/串口接收/EN -> 等 200ms -> 对齐零电角 -> 初始化解缠绕 -> 清 PID -> 启动 TIM4 ISR
	/* 初始化顺序：
 * 1) 启动三相PWM（TIM2 CH1/2/3）；
 * 2) 启动ADC DMA（两路电流），并做一次“电流偏置校准”；
 * 3) 启动串口中断接收（逐字节），EN脚拉高（允许驱动）；
 * 4) 稍等200ms后做零电角对齐 Align_ZeroElectricalAngle()；
 * 5) 用 get_stable_angle 初始化机械角累计器（last/mech 都置成当前角）；
 * 6) 清PID内部状态，最后启动 TIM4 中断（真正进入控制循环）。
 */
  HAL_TIM_PWM_Start(&htim2, TIM_CHANNEL_1);
  HAL_TIM_PWM_Start(&htim2, TIM_CHANNEL_2);
  HAL_TIM_PWM_Start(&htim2, TIM_CHANNEL_3);
  HAL_ADC_Start_DMA(&hadc1, (uint32_t*)adc_raw, 2);
  current_offsets_calib(800);
  HAL_UART_Receive_IT(&huart1, &rx_ch, 1);
  HAL_GPIO_WritePin(GPIOA, GPIO_PIN_8, GPIO_PIN_SET);
  HAL_Delay(200);
  Align_ZeroElectricalAngle();

  /* 为角度累加器举行“初始化仪式”时，也使用新函数 */
  float angle_curr = get_stable_angle();
  g_last_mech_angle = angle_curr;
  g_mech_angle = angle_curr;
//  float g_full_rotations = 0.0f; // 确保圈数为0

  pid_reset();
  HAL_TIM_Base_Start_IT(&htim4);

  
  /* USER CODE END 2 */

  /* Infinite loop */
  /* USER CODE BEGIN WHILE */
  while (1)
  {
			// [B14] 主循环（慢任务）：1kHz 读角+解缠绕+电角缓存；20Hz 状态打印（非阻塞串口）
		
				/* 主循环任务（低频）：
 * 1) 每1ms：读取AS5600并更新 g_mech_angle；同时推导“电角缓存” g_angle_el_cache；
 *    —— 控制中断直接用 g_angle_el_cache（避免中断里访问I2C）
 * 2) 每50ms：通过串口打印一次状态（模式/目标/当前位置等）
 * 注意：I2C读角设置了较短超时；读失败就跳过本次更新，不阻塞控制中断。
 */

    static uint32_t t_angle = 0;
    if (HAL_GetTick() - t_angle >= 1) { // ~1 kHz
      t_angle = HAL_GetTick();
      update_cumulative_mechanical_angle();
      /* 电角度的计算源必须与PID控制器的位置源(g_mech_angle)保持一致*/
		update_mechanical_velocity();  // 更新速度
      g_angle_el_cache = norm2pi(g_mech_angle * pole_pairs * Dir - zero_elec_angle);
    }

    static uint32_t t0=0;
if(HAL_GetTick()-t0 > 10){ // 20Hz，实际100Hz
    t0=HAL_GetTick();
    
    if (uart_output_mode == UART_MODE_VOFA) {
        // VOFA+ 模式：发送二进制波形数据
        vofa_send_data();
    } else {
        // 文本模式：发送可读状态信息
        char line[TX_BUFFER_SIZE];
        if (g_mode == MODE_CL_CURRENT) {
            snprintf(line,sizeof(line),
                     "S,mode=%d,Id=%.3f,Iq=%.3f,Ud=%.2f,Uq=%.2f,|U|=%.2f,sat=%d,fault=%d\r\n",
                     (int)g_mode, Id, Iq, Ud_dbg, Uq_dbg, Uabs_dbg, (int)sat_flag, (int)fault_latched);
        } else if (g_mode == MODE_CL_POS) {
            snprintf(line,sizeof(line), "S,mode=%d,Tgt=%.2f,Cur=%.2f\r\n", 
                     (int)g_mode, g_target, g_mech_angle);
        } else if (g_mode == MODE_CL_SPEED) {
            snprintf(line,sizeof(line), "S,mode=%d,TgtVel=%.2f,CurVel=%.2f\r\n",
                     (int)g_mode, g_target, g_mech_velocity);
        } else {
            snprintf(line,sizeof(line), "S,mode=%d,t=%.3f,el=%.3f\r\n", 
                     (int)g_mode, g_target, el_angle);
        }
        uart_safe_print(line);
    }
}
		 
		
		
    /* USER CODE END WHILE */

    /* USER CODE BEGIN 3 */
  }
  /* USER CODE END 3 */
}

/**
  * @brief System Clock Configuration
  * @retval None
  */
void SystemClock_Config(void)
{
  RCC_OscInitTypeDef RCC_OscInitStruct = {0};
  RCC_ClkInitTypeDef RCC_ClkInitStruct = {0};
  RCC_PeriphCLKInitTypeDef PeriphClkInit = {0};

  /** Initializes the RCC Oscillators according to the specified parameters
  * in the RCC_OscInitTypeDef structure.
  */
  RCC_OscInitStruct.OscillatorType = RCC_OSCILLATORTYPE_HSE;
  RCC_OscInitStruct.HSEState = RCC_HSE_ON;
  RCC_OscInitStruct.HSEPredivValue = RCC_HSE_PREDIV_DIV1;
  RCC_OscInitStruct.HSIState = RCC_HSI_ON;
  RCC_OscInitStruct.PLL.PLLState = RCC_PLL_ON;
  RCC_OscInitStruct.PLL.PLLSource = RCC_PLLSOURCE_HSE;
  RCC_OscInitStruct.PLL.PLLMUL = RCC_PLL_MUL9;
  if (HAL_RCC_OscConfig(&RCC_OscInitStruct) != HAL_OK)
  {
    Error_Handler();
  }

  /** Initializes the CPU, AHB and APB buses clocks
  */
  RCC_ClkInitStruct.ClockType = RCC_CLOCKTYPE_HCLK|RCC_CLOCKTYPE_SYSCLK
                              |RCC_CLOCKTYPE_PCLK1|RCC_CLOCKTYPE_PCLK2;
  RCC_ClkInitStruct.SYSCLKSource = RCC_SYSCLKSOURCE_PLLCLK;
  RCC_ClkInitStruct.AHBCLKDivider = RCC_SYSCLK_DIV1;
  RCC_ClkInitStruct.APB1CLKDivider = RCC_HCLK_DIV2;
  RCC_ClkInitStruct.APB2CLKDivider = RCC_HCLK_DIV1;

  if (HAL_RCC_ClockConfig(&RCC_ClkInitStruct, FLASH_LATENCY_2) != HAL_OK)
  {
    Error_Handler();
  }
  PeriphClkInit.PeriphClockSelection = RCC_PERIPHCLK_ADC;
  PeriphClkInit.AdcClockSelection = RCC_ADCPCLK2_DIV6;
  if (HAL_RCCEx_PeriphCLKConfig(&PeriphClkInit) != HAL_OK)
  {
    Error_Handler();
  }
}

/* USER CODE BEGIN 4 */

/* USER CODE END 4 */

/**
  * @brief  This function is executed in case of error occurrence.
  * @retval None
  */
void Error_Handler(void)
{
  /* USER CODE BEGIN Error_Handler_Debug */
  /* User can add his own implementation to report the HAL error return state */
  __disable_irq();
  while (1)
  {
  }
  /* USER CODE END Error_Handler_Debug */
}

#ifdef  USE_FULL_ASSERT
/**
  * @brief  Reports the name of the source file and the source line number
  *         where the assert_param error has occurred.
  * @param  file: pointer to the source file name
  * @param  line: assert_param error line source number
  * @retval None
  */
void assert_failed(uint8_t *file, uint32_t line)
{
  /* USER CODE BEGIN 6 */
  /* User can add his own implementation to report the file name and line number,
     ex: printf("Wrong parameters value: file %s on line %d\r\n", file, line) */
  /* USER CODE END 6 */
}
#endif /* USE_FULL_ASSERT */
