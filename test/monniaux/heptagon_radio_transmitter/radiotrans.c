/* --- Generated the 13/5/2019 at 10:21 --- */
/* --- heptagon compiler, version 1.05.00 (compiled mon. may. 13 10:18:8 CET 2019) --- */
/* --- Command line: /local/STATOR/packages/opam-root/4.07.1/bin/heptc -target c -hepts -s main -target ctrln radiotrans.ept --- */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include "radiotrans.h"

void Radiotrans__transceiver_reset(Radiotrans__transceiver_mem* self) {
  self->ck = Radiotrans__St_Idle;
  self->pnr = false;
}

void Radiotrans__transceiver_step(int enter_tx, int enter_rx, int exit_rx,
                                  int calibrate, int sleep, int wake_up,
                                  int irq_tx_done, int irq_on_packet,
                                  int irq_end_of_packet,
                                  int irq_end_of_calibration,
                                  int irq_fifo_threshold, int ok,
                                  Radiotrans__transceiver_out* _out,
                                  Radiotrans__transceiver_mem* self) {
  
  int v_2;
  Radiotrans__st v_1;
  int v;
  int v_3;
  int v_13;
  Radiotrans__st v_12;
  int v_11;
  Radiotrans__st v_10;
  int v_9;
  Radiotrans__st v_8;
  int v_7;
  int v_6;
  int v_5;
  int v_4;
  int nr_St_Rx_Packet;
  Radiotrans__st ns_St_Rx_Packet;
  int red_St_Rx_Packet;
  int nr_St_Rx;
  Radiotrans__st ns_St_Rx;
  int red_St_Rx;
  int nr_St_Sleep;
  Radiotrans__st ns_St_Sleep;
  int red_St_Sleep;
  int nr_St_Calibrate;
  Radiotrans__st ns_St_Calibrate;
  int red_St_Calibrate;
  int nr_St_Tx;
  Radiotrans__st ns_St_Tx;
  int red_St_Tx;
  int nr_St_Idle;
  Radiotrans__st ns_St_Idle;
  int red_St_Idle;
  Radiotrans__st ns;
  int r;
  int nr;
  r = self->pnr;
  switch (self->ck) {
    case Radiotrans__St_Rx_Packet:
      if (irq_end_of_packet) {
        ns_St_Rx_Packet = Radiotrans__St_Idle;
        nr_St_Rx_Packet = true;
      } else {
        ns_St_Rx_Packet = Radiotrans__St_Rx_Packet;
        nr_St_Rx_Packet = false;
      };
      red_St_Rx_Packet = true;
      ns = ns_St_Rx_Packet;
      nr = nr_St_Rx_Packet;
      _out->red = red_St_Rx_Packet;
      break;
    case Radiotrans__St_Rx:
      v = (exit_rx&&ok);
      if (v) {
        v_1 = Radiotrans__St_Idle;
      } else {
        v_1 = Radiotrans__St_Rx;
      };
      if (irq_on_packet) {
        ns_St_Rx = Radiotrans__St_Rx_Packet;
      } else {
        ns_St_Rx = v_1;
      };
      if (v) {
        v_2 = true;
      } else {
        v_2 = false;
      };
      if (irq_on_packet) {
        nr_St_Rx = true;
      } else {
        nr_St_Rx = v_2;
      };
      red_St_Rx = true;
      ns = ns_St_Rx;
      nr = nr_St_Rx;
      _out->red = red_St_Rx;
      break;
    case Radiotrans__St_Sleep:
      v_3 = (wake_up&&ok);
      if (v_3) {
        ns_St_Sleep = Radiotrans__St_Idle;
        nr_St_Sleep = true;
      } else {
        ns_St_Sleep = Radiotrans__St_Sleep;
        nr_St_Sleep = false;
      };
      red_St_Sleep = false;
      ns = ns_St_Sleep;
      nr = nr_St_Sleep;
      _out->red = red_St_Sleep;
      break;
    case Radiotrans__St_Calibrate:
      if (irq_end_of_calibration) {
        ns_St_Calibrate = Radiotrans__St_Idle;
        nr_St_Calibrate = true;
      } else {
        ns_St_Calibrate = Radiotrans__St_Calibrate;
        nr_St_Calibrate = false;
      };
      red_St_Calibrate = false;
      ns = ns_St_Calibrate;
      nr = nr_St_Calibrate;
      _out->red = red_St_Calibrate;
      break;
    case Radiotrans__St_Tx:
      if (irq_tx_done) {
        ns_St_Tx = Radiotrans__St_Idle;
        nr_St_Tx = true;
      } else {
        ns_St_Tx = Radiotrans__St_Tx;
        nr_St_Tx = false;
      };
      red_St_Tx = true;
      ns = ns_St_Tx;
      nr = nr_St_Tx;
      _out->red = red_St_Tx;
      break;
    case Radiotrans__St_Idle:
      v_4 = (enter_tx&&ok);
      v_5 = (calibrate&&ok);
      v_6 = (sleep&&ok);
      v_7 = (enter_rx&&ok);
      if (v_7) {
        v_8 = Radiotrans__St_Rx;
      } else {
        v_8 = Radiotrans__St_Idle;
      };
      if (v_6) {
        v_10 = Radiotrans__St_Sleep;
      } else {
        v_10 = v_8;
      };
      if (v_5) {
        v_12 = Radiotrans__St_Calibrate;
      } else {
        v_12 = v_10;
      };
      if (v_4) {
        ns_St_Idle = Radiotrans__St_Tx;
      } else {
        ns_St_Idle = v_12;
      };
      ns = ns_St_Idle;
      if (v_7) {
        v_9 = true;
      } else {
        v_9 = false;
      };
      if (v_6) {
        v_11 = true;
      } else {
        v_11 = v_9;
      };
      if (v_5) {
        v_13 = true;
      } else {
        v_13 = v_11;
      };
      if (v_4) {
        nr_St_Idle = true;
      } else {
        nr_St_Idle = v_13;
      };
      nr = nr_St_Idle;
      red_St_Idle = false;
      _out->red = red_St_Idle;
      break;
    default:
      break;
  };
  self->ck = ns;
  self->pnr = nr;;
}

void Radiotrans__adc_reset(Radiotrans__adc_mem* self) {
  self->ck = Radiotrans__St_1_Off;
  self->pnr = false;
}

void Radiotrans__adc_step(int adc_on, int adc_off, int ok,
                          Radiotrans__adc_out* _out,
                          Radiotrans__adc_mem* self) {
  
  int v;
  int v_14;
  int nr_St_1_On;
  Radiotrans__st_1 ns_St_1_On;
  int o_St_1_On;
  int nr_St_1_Off;
  Radiotrans__st_1 ns_St_1_Off;
  int o_St_1_Off;
  Radiotrans__st_1 ns;
  int r;
  int nr;
  r = self->pnr;
  switch (self->ck) {
    case Radiotrans__St_1_On:
      v = (adc_off&&ok);
      if (v) {
        ns_St_1_On = Radiotrans__St_1_Off;
        nr_St_1_On = true;
      } else {
        ns_St_1_On = Radiotrans__St_1_On;
        nr_St_1_On = false;
      };
      o_St_1_On = true;
      ns = ns_St_1_On;
      nr = nr_St_1_On;
      _out->o = o_St_1_On;
      break;
    case Radiotrans__St_1_Off:
      v_14 = (adc_on&&ok);
      if (v_14) {
        ns_St_1_Off = Radiotrans__St_1_On;
      } else {
        ns_St_1_Off = Radiotrans__St_1_Off;
      };
      ns = ns_St_1_Off;
      if (v_14) {
        nr_St_1_Off = true;
      } else {
        nr_St_1_Off = false;
      };
      nr = nr_St_1_Off;
      o_St_1_Off = false;
      _out->o = o_St_1_Off;
      break;
    default:
      break;
  };
  self->ck = ns;
  self->pnr = nr;;
}

void Radiotrans__main_reset(Radiotrans__main_mem* self) {
  self->ck = Radiotrans__St_3_Idle;
  self->pnr_1 = false;
  self->ck_1 = Radiotrans__St_2_Off;
  self->pnr = false;
}

void Radiotrans__main_step(int enter_tx, int enter_rx, int exit_rx,
                           int calibrate, int sleep, int wake_up,
                           int irq_tx_done, int irq_on_packet,
                           int irq_end_of_packet, int irq_end_of_calibration,
                           int irq_fifo_threshold, int adc_on, int adc_off,
                           Radiotrans__main_out* _out,
                           Radiotrans__main_mem* self) {
  Radiotrans_controller__main_ctrlr0_out Radiotrans_controller__main_ctrlr0_out_st;
  
  int v_15;
  int v;
  int ok_r;
  int ok_a;
  int v_18;
  Radiotrans__st_3 v_17;
  int v_16;
  int v_19;
  int v_29;
  Radiotrans__st_3 v_28;
  int v_27;
  Radiotrans__st_3 v_26;
  int v_25;
  Radiotrans__st_3 v_24;
  int v_23;
  int v_22;
  int v_21;
  int v_20;
  int nr_1_St_3_Rx_Packet;
  Radiotrans__st_3 ns_1_St_3_Rx_Packet;
  int red_1_St_3_Rx_Packet;
  int nr_1_St_3_Rx;
  Radiotrans__st_3 ns_1_St_3_Rx;
  int red_1_St_3_Rx;
  int nr_1_St_3_Sleep;
  Radiotrans__st_3 ns_1_St_3_Sleep;
  int red_1_St_3_Sleep;
  int nr_1_St_3_Calibrate;
  Radiotrans__st_3 ns_1_St_3_Calibrate;
  int red_1_St_3_Calibrate;
  int nr_1_St_3_Tx;
  Radiotrans__st_3 ns_1_St_3_Tx;
  int red_1_St_3_Tx;
  int nr_1_St_3_Idle;
  Radiotrans__st_3 ns_1_St_3_Idle;
  int red_1_St_3_Idle;
  int v_30;
  int v_31;
  int nr_St_2_On;
  Radiotrans__st_2 ns_St_2_On;
  int o_St_2_On;
  int nr_St_2_Off;
  Radiotrans__st_2 ns_St_2_Off;
  int o_St_2_Off;
  Radiotrans__st_3 ns_1;
  int r_1;
  int nr_1;
  Radiotrans__st_2 ns;
  int r;
  int nr;
  int adc_on_1;
  int adc_off_1;
  int ok_1;
  int o;
  int enter_tx_1;
  int enter_rx_1;
  int exit_rx_1;
  int calibrate_1;
  int sleep_1;
  int wake_up_1;
  int irq_tx_done_1;
  int irq_on_packet_1;
  int irq_end_of_packet_1;
  int irq_end_of_calibration_1;
  int irq_fifo_threshold_1;
  int ok;
  int red_1;
  r_1 = self->pnr_1;
  irq_fifo_threshold_1 = irq_fifo_threshold;
  irq_end_of_calibration_1 = irq_end_of_calibration;
  irq_end_of_packet_1 = irq_end_of_packet;
  irq_on_packet_1 = irq_on_packet;
  irq_tx_done_1 = irq_tx_done;
  wake_up_1 = wake_up;
  sleep_1 = sleep;
  calibrate_1 = calibrate;
  exit_rx_1 = exit_rx;
  enter_rx_1 = enter_rx;
  enter_tx_1 = enter_tx;
  r = self->pnr;
  adc_off_1 = adc_off;
  adc_on_1 = adc_on;
  switch (self->ck) {
    case Radiotrans__St_3_Rx_Packet:
      if (irq_end_of_packet_1) {
        ns_1_St_3_Rx_Packet = Radiotrans__St_3_Idle;
        nr_1_St_3_Rx_Packet = true;
      } else {
        ns_1_St_3_Rx_Packet = Radiotrans__St_3_Rx_Packet;
        nr_1_St_3_Rx_Packet = false;
      };
      red_1_St_3_Rx_Packet = true;
      red_1 = red_1_St_3_Rx_Packet;
      break;
    case Radiotrans__St_3_Rx:
      red_1_St_3_Rx = true;
      red_1 = red_1_St_3_Rx;
      break;
    case Radiotrans__St_3_Sleep:
      red_1_St_3_Sleep = false;
      red_1 = red_1_St_3_Sleep;
      break;
    case Radiotrans__St_3_Calibrate:
      if (irq_end_of_calibration_1) {
        ns_1_St_3_Calibrate = Radiotrans__St_3_Idle;
        nr_1_St_3_Calibrate = true;
      } else {
        ns_1_St_3_Calibrate = Radiotrans__St_3_Calibrate;
        nr_1_St_3_Calibrate = false;
      };
      red_1_St_3_Calibrate = false;
      red_1 = red_1_St_3_Calibrate;
      break;
    case Radiotrans__St_3_Tx:
      if (irq_tx_done_1) {
        ns_1_St_3_Tx = Radiotrans__St_3_Idle;
        nr_1_St_3_Tx = true;
      } else {
        ns_1_St_3_Tx = Radiotrans__St_3_Tx;
        nr_1_St_3_Tx = false;
      };
      red_1_St_3_Tx = true;
      red_1 = red_1_St_3_Tx;
      break;
    case Radiotrans__St_3_Idle:
      red_1_St_3_Idle = false;
      red_1 = red_1_St_3_Idle;
      break;
    default:
      break;
  };
  _out->red = red_1;
  switch (self->ck_1) {
    case Radiotrans__St_2_On:
      o_St_2_On = true;
      o = o_St_2_On;
      break;
    case Radiotrans__St_2_Off:
      o_St_2_Off = false;
      o = o_St_2_Off;
      break;
    default:
      break;
  };
  _out->a_on = o;
  Radiotrans_controller__main_ctrlr0_step(adc_off, adc_on, calibrate,
                                          self->ck, self->ck_1, enter_rx,
                                          enter_tx, exit_rx,
                                          irq_end_of_calibration,
                                          irq_end_of_packet,
                                          irq_fifo_threshold, irq_on_packet,
                                          irq_tx_done, self->pnr,
                                          self->pnr_1, sleep, wake_up,
                                          &Radiotrans_controller__main_ctrlr0_out_st);
  ok_a = Radiotrans_controller__main_ctrlr0_out_st.ok_a;
  ok_r = Radiotrans_controller__main_ctrlr0_out_st.ok_r;
  ok = ok_r;
  ok_1 = ok_a;
  switch (self->ck) {
    case Radiotrans__St_3_Rx:
      v_16 = (exit_rx_1&&ok);
      if (v_16) {
        v_17 = Radiotrans__St_3_Idle;
      } else {
        v_17 = Radiotrans__St_3_Rx;
      };
      if (irq_on_packet_1) {
        ns_1_St_3_Rx = Radiotrans__St_3_Rx_Packet;
      } else {
        ns_1_St_3_Rx = v_17;
      };
      if (v_16) {
        v_18 = true;
      } else {
        v_18 = false;
      };
      if (irq_on_packet_1) {
        nr_1_St_3_Rx = true;
      } else {
        nr_1_St_3_Rx = v_18;
      };
      ns_1 = ns_1_St_3_Rx;
      nr_1 = nr_1_St_3_Rx;
      break;
    case Radiotrans__St_3_Sleep:
      v_19 = (wake_up_1&&ok);
      if (v_19) {
        ns_1_St_3_Sleep = Radiotrans__St_3_Idle;
        nr_1_St_3_Sleep = true;
      } else {
        ns_1_St_3_Sleep = Radiotrans__St_3_Sleep;
        nr_1_St_3_Sleep = false;
      };
      ns_1 = ns_1_St_3_Sleep;
      nr_1 = nr_1_St_3_Sleep;
      break;
    case Radiotrans__St_3_Idle:
      v_20 = (enter_tx_1&&ok);
      v_21 = (calibrate_1&&ok);
      v_22 = (sleep_1&&ok);
      v_23 = (enter_rx_1&&ok);
      if (v_23) {
        v_24 = Radiotrans__St_3_Rx;
      } else {
        v_24 = Radiotrans__St_3_Idle;
      };
      if (v_22) {
        v_26 = Radiotrans__St_3_Sleep;
      } else {
        v_26 = v_24;
      };
      if (v_21) {
        v_28 = Radiotrans__St_3_Calibrate;
      } else {
        v_28 = v_26;
      };
      if (v_20) {
        ns_1_St_3_Idle = Radiotrans__St_3_Tx;
      } else {
        ns_1_St_3_Idle = v_28;
      };
      ns_1 = ns_1_St_3_Idle;
      if (v_23) {
        v_25 = true;
      } else {
        v_25 = false;
      };
      if (v_22) {
        v_27 = true;
      } else {
        v_27 = v_25;
      };
      if (v_21) {
        v_29 = true;
      } else {
        v_29 = v_27;
      };
      if (v_20) {
        nr_1_St_3_Idle = true;
      } else {
        nr_1_St_3_Idle = v_29;
      };
      nr_1 = nr_1_St_3_Idle;
      break;
    case Radiotrans__St_3_Rx_Packet:
      ns_1 = ns_1_St_3_Rx_Packet;
      nr_1 = nr_1_St_3_Rx_Packet;
      break;
    case Radiotrans__St_3_Calibrate:
      ns_1 = ns_1_St_3_Calibrate;
      nr_1 = nr_1_St_3_Calibrate;
      break;
    case Radiotrans__St_3_Tx:
      ns_1 = ns_1_St_3_Tx;
      nr_1 = nr_1_St_3_Tx;
      break;
    default:
      break;
  };
  switch (self->ck_1) {
    case Radiotrans__St_2_On:
      v_30 = (adc_off_1&&ok_1);
      if (v_30) {
        ns_St_2_On = Radiotrans__St_2_Off;
        nr_St_2_On = true;
      } else {
        ns_St_2_On = Radiotrans__St_2_On;
        nr_St_2_On = false;
      };
      ns = ns_St_2_On;
      nr = nr_St_2_On;
      break;
    case Radiotrans__St_2_Off:
      v_31 = (adc_on_1&&ok_1);
      if (v_31) {
        ns_St_2_Off = Radiotrans__St_2_On;
      } else {
        ns_St_2_Off = Radiotrans__St_2_Off;
      };
      ns = ns_St_2_Off;
      if (v_31) {
        nr_St_2_Off = true;
      } else {
        nr_St_2_Off = false;
      };
      nr = nr_St_2_Off;
      break;
    default:
      break;
  };
  self->ck = ns_1;
  self->pnr_1 = nr_1;
  self->ck_1 = ns;
  self->pnr = nr;
  v = (_out->a_on&&_out->red);
  v_15 = !(v);;
}

