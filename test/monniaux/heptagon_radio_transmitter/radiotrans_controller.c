/* --- Generated the 13/5/2019 at 10:21 --- */
/* --- heptagon compiler, version 1.05.00 (compiled mon. may. 13 10:18:8 CET 2019) --- */
/* --- Command line: /local/STATOR/packages/opam-root/4.07.1/bin/heptc -target c radiotrans_controller.ept --- */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include "radiotrans_controller.h"

void Radiotrans_controller__main_ctrlr0_step(int adc_off, int adc_on,
                                             int calibrate,
                                             Radiotrans__st_3 ck,
                                             Radiotrans__st_2 ck_1,
                                             int enter_rx, int enter_tx,
                                             int exit_rx,
                                             int irq_end_of_calibration,
                                             int irq_end_of_packet,
                                             int irq_fifo_threshold,
                                             int irq_on_packet,
                                             int irq_tx_done, int pnr,
                                             int pnr_1, int sleep,
                                             int wake_up,
                                             Radiotrans_controller__main_ctrlr0_out* _out) {
  
  int v_22;
  int v_21;
  int v_20;
  int v_19;
  int v_18;
  int v_17;
  int v_16;
  int v_15;
  int v_14;
  int v_13;
  int v_12;
  int v_11;
  int v_10;
  int v_9;
  int v_8;
  int v_7;
  int v_6;
  int v_5;
  int v_4;
  int v_3;
  int v_2;
  int v_1;
  int v;
  int l52;
  int l51;
  int l50;
  int l49;
  int l48;
  int l47;
  int l46;
  int l45;
  int l44;
  int l43;
  int l42;
  int l41;
  int l40;
  int l39;
  int l38;
  int l37;
  int l36;
  int l35;
  int l34;
  int l33;
  int l32;
  v_22 = (ck==Radiotrans__St_3_Rx_Packet);
  v_21 = !(adc_on);
  l51 = (v_21||irq_end_of_packet);
  v_20 = (ck==Radiotrans__St_3_Tx);
  v_19 = !(adc_on);
  l49 = (v_19||irq_tx_done);
  v_18 = (ck==Radiotrans__St_3_Rx);
  v_17 = !(adc_on);
  v_16 = !(adc_on);
  v_15 = !(adc_on);
  v_14 = !(irq_on_packet);
  l45 = (v_14||v_15);
  if (exit_rx) {
    l46 = l45;
  } else {
    l46 = v_16;
  };
  v_12 = (ck==Radiotrans__St_3_Idle);
  v_13 = !(v_12);
  v_11 = (ck_1==Radiotrans__St_2_On);
  v_9 = !(adc_on);
  v_8 = !(adc_on);
  v_7 = !(enter_tx);
  l38 = (v_7||v_8);
  if (sleep) {
    l39 = l38;
  } else {
    l39 = v_9;
  };
  if (enter_rx) {
    l40 = l39;
  } else {
    l40 = l38;
  };
  if (calibrate) {
    l41 = l38;
  } else {
    l41 = l40;
  };
  v_5 = (ck==Radiotrans__St_3_Rx);
  v_3 = (ck==Radiotrans__St_3_Calibrate);
  v_2 = (ck==Radiotrans__St_3_Sleep);
  v_4 = (v_2||v_3);
  v_6 = (v_4||v_5);
  v_1 = (ck_1==Radiotrans__St_2_Off);
  v = !(enter_tx);
  l32 = (v||adc_off);
  if (sleep) {
    l33 = l32;
  } else {
    l33 = adc_off;
  };
  if (enter_rx) {
    l34 = l33;
  } else {
    l34 = l32;
  };
  if (calibrate) {
    l35 = l32;
  } else {
    l35 = l34;
  };
  l36 = (v_1||l35);
  l37 = (v_6||l36);
  _out->ok_r = l37;
  if (_out->ok_r) {
    l47 = l46;
  } else {
    l47 = v_17;
  };
  v_10 = !(_out->ok_r);
  l42 = (v_10||l41);
  l43 = (v_11||l42);
  l44 = (v_13||l43);
  if (v_18) {
    l48 = l47;
  } else {
    l48 = l44;
  };
  if (v_20) {
    l50 = l49;
  } else {
    l50 = l48;
  };
  if (v_22) {
    l52 = l51;
  } else {
    l52 = l50;
  };
  _out->ok_a = l52;;
}

