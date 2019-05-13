/* --- Generated the 13/5/2019 at 10:21 --- */
/* --- heptagon compiler, version 1.05.00 (compiled mon. may. 13 10:18:8 CET 2019) --- */
/* --- Command line: /local/STATOR/packages/opam-root/4.07.1/bin/heptc -target c -hepts -s main -target ctrln radiotrans.ept --- */

#ifndef RADIOTRANS_H
#define RADIOTRANS_H

#include "radiotrans_types.h"
#include "radiotrans_controller.h"
typedef struct Radiotrans__transceiver_mem {
  Radiotrans__st ck;
  int pnr;
} Radiotrans__transceiver_mem;

typedef struct Radiotrans__transceiver_out {
  int red;
} Radiotrans__transceiver_out;

void Radiotrans__transceiver_reset(Radiotrans__transceiver_mem* self);

void Radiotrans__transceiver_step(int enter_tx, int enter_rx, int exit_rx,
                                  int calibrate, int sleep, int wake_up,
                                  int irq_tx_done, int irq_on_packet,
                                  int irq_end_of_packet,
                                  int irq_end_of_calibration,
                                  int irq_fifo_threshold, int ok,
                                  Radiotrans__transceiver_out* _out,
                                  Radiotrans__transceiver_mem* self);

typedef struct Radiotrans__adc_mem {
  Radiotrans__st_1 ck;
  int pnr;
} Radiotrans__adc_mem;

typedef struct Radiotrans__adc_out {
  int o;
} Radiotrans__adc_out;

void Radiotrans__adc_reset(Radiotrans__adc_mem* self);

void Radiotrans__adc_step(int adc_on, int adc_off, int ok,
                          Radiotrans__adc_out* _out,
                          Radiotrans__adc_mem* self);

typedef struct Radiotrans__main_mem {
  Radiotrans__st_3 ck;
  Radiotrans__st_2 ck_1;
  int pnr_1;
  int pnr;
} Radiotrans__main_mem;

typedef struct Radiotrans__main_out {
  int a_on;
  int red;
} Radiotrans__main_out;

void Radiotrans__main_reset(Radiotrans__main_mem* self);

void Radiotrans__main_step(int enter_tx, int enter_rx, int exit_rx,
                           int calibrate, int sleep, int wake_up,
                           int irq_tx_done, int irq_on_packet,
                           int irq_end_of_packet, int irq_end_of_calibration,
                           int irq_fifo_threshold, int adc_on, int adc_off,
                           Radiotrans__main_out* _out,
                           Radiotrans__main_mem* self);

#endif // RADIOTRANS_H
