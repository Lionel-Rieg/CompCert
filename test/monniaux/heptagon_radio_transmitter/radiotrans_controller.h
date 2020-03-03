/* --- Generated the 13/5/2019 at 10:21 --- */
/* --- heptagon compiler, version 1.05.00 (compiled mon. may. 13 10:18:8 CET 2019) --- */
/* --- Command line: /local/STATOR/packages/opam-root/4.07.1/bin/heptc -target c radiotrans_controller.ept --- */

#ifndef RADIOTRANS_CONTROLLER_H
#define RADIOTRANS_CONTROLLER_H

#include "radiotrans_controller_types.h"
#include "radiotrans.h"
typedef struct Radiotrans_controller__main_ctrlr0_out {
  int ok_a;
  int ok_r;
} Radiotrans_controller__main_ctrlr0_out;

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
                                             Radiotrans_controller__main_ctrlr0_out* _out);

#endif // RADIOTRANS_CONTROLLER_H
