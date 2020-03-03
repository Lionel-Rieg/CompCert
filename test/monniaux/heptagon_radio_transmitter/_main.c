/* --- Generated the 13/5/2019 at 10:21 --- */
/* --- heptagon compiler, version 1.05.00 (compiled mon. may. 13 10:18:8 CET 2019) --- */
/* --- Command line: /local/STATOR/packages/opam-root/4.07.1/bin/heptc -target c -hepts -s main -target ctrln radiotrans.ept --- */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include "_main.h"
#include "../clock.h"
#include "../dm_random.c"

static inline int get_bool(void) {
  return dm_random_uint32() & 1;
}

Radiotrans__main_mem mem;
int main(int argc, char** argv) {
  int step_c;
  int step_max;
  int enter_tx;
  int enter_rx;
  int exit_rx;
  int calibrate;
  int sleep;
  int wake_up;
  int irq_tx_done;
  int irq_on_packet;
  int irq_end_of_packet;
  int irq_end_of_calibration;
  int irq_fifo_threshold;
  int adc_on;
  int adc_off;
  Radiotrans__main_out _res;
  step_c = 0;
  step_max = 1000;
  if ((argc==2)) {
    step_max = atoi(argv[1]);
  };

  clock_prepare();
  clock_start();
  Radiotrans__main_reset(&mem);
  while ((!(step_max)||(step_c<step_max))) {
    step_c = (step_c+1);

    enter_tx = get_bool();
    enter_rx = get_bool();
    exit_rx = get_bool();
    calibrate = get_bool();
    sleep = get_bool();
    wake_up = get_bool();
    irq_tx_done = get_bool();
    irq_on_packet = get_bool();
    irq_end_of_packet = get_bool();
    irq_end_of_calibration = get_bool();
    irq_fifo_threshold = get_bool();
    adc_on = get_bool();
    adc_off = get_bool();
    
    Radiotrans__main_step(enter_tx, enter_rx, exit_rx, calibrate, sleep,
                          wake_up, irq_tx_done, irq_on_packet,
                          irq_end_of_packet, irq_end_of_calibration,
                          irq_fifo_threshold, adc_on, adc_off, &_res, &mem);
#if 0
    printf("%d\n", _res.a_on);
    printf("%d\n", _res.red);
    fflush(stdout);
#endif
  };
  clock_stop();
  print_total_clock();
  return 0;
}

