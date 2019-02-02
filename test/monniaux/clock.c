#include "cycles.h"
#include <stdio.h>

static cycle_t total_clock, last_start;

void clock_prepare(void) {
  cycle_count_config();
}

void clock_start(void) {
  last_start = get_cycle();
}

void clock_stop(void) {
  total_clock += get_cycle() - last_start;
}

cycle_t get_total_clock(void) {
  return total_clock;
}

void print_total_clock(void) {
  printf("cycles: %lu\n", total_clock);
}

void printerr_total_clock(void) {
  fprintf(stderr, "cycles: %lu\n", total_clock);
}
