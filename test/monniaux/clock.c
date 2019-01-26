#include "cycles.h"

static cycle_t total_clock, last_start;

void clock_start(void) {
  last_start = get_cycle();
}

void clock_stop(void) {
  total_clock += get_cycle() - last_start;
}

cycle_t get_total_clock(void) {
  return total_clock;
}
