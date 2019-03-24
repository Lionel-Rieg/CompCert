#include <stdint.h>
#include <stdio.h>
#include <inttypes.h>
#include "../clock.h"

typedef uint32_t data;

data silly_computation(void) {
  data x = 1;
  for(int i=0; i<10000; i++) {
    x = x * (((x & 0x100) != 0) ? 45561U : 337777U);
  }
  return x;
}

int main() {
  clock_prepare();
  clock_start();
  data result = silly_computation();
  clock_stop();
  printf("result=%" PRIu32 "\ncycles=%" PRIu64 "\n", result, get_total_clock());
  return 0;
}
