#include <stdint.h>
#include <stdio.h>
#include <inttypes.h>
#include "../clock.h"

typedef uint32_t data;

static inline int32_t ternary_int32(int32_t a, int32_t b, int32_t c) {
  return (((-((a) == 0)) & (c)) | ((-((a) != 0)) & (b)));
}
static inline uint32_t ternary_uint32(uint32_t a, uint32_t b, uint32_t c) {
  return ternary_int32(a, b, c);
}

#if defined(__COMPCERT__) && defined(__K1C__)
#define TERNARY(a, b, c) ternary_uint32((a), (b), (c))
#else
#define TERNARY(a, b, c) ((a) ? (b) : (c))
#endif

data silly_computation(void) {
  data x = 1;
  for(int i=0; i<10000; i++) {
     x = x * TERNARY(x & 0x100, 45561U, 337777U);
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
