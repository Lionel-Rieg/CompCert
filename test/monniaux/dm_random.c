#include <stdint.h>

static uint32_t dm_random_uint32(void) {
  static uint32_t current=UINT32_C(0xDEADBEEF);
  current = ((uint64_t) current << 6) % UINT32_C(4294967291);
  return current;
}
