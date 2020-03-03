#include <stdint.h>

uint32_t madd(uint32_t a, uint32_t b, uint32_t c) {
  return a + b*c;
}

uint32_t maddimm(uint32_t a, uint32_t b) {
  return a + b*17113;
}

uint32_t madd2(uint32_t a, uint32_t b, uint32_t c) {
  return c + b*a;
}

uint64_t maddl(uint64_t a, uint64_t b, uint64_t c) {
  return a + b*c;
}

uint64_t maddlimm(uint64_t a, uint64_t b) {
  return a + b*17113;
}

uint64_t maddl2(uint64_t a, uint64_t b, uint64_t c) {
  return c + b*a;
}
