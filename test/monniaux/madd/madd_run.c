#include <stdio.h>
#include <stdint.h>

extern uint32_t madd(uint32_t a, uint32_t b, uint32_t c);
extern uint64_t maddl(uint64_t a, uint64_t b, uint64_t c);

int main() {
  unsigned a = 7, b = 3, c = 4;
  printf("res = %u %lu\n", madd(a, b, c), maddl(a, b, c));
  return 0;
}
