#include <stdio.h>

int main() {
  unsigned long a = 0x12345678ABCDEFUL, b=0x12345118ABCD32UL, c;
  c = __builtin_k1_sbmm8(a, b);
  printf("%lx\n", c);
  return 0;
}
