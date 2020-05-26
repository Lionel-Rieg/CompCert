#include <stdio.h>

int main() {
  {
    unsigned long a = 0x12345678ABCDEFUL, b=0x12345118ABCD32UL, c;
    c = __builtin_kvx_sbmm8(a, b);
    printf("%lx\n", c);
  }
  {
    unsigned long a = 0x0102040810204080UL, b=0x12345118ABCD32UL, c;
    c = __builtin_kvx_sbmm8(a, b);
    printf("%lx\n", c);
  }
  return 0;
}
