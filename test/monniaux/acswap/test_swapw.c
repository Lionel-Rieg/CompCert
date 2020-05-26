#include <stdio.h>

int main() {
  unsigned loc=11, next=12, current=11;
  union {
    __int128 i128;
    struct {
      unsigned long low, high;
    } i64_2;
  } ret;
  ret.i128 = __builtin_kvx_acswapw(&loc, next, current);
  printf("%lx %lx\n", ret.i64_2.low, ret.i64_2.high);
}
