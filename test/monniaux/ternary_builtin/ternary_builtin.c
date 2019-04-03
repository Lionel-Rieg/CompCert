#include <stdio.h>

unsigned essai(int x, unsigned y, unsigned z) {
  return __builtin_ternary_uint(x, y, z);
}

unsigned long essai2(int x, unsigned long y, unsigned long z) {
  return __builtin_ternary_ulong(x, y, z);
}

int main() {
  printf("%ld\n", essai2(0, 42, 69));
  return 0;
}
