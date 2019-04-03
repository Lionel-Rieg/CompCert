#include <stdio.h>

int essai(int x, unsigned y, unsigned z) {
  return __builtin_ternary_uint(x, y, z);
}

int main() {
  printf("%d\n", essai(0, 42, 69));
  return 0;
}
