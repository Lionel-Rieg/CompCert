#include <stdio.h>

unsigned rotate(unsigned x) {
  return (x << 4) | (x >> (32-4));
}

int main() {
  unsigned x = 0x12345678U;
  printf("%X %X\n", x, rotate(x));
}
