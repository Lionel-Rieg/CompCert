#include <stdio.h>

unsigned not(unsigned x) {
  return ~x;
}

unsigned nand(unsigned x, unsigned y) {
  return ~(x & y);
}

unsigned nor(unsigned x, unsigned y) {
  return ~(x | y);
}

int main() {
  unsigned x = 0xF4, y = 0x33;
  printf("%X\n", nor(x, y));
}
