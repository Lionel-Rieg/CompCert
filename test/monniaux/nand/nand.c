#include <stdio.h>

typedef unsigned long scalar;

scalar not(scalar x) {
  return ~x;
}

scalar nand(scalar x, scalar y) {
  return ~(x & y);
}

scalar nor(scalar x, scalar y) {
  return ~(x | y);
}

scalar nxor(scalar x, scalar y) {
  return ~(x ^ y);
}

scalar andn1(scalar x, scalar y) {
  return ~x & y;
}

scalar andn2(scalar x, scalar y) {
  return x & ~y;
}

scalar orn1(scalar x, scalar y) {
  return ~x | y;
}

scalar orn2(scalar x, scalar y) {
  return x | ~y;
}

scalar nandimm(scalar x) {
  return ~x & 45;
}

scalar notnot(scalar x) {
  return ~ ~ x;
}

int main() {
  scalar x = 0xF4, y = 0x33;
  printf("%X\n", nxor(x, y));
}
