#include <stdio.h>

extern unsigned madd(unsigned a, unsigned b, unsigned c);

int main() {
  unsigned a = 7, b = 3, c = 4;
  printf("res = %u\n", madd(a, b, c));
  return 0;
}
