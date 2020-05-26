#include <stdio.h>

int main() {
  long lval = 45;
  long lval2 = __builtin_kvx_afaddd(&lval, 6);
  printf("%ld %ld\n", lval, lval2);
  int ival = 45;
  int ival2 = __builtin_kvx_afaddw(&ival, 6);
  printf("%d %d\n", ival, ival2);
  return 0;
}
