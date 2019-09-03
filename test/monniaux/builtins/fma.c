#define COMPCERT_NO_FP_MACROS
#include <math.h>
#include <stdio.h>
#include <stdlib.h>

int main(int argc, char **argv) {
  if (argc < 4) return 1;
  double x = strtod(argv[1], NULL);
  double y = strtod(argv[2], NULL);
  double z = strtod(argv[3], NULL);
  printf("%g %g %g\n", __builtin_fma(x, y, z), fma(x, y, z), x*y + z);
  printf("%g %g %g\n", __builtin_fma(-x, y, z), fma(-x, y, z), (-x)*y + z);
  return 0;
}
