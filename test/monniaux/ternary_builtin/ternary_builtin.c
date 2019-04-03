#include <stdio.h>
#include <stdlib.h>

int main(int argc, char **argv) {
  int i=0;
  if (argc >= 2) i=atoi(argv[1]);
  printf("%ld\n", __builtin_ternary_int(i, 42, 69));
  printf("%f\n", __builtin_ternary_double(i, 42.0, 69.0));
  return 0;
}
