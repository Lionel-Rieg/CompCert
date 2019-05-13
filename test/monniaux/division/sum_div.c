#include <stdio.h>
#include <stdlib.h>
#include "../clock.h"
 
int main(int argc, char **argv) {
  unsigned modulus = argc < 2 ? 3371 : atoi(argv[1]);
  clock_prepare();
  clock_start();
  unsigned total=0, total_mod=0;
  for(int i=0; i<1000; i++) {
    total += i;
    total_mod = (total_mod + i)%modulus;
  }
  clock_stop();
  print_total_clock();
  printf("%u %u %d\n", total, total_mod, total%modulus == total_mod);
  return 0;
}
