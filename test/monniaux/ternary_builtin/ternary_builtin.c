#include <stdio.h>
#include <stdlib.h>
#include "../ternary.h"

int main(int argc, char **argv) {
  int i=0;
  if (argc >= 2) i=atoi(argv[1]);
  printf("%d\n",ternary_uint32(i, 42, 69));
  return 0;
}
