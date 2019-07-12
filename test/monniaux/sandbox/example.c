#include <stdio.h>
#include "f.h"
#include "../cycles.h"

int main(void){
  cycle_count_config();

  int i;
  int S = 0;

  TIMESTOP(0)
  for (i = 0; i < 1000; i++){
    S += f(i, i*2);
  }
  TIMESTOP(1)

  printf("Final value: %d\n", S);
  TIMESTOP(2)

  TIMEPRINT(2)
  return 0;
}
