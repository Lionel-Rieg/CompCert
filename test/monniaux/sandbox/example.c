#include <stdio.h>
#include "f.h"
#include "../cycles.h"

#if 0
int main(void){
  cycle_count_config();

  int i;
  int S = 0;

  TIMEINIT
  for (i = 0; i < 1000; i++){
    S += f(i, i*2);
  }
  TIMESTOP(0)

  printf("Final value: %d\n", S);
  TIMESTOP(1)

  TIMEPRINT(1)
  return 0;
}
#endif

#if 0
int main(void){
  cycle_count_config();

  TIMEINIT
  int a = 42;
  int b = 21;
  int c = 42+b;
  TIMESTOP(0)
  int d = a + b;
  int e = a + b + c + d;
  TIMESTOP(1)

  TIMEPRINT(1)
  return e;
}
#endif
