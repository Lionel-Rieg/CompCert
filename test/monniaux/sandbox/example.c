#include <stdio.h>
#include "f.h"

int main(void){
  int i;
  int S = 0;
  for (i = 0; i < 1000; i++){
    S += f(i, i*2);
  }

  printf("Final value: %d\n", S);
  return 0;
}
