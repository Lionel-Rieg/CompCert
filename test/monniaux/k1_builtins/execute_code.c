#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef int fun_type(int x);

int poulet(int x) {
  return x*2;
}

int canard(int x) {
  return x*3;
}

#define SIZE 1024
int main() {
  void *buf=malloc(SIZE);
  memcpy(buf, poulet, SIZE);
  int rpoulet = (*((fun_type*) buf))(33);
  memcpy(buf, canard, SIZE);
  int rcanard = (*((fun_type*) buf))(33);
  __builtin_kvx_iinval();
  int rcanard2 = (*((fun_type*) buf))(33);
  free(buf);
  printf("%d %d %d\n", rpoulet, rcanard, rcanard2);
  return 0;
}
