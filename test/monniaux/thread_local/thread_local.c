#include <stdio.h>

_Thread_local int toto;
_Thread_local int toto2 = 45;

int foobar(void) {
  return toto;
}

int main() {
  printf("%d %d\n", toto, toto2);
  return 0;
}
