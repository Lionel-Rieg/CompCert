#include <stdio.h>

int main() {
  char buf1[16], buf2[16];
  for(int i=0; i<16; i++) {
    buf1[i] = i;
  }
  for(int i=0; i<16; i++) {
    buf2[i] = 100+i;
  }
  __builtin_memcpy_aligned(buf1, buf2+3, 4, 1);
  for(int i=0; i<16; i++) {
    printf("%d : %d\n", i, buf1[i]);
  }
}
