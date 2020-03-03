#include <stdio.h>

unsigned get_size(void) {
  return 12;
}

void print_array(unsigned n, const int *t) {
  for(unsigned i=0; i<n; i++) {
    printf("%d\n", t[i]);
  }
}
