#include <stdio.h>
#include <stdlib.h>
#include "../clock.h"

typedef unsigned char data;

/* 8 cycles / iteration */
void fill_buffer(data x, unsigned n, data *buf) {
  for(unsigned i=0; i<n; i++) buf[i] = x;
}

/* 7 cycles / iteration */
void fill_buffer2(data x, unsigned n, data *buf) {
  unsigned i=0;
  if (i<n) {
    do {
       buf[i] = x;
      i++;
    } while (i<n);
  }
}

void fill_buffer10(data x, data *buf) {
  for(unsigned i=0; i<10; i++) buf[i] = x;
}

int main() {
  const size_t n = 10000;
  data *buf = malloc(n * sizeof(data));
  clock_prepare();
  clock_start();
  fill_buffer(42, n, buf);
  clock_stop();
  free(buf);
  print_total_clock();
  return 0;
}
