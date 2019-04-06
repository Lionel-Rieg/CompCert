#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>
#include "../clock.h"

typedef int data;
typedef unsigned index;

int my_bsearch (data *a, index n, data x) {
    index i = 0, j = n - 1;
    while (i <= j) {
        index k = (i + j) / 2;
        if (a[k] == x) {
            return k;
        }
        else if (a[k] < x) {
            i = k + 1;
        }
        else {
            j = k - 1;
        }
    }
    return -1;
}

void random_ascending_fill(data *a, index n) {
  unsigned r = 41;
  data v = 0;
  for(index i=0; i<n; i++) {
    a[i] = v;
    v++;
    if (r & 0x40000000) v++;
    r = r * 97 + 5;
  }
}

int main () {
  index n=5000;
  data *buf=malloc(n*sizeof(data));
  
  cycle_t timestamp1 = get_current_cycle();
  random_ascending_fill(buf, n);
  timestamp1 = get_current_cycle()-timestamp1;

  cycle_t timestamp2 = get_current_cycle();
  index pos = my_bsearch(buf, n, 1501);
  timestamp2 = get_current_cycle()-timestamp2;

  printf("position: %d\nrandom fill cycles: %" PRIu64 "\nsearch cycles: %" PRIu64 "\n", pos, timestamp1, timestamp2);
  
  free(buf);
}
