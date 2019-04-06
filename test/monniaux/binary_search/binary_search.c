#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>
#include "../clock.h"
#include "../ternary.h"

typedef int data;
typedef unsigned index;

/* from Rosetta code */
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

int my_bsearch2 (data *a, index n, data x) {
    index i = 0, j = n - 1;
    while (i <= j) {
        index k = (i + j) / 2;
        if (a[k] == x) {
            return k;
        }
	i = TERNARY32(a[k] < x, k+1, i);
	j = TERNARY32(a[k] > x, k-1, j);
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
  data v=1502;
  data *buf=malloc(n*sizeof(data));
  
  cycle_t timestamp0 = get_current_cycle();
  random_ascending_fill(buf, n);
  timestamp0 = get_current_cycle()-timestamp0;

  cycle_t timestamp1 = get_current_cycle();
  index pos1 = my_bsearch(buf, n, v);
  timestamp1 = get_current_cycle()-timestamp1;

  cycle_t timestamp2 = get_current_cycle();
  index pos2 = my_bsearch(buf, n, v);
  timestamp2 = get_current_cycle()-timestamp2;

  printf("position1: %d\n"
	 "position2: %d\n"
	 "random fill cycles: %" PRIu64 "\n"
	 "search1 cycles: %" PRIu64 "\n"
	 "search2 cycles: %" PRIu64 "\n",
	 pos1, pos2, timestamp0, timestamp1, timestamp2);
  
  free(buf);
}
