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
	index kp1 = k+1, km1 = k-1;
	data ak = a[k];
	i = TERNARY32(ak < x, kp1, i);
	j = TERNARY32(ak > x, km1, j);
        if (ak == x) {
            return k;
        }
    }
    return -1;
}

int my_bsearch3 (data *a, index n, data x) {
  index i = 0, j = n - 1, k;
  k = (i + j) / 2;
  while (i <= j) {
    index kp1 = k+1, km1 = k-1;
    data ak = a[k];
    _Bool lt = ak < x, gt = ak > x;
    i = TERNARY32(lt, kp1, i);
    j = TERNARY32(gt, km1, j);
    if (ak == x) {
      goto end;
    }
    k = (i + j) / 2;
  }
  k=-1;
 end:
  return k;
}

void random_ascending_fill(data *a, index n) {
  unsigned r = 41;
  data v = 0;
  for(index i=0; i<n; i++) {
    a[i] = v;
    v++;
    v = TERNARY32(r & 0x40000000, v+1, v);
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

  my_bsearch(buf, n, v);
  cycle_t timestamp1 = get_current_cycle();
  index pos1 = my_bsearch(buf, n, v);
  timestamp1 = get_current_cycle()-timestamp1;

  cycle_t timestamp2 = get_current_cycle();
  index pos2 = my_bsearch2(buf, n, v);
  timestamp2 = get_current_cycle()-timestamp2;

  cycle_t timestamp3 = get_current_cycle();
  index pos3 = my_bsearch3(buf, n, v);
  timestamp3 = get_current_cycle()-timestamp3;

  printf("position1: %d\n"
	 "position2: %d\n"
	 "position3: %d\n"
	 "random fill cycles: %" PRIu64 "\n"
	 "search1 cycles: %" PRIu64 "\n"
	 "search2 cycles: %" PRIu64 "\n"
	 "search3 cycles: %" PRIu64 "\n",
	 pos1, pos2, pos3,
	 timestamp0, timestamp1, timestamp2, timestamp3);
  
  free(buf);
}
