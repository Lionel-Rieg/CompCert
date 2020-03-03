#include "heapsort.h"

/* Rosetta Code */
static inline int max (data *a, int n, int i, int j, int k) {
    int m = i;
    if (j < n && a[j] > a[m]) {
        m = j;
    }
    if (k < n && a[k] > a[m]) {
        m = k;
    }
    return m;
}
 
static void downheap (data *a, int n, int i) {
    while (1) {
        int j = max(a, n, i, 2 * i + 1, 2 * i + 2);
        if (j == i) {
            break;
        }
        data t = a[i];
        a[i] = a[j];
        a[j] = t;
        i = j;
    }
}
 
void heapsort (data *a, int n) {
    int i;
    for (i = (n - 2) / 2; i >= 0; i--) {
        downheap(a, n, i);
    }
    for (i = 0; i < n; i++) {
        data t = a[n - i - 1];
        a[n - i - 1] = a[0];
        a[0] = t;
        downheap(a, n - i - 1, 0);
    }
}

data data_random(void) {
  static uint64_t next = 1325997111;
  next = next * 1103515249 + 12345;
  return next;
}

void data_vec_random(data *a, unsigned len) {
  for(unsigned i=0; i<len; i++) {
    a[i] = data_random();
  }
}

bool data_vec_is_sorted(const data *a, unsigned len) {
  for(unsigned i=0; i<len-1; i++) {
    if (a[i] > a[i+1]) return false;
  }
  return true;
}
