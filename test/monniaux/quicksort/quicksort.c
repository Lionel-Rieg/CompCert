#include "quicksort.h"

/* Rosetta Code */
void quicksort(data *A, int len) {
  if (len < 2) return;
 
  data pivot = A[len / 2];
 
  int i, j;
  for (i = 0, j = len - 1; ; i++, j--) {
    while (A[i] < pivot) i++;
    while (A[j] > pivot) j--;
 
    if (i >= j) break;
 
    data temp = A[i];
    A[i]     = A[j];
    A[j]     = temp;
  }
 
  quicksort(A, i);
  quicksort(A + i, len - i);
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
