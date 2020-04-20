#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>
#include <stdbool.h>
#include "glibc_qsort.h"
#include "../cycles.h"

typedef uint64_t data;

static data data_random(void) {
  static uint64_t next = 1325997111;
  next = next * 1103515249 + 12345;
  return next;
}

static void data_vec_random(data *a, unsigned len) {
  for(unsigned i=0; i<len; i++) {
    a[i] = data_random();
  }
}

static bool data_vec_is_sorted(const data *a, unsigned len) {
  for(unsigned i=0; i<len-1; i++) {
    if (a[i] > a[i+1]) return false;
  }
  return true;
}

static int data_compare(const void *px, const void *py, void *dummy) {
  data x = *((data*) px);
  data y = *((data*) py);
  return x < y ? -1 : (x > y ? 1 : 0);
}

int main (void) {
  cycle_count_config();
  unsigned len=3000;
  data *vec = malloc(sizeof(data) * len);
  data_vec_random(vec, len);
  cycle_t quicksort_time = get_cycle();
  quicksort(vec, len, sizeof(data), data_compare, NULL);
  quicksort_time = get_cycle() - quicksort_time;
  printf("sorted=%s\n"
	 "time cycles:%" PRIu64 "\n",
	 data_vec_is_sorted(vec, len)?"true":"false",
	 quicksort_time);
  free(vec);
  return 0;
}
