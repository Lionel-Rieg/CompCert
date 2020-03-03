#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>
#include "heapsort.h"
#include "../cycles.h"

int main (void) {
  cycle_count_config();
  unsigned len=30000;
  data *vec = malloc(sizeof(data) * len);
  data_vec_random(vec, len);
  cycle_t heapsort_time = get_cycle();
  heapsort(vec, len);
  heapsort_time = get_cycle() - heapsort_time;
  printf("sorted=%s\n"
	 "time cycles:%" PRIu64 "\n",
	 data_vec_is_sorted(vec, len)?"true":"false",
	 heapsort_time);
  free(vec);
  return 0;
}
 
