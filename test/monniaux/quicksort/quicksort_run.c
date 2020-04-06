#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>
#include "quicksort.h"
#include "../cycles.h"

int main (void) {
  cycle_count_config();
  unsigned len=30000;
  data *vec = malloc(sizeof(data) * len);
  data_vec_random(vec, len);
  cycle_t quicksort_time = get_cycle();
  quicksort(vec, len);
  quicksort_time = get_cycle() - quicksort_time;
  printf("sorted=%s\n"
	 "time cycles:%" PRcycle "\n",
	 data_vec_is_sorted(vec, len)?"true":"false",
	 quicksort_time);
  free(vec);
  return 0;
}
 
