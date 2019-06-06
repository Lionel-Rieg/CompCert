#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>
#include <inttypes.h>
#include "xor_and.h"
#include "../clock.h"

int main() {
  const unsigned m = 60, n = 31, p = 50;
  clock_prepare();
  xor_and *a = malloc(sizeof(xor_and) * m * n);
  xor_and_mat_random(m, n, a, n);
  xor_and *b = malloc(sizeof(xor_and) * n * p);
  xor_and_mat_random(n, p, b, p);
  
  xor_and *c1 = malloc(sizeof(xor_and) * m * p);
  cycle_t c1_time = get_current_cycle();
  xor_and_mat_mul1(m, n, p, c1, p, a, n, b, p);
  c1_time = get_current_cycle()-c1_time;
  
  xor_and *c2 = malloc(sizeof(xor_and) * m * p);
  cycle_t c2_time = get_current_cycle();
  xor_and_mat_mul2(m, n, p, c2, p, a, n, b, p);
  c2_time = get_current_cycle()-c2_time;
  
  xor_and *c3 = malloc(sizeof(xor_and) * m * p);
  cycle_t c3_time = get_current_cycle();
  xor_and_mat_mul3(m, n, p, c3, p, a, n, b, p);
  c3_time = get_current_cycle()-c3_time;
  
  xor_and *c4 = malloc(sizeof(xor_and) * m * p);
  cycle_t c4_time = get_current_cycle();
  xor_and_mat_mul4(m, n, p, c4, p, a, n, b, p);
  c4_time = get_current_cycle()-c4_time;

  xor_and *c5 = malloc(sizeof(xor_and) * m * p);
  cycle_t c5_time = get_current_cycle();
  xor_and_mat_mul5(m, n, p, c5, p, a, n, b, p);
  c5_time = get_current_cycle()-c5_time;
  
  xor_and *c6 = malloc(sizeof(xor_and) * m * p);
  cycle_t c6_time = get_current_cycle();
  xor_and_mat_mul6(m, n, p, c6, p, a, n, b, p);
  c6_time = get_current_cycle()-c6_time;
  
  xor_and *c7 = malloc(sizeof(xor_and) * m * p);
  cycle_t c7_time = get_current_cycle();
  xor_and_mat_mul7(m, n, p, c7, p, a, n, b, p);
  c7_time = get_current_cycle()-c7_time;
  
  printf("c1==c2: %s\n"
	 "c1==c3: %s\n"
	 "c1==c4: %s\n"
	 "c1==c5: %s\n"
	 "c1==c6: %s\n"
	 "c1==c7: %s\n"
	 "c1_time = %" PRIu64 "\n"
	 "c2_time = %" PRIu64 "\n"
	 "c3_time = %" PRIu64 "\n"
	 "c4_time = %" PRIu64 "\n"
	 "c5_time = %" PRIu64 "\n"
	 "c6_time = %" PRIu64 "\n"
	 "c7_time = %" PRIu64 "\n",
	
	 xor_and_mat_equal(m, n, c1, p, c2, p)?"true":"false",
	 xor_and_mat_equal(m, n, c1, p, c3, p)?"true":"false",
	 xor_and_mat_equal(m, n, c1, p, c4, p)?"true":"false",
	 xor_and_mat_equal(m, n, c1, p, c5, p)?"true":"false",
	 xor_and_mat_equal(m, n, c1, p, c6, p)?"true":"false",
	 xor_and_mat_equal(m, n, c1, p, c7, p)?"true":"false",
	 
	 c1_time,
	 c2_time,
	 c3_time,
	 c4_time,
	 c5_time,
	 c6_time,
	 c7_time);
  
  free(a);
  free(b);
  free(c1);
  free(c2);
  free(c3);
  free(c4);
  free(c5);
  free(c6);
  free(c7);
  return 0;
}
