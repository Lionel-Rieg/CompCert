#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>
#include <inttypes.h>
#include "float_mat.h"
#include "../cycles.h"

/* FIXME DMonniaux should be in the other but branches and float_of_int not implemented */
bool REAL_mat_equal(unsigned m,
		      unsigned n,
		      const REAL *a, unsigned stride_a,
		      const REAL *b, unsigned stride_b) {
  for(unsigned i=0; i<m; i++) {
    for(unsigned j=0; j<n; j++) {
      if (a[i*stride_a + j] != b[i*stride_b + j]) return false;
    }
  }
  return true;
}

REAL REAL_random(void) {
  static uint64_t next = 1325997111;
  next = next * 1103515249 + 12345;
  return next % 1000;
}

void REAL_mat_random(unsigned m,
		       unsigned n,
		       REAL *a, unsigned stride_a) {
  for(unsigned i=0; i<m; i++) {
    for(unsigned j=0; j<n; j++) {
      a[i*stride_a + j] = REAL_random();
    }
  }
}

int main() {
  const unsigned m = 60, n = 31, p = 50;
  cycle_count_config();
  REAL *a = malloc(sizeof(REAL) * m * n);
  REAL_mat_random(m, n, a, n);
  REAL *b = malloc(sizeof(REAL) * n * p);
  REAL_mat_random(n, p, b, p);
  
  REAL *c1 = malloc(sizeof(REAL) * m * p);
  cycle_t c1_time = get_cycle();
  REAL_mat_mul1(m, n, p, c1, p, a, n, b, p);
  c1_time = get_cycle()-c1_time;
  
  REAL *c2 = malloc(sizeof(REAL) * m * p);
  cycle_t c2_time = get_cycle();
  REAL_mat_mul2(m, n, p, c2, p, a, n, b, p);
  c2_time = get_cycle()-c2_time;
  
  REAL *c3 = malloc(sizeof(REAL) * m * p);
  cycle_t c3_time = get_cycle();
  REAL_mat_mul3(m, n, p, c3, p, a, n, b, p);
  c3_time = get_cycle()-c3_time;
  
  REAL *c4 = malloc(sizeof(REAL) * m * p);
  cycle_t c4_time = get_cycle();
  REAL_mat_mul4(m, n, p, c4, p, a, n, b, p);
  c4_time = get_cycle()-c4_time;

  REAL *c5 = malloc(sizeof(REAL) * m * p);
  cycle_t c5_time = get_cycle();
  REAL_mat_mul5(m, n, p, c5, p, a, n, b, p);
  c5_time = get_cycle()-c5_time;
  
  REAL *c6 = malloc(sizeof(REAL) * m * p);
  cycle_t c6_time = get_cycle();
  REAL_mat_mul6(m, n, p, c6, p, a, n, b, p);
  c6_time = get_cycle()-c6_time;
  
  REAL *c7 = malloc(sizeof(REAL) * m * p);
  cycle_t c7_time = get_cycle();
  REAL_mat_mul7(m, n, p, c7, p, a, n, b, p);
  c7_time = get_cycle()-c7_time;
  
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
	
	 REAL_mat_equal(m, n, c1, p, c2, p)?"true":"false",
	 REAL_mat_equal(m, n, c1, p, c3, p)?"true":"false",
	 REAL_mat_equal(m, n, c1, p, c4, p)?"true":"false",
	 REAL_mat_equal(m, n, c1, p, c5, p)?"true":"false",
	 REAL_mat_equal(m, n, c1, p, c6, p)?"true":"false",
	 REAL_mat_equal(m, n, c1, p, c7, p)?"true":"false",
	 
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
  return 0;
}
