#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>
#include <inttypes.h>
#include "modint.h"

typedef uint64_t cycle_t;

#ifdef __K1C__
#include <mppa_bare_runtime/k1c/registers.h>
static inline void cycle_count_config(void)
{
        /* config pmc for cycle count */
        uint64_t pmc_value = __builtin_k1_get(K1_SFR_PMC);

        pmc_value &= ~(0xfULL);
        __builtin_k1_set(K1_SFR_PMC, pmc_value);
}

static inline uint64_t get_cycle(void)
{
        return __builtin_k1_get(K1_SFR_PM0);
}
#else
static inline void cycle_count_config(void) { }
#ifdef  __x86_64__
#include <x86intrin.h>
static inline cycle_t get_cycle(void) { return __rdtsc(); }
#else
static inline cycle_t get_cycle(void) { return 0; }
#endif
#endif

int main() {
  const unsigned m = 40, n = 20, p = 30;
  cycle_count_config();
  modint *a = malloc(sizeof(modint) * m * n);
  modint_mat_random(m, n, a, n);
  modint *b = malloc(sizeof(modint) * n * p);
  modint_mat_random(n, p, b, p);
  
  modint *c1 = malloc(sizeof(modint) * m * p);
  cycle_t c1_time = get_cycle();
  modint_mat_mul1(m, n, p, c1, p, a, n, b, p);
  c1_time = get_cycle()-c1_time;
  
  modint *c2 = malloc(sizeof(modint) * m * p);
  cycle_t c2_time = get_cycle();
  modint_mat_mul2(m, n, p, c2, p, a, n, b, p);
  c2_time = get_cycle()-c2_time;
  
  printf("equal = %s\n"
	 "c1_time = %" PRIu64 "\n"
	 "c2_time = %" PRIu64 "\n",
	 modint_mat_equal(m, n, c1, p, c2, p)?"true":"false",
	 c1_time,
	 c2_time);
  
  free(a);
  free(b);
  free(c1);
  free(c2);
  return 0;
}
