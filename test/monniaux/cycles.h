#include <inttypes.h>
#include <stdio.h>
typedef unsigned long cycle_t;

#ifdef MAX_MEASURES
  static cycle_t _last_stop[MAX_MEASURES] = {0};
  static cycle_t _total_cycles[MAX_MEASURES] = {0};
#endif

#ifdef __K1C__
#include <../../k1-cos/include/hal/cos_registers.h>

static inline void cycle_count_config(void)
{
        /* config pmc for cycle count */
        cycle_t pmc_value = __builtin_k1_get(COS_SFR_PMC);

        pmc_value &= ~(0xfULL);
        __builtin_k1_set(COS_SFR_PMC, pmc_value);
}

static inline cycle_t get_cycle(void)
{
        return __builtin_k1_get(COS_SFR_PM0);
}

#else // not K1C
static inline void cycle_count_config(void) { }

#ifdef  __x86_64__
#include <x86intrin.h>
static inline cycle_t get_cycle(void) { return __rdtsc(); }

#elif __riscv
static inline cycle_t get_cycle(void) {
  cycle_t cycles;
  asm volatile ("rdcycle %0" : "=r" (cycles));
  return cycles;
}

#else
static inline cycle_t get_cycle(void) { return 0; }
#endif
#endif

#ifdef MAX_MEASURES
  #define TIMEINIT(i) {_last_stop[i] = get_cycle();}
  #define TIMESTOP(i) {cycle_t cur = get_cycle(); _total_cycles[i] += cur - _last_stop[i]; _last_stop[i] = cur;}
  #define TIMEPRINT(n) { for (int i = 0; i <= n; i++) printf("%d cycles: %" PRIu64 "\n", i, _total_cycles[i]); }
#endif
