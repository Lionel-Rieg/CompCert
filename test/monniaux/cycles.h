typedef unsigned long cycle_t;

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
#else
static inline cycle_t get_cycle(void) { return 0; }
#endif
#endif
