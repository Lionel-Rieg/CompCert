typedef unsigned long cycle_t;

#ifdef __K1C__
#ifdef __K1C_COS__
#include <hal/cos_registers.h>
#define K1_SFR_PMC COS_SFR_PMC
#define K1_SFR_PM0 COS_SFR_PM0
#else
#include <mppa_bare_runtime/k1c/registers.h>
#endif
static inline void cycle_count_config(void)
{
        /* config pmc for cycle count */
        cycle_t pmc_value = __builtin_k1_get(K1_SFR_PMC);

        pmc_value &= ~(0xfULL);
        __builtin_k1_set(K1_SFR_PMC, pmc_value);
}

static inline cycle_t get_cycle(void)
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
