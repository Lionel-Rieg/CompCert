#include <stdint.h>
#include <inttypes.h>
#include <stdio.h>

#ifdef __K1C__
typedef uint64_t cycle_t;
#define PRcycle PRId64

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

#if defined(__i386__) || defined( __x86_64__)
#define PRcycle PRId64
typedef uint64_t cycle_t;
#include <x86intrin.h>
static inline cycle_t get_cycle(void) { return __rdtsc(); }

#elif __riscv
#ifdef __riscv32
#define PRcycle PRId32
typedef uint32_t cycle_t;
#else
#define PRcycle PRId64
typedef uint64_t cycle_t;
#endif
static inline cycle_t get_cycle(void) {
  cycle_t cycles;
  asm volatile ("rdcycle %0" : "=r" (cycles));
  return cycles;
}

#elif defined (__ARM_ARCH) // && (__ARM_ARCH >= 6)
#if (__ARM_ARCH < 8)
typedef uint32_t cycle_t;
#define PRcycle PRId32

#ifdef ARM_NO_PRIVILEGE
static inline cycle_t get_cycle(void) {
  return 0;
}
#else
/* need this kernel module
https://github.com/zertyz/MTL/tree/master/cpp/time/kernel/arm */
static inline cycle_t get_cycle(void) {
  cycle_t cycles;
  __asm__ volatile ("mrc p15, 0, %0, c9, c13, 0":"=r" (cycles));
  return cycles;
}
#endif
#else
#define PRcycle PRId64
typedef uint64_t cycle_t;

#ifdef ARM_NO_PRIVILEGE
static inline cycle_t get_cycle(void) {
  return 0;
}
#else
/* need this kernel module:
https://github.com/jerinjacobk/armv8_pmu_cycle_counter_el0

on 5+ kernels, remove first argument of access_ok macro */
static inline cycle_t get_cycle(void)
{
  uint64_t val;
  __asm__ volatile("mrs %0, pmccntr_el0" : "=r"(val));
  return val;
}
#endif
#endif

#else
#define PRcycle PRId32
typedef uint32_t cycle_t;
static inline cycle_t get_cycle(void) { return 0; }
#endif
#endif

#ifdef MAX_MEASURES
  #define TIMEINIT(i) {_last_stop[i] = get_cycle();}
  #define TIMESTOP(i) {cycle_t cur = get_cycle(); _total_cycles[i] += cur - _last_stop[i]; _last_stop[i] = cur;}
  #define TIMEPRINT(n) { for (int i = 0; i <= n; i++) printf("%d cycles: %" PRIu64 "\n", i, _total_cycles[i]); }
#endif


#ifdef MAX_MEASURES
  static cycle_t _last_stop[MAX_MEASURES] = {0};
  static cycle_t _total_cycles[MAX_MEASURES] = {0};
#endif
