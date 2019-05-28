extern long __divdi3 (long a, long b);

long i64_sdiv (long a, long b)
{
  return __divdi3 (a, b);
}

int i32_sdiv (int a, int b)
{
  return __divdi3 (a, b);
}

#ifdef __K1C_COS__
#include <hal/cos_registers.h>
#define K1_SFR_CS_IO_MASK COS_SFR_CS_IO_MASK
#define K1_SFR_CS_DZ_MASK COS_SFR_CS_DZ_MASK
#define K1_SFR_CS_OV_MASK COS_SFR_CS_OV_MASK
#define K1_SFR_CS_UN_MASK COS_SFR_CS_UN_MASK
#define K1_SFR_CS_IN_MASK COS_SFR_CS_IN_MASK
#define K1_SFR_CS COS_SFR_CS
#else
#include <mppa_bare_runtime/k1c/registers.h>
#endif

/* DM FIXME this is for floating point */
int fetestexcept(int excepts) {
  int mask = (K1_SFR_CS_IO_MASK | K1_SFR_CS_DZ_MASK | K1_SFR_CS_OV_MASK | K1_SFR_CS_UN_MASK | K1_SFR_CS_IN_MASK) & excepts;
  unsigned long long cs = __builtin_k1_get(K1_SFR_CS);
  return cs & mask;
}

int feclearexcept(int excepts) {
  int mask = (K1_SFR_CS_IO_MASK | K1_SFR_CS_DZ_MASK | K1_SFR_CS_OV_MASK | K1_SFR_CS_UN_MASK | K1_SFR_CS_IN_MASK) & excepts;
  __builtin_k1_wfxl(K1_SFR_CS, mask);
  return 0;
}
