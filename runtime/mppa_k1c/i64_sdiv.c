extern long __divdi3 (long a, long b);

int i32_sdiv (int a, int b)
{
  return __divdi3 (a, b);
}

#ifdef OUR_OWN_FE_EXCEPT
#include <../../k1-cos/include/hal/cos_registers.h>

/* DM FIXME this is for floating point */
int fetestexcept(int excepts) {
  int mask = (COS_SFR_CS_IO_MASK | COS_SFR_CS_DZ_MASK | COS_SFR_CS_OV_MASK | COS_SFR_CS_UN_MASK | COS_SFR_CS_IN_MASK) & excepts;
  unsigned long long cs = __builtin_k1_get(COS_SFR_CS);
  return cs & mask;
}

int feclearexcept(int excepts) {
  int mask = (COS_SFR_CS_IO_MASK | COS_SFR_CS_DZ_MASK | COS_SFR_CS_OV_MASK | COS_SFR_CS_UN_MASK | COS_SFR_CS_IN_MASK) & excepts;
  __builtin_k1_wfxl(COS_SFR_CS, mask);
  return 0;
}
#endif
