#include <stdio.h>
#include <fenv.h>
#include <float.h>

#ifdef __K1C__
#include <mppa_bare_runtime/k1c/registers.h>
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
#endif

#pragma STDC FENV_ACCESS ON

double add(double x, double y) {
  return x+y;
}

double mul(double x, double y) {
  return x*y;
}

int main() {
  printf("%x\n", fetestexcept(FE_ALL_EXCEPT));
  double v1 = add(3.0, 0.1);
  printf("%x\n", fetestexcept(FE_ALL_EXCEPT));
  feclearexcept(FE_INEXACT);
  printf("%x\n", fetestexcept(FE_ALL_EXCEPT));
  double v2 = mul(DBL_MAX, DBL_MAX);
  printf("%g %x\n", v2, fetestexcept(FE_ALL_EXCEPT));
  feclearexcept(FE_ALL_EXCEPT);
  double v3 = mul(DBL_MIN, DBL_MIN);
  printf("%g %x\n", v3, fetestexcept(FE_ALL_EXCEPT));
}
