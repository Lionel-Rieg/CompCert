#include <stdio.h>
#include <fenv.h>
#include <float.h>

#pragma STDC FENV_ACCESS ON

#if defined(__K1C__) && !defined(__COMPCERT__)
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

double add_double(double x, double y) {
  return x+y;
}

double mul_double(double x, double y) {
  return x*y;
}

float mul_float(float x, float y) {
  return x*y;
}

float double2float(double x) {
  return x;
}

float uint2float(unsigned x) {
  return x;
}

double ulong2double(unsigned long x) {
  return x;
}

unsigned double2uint(double x) {
  return x;
}

int main() {
  printf("%x\n", fetestexcept(FE_ALL_EXCEPT));

  double v1 = add_double(3.0, 0.1);
  printf("%x\n", fetestexcept(FE_ALL_EXCEPT));
  feclearexcept(FE_INEXACT);

  printf("%x\n", fetestexcept(FE_ALL_EXCEPT));
  double v2 = mul_double(DBL_MAX, DBL_MAX);
  printf("%g %x\n", v2, fetestexcept(FE_ALL_EXCEPT));
  feclearexcept(FE_ALL_EXCEPT);

  double v3 = mul_double(DBL_MIN, DBL_MIN);
  printf("%g %x\n", v3, fetestexcept(FE_ALL_EXCEPT));
  feclearexcept(FE_ALL_EXCEPT);

  double v4 = double2float(DBL_MAX);
  printf("%g %x\n", v4, fetestexcept(FE_ALL_EXCEPT));
  feclearexcept(FE_ALL_EXCEPT);

  float v5 = uint2float(0xC07FDFFFU);
  printf("%g %x\n", v5, fetestexcept(FE_ALL_EXCEPT)); // BUG 0 should have INEXACT
  feclearexcept(FE_ALL_EXCEPT);

  double v6 = ulong2double(0x11217763AFF77C7CUL);
  printf("%a %x\n", v6, fetestexcept(FE_ALL_EXCEPT)); // BUG 0 should have INEXACT; correct on x86
  feclearexcept(FE_ALL_EXCEPT);

  double v6b = ulong2double(0xFFFFFFFFFFFFFFFFUL);
  printf("%a %x\n", v6b, fetestexcept(FE_ALL_EXCEPT)); // BUG 0 should have INEXACT; correct on x86
  feclearexcept(FE_ALL_EXCEPT);

  unsigned v7 = double2uint(-0.25); // softfloat says "0 and inexact" but here we have "0 and overflow" (due to negative input for unsigned?)
  // unsure if (unsigned) (-0.25) should be 0 or an error
  // BUG C99 annex F says that the error is invalid op not overflow
  printf("%u %x\n", v7, fetestexcept(FE_ALL_EXCEPT));
  feclearexcept(FE_ALL_EXCEPT);

  // +41F.307672C5496EF in Berkeley Soft Float test
  double d8 = 0x1.307672C5496EFp32;
  unsigned v8 = double2uint(d8);
  printf("%g %x %x\n", d8, v8, fetestexcept(FE_ALL_EXCEPT));
  // BUG reports 307672C5 and inexact, but should report overflow
  // bug comes from x86 https://gcc.gnu.org/bugzilla/show_bug.cgi?id=89175
  feclearexcept(FE_ALL_EXCEPT);
  // all f64_to_ui32_rx_minMag errors explained by
  // 1) round to uin64 2) take 32 low order bits no precautions

  double d8b = 0x1.307672C5496EFp70;
  unsigned v8b = double2uint(d8b);
  printf("d8b %g %x %x\n", d8b, v8b, fetestexcept(FE_ALL_EXCEPT));
  feclearexcept(FE_ALL_EXCEPT);

  // +380.FFFFFFFFFFFFF  => +01.000000 ...ux  expected +01.000000 ....x
  // Bug in soft float?
  double v9 = double2float(0x1.FFFFFFFFFFFFFp-127);
  printf("%a %x\n", v9, fetestexcept(FE_ALL_EXCEPT));
  feclearexcept(FE_ALL_EXCEPT);

  // +00.7FFFFF  +7F.000001  => +01.000000 ...ux  expected +01.000000 ....x
  float v10 = mul_float(0x0.7FFFFFp-126, 0x1.000001p+0);
  printf("%a %x\n", v10, fetestexcept(FE_ALL_EXCEPT));
  feclearexcept(FE_ALL_EXCEPT);
}
