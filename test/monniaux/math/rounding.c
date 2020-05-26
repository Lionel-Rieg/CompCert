#include <stdio.h>
#include <fenv.h>

#ifdef __KVX__
#include <mppa_bare_runtime/kvx/registers.h>
int fesetround(int rounding_mode) {
  if (rounding_mode < 0 || rounding_mode > 3) return 1;
  unsigned long long cs = __builtin_kvx_get(K1_SFR_CS);
  cs = (cs & ~(3 << 16)) | (rounding_mode << 16);
  __builtin_kvx_set(K1_SFR_CS, cs);
  return 0;
}

int fegetround(void) {
  unsigned long long cs = __builtin_kvx_get(K1_SFR_CS);
  return (cs >> 16) & 3;
}
#endif

#pragma STDC FENV_ACCESS ON

double add(double x) {
  return x+0.1;
}

int main() {
  if (fesetround(FE_DOWNWARD)) {
    printf("fesetround(FE_DOWNWARD) unsuccessful\n");
  }
  double low = add(3.0);
  if (fesetround(FE_UPWARD)) {
    printf("fesetround(FE_UPWARD) unsuccessful\n");
  }
  double high = add(3.0);
  printf("%d %a %d\n", low==high, high-low, fegetround());
}
