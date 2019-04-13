#include <stdio.h>
#include <fenv.h>

#pragma STDC FENV_ACCESS ON

double inverse(double x) {
  return 1.0 / x;
}

int main() {
  if (fesetround(FE_DOWNWARD)) {
    printf("fesetround(FE_DOWNWARD) unsuccessful\n");
  }
  double low = inverse(3.0);
  if (fesetround(FE_UPWARD)) {
    printf("fesetround(FE_UPWARD) unsuccessful\n");
  }
  double high = inverse(3.0);
  printf("%d %a\n", low==high, high-low);
}
