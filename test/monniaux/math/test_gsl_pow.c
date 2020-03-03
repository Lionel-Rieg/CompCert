#include <math.h>
#include <stdio.h>

double gsl_pow_uint(double x, unsigned int n);

double gsl_pow_int(double x, int n)
{
  unsigned int un;

  if(n < 0) {
    x = 1.0/x;
    un = -n;
  } else {
    un = n;
  }

  return gsl_pow_uint(x, un);
}

double gsl_pow_uint(double x, unsigned int n)
{
  double value = 1.0;

  /* repeated squaring method 
   * returns 0.0^0 = 1.0, so continuous in x
   */
  do {
     if(n & 1) value *= x;  /* for n odd */
     n >>= 1;
     x *= x;
  } while (n);

  return value;
}

int main() {
  double y, y_expected;
  for (int n = -9; n < 10; n++) {
    y = gsl_pow_int (-3.14, n);
    y_expected = pow (-3.14, n);
    printf("%d %g %g\n", n, y, y_expected);
  }
  return 0;
}
