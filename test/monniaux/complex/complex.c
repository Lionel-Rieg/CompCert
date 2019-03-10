#include <stdio.h>

typedef struct {
  double re, im;
} complex_double;

static inline void add_complex_double(complex_double *r,
				      const complex_double *x,
				      const complex_double *y) {
  double re = x->re + y->re;
  double im = x->im + y->im;
  r->re = re;
  r->im = im;
}

int main() {
  complex_double a = { 1, 2 };
  complex_double b = { 7, 4 };
  complex_double r;
  add_complex_double(&r, &a, &b);
  printf("%g %g\n", r.re, r.im);
}
