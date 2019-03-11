#include <stdio.h>

typedef struct {
  double re, im;
} COMPLEX;

static inline void COMPLEX_zero(COMPLEX *r) {
  r->re = r->im = 0.0;
}

static inline void COMPLEX_add(COMPLEX *r,
				      const COMPLEX *x,
				      const COMPLEX *y) {
  double re = x->re + y->re;
  double im = x->im + y->im;
  r->re = re;
  r->im = im;
}

static inline void COMPLEX_mul(COMPLEX *r,
				      const COMPLEX *x,
				      const COMPLEX *y) {
  double re = x->re * y->re - x->im * y->im;
  double im = x->im * y->re + x->re * y->im;
  r->re = re;
  r->im = im;
}

static inline void COMPLEX_mul_add(COMPLEX *r,
				      const COMPLEX *x,
				      const COMPLEX *y) {
  double re = r->re + x->re * y->re - x->im * y->im;
  double im = r->im + x->im * y->re + x->re * y->im;
  r->re = re;
  r->im = im;
}


void COMPLEX_mat_mul1(unsigned m, unsigned n, unsigned p,
		     COMPLEX * restrict c, unsigned stride_c,
		     const COMPLEX *a, unsigned stride_a,
		     const COMPLEX *b, unsigned stride_b) {
  for(unsigned i=0; i<m; i++) {
    for(unsigned k=0; k<p; k++) {
      COMPLEX_zero(c+i*stride_c+k);
    }
  }
  for(unsigned i=0; i<m; i++) {
    for(unsigned k=0; k<p; k++) {
      for(unsigned j=0; j<n; j++) {
	COMPLEX_mul_add(c+i*stride_c+k, a+i*stride_a+j, b+j*stride_b+k); 
      }
    }
  }
}

int main() {
  COMPLEX a = { 1, 2 };
  COMPLEX b = { 7, 4 };
  COMPLEX r;
  COMPLEX_mul(&r, &a, &b);
  printf("%g %g\n", r.re, r.im);
}
