#include <stdio.h>
#include <stdbool.h>
#include <stdlib.h>
#include <inttypes.h>
#include "../clock.h"

typedef double REAL;

typedef struct {
  REAL re, im;
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

static inline void COMPLEX_mul_addto(COMPLEX *r,
				      const COMPLEX *x,
				      const COMPLEX *y) {
  double re = r->re + x->re * y->re - x->im * y->im;
  double im = r->im + x->im * y->re + x->re * y->im;
  r->re = re;
  r->im = im;
}

#define MACRO_COMPLEX_mul_addto(rre, rim, x, y)	\
  { \
    double xre = (x).re, xim=(x).im, \
           yre = (y).re, yim=(y).im; \
    (rre) += xre * yre - xim * yim; \
    (rim) += xim * yre + xre * yim; \
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
	COMPLEX_mul_addto(c+i*stride_c+k, a+i*stride_a+j, b+j*stride_b+k); 
      }
    }
  }
}

#define UNROLL 4

#undef CHUNK
#define CHUNK \
  COMPLEX_mul_addto(&total, pa_i_j, pb_j_k);				\
  pa_i_j ++;								\
  pb_j_k = (COMPLEX*) ((char*) pb_j_k + stride_b_scaled);

void COMPLEX_mat_mul8(unsigned m, unsigned n, unsigned p,
		     COMPLEX * c, unsigned stride_c,
		     const COMPLEX *a, unsigned stride_a,
		     const COMPLEX *b, unsigned stride_b) {
  const COMPLEX *pa_i = a;
  COMPLEX * pc_i = c;
  size_t stride_b_scaled = sizeof(COMPLEX) * stride_b;
  for(unsigned i=0; i<m; i++) {
    for(unsigned k=0; k<p; k++) {
      const COMPLEX *pb_j_k = b+k, *pa_i_j = pa_i;
      COMPLEX total;
      COMPLEX_zero(&total);
      {
	unsigned j4=0, n4=n/UNROLL;
	if (n4 > 0) {
	  do {
            CHUNK
	    CHUNK
	    CHUNK
	    CHUNK
	    j4++;
	  } while (j4 < n4);
	}
      }
      {
	unsigned j4=0, n4=n%UNROLL;
	if (n4 > 0) {
	  do {
	    CHUNK
	    j4++;
	  } while (j4 < n4);
	}
      }
      pc_i[k] = total;
    }
    pa_i += stride_a;
    pc_i += stride_c;
  }
}

#undef CHUNK
#define CHUNK \
  MACRO_COMPLEX_mul_addto(totalre, totalim, *pa_i_j, *pb_j_k)	      	\
  pa_i_j ++;								\
  pb_j_k = (COMPLEX*) ((char*) pb_j_k + stride_b_scaled);

void COMPLEX_mat_mul9(unsigned m, unsigned n, unsigned p,
		     COMPLEX * c, unsigned stride_c,
		     const COMPLEX *a, unsigned stride_a,
		     const COMPLEX *b, unsigned stride_b) {
  const COMPLEX *pa_i = a;
  COMPLEX * pc_i = c;
  size_t stride_b_scaled = sizeof(COMPLEX) * stride_b;
  for(unsigned i=0; i<m; i++) {
    for(unsigned k=0; k<p; k++) {
      const COMPLEX *pb_j_k = b+k, *pa_i_j = pa_i;
      REAL totalre=0.0, totalim=0.0;
      {
	unsigned j4=0, n4=n/UNROLL;
	if (n4 > 0) {
	  do {
            CHUNK
	    CHUNK
	    CHUNK
	    CHUNK
	    j4++;
	  } while (j4 < n4);
	}
      }
      {
	unsigned j4=0, n4=n%UNROLL;
	if (n4 > 0) {
	  do {
	    CHUNK
	    j4++;
	  } while (j4 < n4);
	}
      }
      pc_i[k].re = totalre;
      pc_i[k].im = totalim;
    }
    pa_i += stride_a;
    pc_i += stride_c;
  }
}

bool COMPLEX_equal(const COMPLEX *a,
		   const COMPLEX *b) {
  return a->re==b->re && a->im==b->im;
}

bool COMPLEX_mat_equal(unsigned m,
		      unsigned n,
		      const COMPLEX *a, unsigned stride_a,
		      const COMPLEX *b, unsigned stride_b) {
  for(unsigned i=0; i<m; i++) {
    for(unsigned j=0; j<n; j++) {
      if (! COMPLEX_equal(a+i*stride_a + j, b+i*stride_b + j)) {
	printf("at %u,%u: (%g,%g) vs (%g,%g)\n", i, j,
	       a[i*stride_a + j].re, a[i*stride_a + j].im,
	       b[i*stride_b + j].re, b[i*stride_b + j].im);
	return false;
      }
    }
  }
  return true;
}

REAL REAL_random(void) {
  static uint64_t next = 1325997111;
  next = next * 1103515249 + 12345;
  return next % 1000;
}

void COMPLEX_mat_random(unsigned m,
		       unsigned n,
		       COMPLEX *a, unsigned stride_a) {
  for(unsigned i=0; i<m; i++) {
    for(unsigned j=0; j<n; j++) {
      a[i*stride_a + j].re = REAL_random();
      a[i*stride_a + j].im = REAL_random();
    }
  }
}


int main() {
    const unsigned m = 60, n = 31, p = 50;
  clock_prepare();
  COMPLEX *a = malloc(sizeof(COMPLEX) * m * n);
  COMPLEX_mat_random(m, n, a, n);
  COMPLEX *b = malloc(sizeof(COMPLEX) * n * p);
  COMPLEX_mat_random(n, p, b, p);
  
  COMPLEX *c1 = malloc(sizeof(COMPLEX) * m * p);
  cycle_t c1_time = get_current_cycle();
  COMPLEX_mat_mul1(m, n, p, c1, p, a, n, b, p);
  c1_time = get_current_cycle()-c1_time;
    
  COMPLEX *c8 = malloc(sizeof(COMPLEX) * m * p);
  cycle_t c8_time = get_current_cycle();
  COMPLEX_mat_mul8(m, n, p, c8, p, a, n, b, p);
  c8_time = get_current_cycle()-c8_time;
    
  COMPLEX *c9 = malloc(sizeof(COMPLEX) * m * p);
  cycle_t c9_time = get_current_cycle();
  COMPLEX_mat_mul9(m, n, p, c9, p, a, n, b, p);
  c9_time = get_current_cycle()-c9_time;
  
  printf("c1==c8: %s\n"
	 "c1==c9: %s\n"
	 "c1_time = %" PRIu64 "\n"
	 "c8_time = %" PRIu64 "\n"
	 "c9_time = %" PRIu64 "\n",
	
	 COMPLEX_mat_equal(m, n, c1, p, c8, p)?"true":"false",
	 COMPLEX_mat_equal(m, n, c1, p, c9, p)?"true":"false",
	 
	 c1_time,
	 c8_time,
	 c9_time);
  
  free(a);
  free(b);
  free(c1);
  free(c8);
  free(c9);
  return 0;
}
