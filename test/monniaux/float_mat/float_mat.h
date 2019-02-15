#include <stdint.h>
#include <stdbool.h>

typedef double REAL;

void REAL_mat_mul1(unsigned m, unsigned n, unsigned p,
		     REAL * restrict c, unsigned stride_c,
		     const REAL *a, unsigned stride_a,
		     const REAL *b, unsigned stride_b);

void REAL_mat_mul2(unsigned m, unsigned n, unsigned p,
		     REAL * restrict c, unsigned stride_c,
		     const REAL *a, unsigned stride_a,
		     const REAL *b, unsigned stride_b);

void REAL_mat_mul3(unsigned m, unsigned n, unsigned p,
		     REAL * restrict c, unsigned stride_c,
		     const REAL *a, unsigned stride_a,
		     const REAL *b, unsigned stride_b);

void REAL_mat_mul4(unsigned m, unsigned n, unsigned p,
		     REAL * restrict c, unsigned stride_c,
		     const REAL *a, unsigned stride_a,
		     const REAL *b, unsigned stride_b);

void REAL_mat_mul5(unsigned m, unsigned n, unsigned p,
		     REAL * restrict c, unsigned stride_c,
		     const REAL *a, unsigned stride_a,
		     const REAL *b, unsigned stride_b);

void REAL_mat_mul6(unsigned m, unsigned n, unsigned p,
		     REAL * restrict c, unsigned stride_c,
		     const REAL *a, unsigned stride_a,
		     const REAL *b, unsigned stride_b);

void REAL_mat_mul7(unsigned m, unsigned n, unsigned p,
		     REAL * restrict c, unsigned stride_c,
		     const REAL *a, unsigned stride_a,
		     const REAL *b, unsigned stride_b);

REAL REAL_random(void);

void REAL_mat_random(unsigned m,
		       unsigned n,
		       REAL *a, unsigned stride_a);

bool REAL_mat_equal(unsigned m,
		      unsigned n,
		      const REAL *a, unsigned stride_a,
		      const REAL *b, unsigned stride_b);
