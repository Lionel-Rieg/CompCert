#include <stdint.h>
#include <stdbool.h>

typedef uint32_t modint;
#define MODULUS 257

void modint_mat_mul1(unsigned m, unsigned n, unsigned p,
		     modint * restrict c, unsigned stride_c,
		     const modint *a, unsigned stride_a,
		     const modint *b, unsigned stride_b);

void modint_mat_mul2(unsigned m, unsigned n, unsigned p,
		     modint * restrict c, unsigned stride_c,
		     const modint *a, unsigned stride_a,
		     const modint *b, unsigned stride_b);

modint modint_random(void);

void modint_mat_random(unsigned m,
		       unsigned n,
		       modint *a, unsigned stride_a);

bool modint_mat_equal(unsigned m,
		      unsigned n,
		      const modint *a, unsigned stride_a,
		      const modint *b, unsigned stride_b);
