#include <stdint.h>
#include <stdbool.h>

typedef uint64_t xor_and;

void xor_and_mat_mul1(unsigned m, unsigned n, unsigned p,
		     xor_and * restrict c, unsigned stride_c,
		     const xor_and *a, unsigned stride_a,
		     const xor_and *b, unsigned stride_b);

void xor_and_mat_mul2(unsigned m, unsigned n, unsigned p,
		     xor_and * restrict c, unsigned stride_c,
		     const xor_and *a, unsigned stride_a,
		     const xor_and *b, unsigned stride_b);

void xor_and_mat_mul3(unsigned m, unsigned n, unsigned p,
		     xor_and * restrict c, unsigned stride_c,
		     const xor_and *a, unsigned stride_a,
		     const xor_and *b, unsigned stride_b);

void xor_and_mat_mul4(unsigned m, unsigned n, unsigned p,
		     xor_and * restrict c, unsigned stride_c,
		     const xor_and *a, unsigned stride_a,
		     const xor_and *b, unsigned stride_b);

void xor_and_mat_mul5(unsigned m, unsigned n, unsigned p,
		     xor_and * restrict c, unsigned stride_c,
		     const xor_and *a, unsigned stride_a,
		     const xor_and *b, unsigned stride_b);

void xor_and_mat_mul6(unsigned m, unsigned n, unsigned p,
		     xor_and * restrict c, unsigned stride_c,
		     const xor_and *a, unsigned stride_a,
		     const xor_and *b, unsigned stride_b);

void xor_and_mat_mul7(unsigned m, unsigned n, unsigned p,
		     xor_and * restrict c, unsigned stride_c,
		     const xor_and *a, unsigned stride_a,
		     const xor_and *b, unsigned stride_b);

xor_and xor_and_random(void);

void xor_and_mat_random(unsigned m,
		       unsigned n,
		       xor_and *a, unsigned stride_a);

bool xor_and_mat_equal(unsigned m,
		      unsigned n,
		      const xor_and *a, unsigned stride_a,
		      const xor_and *b, unsigned stride_b);
