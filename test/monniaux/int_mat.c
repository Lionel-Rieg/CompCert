#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>

typedef uint32_t modint;

#define MODULUS 257

void modint_mat_mul1(unsigned m, unsigned n, unsigned p,
		     modint * restrict c, unsigned stride_c,
		     const modint *a, unsigned stride_a,
		     const modint *b, unsigned stride_b) {
  for(unsigned i=0; i<m; i++) {
    for(unsigned k=0; k<p; k++) {
      c[i*stride_c+k] = 0;
    }
  }
  for(unsigned i=0; i<m; i++) {
    for(unsigned k=0; k<p; k++) {
      for(unsigned j=0; j<n; j++) {
	c[i*stride_c+k] += a[i*stride_a+j] * b[j*stride_b+k]; 
      }
    }
  }
  for(unsigned i=0; i<m; i++) {
    for(unsigned k=0; k<p; k++) {
      c[i*stride_c+k] %= MODULUS;
    }
  }  
}

void modint_mat_mul2(unsigned m, unsigned n, unsigned p,
		     modint * restrict c, unsigned stride_c,
		     const modint *a, unsigned stride_a,
		     const modint *b, unsigned stride_b) {
  for(unsigned i=0; i<m; i++) {
    for(unsigned k=0; k<p; k++) {
      modint total = 0;
      for(unsigned j=0; j<n; j++) {
	total += a[i*stride_a + j] * b[j*stride_b + k];
      }
      c[i*stride_c+k] = total % MODULUS;
    }
  }
}

modint modint_random(void) {
  static uint64_t next = 1325997111;
  next = next * 1103515245 + 12345;
  return next % MODULUS;
}

void modint_mat_random(unsigned m,
		       unsigned n,
		       modint *a, unsigned stride_a) {
  for(unsigned i=0; i<m; i++) {
    for(unsigned j=0; j<n; j++) {
      a[i*stride_a + j] = modint_random();
    }
  }
}

bool modint_mat_equal(unsigned m,
		      unsigned n,
		      const modint *a, unsigned stride_a,
		      const modint *b, unsigned stride_b) {
  for(unsigned i=0; i<m; i++) {
    for(unsigned j=0; j<n; j++) {
      if (a[i*stride_a + j] != b[i*stride_b + j]) return false;
    }
  }
  return true;
}

int main() {
  const unsigned m = 200, n = 100, p = 150;
  modint *a = malloc(sizeof(modint) * m * n);
  modint_mat_random(m, n, a, n);
  modint *b = malloc(sizeof(modint) * n * p);
  modint_mat_random(n, p, b, p);
  modint *c1 = malloc(sizeof(modint) * m * p);
  modint_mat_mul1(m, n, p, c1, p, a, n, b, p);  
  modint *c2 = malloc(sizeof(modint) * m * p);
  modint_mat_mul2(m, n, p, c2, p, a, n, b, p);
  printf("equal = %s\n", modint_mat_equal(m, n, c1, p, c2, p)?"true":"false");
  free(a);
  free(b);
  free(c1);
  free(c2);
  return 0;
}
