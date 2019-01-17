#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>
#include "modint.h"

int main() {
  const unsigned m = 40, n = 20, p = 30;
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
