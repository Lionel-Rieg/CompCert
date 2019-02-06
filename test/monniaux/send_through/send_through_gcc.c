#include <stdio.h>
#include "send_through.h"

double sum_int_double(int x, double y) {
  return x + y;
}

int main() {
  double x = send_through(sum_int_double, 2, 3, 4.5);
  printf("x[gcc] = %f\n", x);
  print_from_ccomp(x);
}
