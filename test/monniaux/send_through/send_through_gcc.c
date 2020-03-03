#include <stdio.h>
#include "send_through.h"

double sum_int_double(int x, double y) {
  return x + y;
}

float sum_int_float(int x, float y) {
  return x + y;
}

int main() {
  double x = send_through_double(sum_int_double, 2, 3, 4.5);
  float y = send_through_float(sum_int_float, 2, 3, 4.5f);
  printf("x[gcc] = %f\n", x);
  printf("y[gcc] = %f\n", y);
  print_from_ccomp(x);
}
