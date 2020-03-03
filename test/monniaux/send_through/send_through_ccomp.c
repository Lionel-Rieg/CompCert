#include <stdio.h>
#include <math.h>
#include "send_through.h"

double send_through_double(op_int_double f, int x, int y, double z) {
  double w= f(x, f(y, z));
  int mu = 1;
  return w;
}

float send_through_float(op_int_float f, int x, int y, float z) {
  float w= f(x, f(y, z));
  int mu = 1;
  return w;
}

void print_from_ccomp(double x) {
  printf("x=%e x=%f x=%g x=%.03e x=%.03f x=%.03g x[rounded]=%ld\n",
	 x, x, x, x, x, x, lrint(x));
}
