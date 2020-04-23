#ifndef PREDICTED
#define PREDICTED 0
#endif

int expect(int x, int *y, int *z) {
  return __builtin_expect(x, PREDICTED) ? *y : *z;
}
