#include "../clock.h"

extern void latency(int *p);

int main() {
  int x;
  clock_start();
  latency(&x);
  clock_stop();
  print_total_clock();
}
