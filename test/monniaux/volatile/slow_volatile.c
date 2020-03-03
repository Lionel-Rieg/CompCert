#include "../clock.h"

volatile int output;

int main() {
  clock_prepare();
  clock_start();
  for(int i=0; i<1000; i++) {
    output = 0;
  }
  clock_stop();
  print_total_clock();
  return 0;
}
