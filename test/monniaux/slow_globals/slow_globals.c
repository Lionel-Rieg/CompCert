#include "../clock.h"

extern void nothing(void);
int variable;

int main() {
  clock_prepare();
  clock_start();
  for(int i=0; i<1000; i++) {
    variable++;
    nothing();
  }
  clock_stop();
  print_total_clock();
}
