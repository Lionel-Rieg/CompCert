#define VERIMAG_MEASUREMENTS
#ifdef VERIMAG_MEASUREMENTS
#include "../clock.h"
#endif

int picosat_main (int, char **);

int
main (int argc, char **argv)
{

#ifdef VERIMAG_MEASUREMENTS
  clock_prepare();
  clock_start();
#endif

  int ret= picosat_main (argc, argv);

#ifdef VERIMAG_MEASUREMENTS
  clock_stop();
  print_total_clock();
#endif

  return ret;
}
