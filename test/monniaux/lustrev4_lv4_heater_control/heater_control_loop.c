/********
* ec2c version 0.67
* c main file generated for node : heater_control 
* to be used with : heater_control.c 
* and             : heater_control.h 
* context   method = HEAP
* ext call  method = PROCEDURES
********/
#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>
#include "../clock.h"
#include "../dm_random.c"
#include "heater_control.h"

/* Print a promt ? ************************/
static int ISATTY;
/* MACROS DEFINITIONS ****************/
#ifndef TT
#define TT "true"
#endif
#ifndef FF
#define FF "false"
#endif
#ifndef BB
#define BB "bottom"
#endif
#ifdef CKCHECK
/* set this macro for testing output clocks */
#endif

/* Standard Input procedures **************/
_real _get_real(char* n){
  return (dm_random_uint32()%70000U) * 1E-3 -20.0;
}
/* Standard Output procedures **************/
void _put_bool(char* n, _boolean b){
  printf("%s: %d\n", n, b);
}
/* Output procedures **********************/
void heater_control_O_Heat_on(void* cdata, _boolean _V) {
  // _put_bool("Heat_on", _V);
}
/* Main procedure *************************/
int main(){
   
   /* Context allocation */
   struct heater_control_ctx* ctx = heater_control_new_ctx(NULL);
   /* Main loop */
   clock_prepare();
   clock_start();
   heater_control_reset(ctx);
   for(int count=0; count<1000; count++){
      heater_control_I_T(ctx, _get_real("T"));
      heater_control_I_T1(ctx, _get_real("T1"));
      heater_control_I_T2(ctx, _get_real("T2"));
      heater_control_I_T3(ctx, _get_real("T3"));
      heater_control_step(ctx);
      
   }
   clock_stop();
   print_total_clock();
   return 0;
}
