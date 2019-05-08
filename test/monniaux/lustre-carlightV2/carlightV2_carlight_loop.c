/* This file was generated by lv6 version master.737 (2727a7744111c84f7984634d2bd3ad6f7c6c7ff9). */
/*  lv6 carlightV2.lus -n carlight --to-c */
/* on vanoise the 08/05/2019 at 22:54:09 */

#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>
#include "carlightV2_carlight.h"
#include "../clock.h"

/* MACROS DEFINITIONS ****************/
#ifndef TT
#define TT "1"
#endif
#ifndef FF
#define FF "0"
#endif
#ifndef BB
#define BB "bottom"
#endif
#ifdef CKCHECK
/* set this macro for testing output clocks */
#endif

static uint32_t dm_random_uint32(void) {
  static uint32_t current=UINT32_C(0xDEADBEEF);
  current = ((uint64_t) current << 6) % UINT32_C(4294967291);
  return current;
}

/* Standard Input procedures **************/
_boolean _get_bool(char* n){
  return dm_random_uint32() & 1;
}
_integer _get_int(char* n){
  return (_integer) (dm_random_uint32() % 21) - 10;
}
_real _get_real(char* n){
  return ((_integer) (dm_random_uint32() % 2000001) - 1000000)*1E-6;  
}

/* Main procedure *************************/
int main(){
  int _s = 0;
  _integer switch_pos;
  _real intensity;
  _boolean is_on;
    carlightV2_carlight_ctx_type* ctx = carlightV2_carlight_ctx_new_ctx(NULL);

  /* Main loop */
  clock_prepare();
  clock_start();

  for(int count=0; count<1000; count++){
    ++_s;
     switch_pos = _get_int("switch_pos");
     intensity = _get_real("intensity");
    carlightV2_carlight_step(switch_pos,intensity,&is_on,ctx);
    // printf("%d %f #outs %d\n",switch_pos,intensity,is_on);
    // printf("%d\n",is_on);
  }
  
  clock_stop();
  print_total_clock();
  
  return 0;  
}
