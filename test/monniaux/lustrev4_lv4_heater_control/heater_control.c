/********
* ec2c version 0.67
* c file generated for node : heater_control 
* context   method = HEAP
* ext call  method = PROCEDURES
********/
#include <stdlib.h>
#include <string.h>
#define _heater_control_EC2C_SRC_FILE
#include "heater_control.h"
/*--------
Internal structure for the call
--------*/
typedef struct  {
   void* client_data;
   //INPUTS
   _real _T;
   _real _T1;
   _real _T2;
   _real _T3;
   //OUTPUTS
   _boolean _Heat_on;
   //REGISTERS
   _boolean M73;
   _boolean M73_nil;
   _boolean M5;
} heater_control_ctx;
/*--------
Output procedures must be defined,
Input procedures must be used:
--------*/
void heater_control_I_T(heater_control_ctx* ctx, _real V){
   ctx->_T = V;
}
void heater_control_I_T1(heater_control_ctx* ctx, _real V){
   ctx->_T1 = V;
}
void heater_control_I_T2(heater_control_ctx* ctx, _real V){
   ctx->_T2 = V;
}
void heater_control_I_T3(heater_control_ctx* ctx, _real V){
   ctx->_T3 = V;
}
extern void heater_control_O_Heat_on(void* cdata, _boolean);
#ifdef CKCHECK
extern void heater_control_BOT_Heat_on(void* cdata);
#endif
/*--------
Internal reset input procedure
--------*/
static void heater_control_reset_input(heater_control_ctx* ctx){
   //NOTHING FOR THIS VERSION...
}
/*--------
Reset procedure
--------*/
void heater_control_reset(heater_control_ctx* ctx){
   ctx->M73_nil = _true;
   ctx->M5 = _true;
   heater_control_reset_input(ctx);
}
/*--------
Copy the value of an internal structure
--------*/
void heater_control_copy_ctx(heater_control_ctx* dest, heater_control_ctx
* src){
   memcpy((void*)dest, (void*)src, sizeof(heater_control_ctx));
}
/*--------
Dynamic allocation of an internal structure
--------*/
heater_control_ctx* heater_control_new_ctx(void* cdata){
   heater_control_ctx* ctx = (heater_control_ctx*)calloc(1, sizeof(
heater_control_ctx));
   ctx->client_data = cdata;
   heater_control_reset(ctx);
   return ctx;
}
/*--------
Step procedure
--------*/
void heater_control_step(heater_control_ctx* ctx){
//LOCAL VARIABLES
   _real L16;
   _boolean L15;
   _real L18;
   _real L14;
   _boolean L13;
   _boolean L12;
   _real L24;
   _boolean L23;
   _real L25;
   _real L22;
   _boolean L21;
   _boolean L20;
   _boolean L11;
   _real L30;
   _boolean L29;
   _real L31;
   _real L28;
   _boolean L27;
   _boolean L26;
   _boolean L10;
   _real L32;
   _boolean L38;
   _boolean L37;
   _boolean L40;
   _boolean L39;
   _boolean L36;
   _boolean L42;
   _boolean L41;
   _boolean L35;
   _real L46;
   _real L45;
   _boolean L50;
   _real L49;
   _boolean L48;
   _real L47;
   _real L44;
   _boolean L54;
   _real L53;
   _boolean L52;
   _real L51;
   _real L43;
   _boolean L57;
   _boolean L56;
   _real L59;
   _real L63;
   _real L62;
   _real L65;
   _real L64;
   _real L61;
   _real L58;
   _real L55;
   _real L34;
   _real L9;
   _boolean L8;
   _boolean L68;
   _boolean L71;
   _boolean L70;
   _boolean L67;
   _boolean L7;
   _boolean L4;
   _boolean T73;
//CODE
   L16 = (ctx->_T1 - ctx->_T2);
   L15 = (L16 >= 0.000000);
   L18 = (- L16);
   if (L15) {
      L14 = L16;
   } else {
      L14 = L18;
   }
   L13 = (L14 < 0.500000);
   L12 = (! L13);
   L24 = (ctx->_T1 - ctx->_T3);
   L23 = (L24 >= 0.000000);
   L25 = (- L24);
   if (L23) {
      L22 = L24;
   } else {
      L22 = L25;
   }
   L21 = (L22 < 0.500000);
   L20 = (! L21);
   L11 = (L12 && L20);
   L30 = (ctx->_T2 - ctx->_T3);
   L29 = (L30 >= 0.000000);
   L31 = (- L30);
   if (L29) {
      L28 = L30;
   } else {
      L28 = L31;
   }
   L27 = (L28 < 0.500000);
   L26 = (! L27);
   L10 = (L11 && L26);
   L32 = (- 999.000000);
   L38 = (L13 && L20);
   L37 = (L38 && L26);
   L40 = (L21 && L12);
   L39 = (L40 && L26);
   L36 = (L37 || L39);
   L42 = (L27 && L12);
   L41 = (L42 && L20);
   L35 = (L36 || L41);
   L46 = (ctx->_T1 + ctx->_T2);
   L45 = (L46 + ctx->_T3);
   L50 = (ctx->_T2 < ctx->_T3);
   if (L50) {
      L49 = ctx->_T2;
   } else {
      L49 = ctx->_T3;
   }
   L48 = (ctx->_T1 < L49);
   if (L48) {
      L47 = ctx->_T1;
   } else {
      L47 = L49;
   }
   L44 = (L45 - L47);
   L54 = (ctx->_T2 > ctx->_T3);
   if (L54) {
      L53 = ctx->_T2;
   } else {
      L53 = ctx->_T3;
   }
   L52 = (ctx->_T1 > L53);
   if (L52) {
      L51 = ctx->_T1;
   } else {
      L51 = L53;
   }
   L43 = (L44 - L51);
   L57 = (L13 && L21);
   L56 = (L57 && L27);
   L59 = (L46 / 2.000000);
   L63 = (ctx->_T1 + ctx->_T3);
   L62 = (L63 / 2.000000);
   L65 = (ctx->_T2 + ctx->_T3);
   L64 = (L65 / 2.000000);
   if (L21) {
      L61 = L62;
   } else {
      L61 = L64;
   }
   if (L13) {
      L58 = L59;
   } else {
      L58 = L61;
   }
   if (L56) {
      L55 = L43;
   } else {
      L55 = L58;
   }
   if (L35) {
      L34 = L43;
   } else {
      L34 = L55;
   }
   if (L10) {
      L9 = L32;
   } else {
      L9 = L34;
   }
   L8 = (L9 == L32);
   L68 = (L9 < 6.000000);
   L71 = (L9 > 9.000000);
   if (L71) {
      L70 = _false;
   } else {
      L70 = ctx->M73;
   }
   if (L68) {
      L67 = _true;
   } else {
      L67 = L70;
   }
   if (L8) {
      L7 = _false;
   } else {
      L7 = L67;
   }
   if (ctx->M5) {
      L4 = _true;
   } else {
      L4 = L7;
   }
   heater_control_O_Heat_on(ctx->client_data, L4);
   T73 = L4;
   ctx->M73 = T73;
   ctx->M73_nil = _false;
   ctx->M5 = ctx->M5 && !(_true);
}
