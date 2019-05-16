/* This file was generated by lv6 version master.737 (2727a7744111c84f7984634d2bd3ad6f7c6c7ff9). */
/*  lv6 -en -2cgc heater_control.lus -n heater_control */
/* on vanoise the 15/05/2019 at 13:20:10 */
#include "heater_control_heater_control.h"
//// Defining step functions
// Memory initialisation for Lustre_arrow_ctx
void Lustre_arrow_ctx_reset(Lustre_arrow_ctx_type* ctx){
  int _i;
  ctx->_memory = _true;
}

// Initialisation of the  internal structure of Lustre_arrow_ctx
void Lustre_arrow_ctx_init(Lustre_arrow_ctx_type* ctx){
  // ctx->client_data = cdata;
  Lustre_arrow_ctx_reset(ctx);
 }
// Step function(s) for Lustre_arrow_ctx
void Lustre_arrow_step(_boolean i1,_boolean i2,_boolean *out,Lustre_arrow_ctx_type* ctx){  *out = ((ctx->_memory)? i1 : i2);
  ctx->_memory = _false;

} // End of Lustre_arrow_step

// Memory initialisation for Lustre_pre_ctx
void Lustre_pre_ctx_reset(Lustre_pre_ctx_type* ctx){
  int _i;

}

// Initialisation of the  internal structure of Lustre_pre_ctx
void Lustre_pre_ctx_init(Lustre_pre_ctx_type* ctx){
  // ctx->client_data = cdata;
  Lustre_pre_ctx_reset(ctx);
 }
// Step function(s) for Lustre_pre_ctx
void Lustre_pre_get(_boolean *out,Lustre_pre_ctx_type* ctx){
  *out = ctx->_memory;

} // End of Lustre_pre_get

void Lustre_pre_set(_boolean i1,Lustre_pre_ctx_type* ctx){
  ctx->_memory = i1;

} // End of Lustre_pre_set

// Step function(s) for Lustre_slash_ctx
void Lustre_slash_step(_real i1,_real i2,_real *out){
  *out = (i1 / i2);

} // End of Lustre_slash_step

// Memory initialisation for heater_control_heater_control_ctx
void heater_control_heater_control_ctx_reset(heater_control_heater_control_ctx_type* ctx){
  int _i;

    Lustre_pre_ctx_reset(&ctx->Lustre_pre_ctx_tab[0]);
    Lustre_arrow_ctx_reset(&ctx->Lustre_arrow_ctx_tab[0]);
}

// Initialisation of the  internal structure of heater_control_heater_control_ctx
void heater_control_heater_control_ctx_init(heater_control_heater_control_ctx_type* ctx){
  // ctx->client_data = cdata;
  heater_control_heater_control_ctx_reset(ctx);
 }
// Step function(s) for heater_control_heater_control_ctx
void heater_control_heater_control_step(_real T,_real T1,_real T2,_real T3,_boolean *Heat_on,heater_control_heater_control_ctx_type* ctx){   _boolean __split_9_3;
   _real __split_10_3;
   _boolean __split_9_2;
   _real __split_10_2;
   _boolean __split_9_1;
   _real __split_10_1;
   _real __split_1_3;
   _real __split_1_2;
   _real __split_1_1;
   _real __split_2_2;
   _real __split_3_2;
   _real __split_4_2;
   _real __split_5_2;
   _real __split_6_2;
   _real __split_7_2;
   _real __split_8_2;
   _boolean ___split_38_1_2;
   _boolean ___split_38_2_2;
   _boolean ___split_37_1_2;
   _boolean ___split_37_2_2;
   _boolean __split_11_1;
   _real __split_2_1;
   _real __split_3_1;
   _real __split_4_1;
   _real __split_5_1;
   _real __split_6_1;
   _real __split_7_1;
   _real __split_8_1;
   _boolean ___split_38_1_1;
   _boolean ___split_38_2_1;
   _boolean ___split_37_1_1;
   _boolean ___split_37_2_1;
   _boolean __split_43_1;
   _boolean __split_44_1;
   _boolean __split_45_1;
   _boolean __split_46_1;
   _boolean __split_47_1;
   _boolean __split_48_1;
   _boolean __split_49_1;
   _boolean __split_50_1;
   _boolean __split_51_1;
   _boolean __split_52_1;
   _boolean __split_53_1;
   _boolean __split_54_1;
   _boolean __split_55_1;
   _boolean __split_39_1;
   _boolean __split_40_1;
   _boolean __split_41_1;
   _boolean __split_42_1;
   _boolean _split_36;
   _boolean _split_35;
   _boolean _split_34;
   _boolean _split_33;
   _boolean _split_32;
   _boolean _split_31;
   _boolean _split_30;
   _real _split_29;
   _real _split_28;
   _real _split_27;
   _real _split_26;
   _real _split_25;
   _real _split_24;
   _real _split_23;
   _real _split_22;
   _boolean _split_21;
   _real _split_20;
   _boolean _split_19;
   _boolean _split_18;
   _real _split_17;
   _real _split_16;
   _real _split_15;
   _real _split_14;
   _real _split_13;
   _real _split_12;
   _boolean V12;
   _boolean V13;
   _boolean V23;
   _real Tguess;

  _split_16 = T2 - T3;
  __split_10_1 = - _split_16;
  __split_9_1 = _split_16 >= 0.0;
   if (__split_9_1 == _true) {
     _split_17 = _split_16;
   } else {
     _split_17 = __split_10_1;
   }
  V23 = _split_17 < 0.5;
  __split_42_1 = ! V23;
  _split_12 = T1 - T2;
  __split_10_3 = - _split_12;
  __split_9_3 = _split_12 >= 0.0;
   if (__split_9_3 == _true) {
     _split_13 = _split_12;
   } else {
     _split_13 = __split_10_3;
   }
  V12 = _split_13 < 0.5;
  __split_39_1 = ! V12;
  _split_14 = T1 - T3;
  __split_10_2 = - _split_14;
  __split_9_2 = _split_14 >= 0.0;
   if (__split_9_2 == _true) {
     _split_15 = _split_14;
   } else {
     _split_15 = __split_10_2;
   }
  V13 = _split_15 < 0.5;
  __split_40_1 = ! V13;
  __split_41_1 = __split_39_1 & __split_40_1;
  _split_18 = __split_41_1 & __split_42_1;
  __split_43_1 = ! V13;
  __split_44_1 = V12 & __split_43_1;
  __split_45_1 = ! V23;
  __split_46_1 = __split_44_1 & __split_45_1;
  __split_47_1 = ! V12;
  __split_48_1 = V13 & __split_47_1;
  __split_49_1 = ! V23;
  __split_50_1 = __split_48_1 & __split_49_1;
  __split_51_1 = __split_46_1 | __split_50_1;
  __split_54_1 = ! V13;
  __split_52_1 = ! V12;
  __split_53_1 = V23 & __split_52_1;
  __split_55_1 = __split_53_1 & __split_54_1;
  _split_19 = __split_51_1 | __split_55_1;
  ___split_37_1_1 = T2 > T3;
   if (___split_37_1_1 == _true) {
     __split_7_1 = T2;
   } else {
     __split_7_1 = T3;
   }
  ___split_37_2_1 = T1 > __split_7_1;
   if (___split_37_2_1 == _true) {
     __split_8_1 = T1;
   } else {
     __split_8_1 = __split_7_1;
   }
  ___split_38_1_1 = T2 < T3;
   if (___split_38_1_1 == _true) {
     __split_4_1 = T2;
   } else {
     __split_4_1 = T3;
   }
  ___split_38_2_1 = T1 < __split_4_1;
   if (___split_38_2_1 == _true) {
     __split_5_1 = T1;
   } else {
     __split_5_1 = __split_4_1;
   }
  __split_2_1 = T1 + T2;
  __split_3_1 = __split_2_1 + T3;
  __split_6_1 = __split_3_1 - __split_5_1;
  _split_20 = __split_6_1 - __split_8_1;
  __split_1_2 = T1 + T3;
  Lustre_slash_step(__split_1_2,2.0,&_split_24); 
  __split_1_3 = T2 + T3;
  Lustre_slash_step(__split_1_3,2.0,&_split_25); 
   if (V13 == _true) {
     _split_26 = _split_24;
   } else {
     _split_26 = _split_25;
   }
  __split_1_1 = T1 + T2;
  Lustre_slash_step(__split_1_1,2.0,&_split_23); 
   if (V12 == _true) {
     _split_27 = _split_23;
   } else {
     _split_27 = _split_26;
   }
  __split_11_1 = V12 & V13;
  _split_21 = __split_11_1 & V23;
  ___split_37_1_2 = T2 > T3;
   if (___split_37_1_2 == _true) {
     __split_7_2 = T2;
   } else {
     __split_7_2 = T3;
   }
  ___split_37_2_2 = T1 > __split_7_2;
   if (___split_37_2_2 == _true) {
     __split_8_2 = T1;
   } else {
     __split_8_2 = __split_7_2;
   }
  ___split_38_1_2 = T2 < T3;
   if (___split_38_1_2 == _true) {
     __split_4_2 = T2;
   } else {
     __split_4_2 = T3;
   }
  ___split_38_2_2 = T1 < __split_4_2;
   if (___split_38_2_2 == _true) {
     __split_5_2 = T1;
   } else {
     __split_5_2 = __split_4_2;
   }
  __split_2_2 = T1 + T2;
  __split_3_2 = __split_2_2 + T3;
  __split_6_2 = __split_3_2 - __split_5_2;
  _split_22 = __split_6_2 - __split_8_2;
   if (_split_21 == _true) {
     _split_28 = _split_22;
   } else {
     _split_28 = _split_27;
   }
   if (_split_19 == _true) {
     _split_29 = _split_20;
   } else {
     _split_29 = _split_28;
   }
   if (_split_18 == _true) {
     Tguess = -999.0;
   } else {
     Tguess = _split_29;
   }
  _split_30 = Tguess == -999.0;
  _split_31 = Tguess < 6.0;
  Lustre_pre_get(&_split_33,&ctx->Lustre_pre_ctx_tab[0]); 
  _split_32 = Tguess > 9.0;
   if (_split_32 == _true) {
     _split_34 = _false;
   } else {
     _split_34 = _split_33;
   }
   if (_split_31 == _true) {
     _split_35 = _true;
   } else {
     _split_35 = _split_34;
   }
   if (_split_30 == _true) {
     _split_36 = _false;
   } else {
     _split_36 = _split_35;
   }
  Lustre_arrow_step(_true,_split_36,Heat_on,&ctx->Lustre_arrow_ctx_tab[0]); 
  Lustre_pre_set(*Heat_on,&ctx->Lustre_pre_ctx_tab[0]); 

} // End of heater_control_heater_control_step

