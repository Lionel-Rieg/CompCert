/* This file was generated by lv6 version master.737 (2727a7744111c84f7984634d2bd3ad6f7c6c7ff9). */
/*  lv6 carlightV2.lus -n carlight --to-c */
/* on vanoise the 08/05/2019 at 22:54:09 */
#include "carlightV2_carlight.h"
//// Defining step functions
// Memory initialisation for Lustre_arrow_ctx
void Lustre_arrow_ctx_reset(Lustre_arrow_ctx_type* ctx){
  int _i;
  ctx->_memory = _true;
}
// Memory allocation for Lustre_arrow_ctx
Lustre_arrow_ctx_type* Lustre_arrow_ctx_new_ctx(){

   Lustre_arrow_ctx_type* ctx = (Lustre_arrow_ctx_type*)calloc(1, sizeof(Lustre_arrow_ctx_type));
   // ctx->client_data = cdata;
   Lustre_arrow_ctx_reset(ctx);
  return ctx;
}
// Step function(s) for Lustre_arrow_ctx
void Lustre_arrow_step(_boolean i1,_boolean i2,_boolean *out,Lustre_arrow_ctx_type* ctx){  *out = ((ctx->_memory)? i1 : i2);
  ctx->_memory = _false;

} // End of Lustre_arrow_step

// Memory initialisation for Lustre_arrow_2_ctx
void Lustre_arrow_2_ctx_reset(Lustre_arrow_2_ctx_type* ctx){
  int _i;
  ctx->_memory = _true;
}
// Memory allocation for Lustre_arrow_2_ctx
Lustre_arrow_2_ctx_type* Lustre_arrow_2_ctx_new_ctx(){

   Lustre_arrow_2_ctx_type* ctx = (Lustre_arrow_2_ctx_type*)calloc(1, sizeof(Lustre_arrow_2_ctx_type));
   // ctx->client_data = cdata;
   Lustre_arrow_2_ctx_reset(ctx);
  return ctx;
}
// Step function(s) for Lustre_arrow_2_ctx
void Lustre_arrow_2_step(_real i1,_real i2,_real *out,Lustre_arrow_2_ctx_type* ctx){  *out = ((ctx->_memory)? i1 : i2);
  ctx->_memory = _false;

} // End of Lustre_arrow_2_step

// Memory initialisation for Lustre_pre_ctx
void Lustre_pre_ctx_reset(Lustre_pre_ctx_type* ctx){
  int _i;

}
// Memory allocation for Lustre_pre_ctx
Lustre_pre_ctx_type* Lustre_pre_ctx_new_ctx(){

   Lustre_pre_ctx_type* ctx = (Lustre_pre_ctx_type*)calloc(1, sizeof(Lustre_pre_ctx_type));
   // ctx->client_data = cdata;
   Lustre_pre_ctx_reset(ctx);
  return ctx;
}
// Step function(s) for Lustre_pre_ctx
void Lustre_pre_get(_boolean *out,Lustre_pre_ctx_type* ctx){
  *out = ctx->_memory;

} // End of Lustre_pre_get

void Lustre_pre_set(_boolean i1,Lustre_pre_ctx_type* ctx){
  ctx->_memory = i1;

} // End of Lustre_pre_set

// Memory initialisation for Lustre_pre_2_ctx
void Lustre_pre_2_ctx_reset(Lustre_pre_2_ctx_type* ctx){
  int _i;

}
// Memory allocation for Lustre_pre_2_ctx
Lustre_pre_2_ctx_type* Lustre_pre_2_ctx_new_ctx(){

   Lustre_pre_2_ctx_type* ctx = (Lustre_pre_2_ctx_type*)calloc(1, sizeof(Lustre_pre_2_ctx_type));
   // ctx->client_data = cdata;
   Lustre_pre_2_ctx_reset(ctx);
  return ctx;
}
// Step function(s) for Lustre_pre_2_ctx
void Lustre_pre_2_get(_real *out,Lustre_pre_2_ctx_type* ctx){
  *out = ctx->_memory;

} // End of Lustre_pre_2_get

void Lustre_pre_2_set(_real i1,Lustre_pre_2_ctx_type* ctx){
  ctx->_memory = i1;

} // End of Lustre_pre_2_set

// Memory initialisation for carlightV2_carlight_ctx
void carlightV2_carlight_ctx_reset(carlightV2_carlight_ctx_type* ctx){
  int _i;

    carlightV2_front_montant_ctx_reset(&ctx->carlightV2_front_montant_ctx_tab[0]);
    carlightV2_carlight_auto_ctx_reset(&ctx->carlightV2_carlight_auto_ctx_tab[0]);
    Lustre_pre_ctx_reset(&ctx->Lustre_pre_ctx_tab[0]);
}
// Memory allocation for carlightV2_carlight_ctx
carlightV2_carlight_ctx_type* carlightV2_carlight_ctx_new_ctx(){

   carlightV2_carlight_ctx_type* ctx = (carlightV2_carlight_ctx_type*)calloc(1, sizeof(carlightV2_carlight_ctx_type));
   // ctx->client_data = cdata;
   carlightV2_carlight_ctx_reset(ctx);
  return ctx;
}
// Step function(s) for carlightV2_carlight_ctx
void carlightV2_carlight_step(_integer switch_pos,_real intensity,_boolean *is_on,carlightV2_carlight_ctx_type* ctx){   _boolean _split_8;
   _boolean _split_7;
   _boolean _split_6;
   _real _split_5;
   _boolean _split_4;
   _boolean _split_3;
   _boolean _split_2;
   _boolean _split_1;
   _boolean fm_auto;
   _boolean res_auto;

  _split_1 = switch_pos == carlightV2_AUTO;
  carlightV2_front_montant_step(_split_1,&fm_auto,&ctx->carlightV2_front_montant_ctx_tab[0]); 
  Lustre_pre_get(&_split_6,&ctx->Lustre_pre_ctx_tab[0]); 
  switch (switch_pos){
  case carlightV2_AUTO:
  _split_7 = _split_6;
  _split_5 = intensity;
  carlightV2_carlight_auto_step(_split_5,_split_7,&_split_8,&ctx->carlightV2_carlight_auto_ctx_tab[0]); 
  break;
}
  _split_3 = intensity <= 70.0;
  switch (switch_pos){
  case carlightV2_AUTO:
  _split_4 = _split_3;
  _split_2 = fm_auto;
   if (_split_2 == _true) {
     res_auto = _split_4;
   } else {
     res_auto = _split_8;
   }
  *is_on = res_auto;
  break;
  case carlightV2_OFF:
  *is_on = _false;
  break;
  case carlightV2_ON:
  *is_on = _true;
  break;
}
  Lustre_pre_set(*is_on,&ctx->Lustre_pre_ctx_tab[0]); 

} // End of carlightV2_carlight_step

// Memory initialisation for carlightV2_carlight_auto_ctx
void carlightV2_carlight_auto_ctx_reset(carlightV2_carlight_auto_ctx_type* ctx){
  int _i;

    carlightV2_vrai_depuis_n_secondes_ctx_reset(&ctx->carlightV2_vrai_depuis_n_secondes_ctx_tab[0]);
    carlightV2_vrai_depuis_n_secondes_ctx_reset(&ctx->carlightV2_vrai_depuis_n_secondes_ctx_tab[1]);
}
// Memory allocation for carlightV2_carlight_auto_ctx
carlightV2_carlight_auto_ctx_type* carlightV2_carlight_auto_ctx_new_ctx(){

   carlightV2_carlight_auto_ctx_type* ctx = (carlightV2_carlight_auto_ctx_type*)calloc(1, sizeof(carlightV2_carlight_auto_ctx_type));
   // ctx->client_data = cdata;
   carlightV2_carlight_auto_ctx_reset(ctx);
  return ctx;
}
// Step function(s) for carlightV2_carlight_auto_ctx
void carlightV2_carlight_auto_step(_real intensity,_boolean pre_is_on,_boolean *res,carlightV2_carlight_auto_ctx_type* ctx){   _boolean _split_17;
   _boolean _split_16;
   _boolean _split_15;
   _boolean _split_14;
   _boolean _split_13;
   _boolean _split_12;
   _boolean _split_11;
   _boolean _split_10;
   _boolean _split_9;

  _split_14 = intensity < 60.0;
  _split_13 = ! pre_is_on;
  _split_15 = _split_13 & _split_14;
  carlightV2_vrai_depuis_n_secondes_step(_split_15,2.0,&_split_16,&ctx->carlightV2_vrai_depuis_n_secondes_ctx_tab[0]); 
   if (_split_16 == _true) {
     _split_17 = _true;
   } else {
     _split_17 = pre_is_on;
   }
  _split_9 = intensity > 70.0;
  _split_10 = pre_is_on & _split_9;
  carlightV2_vrai_depuis_n_secondes_step(_split_10,3.0,&_split_11,&ctx->carlightV2_vrai_depuis_n_secondes_ctx_tab[1]); 
   if (_split_11 == _true) {
     _split_12 = _false;
   } else {
     _split_12 = pre_is_on;
   }
   if (pre_is_on == _true) {
     *res = _split_12;
   } else {
     *res = _split_17;
   }

} // End of carlightV2_carlight_auto_step

// Memory initialisation for carlightV2_front_montant_ctx
void carlightV2_front_montant_ctx_reset(carlightV2_front_montant_ctx_type* ctx){
  int _i;

    Lustre_pre_ctx_reset(&ctx->Lustre_pre_ctx_tab[0]);
    Lustre_arrow_ctx_reset(&ctx->Lustre_arrow_ctx_tab[0]);
}
// Memory allocation for carlightV2_front_montant_ctx
carlightV2_front_montant_ctx_type* carlightV2_front_montant_ctx_new_ctx(){

   carlightV2_front_montant_ctx_type* ctx = (carlightV2_front_montant_ctx_type*)calloc(1, sizeof(carlightV2_front_montant_ctx_type));
   // ctx->client_data = cdata;
   carlightV2_front_montant_ctx_reset(ctx);
  return ctx;
}
// Step function(s) for carlightV2_front_montant_ctx
void carlightV2_front_montant_step(_boolean x,_boolean *res,carlightV2_front_montant_ctx_type* ctx){   _boolean _split_20;
   _boolean _split_19;
   _boolean _split_18;

  Lustre_pre_get(&_split_18,&ctx->Lustre_pre_ctx_tab[0]); 
  _split_19 = ! _split_18;
  _split_20 = x & _split_19;
  Lustre_pre_set(x,&ctx->Lustre_pre_ctx_tab[0]); 
  Lustre_arrow_step(x,_split_20,res,&ctx->Lustre_arrow_ctx_tab[0]); 

} // End of carlightV2_front_montant_step

// Step function(s) for carlightV2_max_ctx
void carlightV2_max_step(_real x,_real y,_real *res){
   _boolean _split_21;

  _split_21 = x > y;
   if (_split_21 == _true) {
     *res = x;
   } else {
     *res = y;
   }

} // End of carlightV2_max_step

// Memory initialisation for carlightV2_vrai_depuis_n_secondes_ctx
void carlightV2_vrai_depuis_n_secondes_ctx_reset(carlightV2_vrai_depuis_n_secondes_ctx_type* ctx){
  int _i;

    Lustre_pre_2_ctx_reset(&ctx->Lustre_pre_2_ctx_tab[0]);
    Lustre_arrow_2_ctx_reset(&ctx->Lustre_arrow_2_ctx_tab[0]);
}
// Memory allocation for carlightV2_vrai_depuis_n_secondes_ctx
carlightV2_vrai_depuis_n_secondes_ctx_type* carlightV2_vrai_depuis_n_secondes_ctx_new_ctx(){

   carlightV2_vrai_depuis_n_secondes_ctx_type* ctx = (carlightV2_vrai_depuis_n_secondes_ctx_type*)calloc(1, sizeof(carlightV2_vrai_depuis_n_secondes_ctx_type));
   // ctx->client_data = cdata;
   carlightV2_vrai_depuis_n_secondes_ctx_reset(ctx);
  return ctx;
}
// Step function(s) for carlightV2_vrai_depuis_n_secondes_ctx
void carlightV2_vrai_depuis_n_secondes_step(_boolean signal,_real n,_boolean *res,carlightV2_vrai_depuis_n_secondes_ctx_type* ctx){   _real _split_26;
   _real _split_25;
   _real _split_24;
   _real _split_23;
   _boolean _split_22;
   _real tempo;

  _split_22 = ! signal;
  Lustre_pre_2_get(&_split_23,&ctx->Lustre_pre_2_ctx_tab[0]); 
  _split_24 = _split_23 - 0.5;
  carlightV2_max_step(0.0,_split_24,&_split_25); 
   if (_split_22 == _true) {
     _split_26 = n;
   } else {
     _split_26 = _split_25;
   }
  Lustre_arrow_2_step(n,_split_26,&tempo,&ctx->Lustre_arrow_2_ctx_tab[0]); 
  Lustre_pre_2_set(tempo,&ctx->Lustre_pre_2_ctx_tab[0]); 
  *res = tempo == 0.0;

} // End of carlightV2_vrai_depuis_n_secondes_step

