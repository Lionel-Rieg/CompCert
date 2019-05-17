/********
* ec2c version 0.67
* context   method = HEAP
* ext call  method = PROCEDURES
* c header file generated for node : heater_control 
* to be used with : heater_control.c 
********/
#ifndef _heater_control_EC2C_H_FILE
#define _heater_control_EC2C_H_FILE
/*-------- Predefined types ---------*/
#ifndef _EC2C_PREDEF_TYPES
#define _EC2C_PREDEF_TYPES
typedef int _boolean;
typedef int _integer;
typedef char* _string;
typedef double _real;
typedef double _double;
typedef float _float;
#define _false 0
#define _true 1
#endif
/*--------- Pragmas ----------------*/
//MODULE: heater_control 4 1
//IN: _real T
//IN: _real T1
//IN: _real T2
//IN: _real T3
//OUT: _boolean Heat_on
#ifndef _heater_control_EC2C_SRC_FILE
/*--------Context type -------------*/
struct heater_control_ctx;
/*-------- Input procedures -------------*/
extern void heater_control_I_T(struct heater_control_ctx* ctx, _real);
extern void heater_control_I_T1(struct heater_control_ctx* ctx, _real);
extern void heater_control_I_T2(struct heater_control_ctx* ctx, _real);
extern void heater_control_I_T3(struct heater_control_ctx* ctx, _real);
/*-------- Reset procedure -----------*/
extern void heater_control_reset(struct heater_control_ctx* ctx);
/*--------Context copy -------------*/
extern void heater_control_copy_ctx(struct heater_control_ctx* dest, struct 
heater_control_ctx* src);
/*--------Context allocation --------*/
extern struct heater_control_ctx* heater_control_new_ctx(void* client_data);
/*-------- Step procedure -----------*/
extern void heater_control_step(struct heater_control_ctx* ctx);
#endif
#endif
