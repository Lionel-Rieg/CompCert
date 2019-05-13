/* --- Generated the 13/5/2019 at 10:21 --- */
/* --- heptagon compiler, version 1.05.00 (compiled mon. may. 13 10:18:8 CET 2019) --- */
/* --- Command line: /local/STATOR/packages/opam-root/4.07.1/bin/heptc -target c -hepts -s main -target ctrln radiotrans.ept --- */

#ifndef RADIOTRANS_TYPES_H
#define RADIOTRANS_TYPES_H

#include "stdbool.h"
#include "assert.h"
#include "pervasives.h"
#include "radiotrans_controller_types.h"
typedef enum {
  Radiotrans__St_3_Tx,
  Radiotrans__St_3_Sleep,
  Radiotrans__St_3_Rx_Packet,
  Radiotrans__St_3_Rx,
  Radiotrans__St_3_Idle,
  Radiotrans__St_3_Calibrate
} Radiotrans__st_3;

Radiotrans__st_3 Radiotrans__st_3_of_string(char* s);

char* string_of_Radiotrans__st_3(Radiotrans__st_3 x, char* buf);

typedef enum {
  Radiotrans__St_2_On,
  Radiotrans__St_2_Off
} Radiotrans__st_2;

Radiotrans__st_2 Radiotrans__st_2_of_string(char* s);

char* string_of_Radiotrans__st_2(Radiotrans__st_2 x, char* buf);

typedef enum {
  Radiotrans__St_1_On,
  Radiotrans__St_1_Off
} Radiotrans__st_1;

Radiotrans__st_1 Radiotrans__st_1_of_string(char* s);

char* string_of_Radiotrans__st_1(Radiotrans__st_1 x, char* buf);

typedef enum {
  Radiotrans__St_Tx,
  Radiotrans__St_Sleep,
  Radiotrans__St_Rx_Packet,
  Radiotrans__St_Rx,
  Radiotrans__St_Idle,
  Radiotrans__St_Calibrate
} Radiotrans__st;

Radiotrans__st Radiotrans__st_of_string(char* s);

char* string_of_Radiotrans__st(Radiotrans__st x, char* buf);

#endif // RADIOTRANS_TYPES_H
