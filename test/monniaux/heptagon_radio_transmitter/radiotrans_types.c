/* --- Generated the 13/5/2019 at 10:21 --- */
/* --- heptagon compiler, version 1.05.00 (compiled mon. may. 13 10:18:8 CET 2019) --- */
/* --- Command line: /local/STATOR/packages/opam-root/4.07.1/bin/heptc -target c -hepts -s main -target ctrln radiotrans.ept --- */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include "radiotrans_types.h"

Radiotrans__st_3 Radiotrans__st_3_of_string(char* s) {
  if ((strcmp(s, "St_3_Tx")==0)) {
    return Radiotrans__St_3_Tx;
  };
  if ((strcmp(s, "St_3_Sleep")==0)) {
    return Radiotrans__St_3_Sleep;
  };
  if ((strcmp(s, "St_3_Rx_Packet")==0)) {
    return Radiotrans__St_3_Rx_Packet;
  };
  if ((strcmp(s, "St_3_Rx")==0)) {
    return Radiotrans__St_3_Rx;
  };
  if ((strcmp(s, "St_3_Idle")==0)) {
    return Radiotrans__St_3_Idle;
  };
  if ((strcmp(s, "St_3_Calibrate")==0)) {
    return Radiotrans__St_3_Calibrate;
  };
}

char* string_of_Radiotrans__st_3(Radiotrans__st_3 x, char* buf) {
  switch (x) {
    case Radiotrans__St_3_Tx:
      strcpy(buf, "St_3_Tx");
      break;
    case Radiotrans__St_3_Sleep:
      strcpy(buf, "St_3_Sleep");
      break;
    case Radiotrans__St_3_Rx_Packet:
      strcpy(buf, "St_3_Rx_Packet");
      break;
    case Radiotrans__St_3_Rx:
      strcpy(buf, "St_3_Rx");
      break;
    case Radiotrans__St_3_Idle:
      strcpy(buf, "St_3_Idle");
      break;
    case Radiotrans__St_3_Calibrate:
      strcpy(buf, "St_3_Calibrate");
      break;
    default:
      break;
  };
  return buf;
}

Radiotrans__st_2 Radiotrans__st_2_of_string(char* s) {
  if ((strcmp(s, "St_2_On")==0)) {
    return Radiotrans__St_2_On;
  };
  if ((strcmp(s, "St_2_Off")==0)) {
    return Radiotrans__St_2_Off;
  };
}

char* string_of_Radiotrans__st_2(Radiotrans__st_2 x, char* buf) {
  switch (x) {
    case Radiotrans__St_2_On:
      strcpy(buf, "St_2_On");
      break;
    case Radiotrans__St_2_Off:
      strcpy(buf, "St_2_Off");
      break;
    default:
      break;
  };
  return buf;
}

Radiotrans__st_1 Radiotrans__st_1_of_string(char* s) {
  if ((strcmp(s, "St_1_On")==0)) {
    return Radiotrans__St_1_On;
  };
  if ((strcmp(s, "St_1_Off")==0)) {
    return Radiotrans__St_1_Off;
  };
}

char* string_of_Radiotrans__st_1(Radiotrans__st_1 x, char* buf) {
  switch (x) {
    case Radiotrans__St_1_On:
      strcpy(buf, "St_1_On");
      break;
    case Radiotrans__St_1_Off:
      strcpy(buf, "St_1_Off");
      break;
    default:
      break;
  };
  return buf;
}

Radiotrans__st Radiotrans__st_of_string(char* s) {
  if ((strcmp(s, "St_Tx")==0)) {
    return Radiotrans__St_Tx;
  };
  if ((strcmp(s, "St_Sleep")==0)) {
    return Radiotrans__St_Sleep;
  };
  if ((strcmp(s, "St_Rx_Packet")==0)) {
    return Radiotrans__St_Rx_Packet;
  };
  if ((strcmp(s, "St_Rx")==0)) {
    return Radiotrans__St_Rx;
  };
  if ((strcmp(s, "St_Idle")==0)) {
    return Radiotrans__St_Idle;
  };
  if ((strcmp(s, "St_Calibrate")==0)) {
    return Radiotrans__St_Calibrate;
  };
}

char* string_of_Radiotrans__st(Radiotrans__st x, char* buf) {
  switch (x) {
    case Radiotrans__St_Tx:
      strcpy(buf, "St_Tx");
      break;
    case Radiotrans__St_Sleep:
      strcpy(buf, "St_Sleep");
      break;
    case Radiotrans__St_Rx_Packet:
      strcpy(buf, "St_Rx_Packet");
      break;
    case Radiotrans__St_Rx:
      strcpy(buf, "St_Rx");
      break;
    case Radiotrans__St_Idle:
      strcpy(buf, "St_Idle");
      break;
    case Radiotrans__St_Calibrate:
      strcpy(buf, "St_Calibrate");
      break;
    default:
      break;
  };
  return buf;
}

