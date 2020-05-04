/* *************************************************************/
/*                                                             */
/*             The Compcert verified compiler                  */
/*                                                             */
/*           David Monniaux     CNRS, VERIMAG                  */
/*                                                             */
/*  Copyright VERIMAG. All rights reserved.                    */
/*  This file is distributed under the terms of the INRIA      */
/*  Non-Commercial License Agreement.                          */
/*                                                             */
/* *************************************************************/

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <errno.h>

typedef uint8_t md5_hash[16];
typedef uint64_t condition_counters[2];

static void write_id(FILE *fp, md5_hash *hash) {
  fwrite(hash, 16, 1, fp);
}

#define BYTE(counter, i) ((counter >> (8*i)) & 0xFF)
static void write_counter(FILE *fp, uint64_t counter) {
  putc(BYTE(counter, 0), fp);
  putc(BYTE(counter, 1), fp);
  putc(BYTE(counter, 2), fp);
  putc(BYTE(counter, 3), fp);
  putc(BYTE(counter, 4), fp);
  putc(BYTE(counter, 5), fp);
  putc(BYTE(counter, 6), fp);
  putc(BYTE(counter, 7), fp);
}

void _compcert_write_profiling_table(unsigned int nr_items,
				      md5_hash id_table[],
				      condition_counters counter_table[]) {
  errno = 0;

  const char *filename = getenv("COMPCERT_PROFILING_DATA");
  if (filename) {
    if (!*filename) return;
  } else {
    filename = "compcert_profiling.dat";
  }
  
  FILE *fp = fopen(filename, "a");
  //fprintf(stderr, "successfully opened profiling file\n");
  if (fp == NULL) {
    perror("open CompCert profiling data for writing");
    return;
  }
  
  for(unsigned int i=0; i<nr_items; i++) {
    write_id(fp, &id_table[i]);
    write_counter(fp, counter_table[i][0]);
    write_counter(fp, counter_table[i][1]);
  }
  //fprintf(stderr, "successfully written profiling file\n");

  fclose(fp);
  //fprintf(stderr, "successfully closed profiling file\n");
  if (errno != 0) {
    perror("write CompCert profiling data");
    return;
  }
  // fprintf(stderr, "write CompCert profiling data: no error\n");
}
