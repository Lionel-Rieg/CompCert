#include <stdint.h>
#include <stdio.h>
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
  
  FILE *fp = fopen("compcert_profiling.dat", "a");
  if (fp == NULL) {
    perror("open CompCert profiling data for writing");
    return;
  }
  
  for(unsigned int i=0; i<nr_items; i++) {
    write_id(fp, &id_table[i]);
    write_counter(fp, counter_table[i][0]);
    write_counter(fp, counter_table[i][1]);
  }

  fclose(fp);
  if (errno != 0) {
    perror("write CompCert profiling data");
    return;
  }
}
