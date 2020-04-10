/*
For knowing how to write assembly profiling stubs.
 */

#include <stdint.h>
#include <stdio.h>
#include <errno.h>

typedef uint8_t md5_hash[16];
typedef uint64_t condition_counters[2];

void _compcert_write_profiling_table(unsigned int nr_items,
				     md5_hash id_table[],
				     condition_counters counter_table[]);

static md5_hash id_table[42] = {{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16}};
static condition_counters counter_table[42];

void write_profile(void) {
  _compcert_write_profiling_table(42, id_table, counter_table);
}

static _Atomic uint64_t counter;

void incr_counter(void) {
  counter++;
}
