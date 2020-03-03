#include <stdint.h>
#include <stdbool.h>

typedef uint64_t data;
void quicksort(data *A, int len);
void data_vec_random(data *a, unsigned len);
bool data_vec_is_sorted(const data *a, unsigned len);
