#ifndef __MMULT_H__
#define __MMULT_H__

#include "../lib/types.h"

void mmult_row(uint64_t *A, const uint64_t *B, const uint64_t *C);
void mmult_column(uint64_t *A, const uint64_t *B, const uint64_t *C);
void mmult_strassen(uint64_t *A, const uint64_t *B, const uint64_t *C);

#endif /* __MMULT_H__ */
