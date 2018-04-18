#include "../lib/types.h"
#include "../lib/prng.h"

#define __UNIT_TEST_MMULT__

#ifdef __UNIT_TEST_MMULT__
#define SIZE 50
#else
#include "test.h"
#endif

void mmult_row(uint64_t C[][SIZE], uint64_t A[][SIZE], uint64_t B[][SIZE]){
    for (int i = 0 ; i < SIZE ; i++)
        for (int j = 0 ; j < SIZE ; j++)
            C[i][j] = 0;

    for (int i = 0 ; i < SIZE ; i++)
        for (int j = 0 ; j < SIZE ; j++)
            for (int k = 0 ; k < SIZE ; k++)
                C[i][j] += A[i][k] * B[k][j];
}

void mmult_col(uint64_t C[][SIZE], uint64_t A[][SIZE], uint64_t B[][SIZE]){
    for (int i = 0 ; i < SIZE ; i++)
        for (int j = 0 ; j < SIZE ; j++)
            C[i][j] = 0;

    for (int k = 0 ; k < SIZE ; k++)
        for (int i = 0 ; i < SIZE ; i++)
            for (int j = 0 ; j < SIZE ; j++)
                C[i][j] += A[i][k] * B[k][j];
}

#ifdef __UNIT_TEST_MMULT__
static uint64_t C1[SIZE][SIZE], C2[SIZE][SIZE], A[SIZE][SIZE], B[SIZE][SIZE];

int main(void){
    srand(42);

    for (int i = 0 ; i < SIZE ; i++)
        for (int j = 0 ; j < SIZE ; j++){
            A[i][j] = randlong();
            B[i][j] = randlong();
        }

    mmult_row(C1, A, B);
    mmult_col(C2, A, B);

    for (int i = 0 ; i < SIZE ; i++)
        for (int j = 0 ; j < SIZE ; j++)
            if (C1[i][j] != C2[i][j])
                return -1;

    return 0;
}
#endif /* __UNIT_TEST_MMULT__ */
