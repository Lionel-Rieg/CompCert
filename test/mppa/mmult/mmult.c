#include "../prng/types.h"
#include "../prng/prng.h"

#define __UNIT_TEST_MMULT__

#ifdef __UNIT_TEST_MMULT__
#define SIZE 10
#else
#include "test.h"
#endif

void mmult_row(uint64_t C[][SIZE], uint64_t A[][SIZE], uint64_t B[][SIZE]){
    int i, j, k;

    for (i = 0 ; i < SIZE ; i++)
        for (j = 0 ; j < SIZE ; j++)
            C[i][j] = 0;

    for (i = 0 ; i < SIZE ; i++)
        for (j = 0 ; j < SIZE ; j++)
            for (k = 0 ; k < SIZE ; k++)
                C[i][j] += A[i][k] * B[k][j];
}

void mmult_col(uint64_t C[][SIZE], uint64_t A[][SIZE], uint64_t B[][SIZE]){
    int i, j, k;

    for (i = 0 ; i < SIZE ; i++)
        for (j = 0 ; j < SIZE ; j++)
            C[i][j] = 0;

    for (k = 0 ; k < SIZE ; k++)
        for (i = 0 ; i < SIZE ; i++)
            for (j = 0 ; j < SIZE ; j++)
                C[i][j] += A[i][k] * B[k][j];
}

typedef struct mblock {
    int imin, imax, jmin, jmax;
    uint64_t *mat;
} mblock;

#define MAT_XY(mat, x, y) (mat)[(x)*SIZE + (y)]
#define MAT_IJ(block, i, j) MAT_XY((block)->mat, (block)->imin + (i), block->jmin + (j))

void divac_mul(mblock *C, const mblock *A, const mblock *B){
    const int size = C->imax - C->imin;
    int i, j, k;

    for (i = 0 ; i < size ; i++)
        for (j = 0 ; j < size ; j++)
            for (k = 0 ; k < size ; k++)
                MAT_IJ(C, i, j) += MAT_IJ(A, i, k) * MAT_IJ(B, k, j);
}

#define BLOCK_X_MID(block) ((block)->imin + (block)->imax) / 2
#define BLOCK_Y_MID(block) ((block)->jmin + (block)->jmax) / 2

#define MAKE_MBLOCK(newb, block, I, J) \
    mblock newb = {.mat=(block)->mat};\
    if ((I) == 0){\
        newb.imin = (block)->imin;\
        newb.imax = BLOCK_X_MID((block));\
    } else {\
        newb.imin = BLOCK_X_MID((block));\
        newb.imax = (block)->imax;\
    } if ((J) == 0){\
        newb.jmin = (block)->jmin;\
        newb.jmax = BLOCK_Y_MID((block));\
    } else {\
        newb.jmin = BLOCK_Y_MID((block));\
        newb.jmax = (block)->jmax;\
    }

void divac_part(mblock *C, const mblock *A, const mblock *B);

void divac_wrap(mblock *C      , char IC, char JC,
                   const mblock *A, char IA, char JA,
                   const mblock *B, char IB, char JB){
    MAKE_MBLOCK(Cb, C, IC, JC);
    MAKE_MBLOCK(Ab, A, IA, JA);
    MAKE_MBLOCK(Bb, B, IB, JB);

    divac_part(&Cb, &Ab, &Bb);
}


void divac_part(mblock *C, const mblock *A, const mblock *B){
    const int size = C->imax - C->imin;

    if (size % 2 == 1)
        divac_mul(C, A, B);
    else{
        /* C_00 = A_00 B_00 + A_01 B_10 */
        divac_wrap(C, 0, 0, A, 0, 0, B, 0, 0);
        divac_wrap(C, 0, 0, A, 0, 1, B, 1, 0);

        /* C_10 = A_10 B_00 + A_11 B_10 */
        divac_wrap(C, 1, 0, A, 1, 0, B, 0, 0);
        divac_wrap(C, 1, 0, A, 1, 1, B, 1, 0);

        /* C_01 = A_00 B_01 + A_01 B_11 */
        divac_wrap(C, 0, 1, A, 0, 0, B, 0, 1);
        divac_wrap(C, 0, 1, A, 0, 1, B, 1, 1);

        /* C_11 = A_10 B_01 + A_11 B_11 */
        divac_wrap(C, 1, 1, A, 1, 0, B, 0, 1);
        divac_wrap(C, 1, 1, A, 1, 1, B, 1, 1);
    }
    
}

void mmult_divac(uint64_t C[][SIZE], uint64_t A[][SIZE], uint64_t B[][SIZE]){
    mblock Cb = {.mat = (uint64_t *) C, .imin = 0, .imax = SIZE, .jmin = 0, .jmax = SIZE};
    mblock Ab = {.mat = (uint64_t *) A , .imin = 0, .imax = SIZE, .jmin = 0, .jmax = SIZE};
    mblock Bb = {.mat = (uint64_t *) B , .imin = 0, .imax = SIZE, .jmin = 0, .jmax = SIZE};

    divac_part(&Cb, &Ab, &Bb);
}

#ifdef __UNIT_TEST_MMULT__
static uint64_t C1[SIZE][SIZE], C2[SIZE][SIZE], C3[SIZE][SIZE];
static uint64_t A[SIZE][SIZE], B[SIZE][SIZE];

int main(void){
    srand(42);
    int i, j;

    for (i = 0 ; i < SIZE ; i++)
        for (j = 0 ; j < SIZE ; j++){
            A[i][j] = randlong();
            B[i][j] = randlong();
        }

    mmult_row(C1, A, B);
    mmult_col(C2, A, B);
    mmult_divac(C3, A, B);

    for (i = 0 ; i < SIZE ; i++)
        for (j = 0 ; j < SIZE ; j++)
            if (!(C1[i][j] == C2[i][j] && C1[i][j] == C3[i][j]))
                return -1;

    return 0;
}
#endif /* __UNIT_TEST_MMULT__ */
