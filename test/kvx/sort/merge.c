#include "../prng/prng.h"
#include "../prng/types.h"

//https://en.wikipedia.org/wiki/Merge_sort

#ifdef __UNIT_TEST_MERGE__
#define SIZE 100
#else
#include "test.h"
#endif

int min(int a, int b){
    return (a < b)?a:b;
}

void BottomUpMerge(const uint64_t *A, int iLeft, int iRight, int iEnd, uint64_t *B)
{
    int i = iLeft, j = iRight, k;
    for (k = iLeft; k < iEnd; k++) {
        if (i < iRight && (j >= iEnd || A[i] <= A[j])) {
            B[k] = A[i];
            i = i + 1;
        } else {
            B[k] = A[j];
            j = j + 1;    
        }
    } 
}

void CopyArray(uint64_t *to, const uint64_t *from)
{
    const int n = SIZE;
    int i;

    for(i = 0; i < n; i++)
        to[i] = from[i];
}

void BottomUpMergeSort(uint64_t *A, uint64_t *B)
{
    const int n = SIZE;
    int width, i;

    for (width = 1; width < n; width = 2 * width)
    {
        for (i = 0; i < n; i = i + 2 * width)
        {
            BottomUpMerge(A, i, min(i+width, n), min(i+2*width, n), B);
        }
        CopyArray(A, B);
    }
}

int merge_sort(uint64_t *res, const uint64_t *T){
    int i;

    if (SIZE <= 0)
        return -1;

    uint64_t B[SIZE];
    uint64_t *A = res;
    for (i = 0 ; i < SIZE ; i++)
        A[i] = T[i];

    BottomUpMergeSort(A, B);

    return 0;
}

#ifdef __UNIT_TEST_MERGE__
int main(void){
    uint64_t T[SIZE];
    uint64_t res[SIZE];
    int i;
    srand(42);

    for (i = 0 ; i < SIZE ; i++)
        T[i] = randlong();

    /* Sorting the table */
    if (merge_sort(res, T) < 0) return -1;

    /* Computing max(T) */
    uint64_t max = T[0];
    for (i = 1 ; i < SIZE ; i++)
        if (T[i] > max)
            max = T[i];

    /* We should have: max(T) == res[SIZE] */
    return !(max == res[SIZE-1]);
}
#endif // __UNIT_TEST_MERGE__
