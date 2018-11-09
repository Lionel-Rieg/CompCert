#include "../prng/prng.h"
#include "../prng/types.h"

#ifdef __UNIT_TEST_SELECTION__
#define SIZE 100
#else
#include "test.h"
#endif

void swap_sel(uint64_t *a, uint64_t *b){
    uint64_t tmp = *a;
    *a = *b;
    *b = tmp;
}

int select_sort(uint64_t *res, const uint64_t *T){
    int i, j, iMin;

    if (SIZE <= 0)
        return -1;

    for (i = 0 ; i < SIZE ; i++)
        res[i] = T[i];

    for (j = 0 ; j < SIZE ; j++){
        iMin = j;
        for (i = j+1 ; i < SIZE ; i++)
            if (res[i] < res[iMin])
                iMin = i;

        if (iMin != j)
            swap_sel (&res[j], &res[iMin]);
    }

    return 0;
}

#ifdef __UNIT_TEST_SELECTION__
int main(void){
    uint64_t T[SIZE];
    uint64_t res[SIZE];
    uint64_t max;
    int i;
    srand(42);

    for (i = 0 ; i < SIZE ; i++)
        T[i] = randlong();

    /* Sorting the table */
    if (select_sort(res, T) < 0) return -1;

    /* Computing max(T) */
    max = T[0];
    for (i = 1 ; i < SIZE ; i++)
        if (T[i] > max)
            max = T[i];

    /* We should have: max(T) == res[SIZE] */
    return !(max == res[SIZE-1]);
}
#endif // __UNIT_TEST_SELECTION__

