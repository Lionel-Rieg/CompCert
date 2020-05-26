#include "../prng/prng.h"
#include "../prng/types.h"

#include "test.h"
#include "insertion.h"
#include "selection.h"
#include "merge.h"

int main(void){
    uint64_t T[SIZE];
    uint64_t res1[SIZE], res2[SIZE], res3[SIZE];
    int i;
    srand(42);

    for (i = 0 ; i < SIZE ; i++)
        T[i] = randlong();

    /* insertion sort */
    if (insert_sort(res1, T) < 0) return -1;

    /* selection sort */
    if (select_sort(res2, T) < 0) return -2;

    /* merge sort */
    if (merge_sort(res3, T) < 0) return -3;

    /* We should have: res1[i] == res2[i] == res3[i] */
    for (i = 0 ; i < SIZE ; i++){
        if (!(res1[i] == res2[i] && res2[i] == res3[i]))
            return -4;
    }

    return 0;
}
