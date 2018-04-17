#include "../lib/prng.h"
#include "../lib/types.h"

void swap(uint64_t *a, uint64_t *b){
    uint64_t tmp = *a;
    *a = *b;
    *b = tmp;
}

int selection_sort(uint64_t *res, const uint64_t *T, int size){
    if (size <= 0)
        return -1;

    for (int i = 0 ; i < size ; i++)
        res[i] = T[i];

    for (int j = 0 ; j < size ; j++){
        int i;
        int iMin = j;
        for (i = j+1 ; i < size ; i++)
            if (res[i] < res[iMin])
                iMin = i;

        if (iMin != j)
            swap (&res[j], &res[iMin]);
    }

    return 0;
}

#ifdef __UNIT_TEST_SELECTION__
#define SIZE 100

int main(void){
    uint64_t T[SIZE];
    uint64_t res[SIZE];
    srand(42);

    for (int i = 0 ; i < SIZE ; i++)
        T[i] = randlong();

    /* Sorting the table */
    if (selection_sort(res, T, SIZE) < 0) return -1;

    /* Computing max(T) */
    uint64_t max = T[0];
    for (int i = 1 ; i < SIZE ; i++)
        if (T[i] > max)
            max = T[i];

    /* We should have: max(T) == res[SIZE] */
    return !(max == res[SIZE-1]);
}
#endif // __UNIT_TEST_SELECTION__

