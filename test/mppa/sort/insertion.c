#include "../lib/prng.h"
#include "../lib/types.h"

#ifdef __UNIT_TEST_INSERTION__
#define SIZE 100
#else
#include "test.h"
#endif

void swap_ins(uint64_t *a, uint64_t *b){
    uint64_t tmp = *a;
    *a = *b;
    *b = tmp;
}

int insert_sort(uint64_t *res, const uint64_t *T){
    if (SIZE <= 0)
        return -1;

    for (int i = 0 ; i < SIZE ; i++)
        res[i] = T[i];

    for (int i = 0 ; i < SIZE-1 ; i++){
        if (res[i] > res[i+1]){
            swap_ins(&res[i], &res[i+1]);
            for (int j = i ; j > 0 ; j--)
                if (res[j-1] > res[j])
                    swap_ins(&res[j-1], &res[j]);
        }
    }

    return 0;
}

#ifdef __UNIT_TEST_INSERTION__
int main(void){
    uint64_t T[SIZE];
    uint64_t res[SIZE];
    srand(42);

    for (int i = 0 ; i < SIZE ; i++)
        T[i] = randlong();

    /* Sorting the table */
    if (insert_sort(res, T) < 0) return -1;

    /* Computing max(T) */
    uint64_t max = T[0];
    for (int i = 1 ; i < SIZE ; i++)
        if (T[i] > max)
            max = T[i];

    /* We should have: max(T) == res[SIZE] */
    return !(max == res[SIZE-1]);
}
#endif // __UNIT_TEST_INSERTION__
