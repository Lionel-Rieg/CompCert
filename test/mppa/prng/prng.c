// https://en.wikipedia.org/wiki/Linear_congruential_generator -> MMIX Donald Knuth
// modulo 2^64 = no need to do it explicitly

#include "types.h"

#define MULTIPLIER 6364136223846793005LL
#define INCREMENT 1442695040888963407LL

static uint64_t current;

void srand(uint64_t seed){
    current = seed;
}

uint64_t randlong(void){
    return (current = MULTIPLIER * current + INCREMENT);
}

#ifdef __UNIT_TEST_PRNG__
char bytewise_sum(uint64_t to_check){
    char sum = 0;
    int i;

    for (i = 0 ; i < 8 ; i++)
        sum += (to_check & (uint64_t)(0xFFULL << i*8)) >> i*8;

    return sum;
}

int main(void){
    srand(42);
    int i;

    for (i = 0 ; i < 1000 ; i++)
        randlong();

    uint64_t last = randlong();

    return !((unsigned char)bytewise_sum(last) == 155);
}
#endif // __UNIT_TEST_PRNG__
