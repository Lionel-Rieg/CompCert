// https://en.wikipedia.org/wiki/Linear_congruential_generator -> MMIX Donald Knuth
// modulo 2^64 = no need to do it explicitly

#define MULTIPLIER 6364136223846793005LL
#define INCREMENT 1442695040888963407LL

static unsigned long long current;

void srand(long long seed){
    seed = current;
}

unsigned long long randlong(void){
    return (current = MULTIPLIER * current + INCREMENT);
}

#ifdef __UNIT_TEST__
char bytewise_sum(unsigned long long to_check){
    char sum = 0;

    for (int i = 0 ; i < 8 ; i++)
        sum += (to_check & (unsigned long long)(0xFFULL << i*8)) >> i*8;

    return sum;
}

int main(void){
    srand(42);

    if (bytewise_sum(0xdeadbeefb00b1355ULL) != 91)
        return 1;

    for (int i = 0 ; i < 1000 ; i++)
        randlong();

    unsigned long long last = randlong();

    return !((unsigned char)bytewise_sum(last) == 251);
}
#endif // __UNIT_TEST__
