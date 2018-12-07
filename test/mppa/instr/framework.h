#ifndef __FRAMEWORK_H__
#define __FRAMEWORK_H__

#include "../prng/prng.c"

int printf(const char *, ...);

#define BEGIN_TEST_N(type, N)\
    int main(void){\
        type t[N], c, i, j, S;\
        srand(0);\
        S = 0;\
        for (i = 0 ; i < 100 ; i++){\
            c = randlong();\
            for (j = 0 ; j < N ; j++)\
                t[j] = randlong();\
    /* END BEGIN_TEST_N */

#define BEGIN_TEST(type)\
    int main(void){\
        type a, b, c, i, S;\
        srand(0);\
        S = 0;\
        for (i = 0 ; i < 100 ; i++){\
            c = randlong();\
            a = randlong();\
            b = randlong();
    /* END BEGIN_TEST */
            
/* In between BEGIN_TEST and END_TEST : definition of c */

#define END_TEST()\
            printf("%llu\n", c);\
            S += c;\
        }\
        return S;\
    }
    /* END END_TEST */

#endif
