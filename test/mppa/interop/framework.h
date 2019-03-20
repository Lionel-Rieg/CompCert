#ifndef __FRAMEWORK_H__
#define __FRAMEWORK_H__

#include <stdio.h>
#include "../prng/prng.c"

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
        type a, b, c, S;\
        int i;\
        srand(0);\
        S = 0;\
        for (i = 0 ; i < 100 ; i++){\
            c = randlong();\
            a = randlong();\
            b = randlong();
    /* END BEGIN_TEST */
            
/* In between BEGIN_TEST and END_TEST : definition of c */

#define END_TEST64()\
            printf("%llu\t%llu\t%llu\n", a, b, c);\
            S += c;\
        }\
        return S;\
    }
    /* END END_TEST64 */

#define END_TEST32()\
            printf("%u\t%u\t%u\n", a, b, c);\
            S += c;\
        }\
        return S;\
    }
    /* END END_TEST32 */

#define END_TESTF32()\
            printf("%e\t%e\t%e\n", a, b, c);\
            S += c;\
        }\
        return 0;\
    }
    /* END END_TESTF32 */

#define END_TESTF64()\
            printf("%e\t%e\t%e\n", a, b, c);\
            S += c;\
        }\
        return 0;\
    }
    /* END END_TESTF64 */

#endif


