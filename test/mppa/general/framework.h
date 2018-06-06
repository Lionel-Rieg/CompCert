#ifndef __FRAMEWORK_H__
#define __FRAMEWORK_H__

#include "../lib/prng.c"

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
            S += c;\
        }\
        return S;\
    }
    /* END END_TEST */

#endif
