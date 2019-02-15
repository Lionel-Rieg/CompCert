#include "framework.h"

BEGIN_TEST(long long int)
{
    int j;

    for (j = 0 ; j < (b & 0x8LL) ; j++)
        c += a;
}
END_TEST64()
