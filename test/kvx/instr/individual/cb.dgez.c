#include "framework.h"

BEGIN_TEST(long long)
{
    if (0 > (a & 0x1LL))
        c = 1;
    else
        c = 0;
}
END_TEST64()
