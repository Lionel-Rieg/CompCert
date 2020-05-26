#include "framework.h"

BEGIN_TEST(long long)
{
    if (a & 0x1LL > 0)
        c = 1;
    else
        c = 0;
}
END_TEST64()
