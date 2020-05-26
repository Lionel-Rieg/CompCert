#include "framework.h"

BEGIN_TEST(long long)
{
    c = ((a & 0x1LL) == (b & 0x1LL));
}
END_TEST64()
