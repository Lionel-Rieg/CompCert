#include "framework.h"

BEGIN_TEST(unsigned long long)
{
    c = (a > b);
    c += (a <= b);
    c += (a < b);
    c += ((a & 0x1ULL) != (b & 0x1ULL));
}
END_TEST64()
