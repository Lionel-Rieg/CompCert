#include "framework.h"

BEGIN_TEST(unsigned int)
{
    c = (long long) a;
    c += (a >= b);
    c += (a > b);
    c += (a <= b);
    c += (a < b);
    c += ((a & 0x1U) != (b & 0x1U));
}
END_TEST32()
