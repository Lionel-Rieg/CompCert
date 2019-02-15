#include "framework.h"

BEGIN_TEST(int)
{
    b = !(a & 0x01);
    if (!b)
        c = 0;
    else
        c = 1;
}
END_TEST32()
