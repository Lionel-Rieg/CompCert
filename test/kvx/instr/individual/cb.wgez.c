#include "framework.h"

BEGIN_TEST(int)
{
    if (0 > (a & 0x1) - 1)
        c = 1;
    else
        c = 0;
}
END_TEST32()
