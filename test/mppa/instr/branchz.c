#include "framework.h"

BEGIN_TEST(int)
{
    if (a & 0x1 == 0)
        c = 0;
    else
        c = 1;
}
END_TEST32()
