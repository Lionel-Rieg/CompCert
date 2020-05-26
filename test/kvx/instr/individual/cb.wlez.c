#include "framework.h"

BEGIN_TEST(int)
{
    if ((a & 0x1) > 0)
        c = 1;
    else
        c = 0;
}
END_TEST32()
