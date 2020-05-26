#include "framework.h"

BEGIN_TEST(int)
{
    int k;
    for (k = 0 ; k < (b & 0x8) ; k++)
        c += a;
}
END_TEST32()
