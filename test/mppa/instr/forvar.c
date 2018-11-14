#include "framework.h"

BEGIN_TEST(int)
{
    int j;
    for (j = 0 ; j < (b & 0x8) ; j++)
        c += a;
}
END_TEST()
