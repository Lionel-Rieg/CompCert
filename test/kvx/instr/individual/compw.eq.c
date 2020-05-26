#include "framework.h"

BEGIN_TEST(int)
{
    c = ((a & 0x1) == (b & 0x1));
}
END_TEST32()
