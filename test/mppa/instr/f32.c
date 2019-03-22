#include "framework.h"

BEGIN_TEST(float)
    c = ((float)a + (float)b);
    c += ((float)a * (float)b);
    c += (-(float)a);
    c += ((float)a - (float)b);
END_TESTF32()
