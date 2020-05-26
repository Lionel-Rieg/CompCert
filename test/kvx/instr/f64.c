#include "framework.h"

BEGIN_TEST(double)
    c = ((double)a + (double)b);
    c += ((double)a * (double)b);
    c += (-(double)a);
    c += ((double)a - (double)b);
END_TESTF64()
