#include "framework.h"

BEGIN_TEST_N(unsigned long long, 1)
{
    c = __builtin_kvx_clzd(t[0]);
}
END_TEST()
