#include "framework.h"

BEGIN_TEST_N(unsigned long long, 2)
{
    c = __builtin_kvx_satd(t[0], t[1]);
}
END_TEST()
