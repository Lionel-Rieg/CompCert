#include "framework.h"

BEGIN_TEST(long long)
{
    c = a >> (b & 0x8LL);
}
END_TEST64()
