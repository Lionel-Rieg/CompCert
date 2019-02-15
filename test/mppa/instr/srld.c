#include "framework.h"

BEGIN_TEST(unsigned long long)
{
    c = a >> (b & 0x8ULL);
}
END_TEST64()
