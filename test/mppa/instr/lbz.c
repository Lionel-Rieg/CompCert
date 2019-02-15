#include "framework.h"

BEGIN_TEST(int)
{
    unsigned char s[] = "Tim is sorry at the playa\n";

    c = s[a & (sizeof(s) - 1)];
}
END_TEST32()
