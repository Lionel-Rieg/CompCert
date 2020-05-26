#include "framework.h"

BEGIN_TEST(int)
{
    char s[] = "Tome and Cherry at the playa\n";

    c = s[(a & (sizeof(s)-1))];
}
END_TEST32()
