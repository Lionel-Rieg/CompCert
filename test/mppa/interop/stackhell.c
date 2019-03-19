#include "framework.h"
#include "common.h"

BEGIN_TEST(double)
  c = stackhell(a, b, a*b, a*b, a*2, b*2, a*2*b, a*b*2, (a*b)*2, (a*b)*2,
                  2*a, 2*b, a*b, a*b, a*3, b*3, a*3*b, a*b*3, (a*b)*3, (a*b)*3,
                  3*a, 3*b, a*b, a*b, a*4, b*4, a*4*b, a*b*4, (a*b)*4, (a*b)*4);
  
END_TESTF64()
