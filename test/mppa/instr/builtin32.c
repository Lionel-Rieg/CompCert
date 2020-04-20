#include "framework.h"

BEGIN_TEST(int)
  int *ptr = &c;
#ifdef __K1C__
  int d = c;
  a = __builtin_k1_alclrw(ptr);
  c = d;

#endif
END_TEST32()

