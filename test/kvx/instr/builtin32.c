#include "framework.h"

BEGIN_TEST(int)
  int *ptr = &c;
#ifdef __KVX__
  int d = c;
  a = __builtin_kvx_alclrw(ptr);
  c = d;

#endif
END_TEST32()

