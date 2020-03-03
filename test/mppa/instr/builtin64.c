#include "framework.h"

BEGIN_TEST(long long)
  long long *ptr = &c;
#ifdef __K1C__
  long long d = c;
  a = __builtin_k1_alclrd(ptr);
  c = d;
  c += a;

  c += __builtin_clzll(a);

  /* Removed the AFADDD builtin who was incorrect in CompCert, see #157 */
  // a = __builtin_k1_afaddd(ptr, a);
  // a = __builtin_k1_afaddd(ptr, a);
#endif
END_TEST64()
