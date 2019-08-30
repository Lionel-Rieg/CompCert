#include "framework.h"

BEGIN_TEST(long long)
  long long *ptr = &c;
#ifdef __K1C__
  /* Removed the AFADDD builtin who was incorrect in CompCert, see #157 */
  // a = __builtin_k1_afaddd(ptr, a);
  // a = __builtin_k1_afaddd(ptr, a);
#endif
END_TEST64()
