#include "framework.h"

int make(int a){
  return a;
}

int sum(int a, int b){
    return make(a+b);
}

BEGIN_TEST(int)
{
    c = sum(a, b);
}
END_TEST32()
/* RETURN VALUE: 60 */
