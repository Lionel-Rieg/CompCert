#include "framework.h"

float int2float(int v){
  return v;
}

BEGIN_TEST(int)
    c = (int) int2float(a) + (int) int2float(b) + (int) int2float(42.3);
END_TEST32()
