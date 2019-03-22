#include "framework.h"

double long2double(long v){
  return v;
}

BEGIN_TEST(long)
    c = (long) long2double(a) + (long) long2double(b) + (long) long2double(42.3);
END_TEST64()
