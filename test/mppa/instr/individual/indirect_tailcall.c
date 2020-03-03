#include "framework.h"

long long sum(long long a, long long b){
  return a+b;
}

long long diff(long long a, long long b){
  return a-b;
}

long long mul(long long a, long long b){
  return a*b;
}

long long random_op(long long a, long long b){
  long long d = 3;
  long long (*op)(long long, long long);

  if (a % d == 0)
    op = sum;
  else if (a % d == 1)
    op = diff;
  else
    op = mul;

  return op(a, b);
}

BEGIN_TEST(long long)
{
  c += random_op(a, b);
}
END_TEST64()
