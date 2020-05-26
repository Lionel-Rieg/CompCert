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

long long make(long long a){
  return a;
}

BEGIN_TEST(long long)
{
  long long d = 3;
  long long (*op)(long long, long long);

  if (a % d == 0)
    op = sum;
  else if (a % d == 1)
    op = diff;
  else
    op = mul;

  c += op(make(a), make(b));
}
END_TEST64()
