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

double long2double(long v){
  return v;
}

BEGIN_TEST(long long)
    c = a&b;
    c += a*b;
    c += -a;
    c += a | b;
    c += a-b;
    c += a >> (b & 0x8LL);
    c += a >> (b & 0x8ULL);
    c += a % b;

  long long d = 3;
  long long (*op)(long long, long long);

  if (a % d == 0)
    op = sum;
  else if (a % d == 1)
    op = diff;
  else
    op = mul;

  c += op(make(a), make(b));
  c += random_op(a, b);
    c += a/b;
    c += a^b;
    c += (unsigned int) a;

    if (0 != (a & 0x1LL))
        c += 1;
    else
        c += 2;

    if (0 > (a & 0x1LL))
        c += 4;
    else
        c += 8;

    if (0 >= (a & 0x1LL) - 1)
        c += 16;
    else
        c += 32;

    if (a & 0x1LL > 0)
        c += 64;
    else
        c += 128;

    if ((a & 0x1LL) - 1 >= 0)
        c += 256;
    else
        c += 512;

    if (0 == (a & 0x1LL))
        c += 1024;
    else
        c += 2048;

    c += ((a & 0x1LL) == (b & 0x1LL));
    c += (a >= b);
    c += (a > b);
    c += (a <= b);
    c += (a < b);
    c += (long) long2double(a) + (long) long2double(b) + (long) long2double(42.3);

    int j;

    for (j = 0 ; j < (b & 0x8LL) ; j++)
        c += a;

    c += ((a & 0x1LL) == (b & 0x1LL));

END_TEST64()
