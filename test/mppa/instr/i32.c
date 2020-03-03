#include "framework.h"

int sum(int a, int b){
    return a+b;
}

int make(int a){
    return a;
}

int tailsum(int a, int b){
    return make(a+b);
}

int fact(int a){
  int r = 1;
  int i;
  for (i = 1; i < a; i++)
    r *= i;
  return r;
}

float int2float(int v){
  return v;
}

BEGIN_TEST(int)
    c = a+b;
    c += a&b;

    /* testing if, cb version */
    if ((a & 0x1) == 1)
        c += fact(1);
    else
        c += fact(2);

    if (a & 0x1 == 0)
        c += fact(4);
    else
        c += fact(8);

    if (a & 0x1 == 0)
        c += fact(4);
    else
        c += fact(8);

    b = !(a & 0x01);
    if (!b)
        c += fact(16);
    else
        c += fact(32);

    c += sum(make(a), make(b));
    c += (long long) a;

    if (0 > (a & 0x1) - 1)
        c += fact(64);
    else
        c += fact(128);

    if (0 >= (a & 0x1))
        c += fact(256);
    else
        c += fact(512);

    if ((a & 0x1) > 0)
        c += fact(1024);
    else
        c += fact(2048);

    if ((a & 0x1) - 1 >= 0)
        c += fact(4096);
    else
        c += fact(8192);

    /* cmoved version */
    if ((a & 0x1) == 1)
        c += 1;
    else
        c += 2;

    if (a & 0x1 == 0)
        c += 4;
    else
        c += 8;

    if (a & 0x1 == 0)
        c += 4;
    else
        c += 8;

    b = !(a & 0x01);
    if (!b)
        c += 16;
    else
        c += 32;

    if (0 > (a & 0x1) - 1)
        c += 64;
    else
        c += 128;

    if (0 >= (a & 0x1))
        c += 256;
    else
        c += 512;

    if ((a & 0x1) > 0)
        c += 1024;
    else
        c += 2048;

    if ((a & 0x1) - 1 >= 0)
        c += 4096;
    else
        c += 8192;

    c += ((a & 0x1) == (b & 0x1));
    c += (a > b);
    c += (a <= b);
    c += (a < b);
    c += (a + b) / 2;
    c += (int) int2float(a) + (int) int2float(b) + (int) int2float(42.3);
    c += (a << 4); // addx16w
    c += (a << 3); // addx8w
    c += (a << 2); // addx4w
    c += (a << 1); // addx2w

    c += ~a & b; // andnw

    int j;
    for (j = 0 ; j < 10 ; j++)
        c += a;
    int k;
    for (k = 0 ; k < (b & 0x8) ; k++)
        c += a;

    char s[] = "Tome and Cherry at the playa\n";
    c += s[(a & (sizeof(s)-1))];

    unsigned char s2[] = "Tim is sorry at the playa\n";
    c += s2[a & (sizeof(s) - 1)];

    c += a*b;
    c += a-b;
    c += a << (b & 0x8);

    c += sum(a, b);
END_TEST32()
