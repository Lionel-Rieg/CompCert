#if COMPLIQUE
unsigned long long
udivmoddi4(unsigned long long num, unsigned long long den, int modwanted);

long long
i64_sdiv (long long a, long long b)
{
  int neg = 0;
  long long res;

  if (a < 0)
    {
      a = -a;
      neg = !neg;
    }

  if (b < 0)
    {
      b = -b;
      neg = !neg;
    }

  res = udivmoddi4 (a, b, 0);

  if (neg)
    res = -res;

  return res;
}

#else
extern long __divdi3 (long a, long b);

long i64_sdiv (long a, long b)
{
  return __divdi3 (a, b);
}

int i32_sdiv (int a, int b)
{
  return __divdi3 (a, b);
}

extern double __divdf3(double, double);
double f64_div(double a, double b) {
  return __divdf3(a, b);
}

extern float __divsf3(float, float);
float f32_div(float a, float b) {
  return __divsf3(a, b);
}
#endif
