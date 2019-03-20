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
#endif
