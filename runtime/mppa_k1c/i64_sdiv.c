unsigned long long
udivmoddi4(unsigned long long num, unsigned long long den, int modwanted);

long long
__compcert_i64_sdiv (long long a, long long b)
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

