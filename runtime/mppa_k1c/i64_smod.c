unsigned long long
udivmoddi4(unsigned long long num, unsigned long long den, int modwanted);

long long
i64_smod (long long a, long long b)
{
  int neg = 0;
  long long res;

  if (a < 0)
    {
      a = -a;
      neg = 1;
    }

  if (b < 0)
    b = -b;

  res = udivmoddi4 (a, b, 1);

  if (neg)
    res = -res;

  return res;
}
