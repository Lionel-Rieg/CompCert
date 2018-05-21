unsigned long long
udivmoddi4(unsigned long long num, unsigned long long den, int modwanted);

unsigned long long i64_udiv (unsigned long long a, unsigned long long b)
{
  return udivmoddi4 (a, b, 0);
}

