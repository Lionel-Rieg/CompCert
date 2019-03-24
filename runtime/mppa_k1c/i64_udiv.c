#ifdef COMPLIQUE
unsigned long long
udivmoddi4(unsigned long long num, unsigned long long den, int modwanted);

unsigned long long i64_udiv (unsigned long long a, unsigned long long b)
{
  return udivmoddi4 (a, b, 0);
}

#else
extern long __udivdi3 (long a, long b);

unsigned long i64_udiv (unsigned long a, unsigned long b)
{
  return __udivdi3 (a, b);
}

unsigned int i32_udiv (unsigned int a, unsigned int b)
{
  return __udivdi3 (a, b);
}
#endif
