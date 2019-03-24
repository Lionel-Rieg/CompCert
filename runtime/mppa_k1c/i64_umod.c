#ifdef COMPLIQUE
unsigned long long
udivmoddi4(unsigned long long num, unsigned long long den, int modwanted);

unsigned long long
i64_umod (unsigned long long a, unsigned long long b)
{
  return udivmoddi4 (a, b, 1);
}

#else
extern unsigned long __umoddi3 (unsigned long a, unsigned long b);

unsigned long i64_umod (unsigned long a, unsigned long b)
{
  return __umoddi3 (a, b);
}

unsigned int i32_umod (unsigned int a, unsigned int b)
{
  return __umoddi3 (a, b);
}
#endif
