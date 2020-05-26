extern unsigned long __udivdi3 (unsigned long a, unsigned long b);

unsigned i32_udiv (unsigned a, unsigned b)
{
  return __udivdi3 (a, b);
}
