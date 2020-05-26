extern unsigned long __umoddi3 (unsigned long a, unsigned long b);

unsigned i32_umod (unsigned a, unsigned b)
{
  return __umoddi3 (a, b);
}
