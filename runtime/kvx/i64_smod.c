extern long __moddi3 (long a, long b);
int i32_smod (int a, int b)
{
  return __moddi3 (a, b);
}
