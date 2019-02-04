/* simplified version of c-strtod.i */

extern double getdouble(void);
extern void intptr(void);

double bidule (void)
{
  double r;
  r = getdouble();
  intptr();
  return r;
}
