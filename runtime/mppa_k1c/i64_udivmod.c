#ifdef __K1_TINYK1__
unsigned long long
udivmoddi4(unsigned long long num, unsigned long long den, int modwanted)
{
  unsigned long long bit = 1;
  unsigned long long res = 0;

  while (den < num && bit && !(den & (1L<<31)))
    {
      den <<=1;
      bit <<=1;
    }
  while (bit)
    {
      if (num >= den)
	{
	  num -= den;
	  res |= bit;
	}
      bit >>=1;
      den >>=1;
    }
  if (modwanted) return num;
  return res;
}

#else

/* Number of leading zeroes */
static int i64_nlzd(unsigned x)
{
  if (x == 0) return 64;
  int n = 0;
  if (x <= 0x00000000FFFFFFFFl) { n += 32; x <<= 32; }
  if (x <= 0x0000FFFFFFFFFFFFl) { n += 16; x <<= 16; }
  if (x <= 0x00FFFFFFFFFFFFFFl) { n += 8; x <<= 8; }
  if (x <= 0x0FFFFFFFFFFFFFFFl) { n += 4; x <<= 4; }
  if (x <= 0x3FFFFFFFFFFFFFFFl) { n += 2; x <<= 2; }
  if (x <= 0x7FFFFFFFFFFFFFFFl) { n += 1; x <<= 1; }
  return n;
}

static unsigned long long i64_stsud(unsigned rz, unsigned ry)
{
    return ry >= rz ? ry - rz << 1 | 1 : ry << 1;
}

/* THIS IS THE PREVIOUS VERSION, USED ON BOSTAN AND ANDEY */
unsigned long long
udivmoddi4(unsigned long long num, unsigned long long den, int modwanted)
{
    unsigned long long r = num, q = 0;

    if(den <= r) {
	//unsigned k = __builtin_clzll (den) - __builtin_clzll (r);
    unsigned k = i64_nlzd(den) - i64_nlzd(r);
	den = den << k;
	if(r >= den) {
	    r = r - den;
	    q = 1LL << k;
	}
	if(k != 0) {
	    unsigned i = k;
	    den = den >> 1;
	    do {
        r = i64_stsud(den, r);
		//r = __builtin_k1_stsud (den, r);
		i--;
	    } while (i!= 0);
	    q = q + r;
	    r = r >> k;
	    q = q - (r << k);
	}
    }

    return modwanted ? r : q;
}
#endif	/* __K1_TINYK1__ */

