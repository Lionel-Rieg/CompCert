#if 0
/* THIS IS THE PREVIOUS VERSION, USED ON BOSTAN AND ANDEY */
unsigned long long
udivmoddi4(unsigned long long num, unsigned long long den, int modwanted)
{
    unsigned long long r = num, q = 0;

    if(den <= r) {
	unsigned k = __builtin_clzll (den) - __builtin_clzll (r);
	den = den << k;
	if(r >= den) {
	    r = r - den;
	    q = 1LL << k;
	}
	if(k != 0) {
	    unsigned i = k;
	    den = den >> 1;
	    do {
		r = __builtin_k1_stsud (den, r);
		i--;
	    } while (i!= 0);
	    q = q + r;
	    r = r >> k;
	    q = q - (r << k);
	}
    }

    return modwanted ? r : q;
}
#endif
