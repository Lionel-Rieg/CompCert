#ifndef __CCOMP_KIC_FIXES_H
#define __CCOMP_KIC_FIXES_H

#if ! (defined(__COMPCERT__) && defined (__K1C__))
#error This header is solely for CompCert on K1C
#endif

#undef __GNUC__
#define __thread

struct __int128_ccomp { long __int128_ccomp_low; long __int128_ccomp_high; };

#define __int128 struct __int128_ccomp
#define __builtin_k1_acswapd __compcert_acswapd
extern __int128 __compcert_acswapd(unsigned long long *address, unsigned long long new_value, unsigned long long old_value);
#endif
