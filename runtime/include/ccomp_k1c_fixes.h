/* *************************************************************/
/*                                                             */
/*             The Compcert verified compiler                  */
/*                                                             */
/*           Sylvain Boulmé     Grenoble-INP, VERIMAG          */
/*           David Monniaux     CNRS, VERIMAG                  */
/*           Cyril Six          Kalray                         */
/*                                                             */
/*  Copyright Kalray. Copyright VERIMAG. All rights reserved.  */
/*  This file is distributed under the terms of the INRIA      */
/*  Non-Commercial License Agreement.                          */
/*                                                             */
/* *************************************************************/


#ifndef __CCOMP_KIC_FIXES_H
#define __CCOMP_KIC_FIXES_H

#if ! (defined(__COMPCERT__) && defined (__K1C__))
#error This header is solely for CompCert on K1C
#endif

#undef __GNUC__
#define __thread _Thread_local

struct __int128_ccomp { long __int128_ccomp_low; long __int128_ccomp_high; };

#define __int128 struct __int128_ccomp

#define __builtin_k1_acswapd __compcert_acswapd
extern __int128 __compcert_acswapd(void *address, unsigned long long new_value, unsigned long long old_value);

#define __builtin_k1_acswapw __compcert_acswapw
extern __int128 __compcert_acswapw(void *address, unsigned long long new_value, unsigned long long old_value);

#define __builtin_k1_afaddd __compcert_afaddd
extern long long __compcert_afaddd(void *address, unsigned long long incr);

#define __builtin_k1_afaddw __compcert_afaddw
extern int __compcert_afaddw(void *address, unsigned int incr);
#endif

/* #define __builtin_expect(x, y) (x) */
#define __builtin_ctz(x) __builtin_k1_ctzw(x)
#define __builtin_clz(x) __builtin_k1_clzw(x)
