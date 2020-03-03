#ifndef _COMPCERT_MATH_H
#define _COMPCERT_MATH_H

#define isfinite(__y) (fpclassify((__y)) >= FP_ZERO)

#include_next <math.h>

#ifndef COMPCERT_NO_FP_MACROS
#define fmin(x, y) __builtin_fmin((x),(y))
#define fmax(x, y) __builtin_fmax((x),(y))
#define fminf(x, y) __builtin_fminf((x),(y))
#define fmaxf(x, y) __builtin_fmaxf((x),(y))
#define fabs(x) __builtin_fabs((x))
#define fabsf(x) __builtin_fabsf((x))
#define fma(x, y, z) __builtin_fma((x),(y),(z))
#define fmaf(x, y, z) __builtin_fmaf((x),(y),(z))
#endif

#endif
