#ifndef _COMPCERT_MATH_H
#define _COMPCERT_MATH_H

#define isfinite(__y) (fpclassify((__y)) >= FP_ZERO)

#ifndef COMPCERT_NO_FP_MACROS
#define fmin(x, y) __builtin_fmin((x),(y))
#define fmax(x, y) __builtin_fmax((x),(y))
#define fminf(x, y) __builtin_fminf((x),(y))
#define fmaxf(x, y) __builtin_fmaxf((x),(y))
#define fabs(x) __builtin_fabs((x))
#define fabsf(x) __builtin_fabsf((x))
#endif

#include_next <math.h>
#endif
