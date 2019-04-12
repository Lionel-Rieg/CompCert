#ifndef _COMPCERT_MATH_H
#define _COMPCERT_MATH_H

#define isfinite(__y) (fpclassify((__y)) >= FP_ZERO)

#include_next <math.h>
#endif
