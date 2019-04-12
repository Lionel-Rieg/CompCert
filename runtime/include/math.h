#define isfinite(__y) (fpclassify(__y) >= FP_ZERO)

#include_next <math.h>
