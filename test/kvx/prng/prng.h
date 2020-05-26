#ifndef __PRNG_H__
#define __PRNG_H__

#include "types.h"

void srand(uint64_t seed);

uint64_t randlong(void);

#endif // __PRNG_H__
