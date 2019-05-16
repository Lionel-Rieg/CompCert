/*
D. Monniaux
CNRS / VERIMAG
Demonstration of number theoretic transform (Fast Fourier transform in a finite field) in Z/(2^16+1)Z for buffer of length 2^16.

FFT original code from Rosetta Code.
*/

#include <assert.h>
#include <stdint.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../clock.h"

typedef uint32_t modint;
typedef int32_t smodint;

static modint invm(modint a0, modint b0)
{
  smodint a=a0, b=b0, q;
  smodint x0 = 0, x1 = 1, t;
  if (b == 1) return 1;
  while (a > 1) {
    q = a / b;
    t = b; b = a % b; a = t;
    t = x0; x0 = x1 - q * x0; x1 = t;
  }
  if (x1 < 0) x1 += b0;
  assert((x1 * a0) % b0 == 1);
  return x1;
}

static inline modint mulm(modint a, modint b, modint m) {
  return (a * b) % m;
}

static inline modint addm(modint a, modint b, modint m) {
  return (a + b) % m;
}

static inline modint subm(modint a, modint b, modint m) {
  return (a + (m - b)) % m;
}

static inline modint powm_u(modint a, modint exponent, modint m) {
  modint x = 1;
  while (exponent > 0) {
    if (exponent % 2) x = mulm(x, a, m);
    exponent /= 2;
    a = mulm(a, a, m);
  }
  return x;
}

static inline modint powm(modint a, smodint exponent, modint m) {
  if (exponent == 0) return 1;
  else if (exponent > 0) return powm_u(a, exponent, m);
  else /* exponent < 0 */ return powm(invm(a, m), -exponent, m);
}

static void _fft(modint modulus,
		 modint root_of_unit,
		 modint buf[], modint out[],
		 unsigned n, unsigned step)
{
  if (step < n) {
    modint root_of_unit2 = mulm(root_of_unit, root_of_unit, modulus);
    _fft(modulus, root_of_unit2, out, buf, n, step * 2);
    _fft(modulus, root_of_unit2, out + step, buf + step, n, step * 2);

    modint exp = 1;
    for (unsigned i = 0; i < n; i += 2 * step) {
      modint t = mulm(exp, out[i + step], modulus);
      buf[i / 2]     = addm(out[i], t, modulus);
      buf[(i + n)/2] = subm(out[i], t, modulus);
      exp = mulm(exp, root_of_unit, modulus);
    }
  }
}
 
void fft(modint modulus, modint root_of_unit, modint buf[], unsigned n)
{
  modint *out = malloc(sizeof(modint) * n);
  memcpy(out, buf, sizeof(modint) * n);
 
  _fft(modulus, root_of_unit, buf, out, n, 1);
  free(out);
}

static void negate(modint MODULUS, modint buf[restrict], unsigned n) {
  for(unsigned i=0; i<n; i++) {
    if (buf[i]) buf[i] = MODULUS-buf[i];
  }
}

static void mulvecm(modint modulus, modint buf[restrict], unsigned n, modint coef) {
  for(unsigned i=0; i<n; i++) {
    buf[i] = mulm(buf[i], coef, modulus);
  }
}

#define LOG_LENGTH 16
#define LENGTH (1 << LOG_LENGTH)
#define MUL_MODULUS LENGTH
#define MODULUS (MUL_MODULUS + 1)

modint randm(modint modulus) {
  static modint state = 0x42;
  state = state * UINT64_C(9223372036854775837) + 0x2017;
  return state % modulus;
}

int main() {
#if 0
  modint root_of_unit = 1;
  for(modint i=1; i<MODULUS; i++) {
    if (powm_u(i, MUL_MODULUS/2, MODULUS) != 1) {
      root_of_unit = i;
      break;
    }
  }
#else
  modint root_of_unit = 3;
#endif
  assert(root_of_unit != 1);
  //printf("root of unit = %" PRIu64 "\n", root_of_unit);

  modint *buf = malloc(LENGTH * sizeof(modint)),
    *save = malloc(LENGTH * sizeof(modint));

  for(unsigned i=0; i<LENGTH; i++) {
    buf[i] = randm(MODULUS);
  }
  
  memcpy(save, buf, LENGTH * sizeof(modint));

  clock_start();
  fft(MODULUS, root_of_unit, buf, LENGTH);
  fft(MODULUS, invm(root_of_unit, MODULUS), buf, LENGTH);
  clock_stop();
  print_total_clock();

#if 0
  /* can be replaced by x -> -x */
  mulvecm(MODULUS, buf, LENGTH, invm(LENGTH, MODULUS));
#else
  negate(MODULUS, buf, LENGTH);  
#endif
  printf("compare = %d\n", memcmp(buf, save, LENGTH * sizeof(modint)));
	 
  /*
  printf("buf[0] = %" PRIu64 "\n", buf[0]);
  printf("buf[1] = %" PRIu64 "\n", buf[1]);
  printf("buf[2] = %" PRIu64 "\n", buf[2]);
  printf("buf[3] = %" PRIu64 "\n", buf[3]);
  printf("buf[4] = %" PRIu64 "\n", buf[4]);
  */
  
  free(buf);
  free(save);
}
