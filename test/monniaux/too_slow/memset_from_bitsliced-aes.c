#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "../clock.h"

typedef uint64_t a;
a n[128];
int o, bs_expand_key_k;
void b(a (*)[], uint8_t *);
void c(uint8_t d, uint8_t e, size_t f, uint8_t g, uint8_t iv) {
  a i[1];
  b(i, g);
}

void b(a (*i)[], uint8_t *j) {
  for (; o < 176; o += 8) {
    bs_expand_key_k = 4;
    for (; bs_expand_key_k < 128; bs_expand_key_k += 128 / 64)
      ;
    memset(n, 0, sizeof(n));
  }
}

void aes_ctr_test() {
  uint8_t k = "";
  uint8_t l = "";
  uint8_t m = "";
  uint8_t output[4];
  c(output, m, 4, k, l);
}

int main(int argc, char * argv[])
{
  clock_prepare();
  
    clock_start();

    aes_ctr_test();
    clock_stop();
    print_total_clock();
    
    return 0;
}
