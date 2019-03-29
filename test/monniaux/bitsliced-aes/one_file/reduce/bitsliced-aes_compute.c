#include <stdint.h>
#include <string.h>
int i[1];
int j, bs_transpose_dst_k, k, s, o;
void a(int (*)[], uint8_t *);
void b(uint8_t c, uint8_t d, size_t e, uint8_t f, uint8_t g) {
  int l[1];
  a(l, f);
}
void a(int (*l)[], uint8_t *m) {
  for (; o < 76; o += 8) {
    {
      int *n = i;
      bs_transpose_dst_k = 0;
      for (; bs_transpose_dst_k < 64; bs_transpose_dst_k++) {
        j = 0;
        for (; j < 64; j++) {
          k = &s;
          n[j] = k & 1;
        }
      }
    }
  }
}
void aes_ecb_test() {}
void aes_ctr_test() {
  uint8_t p = "";
  uint8_t q = "";
  uint8_t r = "";
  uint8_t output[4];
  b(output, r, 4, p, q);
}
