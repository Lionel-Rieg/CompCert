#include <stdio.h>
#include <stdint.h>

#define GET_FIELD_L(x, stop, start) (((x) << (63-(stop))) >> (63-(stop)+(start)))
#define FIELD_MASK(stop, start) ((1ULL<<(stop)) - (1ULL<<(start)) + (1ULL<<(stop)))

#define SET_FIELD_L(x, stop, start, y) (((x) & ~FIELD_MASK(stop, start)) | ((y << start) & FIELD_MASK(stop, start)))

uint64_t get_f2(uint64_t x) {
  return GET_FIELD_L(x, 47, 16);
}

uint64_t set_f2(uint64_t x, uint64_t y) {
  return SET_FIELD_L(x, 47, 16, y);
}

int main() {
  printf("%lx %lx\n", FIELD_MASK(47, 16), set_f2(0x12345678ABCD1234ULL, 0x11112222ULL));
}
