#include <stdint.h>

static inline int32_t ternary_int32(int32_t a, int32_t b, int32_t c) {
  return (((-((a) == 0)) & (c)) | ((-((a) != 0)) & (b)));
}
static inline uint32_t ternary_uint32(uint32_t a, uint32_t b, uint32_t c) {
  return ternary_int32(a, b, c);
}

static inline int64_t ternary_int64(int64_t a, int64_t b, int64_t c) {
  return (((-((a) == 0)) & (c)) | ((-((a) != 0)) & (b)));
}
static inline uint64_t ternary_uint64(uint64_t a, uint64_t b, uint64_t c) {
  return ternary_int64(a, b, c);
}

#if defined(__COMPCERT__) && defined(__K1C__)
#define TERNARY32(a, b, c) ternary_uint32((a), (b), (c))
#define TERNARY64(a, b, c) ternary_uint64((a), (b), (c))
#else
#define TERNARY32(a, b, c) ((a) ? (b) : (c))
#define TERNARY64(a, b, c) ((a) ? (b) : (c))
#endif
