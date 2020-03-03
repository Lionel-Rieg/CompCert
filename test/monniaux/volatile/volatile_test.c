#include <stdint.h>
#include <float.h>
#include <stdio.h>

#define TEST_TYPE(type, min, max)			\
  { \
    volatile type var; \
    var = min; \
    if (var != min) { \
      printf("%s: wrong min\n", #type); \
    } \
    var = max; \
    if (var != max) { \
      printf("%s: wrong max\n", #type); \
    } \
  }

#define TEST_INT_TYPE(type, min, max) TEST_TYPE(type##_t, min, max)

int main() {
  TEST_INT_TYPE(uint8, 0, UINT8_MAX);
  TEST_INT_TYPE(int8, INT8_MIN, INT8_MAX);
  TEST_INT_TYPE(uint16, 0, UINT16_MAX);
  TEST_INT_TYPE(int16, INT16_MIN, INT16_MAX);
  TEST_INT_TYPE(uint32, 0, UINT32_MAX);
  TEST_INT_TYPE(int32, INT32_MIN, INT32_MAX);
  TEST_INT_TYPE(uint64, 0, UINT64_MAX);
  TEST_INT_TYPE(int64, INT64_MIN, INT64_MAX);
  
  TEST_TYPE(float, FLT_MIN, FLT_MAX);
  TEST_TYPE(double, DBL_MIN, DBL_MAX);
  return 0;
}
