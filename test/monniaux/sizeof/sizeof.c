#include <stdio.h>
#include <stdbool.h>
#include <stdint.h>
#include <inttypes.h>

#define PRINT_SIZE(t) printf("%s\t%zd\n", #t, sizeof(t))
#define PRINT_SIZES_INTN(n) \
  PRINT_SIZE(int##n##_t);   \
  PRINT_SIZE(uint##n##_t);	  \
  PRINT_SIZE(int_least##n##_t);	  \
  PRINT_SIZE(uint_least##n##_t);  \
  PRINT_SIZE(int_fast##n##_t);    \
  PRINT_SIZE(uint_fast##n##_t)

typedef void fun(void);

int main() {
  PRINT_SIZE(bool);
  PRINT_SIZE(char);
  PRINT_SIZE(short);
  PRINT_SIZE(int);
  PRINT_SIZE(long);
  PRINT_SIZE(long long);

  PRINT_SIZE(void*);
  PRINT_SIZE(fun*);

  PRINT_SIZE(float);
  PRINT_SIZE(double);
  PRINT_SIZE(long double);
    
  PRINT_SIZE(ptrdiff_t);
  PRINT_SIZE(size_t);
  PRINT_SIZE(wchar_t);
  PRINT_SIZE(intptr_t);
  PRINT_SIZE(uintptr_t);
  PRINT_SIZE(intmax_t);
  PRINT_SIZE(uintmax_t);
 
  PRINT_SIZES_INTN(8);
  PRINT_SIZES_INTN(16);
  PRINT_SIZES_INTN(32);
  PRINT_SIZES_INTN(64);

  return 0;
}
