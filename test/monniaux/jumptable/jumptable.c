#include <stdio.h>

#define CASE(x) case x: return 100+x;

int big_switch(int x) {
  switch (x) {
    CASE(0)
    CASE(1)
    CASE(2)
    CASE(3)
    CASE(4)
    CASE(5)
    CASE(6)
    CASE(7)
    CASE(8)
    CASE(9)
    CASE(10)
    CASE(11)
    CASE(12)
    CASE(13)
    CASE(14)
    CASE(15)
  }
  return 99;
}

int main() {
  for(int i=-1; i<16; i++) {
    if (big_switch(i) != 100+i) {
      printf("error at %d\n", i);
    }
  }
  return 0;
}
