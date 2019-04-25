#include <stdio.h>

struct fields {
  unsigned f0 : 3;
  unsigned f1 : 5;
  signed f2 : 3;
};

int get_f1(struct fields x) {
  return x.f1;
}

int get_f2(struct fields x) {
  return x.f2;
}

int main() {
  struct fields x = {1, 2, -1};
  printf("%d %d\n", get_f1(x), get_f2(x));
}
