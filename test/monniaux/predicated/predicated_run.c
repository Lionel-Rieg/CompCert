#include <stdio.h>

extern void predicated_write(int flag, long *buf, long data);
extern long predicated_read(long defval, int flag, long *buf);

int main() {
  long buf[2] = {42, 69};
  printf("%ld\n", buf[1]);
  predicated_write(0, buf, 33);
  printf("%ld\n", buf[1]);
  predicated_write(1, buf, 45);
  printf("%ld\n", buf[1]);
  printf("%ld\n", predicated_read(1515, 0, buf));
  printf("%ld\n", predicated_read(1789, 1, buf));
  return 0;
}
