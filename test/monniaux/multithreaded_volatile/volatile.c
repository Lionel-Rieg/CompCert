#include <stdio.h>
#include <time.h>
#include <pthread.h>

typedef unsigned data;

static inline data powM(data x, unsigned e) {
  data y = 1;
  for(unsigned i=0; i<e; i++) {
    y = (y * x) % 65537;
  }
  return y;
}

void* second_thread_entry(void *ptr) {
  *((volatile data*) ptr) = powM(3, 65536);
  return NULL;
}

int main() {
  pthread_t second_thread_id;
  volatile data value;
  pthread_create(&second_thread_id, NULL,
                 second_thread_entry, (void*) &value);
  value = 69;
  data correct = powM(3, 65536*2);
  data read = value;
  pthread_join(second_thread_id, NULL);
  printf("%u %u %s\n", read, correct, read == correct ? "OK" : "FAIL");
}
