#include <pthread.h>
#include <stdio.h>
#include <time.h>

#define VOLATILE volatile

typedef unsigned data;

static data powm(data x, unsigned e, data m) {
  data y = 1;
  for(unsigned i=0; i<e; i++) {
    y = (y * x) % m;
  }
  return y;
}

void* second_thread_entry(void *ptr) {
  *((data*) ptr) = powm(3, 65536, 65537);
  return NULL;
}

int main() {
  pthread_t second_thread_id;
  VOLATILE data value;
  pthread_create(&second_thread_id, NULL,
                 second_thread_entry, (void*) &value);
  value = 0;
  data correct = powm(3, 65536*4, 65537);;
  data read = value;
  pthread_join(second_thread_id, NULL);
  printf("%u %u\n", correct, read);
}
