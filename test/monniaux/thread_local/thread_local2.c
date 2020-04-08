#include <stdio.h>
#include <pthread.h>

_Thread_local int toto;
_Thread_local int toto2 = 45;

void* poulet(void * dummy) {
  printf("%p %p\n", &toto, &toto2);
  return NULL;
}

int main() {
  pthread_t thr;
  poulet(NULL);
  pthread_create(&thr, NULL, poulet, NULL);
  pthread_join(thr, NULL);
  return 0;
}
