#include <mppa_bare_runtime/k1c/registers.h>

void test_system_regs(void) {
  __builtin_k1_wfxl(K1_SFR_EV4, 0x1000ULL);
  __builtin_k1_wfxm(K1_SFR_EV4, 0x2000ULL);
  __builtin_k1_get(K1_SFR_EV4);
  __builtin_k1_set(K1_SFR_EV4, 0x4000ULL);
}

void test_loads(void *addr) {
  __builtin_k1_ldu(addr);
}

void test_stops(void) {
  __builtin_k1_await();
  __builtin_k1_sleep();
  __builtin_k1_stop();
  __builtin_k1_barrier();
  __builtin_k1_fence();
}
