#include <stdio.h>
#include <mppa_bare_runtime/k1c/registers.h>

void test_system_regs(void) {
  __builtin_k1_wfxl(K1_SFR_EV4, 0x1000ULL);
  __builtin_k1_wfxm(K1_SFR_EV4, 0x2000ULL);
  __builtin_k1_get(K1_SFR_EV4);
  __builtin_k1_set(K1_SFR_EV4, 0x4000ULL);
}

void test_loads(void *addr) {
  __builtin_k1_alclrd(addr);
  __builtin_k1_alclrw(addr);
  __builtin_k1_lbzu(addr);
  __builtin_k1_lhzu(addr);
  __builtin_k1_lwzu(addr);
  __builtin_k1_ldu(addr);
  __builtin_k1_dinvall(addr);
  __builtin_k1_dtouchl(addr);
  __builtin_k1_dzerol(addr);
  __builtin_k1_iinvals(addr);
  /* __builtin_k1_itouchl(addr); */
  __builtin_k1_dzerol(addr);
}

void test_stops(void) {
  __builtin_k1_await();
  __builtin_k1_sleep();
  __builtin_k1_stop();
  __builtin_k1_barrier();
  __builtin_k1_fence();
  __builtin_k1_dinval();
  __builtin_k1_iinval();
}

int main() {
  unsigned long long data = 45;
  unsigned long long res = __builtin_k1_alclrd(&data);
  printf("%llu %llu\n", res, data);
}
