#include <stdio.h>
#include <mppa_bare_runtime/kvx/registers.h>

void test_system_regs(void) {
  __builtin_kvx_wfxl(K1_SFR_EV4, 0x1000ULL);
  __builtin_kvx_wfxm(K1_SFR_EV4, 0x2000ULL);
  __builtin_kvx_get(K1_SFR_EV4);
  __builtin_kvx_set(K1_SFR_EV4, 0x4000ULL);
}

void test_loads(void *addr) {
  __builtin_kvx_alclrd(addr);
  __builtin_kvx_alclrw(addr);
  __builtin_kvx_lbzu(addr);
  __builtin_kvx_lhzu(addr);
  __builtin_kvx_lwzu(addr);
  __builtin_kvx_ldu(addr);
  __builtin_kvx_dinvall(addr);
  __builtin_kvx_dtouchl(addr);
  __builtin_kvx_dzerol(addr);
  __builtin_kvx_iinvals(addr);
  /* __builtin_kvx_itouchl(addr); */
  __builtin_kvx_dzerol(addr);
}

void test_stops(void) {
  __builtin_kvx_await();
  __builtin_kvx_sleep();
  __builtin_kvx_stop();
  __builtin_kvx_barrier();
  __builtin_kvx_fence();
  __builtin_kvx_dinval();
  __builtin_kvx_iinval();
}

int main() {
  unsigned long long data = 45;
  unsigned long long res = __builtin_kvx_alclrd(&data);
  printf("%llu %llu\n", res, data);
}
