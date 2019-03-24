#include "/home/monniaux/work/Kalray/CompCert/test/monniaux/clock.h"

void aes_ecb_test(void);
void aes_ctr_test(void);

int main(int argc, char * argv[])
{
  clock_prepare();
  
    clock_start();
  
    aes_ecb_test();
    aes_ctr_test();


    clock_stop();
    print_total_clock();
    
    return 0;
}
