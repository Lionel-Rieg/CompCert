extern void callee(void);

void bigspill(int *t) {
  int t0 = t[0];
  int t1 = t[1];
  int t2 = t[2];
  int t3 = t[3];
  int t4 = t[4];
  int t5 = t[5];
  int t6 = t[6];
  int t7 = t[7];
  callee();
  t[0] = t0;
  t[1] = t1;
  t[2] = t2;
  t[3] = t3;
  t[4] = t4;
  t[5] = t5;
  t[6] = t6;
  t[7] = t7;
}
