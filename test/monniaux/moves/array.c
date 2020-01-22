void incr_double_array(double *t) {
  double x0 = 1.0;
  double t0 = t[0];
  double x1 = 1.0;
  double t1 = t[1];
  double x2 = 1.0;
  double t2 = t[2];
  double x3 = 1.0;
  double t3 = t[3];
  t0 = t0 + x0;
  t1 = t1 + x1;
  t2 = t2 + x2;
  t3 = t3 + x3;
  t[0] = t0;
  t[1] = t1;
  t[2] = t2;
  t[3] = t3;
}
