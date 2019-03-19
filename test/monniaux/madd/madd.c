unsigned madd(unsigned a, unsigned b, unsigned c) {
  return a + b*c;
}

unsigned maddimm(unsigned a, unsigned b) {
  return a + b*17113;
}

unsigned madd2(unsigned a, unsigned b, unsigned c) {
  return c + b*a;
}
