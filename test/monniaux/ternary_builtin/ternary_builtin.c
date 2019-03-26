int ternary_signed(int x, int v0, int v1) {
  return ((-(x==0)) & v0) | ((-(x!=0)) & v1);
}

int ternary_unsigned(unsigned x, int v0, int v1) {
  return ((-(x==0)) & v0) | ((-(x!=0)) & v1);
}
