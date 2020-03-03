int toto(int *t, int n) {
  int x = t[0];
  for(int i=1; i<n; i++) {
    if (t[i] > t[0]) return i;
  }
  return 0;
}
