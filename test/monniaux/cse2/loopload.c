int find_index(int *t, int n) {
  if (t[0] > 0) return 3;
  while (n > 0) n--;
  return t[0];
}
