extern unsigned get_size(void);
extern void print_array(unsigned n, const int *t);

int main() {
  unsigned n = get_size();
  int tab[n];
  for(unsigned i=0; i<n; i++) tab[i] = i;
  print_array(n, tab);
}
