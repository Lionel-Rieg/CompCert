void addv(double x, double y, int n, int *z)
{
  for(int i=0; i<n; i++) {
    z[i] += (int) (x*y);
  }
}
