int printf(const char *, ...);

int main(void){
  int a = 42;
  char *str = "Hi there";
  printf("%s, I am %u\n", str, a);

  return 0;
}
