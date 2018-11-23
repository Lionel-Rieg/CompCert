#define STACK int a[100];\
  a[42] = 42;

#define ONEARG_OP(arg) (3*arg+2)

#define MULTIARG_OP(arg1, arg2, arg3, arg4) (arg1 ^ arg2 << arg3 - arg4)

#define MANYARG_OP(a0, a1, a2, a3, a4, a5, a6, a7, a8, a9,\
                   a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,\
                   a20, a21, a22, a23, a24, a25, a26, a27, a28, a29)\
  (a0 + a1 * a2 + a3 * a4 + a5 + a6 + a7 - a8 + a9 +\
          a10 + a11 - a12 ^ a13 + a14 - a15 + a16 ^ a17 + a18 + a19 +\
          a20 + a21 + a22 * a23 + a24 + a25 << a26 & a27 + a28 + a29)

void void_void(){
  STACK;
}

long long ll_void(){
  STACK;
  return 0xdeadbeefdeadbeefULL;
}

int i_oneiarg(int arg){
  STACK;
  return ONEARG_OP(arg);
}

int i_multiiargs(int arg1, char arg2, char arg3, int arg4){
  STACK;
  return MULTIARG_OP(arg1, arg2, arg3, arg4);
}

int i_manyiargs(char a0, int a1, char a2, int a3, char a4, char a5, int a6, int a7, char a8, int a9,
                char a10, int a11, char a12, int a13, char a14, char a15, int a16, int a17, char a18, int a19,
                char a20, int a21, char a22, int a23, char a24, char a25, int a26, int a27, char a28, int a29)
{
  STACK;
  return MANYARG_OP(a0, a1, a2, a3, a4, a5, a6, a7, a8, a9,
                   a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
                   a20, a21, a22, a23, a24, a25, a26, a27, a28, a29);
}

int ll_onellarg(long long arg){
  STACK;
  return ONEARG_OP(arg);
}

long long ll_multillargs(long long arg1, char arg2, char arg3, long long arg4){
  STACK;
  return MULTIARG_OP(arg1, arg2, arg3, arg4);
}

long long ll_manyllargs(char a0, long long a1, char a2, long long a3, char a4, char a5, long long a6, long long a7, char a8, long long a9,
                char a10, long long a11, char a12, long long a13, char a14, char a15, long long a16, long long a17, char a18, long long a19,
                char a20, long long a21, char a22, long long a23, char a24, char a25, long long a26, long long a27, char a28, long long a29)
{
  STACK;
  return MANYARG_OP(a0, a1, a2, a3, a4, a5, a6, a7, a8, a9,
                   a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
                   a20, a21, a22, a23, a24, a25, a26, a27, a28, a29);
}
