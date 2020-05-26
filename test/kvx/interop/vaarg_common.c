#include <stdarg.h>

#define STACK int a[100];\
  a[42] = 42;

#define ONEARG_OP(arg) (3*magic(arg)+2)

#define MULTIARG_OP(arg1, arg2, arg3, arg4) (arg1 ^ magic(arg2) << arg3 - arg4)

#define MANYARG_OP(a0, a1, a2, a3, a4, a5, a6, a7, a8, a9,\
                   a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,\
                   a20, a21, a22, a23, a24, a25, a26, a27, a28, a29)\
  (a0 + a1 * a2 + magic(a3) * a4 + a5 + a6 + a7 - a8 + a9 +\
          a10 + a11 - a12 ^ a13 + a14 - magic(a15) + a16 ^ a17 + a18 + a19 +\
          a20 + a21 + a22 * a23 + a24 + a25 << a26 & a27 + a28 + a29)

#define VA_START(vl, arg) va_list vl; va_start(vl, arg)
#define VA_END(vl) va_end(vl)

int magic(long a){
  return a*2 + 42;
}

void void_void(void){
  STACK;
}

long long ll_void(void){
  STACK;
  return 0xdeadbeefdeadbeefULL;
}

// int i_oneiarg(int arg){
int i_oneiarg(int arg, ...){
  STACK;
  VA_START(vl, arg);
  VA_END(vl);
  return ONEARG_OP(arg);
}

//int i_multiiargs(int arg1, char arg2, char arg3, int arg4){
int i_multiiargs(int arg1, ...){
  STACK;
  VA_START(vl, arg1);
  char arg2 = va_arg(vl, int);
  char arg3 = va_arg(vl, int);
  int arg4 = va_arg(vl, int);
  VA_END(vl);
  return MULTIARG_OP(arg1, arg2, arg3, arg4);
}

//int i_manyiargs(char a0, int a1, char a2, int a3, char a4, char a5, int a6, int a7, char a8, int a9,
//                char a10, int a11, char a12, int a13, char a14, char a15, int a16, int a17, char a18, int a19,
//                char a20, int a21, char a22, int a23, char a24, char a25, int a26, int a27, char a28, int a29)
int i_manyiargs(char a0, ...)
{
  STACK;
  VA_START(vl, a0);
  VA_START(vl2, a0);
  int a1 = va_arg(vl, int);
  char a2 = va_arg(vl, int);
  int a3 = va_arg(vl, int);
  char a4 = va_arg(vl,  int);
  char a5 = va_arg(vl, int);
  char b1 = va_arg(vl2, int);
  int a6 = va_arg(vl, int);
  int a7 = va_arg(vl, int);
  char a8 = va_arg(vl, int);
  char b2 = va_arg(vl2, int);
  int a9 = va_arg(vl, int);
  char a10 = va_arg(vl, int);
  int a11 = va_arg(vl, int);
  char a12 = va_arg(vl, int);
  char b3 = va_arg(vl2, int);
  int a13 = va_arg(vl, int);
  char a14 = va_arg(vl, int);
  char a15 = va_arg(vl, int);
  int a16 = va_arg(vl, int);
  int a17 = va_arg(vl, int);
  char a18 = va_arg(vl, int);
  int a19 = va_arg(vl, int);
  char a20 = va_arg(vl, int);
  int a21 = va_arg(vl, int);
  char a22 = va_arg(vl, int);
  int a23 = va_arg(vl, int);
  char a24 = va_arg(vl, int);
  char a25 = va_arg(vl, int);
  int a26 = va_arg(vl, int);
  char b4 = va_arg(vl2, int);
  int a27 = va_arg(vl, int);
  char a28 = va_arg(vl, int);
  int a29 = va_arg(vl, int);
  VA_END(vl);
  VA_END(vl);
  return MANYARG_OP(a0, a1, a2, a3, a4, (a5*b2), a6, a7, a8, a9,
                   (a10*b3), a11, a12, a13, a14, a15, a16, a17, a18, a19,
                   a20, (a21*b1), a22, a23, (a24*b3), a25, a26, a27, a28, a29);
}

//int ll_onellarg(long long arg){
int ll_onellarg(long long arg, ...){
  STACK;
  VA_START(vl, arg);
  VA_END(vl);
  return ONEARG_OP(arg);
}

//long long ll_multillargs(long long arg1, char arg2, char arg3, long long arg4){
long long ll_multillargs(long long arg1, ...){
  STACK;
  VA_START(vl, arg1);
  char arg2 = va_arg(vl, int);
  char arg3 = va_arg(vl, int);
  long long arg4 = va_arg(vl, long long);
  VA_END(vl);
  return MULTIARG_OP(arg1, arg2, arg3, arg4);
}

//long long ll_manyllargs(char a0, int a1, char a2, long long a3, char a4, char a5, long long a6, long long a7, char a8, long long a9,
//                char a10, long long a11, char a12, int a13, char a14, char a15, long long a16, long long a17, char a18, long long a19,
//                char a20, int a21, char a22, long long a23, char a24, char a25, long long a26, int a27, char a28, long long a29)
long long ll_manyllargs(char a0, ...)
{
  STACK;
  VA_START(vl, a0);
  int a1 = va_arg(vl, int);
  char a2 = va_arg(vl, int);
  long long a3 = va_arg(vl, long long);
  char a4 = va_arg(vl,  int);
  char a5 = va_arg(vl, int);
  long long a6 = va_arg(vl, long long);
  long long a7 = va_arg(vl, long long);
  char a8 = va_arg(vl, int);
  long long a9 = va_arg(vl, long long);
  char a10 = va_arg(vl, int);
  long long a11 = va_arg(vl, long long);
  char a12 = va_arg(vl, int);
  int a13 = va_arg(vl, int);
  char a14 = va_arg(vl, int);
  char a15 = va_arg(vl, int);
  long long a16 = va_arg(vl, long long);
  long long a17 = va_arg(vl, long long);
  char a18 = va_arg(vl, int);
  long long a19 = va_arg(vl, long long);
  char a20 = va_arg(vl, int);
  int a21 = va_arg(vl, int);
  char a22 = va_arg(vl, int);
  long long a23 = va_arg(vl, long long);
  char a24 = va_arg(vl, int);
  char a25 = va_arg(vl, int);
  long long a26 = va_arg(vl, long long);
  int a27 = va_arg(vl, int);
  char a28 = va_arg(vl, int);
  long long a29 = va_arg(vl, long long);
  VA_END(vl);
  return MANYARG_OP(a0, a1, a2, a3, a4, a5, a6, a7, a8, a9,
                   a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
                   a20, a21, a22, a23, a24, a25, a26, a27, a28, a29);
}

//long long stackhell(char a0, int a1, char a2, long long a3, char a4, char a5, long long a6, long long a7, char a8, long long a9,
//                char a10, long long a11, char a12, int a13, char a14, char a15, long long a16, long long a17, char a18, long long a19,
//                char a20, int a21, char a22, long long a23, char a24, char a25, long long a26, int a27, char a28, long long a29)
long long stackhell(char a0, ...)
{
  VA_START(vl, a0);
  int a1 = va_arg(vl, int);
  char a2 = va_arg(vl, int);
  long long a3 = va_arg(vl, long long);
  char a4 = va_arg(vl,  int);
  char a5 = va_arg(vl, int);
  long long a6 = va_arg(vl, long long);
  long long a7 = va_arg(vl, long long);
  char a8 = va_arg(vl, int);
  long long a9 = va_arg(vl, long long);
  char a10 = va_arg(vl, int);
  long long a11 = va_arg(vl, long long);
  char a12 = va_arg(vl, int);
  int a13 = va_arg(vl, int);
  char a14 = va_arg(vl, int);
  char a15 = va_arg(vl, int);
  long long a16 = va_arg(vl, long long);
  long long a17 = va_arg(vl, long long);
  char a18 = va_arg(vl, int);
  long long a19 = va_arg(vl, long long);
  char a20 = va_arg(vl, int);
  int a21 = va_arg(vl, int);
  char a22 = va_arg(vl, int);
  long long a23 = va_arg(vl, long long);
  char a24 = va_arg(vl, int);
  char a25 = va_arg(vl, int);
  long long a26 = va_arg(vl, long long);
  int a27 = va_arg(vl, int);
  char a28 = va_arg(vl, int);
  long long a29 = va_arg(vl, long long);
  VA_END(vl);

  long long b0 = a0;
  long long b1 = a1 + b0;
  long long b2 = a2 + b1;
  int b3 = a3 + b2;
  int b4 = a4 + b3;
  int b5 = a5 + b4;
  int b6 = a6 + b5;
  int b7 = a7 + b6;
  char b8 = a8 + b7;
  char b9 = a9 + b8;
  char b10 = a10 + b9;
  char b11 = a11 + b10;
  char b12 = a12 + b11;
  int b13 = a13 + b12;
  long long b14 = a14 + b13;
  long long b15 = a15 + b14;
  long long b16 = a16 + b15;
  long long b17 = a17 + b16;
  long long b18 = a18 + b17;
  long long b19 = a19 + b18;
  long long b20 = a20 + b19;
  long long b21 = a21 + b20;
  long long b22 = a22 + b21;
  long long b23 = a23 + b22;
  long long b24 = a24 + b23;
  long long b25 = a25 + b24;
  long long b26 = a26 + b25;
  long long b27 = a27 + b26;
  int b28 = a28 + b27;
  int b29 = a29 + b28;
  int b30 = b0 + b29;
  int b31 = b1 + b30;
  int b32 = b2 + b31;
  char b33 = b3 + b32;
  char b34 = b4 + b33;
  char b35 = b5 + b34;
  char b36 = b6 + b35;
  char b37 = b7 + b36;
  int b38 = b8 + b37;
  int b39 = b9 + b38;
  int b40 = b0 + b39;
  int b41 = b1 + b40;
  int b42 = b2 + b41;
  int b43 = b3 + b42;
  int b44 = b4 + b43;
  int b45 = b5 + b44;
  int b46 = b6 + b45;
  int b47 = b7 + b46;
  int b48 = b8 + b47;
  long long b49 = b9 + b48;
  long long b50 = b0 + b49;
  long long b51 = b1 + b50;
  long long b52 = b2 + b51;
  long long b53 = b3 + b52;
  long long b54 = b4 + b53;
  long long b55 = b5 + b54;
  long long b56 = b6 + b55;
  long long b57 = b7 + b56;
  int b58 = b8 + b57;
  int b59 = b9 + b58;
  int b60 = b0 + b59;
  int b61 = b1 + b60;
  int b62 = b2 + b61;
  int b63 = b3 + b62;
  int b64 = b4 + b63;
  int b65 = b5 + b64;
  int b66 = b6 + b65;
  int b67 = b7 + b66;
  int b68 = b8 + b67;
  int b69 = b9 + b68;
  char b70 = b0 + b69;
  char b71 = b1 + b70;
  char b72 = b2 + b71;
  char b73 = b3 + b72;
  char b74 = b4 + b73;
  char b75 = b5 + b74;
  char b76 = b6 + b75;
  char b77 = b7 + b76;
  char b78 = b8 + b77;
  char b79 = b9 + b78;
  char b80 = b0 + b79;
  char b81 = b1 + b80;
  char b82 = b2 + b81;
  char b83 = b3 + b82;
  char b84 = b4 + b83;
  int b85 = b5 + b84;
  int b86 = b6 + b85;
  int b87 = b7 + b86;
  int b88 = b8 + b87;
  int b89 = b9 + b88;
  int b90 = b0 + b89;
  int b91 = b1 + b90;
  int b92 = b2 + b91;
  int b93 = b3 + b92;
  int b94 = b4 + b93;
  long long b95 = b5 + b94;
  long long b96 = b6 + b95;
  long long b97 = b7 + b96;
  long long b98 = b8 + b97;
  long long b99 = b9 + b98;
  long long b100 = b0 + b99;
  long long b101 = b1 + b100;
  long long b102 = b2 + b101;
  long long b103 = b3 + b102;
  long long b104 = b4 + b103;
  long long b105 = b5 + b104;
  long long b106 = b6 + b105;
  long long b107 = b7 + b106;
  long long b108 = b8 + b107;
  long long b109 = b9 + b108;
  long long b110 = b0 + b109;
  long long b111 = b1 + b110;
  long long b112 = b2 + b111;
  long long b113 = b3 + b112;
  long long b114 = b4 + b113;
  int b115 = b5 + b114;
  int b116 = b6 + b115;
  int b117 = b7 + b116;
  int b118 = b8 + b117;
  int b119 = b9 + b118;
  int b120 = b0 + b119;
  int b121 = b1 + b120;
  int b122 = b2 + b121;
  int b123 = b3 + b122;
  int b124 = b4 + b123;
  int b125 = b5 + b124;
  char b126 = b6 + b125;
  char b127 = b7 + b126;
  char b128 = b8 + b127;
  char b129 = b9 + b128;
  char b130 = b0 + b129;
  char b131 = b1 + b130;
  char b132 = b2 + b131;
  char b133 = b3 + b132;
  char b134 = b4 + b133;
  char b135 = b5 + b134;
  char b136 = b6 + b135;
  char b137 = b7 + b136;
  char b138 = b8 + b137;
  char b139 = b9 + b138;
  char b140 = b0 + b139;
  char b141 = b1 + b140;
  char b142 = b2 + b141;
  char b143 = b3 + b142;
  char b144 = b4 + b143;
  char b145 = b5 + b144;
  char b146 = b6 + b145;
  char b147 = b7 + b146;
  int b148 = b8 + b147;
  int b149 = b9 + b148;
  int b150 = b0 + b149;
  int b151 = b1 + b150;
  int b152 = b2 + b151;
  int b153 = b3 + b152;
  int b154 = b4 + b153;
  int b155 = b5 + b154;
  int b156 = b6 + b155;
  int b157 = b7 + b156;
  int b158 = b8 + b157;
  int b159 = b9 + b158;
  int b160 = b0 + b159;
  int b161 = b1 + b160;
  int b162 = b2 + b161;
  return MANYARG_OP(a0, a1, a2, a3, a4, a5, a6, a7, a8, a9,
                   a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
                   a20, a21, a22, a23, a24, a25, a26, a27, a28, a29)
    + b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8 + b9
    + b10 + b11 + b12 + b13 + b14 + b15 + b16 + b17 + b18 + b19
    + b20 + b21 + b22 + b23 + b24 + b25 + b26 + b27 + b28 + b29
    + b30 + b31 + b32 + b33 + b34 + b35 + b36 + b37 + b38 + b39
    + b40 + b41 + b42 + b43 + b44 + b45 + b46 + b47 + b48 + b49
    + b50 + b51 + b52 + b53 + b54 + b55 + b56 + b57 + b58 + b59
    + b60 + b61 + b62 + b63 + b64 + b65 + b66 + b67 + b68 + b69
    + b70 + b71 + b72 + b73 + b74 + b75 + b76 + b77 + b78 + b79
    + b80 + b81 + b82 + b83 + b84 + b85 + b86 + b87 + b88 + b89
    + b90 + b91 + b92 + b93 + b94 + b95 + b96 + b97 + b98 + b99
    + b100 + b101 + b102 + b103 + b104 + b105 + b106 + b107 + b108 + b109
    + b110 + b111 + b112 + b113 + b114 + b115 + b116 + b117 + b118 + b119
    + b120 + b121 + b122 + b123 + b124 + b125 + b126 + b127 + b128 + b129
    + b130 + b131 + b132 + b133 + b134 + b135 + b136 + b137 + b138 + b139
    + b140 + b141 + b142 + b143 + b144 + b145 + b146 + b147 + b148 + b149
    + b150 + b151 + b152 + b153 + b154 + b155 + b156 + b157 + b158 + b159
    + b160 + b161 + b162
    ;
}

