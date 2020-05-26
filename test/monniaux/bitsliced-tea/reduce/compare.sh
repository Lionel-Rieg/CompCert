PREFIX=/home/monniaux/work/Kalray/ternary/CompCert
INCLUDES=-I$PREFIX/test/monniaux/bitsliced-tea
CCOMP_K1="$PREFIX/ccomp -fno-unprototyped -O3 $INCLUDES"
GCC_K1="k1-cos-gcc -Werror=implicit -O3 $INCLUDES"
GCC_HOST="gcc -Werror=implicit -O3 $INCLUDES"
FILE=bstea.c

OTHERS_K1="$PREFIX/test/monniaux/bitsliced-tea/bstea_run.gcc.kvx.o $PREFIX/test/monniaux/clock.gcc.kvx.o"
OTHERS_HOST="$PREFIX/test/monniaux/bitsliced-tea/bstea_run.gcc.host.o $PREFIX/test/monniaux/clock.gcc.host.o"

$CCOMP_K1 $FILE $OTHERS_K1 -o bstead.ccomp.kvx &&
$GCC_K1 $FILE $OTHERS_K1 -o bstead.gcc.kvx &&
$GCC_HOST $FILE $OTHERS_HOST -o bstead.gcc.host &&
valgrind -q ./bstead.gcc.host &&
k1-cluster --cycle-based -- bstead.ccomp.kvx > bstead.ccomp.kvx.out &&
k1-cluster --cycle-based -- bstead.gcc.kvx > bstead.gcc.kvx.out &&
grep cycles bstead.ccomp.kvx.out|sed -e 's/cycles: //' > bstead.ccomp.kvx.cycles &&
grep cycles bstead.gcc.kvx.out|sed -e 's/cycles: //' > bstead.gcc.kvx.cycles &&
test `cat bstead.gcc.kvx.cycles` -gt 100000 &&
test `cat bstead.ccomp.kvx.cycles` -gt 200000
