PREFIX=/home/monniaux/work/Kalray/ternary/CompCert
INCLUDES=-I$PREFIX/test/monniaux/bitsliced-tea
CCOMP_K1="$PREFIX/ccomp -fno-unprototyped -O3 $INCLUDES"
GCC_K1="k1-mbr-gcc -Werror=implicit -O3 $INCLUDES"
GCC_HOST="gcc -Werror=implicit -O3 $INCLUDES"
FILE=bstea.c

OTHERS_K1="$PREFIX/test/monniaux/bitsliced-tea/bstea_run.gcc.k1c.o $PREFIX/test/monniaux/clock.gcc.k1c.o"
OTHERS_HOST="$PREFIX/test/monniaux/bitsliced-tea/bstea_run.gcc.host.o $PREFIX/test/monniaux/clock.gcc.host.o"

$CCOMP_K1 $FILE $OTHERS_K1 -o bstead.ccomp.k1c &&
$GCC_K1 $FILE $OTHERS_K1 -o bstead.gcc.k1c &&
$GCC_HOST $FILE $OTHERS_HOST -o bstead.gcc.host &&
valgrind -q ./bstead.gcc.host &&
k1-cluster --cycle-based -- bstead.ccomp.k1c > bstead.ccomp.k1c.out &&
k1-cluster --cycle-based -- bstead.gcc.k1c > bstead.gcc.k1c.out &&
grep cycles bstead.ccomp.k1c.out|sed -e 's/cycles: //' > bstead.ccomp.k1c.cycles &&
grep cycles bstead.gcc.k1c.out|sed -e 's/cycles: //' > bstead.gcc.k1c.cycles &&
test `cat bstead.gcc.k1c.cycles` -gt 100000 &&
test `cat bstead.ccomp.k1c.cycles` -gt 200000
