#!/bin/bash
ROOT=/home/monniaux/work/Kalray/CompCert
SRC=bitsliced-aes_compute.c
MAIN=/home/monniaux/work/Kalray/CompCert/test/monniaux/bitsliced-aes/one_file/reduce/bitsliced-aes_main
k1-cos-gcc -Werror=implicit -Werror=uninitialized -O3 $SRC $ROOT/test/monniaux/clock.gcc.kvx.o $MAIN.gcc.kvx.o -o bitsliced-aes.gcc.kvx &&
$ROOT/ccomp -O3 -fno-unprototyped -O3 $SRC $ROOT/test/monniaux/clock.gcc.kvx.o  $MAIN.gcc.kvx.o -o bitsliced-aes.ccomp.kvx &&
gcc -Werror=implicit -Werror=uninitialized -O3 $SRC  $ROOT/test/monniaux/clock.gcc.host.o $MAIN.c -o bitsliced-aes.gcc.host &&
valgrind ./bitsliced-aes.gcc.host &&
k1-cluster --cycle-based -- ./bitsliced-aes.gcc.kvx > ./bitsliced-aes.gcc.kvx.out &&
k1-cluster --cycle-based -- ./bitsliced-aes.ccomp.kvx > ./bitsliced-aes.ccomp.kvx.out &&
grep cycles ./bitsliced-aes.gcc.kvx.out > ./bitsliced-aes.gcc.kvx.cycles &&
grep cycles ./bitsliced-aes.ccomp.kvx.out > ./bitsliced-aes.ccomp.kvx.cycles &&
sed -i -e 's/cycles: //' ./bitsliced-aes.gcc.kvx.cycles &&
sed -i -e 's/cycles: //' ./bitsliced-aes.ccomp.kvx.cycles &&
test $(cat ./bitsliced-aes.gcc.kvx.cycles) -gt 100000 &&
test $(cat ./bitsliced-aes.ccomp.kvx.cycles) -gt $(expr 2 '*' $(cat ./bitsliced-aes.gcc.kvx.cycles))
