#!/bin/bash
ROOT=/home/monniaux/work/Kalray/CompCert
SRC=bitsliced-aes_compute.c
MAIN=bitsliced-aes_main
k1-mbr-gcc -Werror=implicit -Werror=uninitialized -O3 $SRC $ROOT/test/monniaux/clock.gcc.k1c.o $MAIN.gcc.k1c.o -o bitsliced-aes.gcc.k1c &&
$ROOT/ccomp -O3 -fno-unprototyped -O3 $SRC $ROOT/test/monniaux/clock.gcc.k1c.o  $MAIN.gcc.k1c.o -o bitsliced-aes.ccomp.k1c &&
gcc -Werror=implicit -Werror=uninitialized -O3 $SRC  $ROOT/test/monniaux/clock.gcc.host.o $MAIN.c -o bitsliced-aes.gcc.host &&
valgrind ./bitsliced-aes.gcc.host &&
k1-cluster --cycle-based -- ./bitsliced-aes.gcc.k1c > ./bitsliced-aes.gcc.k1c.out &&
k1-cluster --cycle-based -- ./bitsliced-aes.ccomp.k1c > ./bitsliced-aes.ccomp.k1c.out &&
grep cycles ./bitsliced-aes.gcc.k1c.out > ./bitsliced-aes.gcc.k1c.cycles &&
grep cycles ./bitsliced-aes.ccomp.k1c.out > ./bitsliced-aes.ccomp.k1c.cycles &&
sed -i -e 's/cycles: //' ./bitsliced-aes.gcc.k1c.cycles &&
sed -i -e 's/cycles: //' ./bitsliced-aes.ccomp.k1c.cycles &&
test $(cat ./bitsliced-aes.ccomp.k1c.cycles) -gt 300 &&
test $(cat ./bitsliced-aes.ccomp.k1c.cycles) -gt $(expr 2 '*' $(cat ./bitsliced-aes.gcc.k1c.cycles))
