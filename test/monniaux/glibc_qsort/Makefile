CFLAGS=-Wall -O3
K1C_CC=k1-mbr-gcc
K1C_CFLAGS=-Wall -O3 -pedantic -std=c99
K1C_CCOMP=../../../ccomp
K1C_CCOMPFLAGS=-Wall -O3

PRODUCTS=glibc_qsort.host glibc_qsort.gcc.k1c.out glibc_qsort.ccomp.k1c.out glibc_qsort.ccomp.k1c.s glibc_qsort.gcc.k1c.s glibc_qsort.gcc.k1c glibc_qsort.ccomp.k1c

all:	$(PRODUCTS)

%.gcc.k1c.s: %.c
	$(K1C_CC) $(K1C_CFLAGS) -S $< -o $@

%.gcc.k1c.o: %.gcc.k1c.s
	$(K1C_CC) $(K1C_CFLAGS) -c $< -o $@

%.ccomp.k1c.s: %.c
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) -S $< -o $@

%.ccomp.k1c.o: %.ccomp.k1c.s
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) -c $< -o $@

glibc_qsort.host: glibc_qsort.c glibc_qsort_run.c glibc_qsort.h
	$(CC) $(CFLAGS) glibc_qsort.c glibc_qsort_run.c -o $@

glibc_qsort.gcc.k1c.s glibc_qsort.ccomp.k1c.s glibc_qsort_run.gcc.k1c.s: glibc_qsort.h

glibc_qsort.gcc.k1c: glibc_qsort.gcc.k1c.o glibc_qsort_run.gcc.k1c.o
	$(K1C_CC) $(K1C_CFLAGS) $+ -o $@

glibc_qsort.ccomp.k1c: glibc_qsort.ccomp.k1c.o glibc_qsort_run.gcc.k1c.o
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) $+ -o $@

%.k1c.out: %.k1c
	k1-cluster --cycle-based -- $< | tee $@

clean:
	$(RM) -f $(PRODUCTS) glibc_qsort.gcc.k1c.o glibc_qsort.ccomp.k1c.o glibc_qsort_run.gcc.k1c.o glibc_qsort_run.gcc.k1c.s

.PHONY: clean
