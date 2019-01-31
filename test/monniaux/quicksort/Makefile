CFLAGS=-Wall -O3
K1C_CC=k1-mbr-gcc
K1C_CFLAGS=-Wall -std=c99 -O2
K1C_CCOMP=../../../ccomp
K1C_CCOMPFLAGS=-Wall -O3

PRODUCTS=quicksort.host quicksort.gcc.k1c.out quicksort.ccomp.k1c.out quicksort.ccomp.k1c.s quicksort.gcc.k1c.s quicksort.gcc.k1c quicksort.ccomp.k1c

all:	$(PRODUCTS)

%.gcc.k1c.s: %.c
	$(K1C_CC) $(K1C_CFLAGS) -S $< -o $@

%.gcc.k1c.o: %.gcc.k1c.s
	$(K1C_CC) $(K1C_CFLAGS) -c $< -o $@

%.ccomp.k1c.s: %.c
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) -S $< -o $@

%.ccomp.k1c.o: %.ccomp.k1c.s
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) -c $< -o $@

quicksort.host: quicksort.c quicksort_run.c quicksort.h
	$(CC) $(CFLAGS) quicksort.c quicksort_run.c -o $@

quicksort.gcc.k1c.s quicksort.ccomp.k1c.s quicksort_run.gcc.k1c.s: quicksort.h

quicksort.gcc.k1c: quicksort.gcc.k1c.o quicksort_run.gcc.k1c.o
	$(K1C_CC) $(K1C_CFLAGS) $+ -o $@

quicksort.ccomp.k1c: quicksort.ccomp.k1c.o quicksort_run.gcc.k1c.o
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) $+ -o $@

%.k1c.out: %.k1c
	k1-cluster --cycle-based -- $< | tee $@

clean:
	$(RM) -f $(PRODUCTS) quicksort.gcc.k1c.o quicksort.ccomp.k1c.o quicksort_run.gcc.k1c.o quicksort_run.gcc.k1c.s

.PHONY: clean
