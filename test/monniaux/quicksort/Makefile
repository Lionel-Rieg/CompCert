include ../rules.mk

PRODUCTS=quicksort.host quicksort.gcc.o1.k1c.out quicksort.gcc.k1c.out quicksort.ccomp.k1c.out quicksort.ccomp.k1c.s quicksort.gcc.k1c.s quicksort.gcc.k1c quicksort.ccomp.k1c

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

quicksort.gcc.o1.k1c: quicksort.gcc.o1.k1c.o quicksort_run.gcc.o1.k1c.o
	$(K1C_CC) $(K1C_CFLAGS) $+ -o $@

quicksort.ccomp.k1c: quicksort.ccomp.k1c.o quicksort_run.gcc.k1c.o
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) $+ -o $@

clean:
	$(RM) -f $(PRODUCTS) quicksort.gcc.k1c.o quicksort.ccomp.k1c.o quicksort_run.gcc.k1c.o quicksort_run.gcc.k1c.s

.PHONY: clean
