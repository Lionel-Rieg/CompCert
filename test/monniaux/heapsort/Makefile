CFLAGS=-Wall -O3
K1C_CC=k1-mbr-gcc
K1C_CFLAGS=-Wall -O3 -std=c99
K1C_CCOMP=../../../ccomp
K1C_CCOMPFLAGS=-Wall -O3 -D__thread= -D__int128=int

PRODUCTS=heapsort.host heapsort.gcc.k1c.out heapsort.ccomp.k1c.out heapsort.ccomp.k1c.s heapsort.gcc.k1c.s heapsort.gcc.k1c heapsort.ccomp.k1c

all:	$(PRODUCTS)

%.gcc.k1c.s: %.c
	$(K1C_CC) $(K1C_CFLAGS) -S $< -o $@

%.gcc.k1c.o: %.gcc.k1c.s
	$(K1C_CC) $(K1C_CFLAGS) -c $< -o $@

%.ccomp.k1c.s: %.c
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) -S $< -o $@

%.ccomp.k1c.o: %.ccomp.k1c.s
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) -c $< -o $@

heapsort.host: heapsort.c heapsort_run.c heapsort.h
	$(CC) $(CFLAGS) heapsort.c heapsort_run.c -o $@

heapsort.gcc.k1c.s heapsort.ccomp.k1c.s heapsort_run.gcc.k1c.s: heapsort.h

heapsort.gcc.k1c: heapsort.gcc.k1c.o heapsort_run.gcc.k1c.o
	$(K1C_CC) $(K1C_CFLAGS) $+ -o $@

heapsort.ccomp.k1c: heapsort.ccomp.k1c.o heapsort_run.gcc.k1c.o
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) $+ -o $@

%.k1c.out: %.k1c
	k1-cluster --cycle-based -- $< | tee $@

clean:
	$(RM) -f $(PRODUCTS) heapsort.gcc.k1c.o heapsort.ccomp.k1c.o heapsort_run.gcc.k1c.o heapsort_run.gcc.k1c.s

.PHONY: clean
