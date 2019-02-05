CFLAGS=-Wall -O3
CCOMP=ccomp
CCOMPFLAGS=-Wall -O3
K1C_CC=k1-mbr-gcc
K1C_CFLAGS=-Wall -O3 -std=c99
K1C_CCOMP=../../../ccomp
K1C_CCOMPFLAGS=-Wall -O3

PRODUCTS=bstea.gcc.host.out bstea.ccomp.host.out bstea.gcc.k1c.out bstea.ccomp.k1c.out bstea.ccomp.k1c.s bstea.gcc.k1c.s bstea.gcc.k1c bstea.ccomp.k1c bstea.gcc.host bstea.ccomp.host

all:	$(PRODUCTS)

%.gcc.k1c.s: %.c
	$(K1C_CC) $(K1C_CFLAGS) -S $< -o $@

%.gcc.k1c.o: %.gcc.k1c.s
	$(K1C_CC) $(K1C_CFLAGS) -c $< -o $@

%.ccomp.k1c.s: %.c
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) -S $< -o $@

%.ccomp.k1c.o: %.ccomp.k1c.s
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) -c $< -o $@

%.gcc.gcc.o: %.c
	$(CC) $(CFLAGS) -c $< -o $@

%.ccomp.k1c.o: %.c
	$(CCOMP) $(CCOMPFLAGS) -c $< -o $@

bstea.gcc.host: bstea.c bstea_run.c bstea.h ../clock.o
	$(CC) $(CFLAGS) bstea.c bstea_run.c ../clock.o -o $@

bstea.ccomp.host: bstea.c bstea_run.c bstea.h ../clock.o
	$(CCOMP) $(CCOMPFLAGS) bstea.c bstea_run.c ../clock.o -o $@

bstea.gcc.k1c.s bstea.ccomp.k1c.s bstea_run.gcc.k1c.s: bstea.h

bstea.gcc.k1c: bstea.gcc.k1c.o bstea_run.gcc.k1c.o ../clock.gcc.k1c.o
	$(K1C_CC) $(K1C_CFLAGS) $+ -o $@

bstea.ccomp.k1c: bstea.ccomp.k1c.o bstea_run.gcc.k1c.o ../clock.gcc.k1c.o
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) $+ -o $@

%.k1c.out: %.k1c
	k1-cluster --cycle-based -- $< | tee $@

%.host.out: %.host
	./$< | tee $@

clean:
	$(RM) -f *.k1c *.host *.out *.o *.s

.PHONY: clean
