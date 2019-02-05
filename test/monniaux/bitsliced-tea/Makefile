include ../rules.mk

PRODUCTS=bstea.gcc.host.out bstea.ccomp.host.out bstea.gcc.k1c.out bstea.ccomp.k1c.out bstea.ccomp.k1c.s bstea.gcc.k1c.s bstea.gcc.k1c bstea.ccomp.k1c bstea.gcc.host bstea.ccomp.host

all:	$(PRODUCTS)

bstea.gcc.host: bstea.c bstea_run.c bstea.h ../clock.o
	$(CC) $(CFLAGS) bstea.c bstea_run.c ../clock.o -o $@

bstea.ccomp.host: bstea.c bstea_run.c bstea.h ../clock.o
	$(CCOMP) $(CCOMPFLAGS) bstea.c bstea_run.c ../clock.o -o $@

bstea.gcc.k1c.s bstea.ccomp.k1c.s bstea_run.gcc.k1c.s: bstea.h

bstea.gcc.k1c: bstea.gcc.k1c.o bstea_run.gcc.k1c.o ../clock.gcc.k1c.o
	$(K1C_CC) $(K1C_CFLAGS) $+ -o $@

bstea.ccomp.k1c: bstea.ccomp.k1c.o bstea_run.gcc.k1c.o ../clock.gcc.k1c.o
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) $+ -o $@

clean:
	$(RM) -f *.k1c *.host *.out *.o *.s

.PHONY: clean
