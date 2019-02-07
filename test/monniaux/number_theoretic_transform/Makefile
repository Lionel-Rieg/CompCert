include ../rules.mk

PRODUCTS=ntt.gcc.host.out ntt.ccomp.host.out ntt.gcc.k1c.out ntt.ccomp.k1c.out ntt.ccomp.k1c.s ntt.gcc.k1c.s ntt.gcc.k1c ntt.ccomp.k1c ntt.gcc.host ntt.ccomp.host

all:	$(PRODUCTS)

ntt.gcc.host: ntt.c ../clock.o
	$(CC) $(CFLAGS) ntt.c ../clock.o -o $@

ntt.ccomp.host: ntt.c ../clock.o
	$(CCOMP) $(CCOMPFLAGS) ntt.c ../clock.o -o $@

ntt.gcc.k1c: ntt.gcc.k1c.o ../clock.gcc.k1c.o
	$(K1C_CC) $(K1C_CFLAGS) $+ -o $@

ntt.ccomp.k1c: ntt.ccomp.k1c.o ../clock.gcc.k1c.o
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) $+ -o $@

clean:
	$(RM) -f *.k1c *.host *.out *.o *.s

.PHONY: clean
