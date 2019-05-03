include ../rules.mk

PRODUCTS=complex_mat.gcc.host.out complex_mat.ccomp.host.out \
	complex_mat.gcc.k1c.out complex_mat.gcc.o1.k1c.out complex_mat.ccomp.k1c.out \
	complex_mat.gcc.k1c.s complex_mat.ccomp.k1c.s

all:	$(PRODUCTS)

complex_mat.gcc.host.s complex_mat.ccomp.host.s complex_mat.gcc.k1c.s complex_mat.ccomp.k1c.s : ../clock.h

complex_mat.ccomp.host: complex_mat.ccomp.host.o ../clock.gcc.host.o
	$(CCOMP) $(CCOMPFLAGS) $+ -o $@

complex_mat.gcc.host: complex_mat.gcc.host.o ../clock.gcc.host.o
	$(CC) $(CFLAGS) $+ -o $@

complex_mat.gcc.k1c: complex_mat.gcc.k1c.o ../clock.gcc.k1c.o
	$(K1C_CC) $(K1C_CFLAGS) $+ -o $@

complex_mat.gcc.o1.k1c: complex_mat.gcc.o1.k1c.o ../clock.gcc.k1c.o
	$(K1C_CC) $(K1C_CFLAGS_O1) $+ -o $@

complex_mat.ccomp.k1c: complex_mat.ccomp.k1c.o ../clock.gcc.k1c.o
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) $+ -o $@

clean:
	-rm -f *.o *.s *.k1c

.PHONY: clean
