include ../rules.mk

PRODUCTS=ternary.gcc.host.out ternary.ccomp.host.out \
	ternary.gcc.o1.k1c.out ternary.gcc.k1c.out ternary.ccomp.k1c.out \
	ternary.gcc.k1c.s ternary.ccomp.k1c.s

all:	$(PRODUCTS)

ternary.gcc.host.s ternary.ccomp.host.s ternary.gcc.k1c.s ternary.ccomp.k1c.s : ../clock.h

ternary.ccomp.host: ternary.ccomp.host.o ../clock.gcc.host.o
	$(CCOMP) $(CCOMPFLAGS) $+ -o $@

ternary.gcc.host: ternary.gcc.host.o ../clock.gcc.host.o
	$(CC) $(CFLAGS) $+ -o $@

ternary.gcc.k1c: ternary.gcc.k1c.o ../clock.gcc.k1c.o
	$(K1C_CC) $(K1C_CFLAGS) $+ -o $@

ternary.gcc.o1.k1c: ternary.gcc.o1.k1c.o ../clock.gcc.k1c.o
	$(K1C_CC) $(K1C_CFLAGS_O1) $+ -o $@

ternary.ccomp.k1c: ternary.ccomp.k1c.o ../clock.gcc.k1c.o
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) $+ -o $@

clean:
	-rm -f *.o *.s *.k1c

.PHONY: clean
