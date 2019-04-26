include ../rules.mk

PRODUCTS=binary_search.gcc.host.out binary_search.ccomp.host.out \
	binary_search.gcc.k1c.out binary_search.ccomp.k1c.out \
	binary_search.gcc.o1.k1c.out \
	binary_search.gcc.k1c.s binary_search.ccomp.k1c.s

all:	$(PRODUCTS)

binary_search.gcc.host.s binary_search.ccomp.host.s binary_search.gcc.k1c.s binary_search.ccomp.k1c.s : ../clock.h

binary_search.ccomp.host: binary_search.ccomp.host.o ../clock.gcc.host.o
	$(CCOMP) $(CCOMPFLAGS) $+ -o $@

binary_search.gcc.host: binary_search.gcc.host.o ../clock.gcc.host.o
	$(CC) $(CFLAGS) $+ -o $@

binary_search.gcc.k1c: binary_search.gcc.k1c.o ../clock.gcc.k1c.o
	$(K1C_CC) $(K1C_CFLAGS) $+ -o $@

binary_search.gcc.o1.k1c: binary_search.gcc.o1.k1c.o ../clock.gcc.k1c.o
	$(K1C_CC) $(K1C_CFLAGS_O1) $+ -o $@

binary_search.ccomp.k1c: binary_search.ccomp.k1c.o ../clock.gcc.k1c.o
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) $+ -o $@

clean:
	-rm -f *.o *.s *.k1c

.PHONY: clean
