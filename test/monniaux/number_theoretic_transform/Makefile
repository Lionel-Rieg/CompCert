include ../rules.mk

PRODUCTS=nft.gcc.host.out nft.ccomp.host.out nft.gcc.k1c.out nft.ccomp.k1c.out nft.ccomp.k1c.s nft.gcc.k1c.s nft.gcc.k1c nft.ccomp.k1c nft.gcc.host nft.ccomp.host

all:	$(PRODUCTS)

nft.gcc.host: nft.c ../clock.o
	$(CC) $(CFLAGS) nft.c ../clock.o -o $@

nft.ccomp.host: nft.c ../clock.o
	$(CCOMP) $(CCOMPFLAGS) nft.c ../clock.o -o $@

nft.gcc.k1c: nft.gcc.k1c.o ../clock.gcc.k1c.o
	$(K1C_CC) $(K1C_CFLAGS) $+ -o $@

nft.ccomp.k1c: nft.ccomp.k1c.o ../clock.gcc.k1c.o
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) $+ -o $@

clean:
	$(RM) -f *.k1c *.host *.out *.o *.s

.PHONY: clean
