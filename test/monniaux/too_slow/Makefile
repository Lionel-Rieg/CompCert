include ../rules.mk

PRODUCTS=memset_from_bitsliced-aes.gcc.host.out memset_from_bitsliced-aes.ccomp.host.out \
	memset_from_bitsliced-aes.gcc.k1c.out memset_from_bitsliced-aes.ccomp.k1c.out \
	memset_from_bitsliced-aes.gcc.k1c.s memset_from_bitsliced-aes.ccomp.k1c.s

all:	$(PRODUCTS)

memset_from_bitsliced-aes.gcc.host.s memset_from_bitsliced-aes.ccomp.host.s memset_from_bitsliced-aes.gcc.k1c.s memset_from_bitsliced-aes.ccomp.k1c.s : ../clock.h

memset_from_bitsliced-aes.ccomp.host: memset_from_bitsliced-aes.ccomp.host.o ../clock.gcc.host.o
	$(CCOMP) $(CCOMPFLAGS) $+ -o $@

memset_from_bitsliced-aes.gcc.host: memset_from_bitsliced-aes.gcc.host.o ../clock.gcc.host.o
	$(CC) $(CFLAGS) $+ -o $@

memset_from_bitsliced-aes.gcc.k1c: memset_from_bitsliced-aes.gcc.k1c.o ../clock.gcc.k1c.o
	$(K1C_CC) $(K1C_CFLAGS) $+ -o $@

memset_from_bitsliced-aes.ccomp.k1c: memset_from_bitsliced-aes.ccomp.k1c.o ../clock.gcc.k1c.o
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) $+ -o $@

clean:
	-rm -f *.o *.s *.k1c

.PHONY: clean

