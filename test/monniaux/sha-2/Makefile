CFLAGS=-Wall -O3
K1C_CC=k1-mbr-gcc
K1C_CFLAGS=-Wall -O3 -std=c99
K1C_CCOMP=../../../ccomp
K1C_CCOMPFLAGS=-Wall -O3 -D__thread= -D__int128=int

PRODUCTS=sha-256.host sha-256.gcc.k1c.out sha-256.ccomp.k1c.out sha-256.ccomp.k1c.s sha-256.gcc.k1c.s sha-256.gcc.k1c sha-256.ccomp.k1c

all:	$(PRODUCTS)

%.gcc.k1c.s: %.c
	$(K1C_CC) $(K1C_CFLAGS) -S $< -o $@

%.gcc.k1c.o: %.gcc.k1c.s
	$(K1C_CC) $(K1C_CFLAGS) -c $< -o $@

%.ccomp.k1c.s: %.c
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) -S $< -o $@

%.ccomp.k1c.o: %.ccomp.k1c.s
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) -c $< -o $@

sha-256.host: sha-256.c sha-256_run.c sha-256.h
	$(CC) $(CFLAGS) sha-256.c sha-256_run.c -o $@

sha-256.gcc.k1c.s sha-256.ccomp.k1c.s sha-256_run.gcc.k1c.s: sha-256.h

sha-256.gcc.k1c: sha-256.gcc.k1c.o sha-256_run.gcc.k1c.o
	$(K1C_CC) $(K1C_CFLAGS) $+ -o $@

sha-256.ccomp.k1c: sha-256.ccomp.k1c.o sha-256_run.gcc.k1c.o
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) $+ -o $@

%.k1c.out: %.k1c
	k1-cluster --cycle-based -- $< | tee $@

clean:
	$(RM) -f $(PRODUCTS) sha-256.gcc.k1c.o sha-256.ccomp.k1c.o sha-256_run.gcc.k1c.o sha-256_run.gcc.k1c.s

.PHONY: clean
