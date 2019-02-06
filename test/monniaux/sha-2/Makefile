include ../rules.mk

PRODUCTS=sha-256.host sha-256.gcc.k1c.out sha-256.ccomp.k1c.out sha-256.ccomp.k1c.s sha-256.gcc.k1c.s sha-256.gcc.k1c sha-256.ccomp.k1c

all:	$(PRODUCTS)

sha-256.host: sha-256.c sha-256_run.c sha-256.h
	$(CC) $(CFLAGS) sha-256.c sha-256_run.c -o $@

sha-256.gcc.k1c.s sha-256.ccomp.k1c.s sha-256_run.gcc.k1c.s: sha-256.h

sha-256.gcc.k1c: sha-256.gcc.k1c.o sha-256_run.gcc.k1c.o
	$(K1C_CC) $(K1C_CFLAGS) $+ -o $@

sha-256.ccomp.k1c: sha-256.ccomp.k1c.o sha-256_run.gcc.k1c.o
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) $+ -o $@

clean:
	$(RM) -f $(PRODUCTS) sha-256.gcc.k1c.o sha-256.ccomp.k1c.o sha-256_run.gcc.k1c.o sha-256_run.gcc.k1c.s

.PHONY: clean
