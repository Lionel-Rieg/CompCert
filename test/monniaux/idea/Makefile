CFLAGS=-Wall -O3
CCOMP=ccomp # for host
CCOMPFLAGS=-Wall -O3
K1C_CC=k1-mbr-gcc
K1C_CFLAGS=-Wall -O3 -std=c99
K1C_CCOMP=../../../ccomp
K1C_CCOMPFLAGS=-Wall -O3

PRODUCTS=idea.gcc.host.out idea.ccomp.host.out idea.gcc.k1c.out idea.ccomp.k1c.out idea.ccomp.k1c.s idea.gcc.k1c.s idea.gcc.k1c idea.ccomp.k1c

all:	$(PRODUCTS)

%.gcc.k1c.s: %.c
	$(K1C_CC) $(K1C_CFLAGS) -S $< -o $@

%.gcc.k1c.o: %.gcc.k1c.s
	$(K1C_CC) $(K1C_CFLAGS) -c $< -o $@

%.ccomp.k1c.s: %.c
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) -S $< -o $@

%.ccomp.k1c.o: %.ccomp.k1c.s
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) -c $< -o $@

%.gcc.host.o: %.c
	$(CC) $(K1C_CFLAGS) -c $< -o $@

%.ccomp.host.o: %.c
	$(CCOMP) $(CCOMPFLAGS) -c $< -o $@

idea.gcc.host: idea.c idea.h ../clock.gcc.host.o
	$(CC) $(CFLAGS) idea.c ../clock.gcc.host.o -o $@

idea.ccomp.host: idea.c idea.h ../clock.gcc.host.o
	$(CCOMP) $(CFLAGS) idea.c ../clock.gcc.host.o -o $@

idea.gcc.k1c.s idea.ccomp.k1c.s idea_run.gcc.k1c.s: idea.h

idea.gcc.k1c: idea.gcc.k1c.o ../clock.gcc.k1c.o
	$(K1C_CC) $(K1C_CFLAGS) $+ -o $@

idea.ccomp.k1c: idea.ccomp.k1c.o ../clock.gcc.k1c.o
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) $+ -o $@

%.k1c.out: %.k1c
	k1-cluster --cycle-based -- $< | tee $@

%.host.out: %.host
	./$< | tee $@

clean:
	$(RM) -f $(PRODUCTS) idea.gcc.k1c.o idea.ccomp.k1c.o

.PHONY: clean
