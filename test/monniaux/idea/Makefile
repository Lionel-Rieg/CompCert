include ../rules.mk

PRODUCTS=idea.gcc.host.out idea.ccomp.host.out idea.gcc.o1.k1c.out idea.gcc.k1c.out idea.ccomp.k1c.out idea.ccomp.k1c.s idea.gcc.k1c.s idea.gcc.k1c idea.ccomp.k1c

all:	$(PRODUCTS)

idea.gcc.host: idea.c idea.h ../clock.gcc.host.o
	$(CC) $(CFLAGS) idea.c ../clock.gcc.host.o -o $@

idea.ccomp.host: idea.c idea.h ../clock.gcc.host.o
	$(CCOMP) $(CCOMPFLAGS) idea.c ../clock.gcc.host.o -o $@

idea.gcc.k1c.s idea.ccomp.k1c.s idea_run.gcc.k1c.s: idea.h

idea.gcc.k1c: idea.gcc.k1c.o ../clock.gcc.k1c.o
	$(K1C_CC) $(K1C_CFLAGS) $+ -o $@

idea.gcc.o1.k1c: idea.gcc.o1.k1c.o ../clock.gcc.k1c.o
	$(K1C_CC) $(K1C_CFLAGS_O1) $+ -o $@

idea.ccomp.k1c: idea.ccomp.k1c.o ../clock.gcc.k1c.o
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) $+ -o $@

clean:
	$(RM) -f $(PRODUCTS) idea.gcc.k1c.o idea.ccomp.k1c.o

.PHONY: clean
