src = $(wildcard *.c) tests/tests.c

include ../rules.mk

all: test.gcc.k1c.out test.ccomp.k1c.out test.gcc.host.out test.ccomp.host.out

test.gcc.k1c: $(src:.c=.gcc.k1c.o) ../clock.gcc.k1c.o
	$(K1C_CC) $(K1C_CFLAGS) -o $@ $+

test.ccomp.k1c: $(src:.c=.ccomp.k1c.o) ../clock.gcc.k1c.o
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) -o $@ $+

test.gcc.host: $(src:.c=.gcc.host.o) ../clock.gcc.host.o
	$(CC) $(CFLAGS) -o $@ $+

test.ccomp.host: $(src:.c=.ccomp.host.o) ../clock.gcc.host.o
	$(CCOMP) $(CCOMPFLAGS) -o $@ $+

clean:
	rm -f *.o *.k1c *.host */*.o *.s */*.s *.out
