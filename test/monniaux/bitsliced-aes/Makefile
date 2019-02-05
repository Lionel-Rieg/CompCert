src = $(wildcard *.c) tests/tests.c


CCOMP=ccomp
CCOMPFLAGS=-O3 -Wall
K1C_CC=k1-mbr-gcc
K1C_CFLAGS = -std=c99 -O3 -Wall -Wextra -Werror=implicit
K1C_CCOMP = ../../../ccomp
K1C_CCOMPFLAGS=-O3 -Wall

%.host.gcc.o : %.c
	$(CC) $(CFLAGS) -c -o $@ $<

%.host.ccomp.o : %.c
	$(CCOMP) $(CCOMPFLAGS) -c -o $@ $<

%.gcc.k1c.s: %.c
	$(K1C_CC) $(K1C_CFLAGS) -S $< -o $@

%.gcc.k1c.o: %.gcc.k1c.s
	$(K1C_CC) $(K1C_CFLAGS) -c $< -o $@

%.ccomp.k1c.s: %.c
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) -S $< -o $@

%.ccomp.k1c.o: %.ccomp.k1c.s
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) -c $< -o $@

%.gcc.host.o: %.c
	$(CC) $(CFLAGS) -c $< -o $@

%.ccomp.host.o: %.c
	$(CCOMP) $(CCOMPFLAGS) -c $< -o $@

%.k1c.out : %.k1c
	k1-cluster --cycle-based -- $< |tee $@

%.host.out : %.host
	./$< |tee $@

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
