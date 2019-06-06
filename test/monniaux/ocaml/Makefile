ALL_CFLAGS=-Ibyterun
EXECUTE_ARGS=examples/quicksort

include ../rules.mk

ALL_CCOMPFLAGS=
LDLIBS=-lm

CFILES=$(wildcard byterun/*.c)

CCOMP_K1C_S=$(patsubst %.c,%.ccomp.k1c.s,$(CFILES))
CCOMP_HOST_S=$(patsubst %.c,%.ccomp.host.s,$(CFILES))

GCC_K1C_S=$(patsubst %.c,%.gcc.k1c.s,$(CFILES))
GCC_O1_K1C_S=$(patsubst %.c,%.gcc.o1.k1c.s,$(CFILES))
GCC_HOST_S=$(patsubst %.c,%.gcc.host.s,$(CFILES))

all: $(CCOMP_K1C_S) $(GCC_K1C_S) ocamlrun.ccomp.k1c.out ocamlrun.gcc.k1c.out ocamlrun.gcc.o1.k1c.out

ocamlrun.ccomp.k1c : $(CCOMP_K1C_S) ../clock.gcc.k1c.o
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) $+ -o $@ $(LDLIBS)

ocamlrun.ccomp.host : $(CCOMP_HOST_S) ../clock.gcc.host.o
	$(CCOMP) $(CCOMPFLAGS) $+ -o $@ $(LDLIBS)

ocamlrun.gcc.k1c : $(GCC_K1C_S) ../clock.gcc.k1c.o
	$(K1C_CC) $(K1C_CFLAGS) $+ -o $@ $(LDLIBS)

ocamlrun.gcc.o1.k1c : $(GCC_O1_K1C_S) ../clock.gcc.k1c.o
	$(K1C_CC) $(K1C_CFLAGS_O1) $+ -o $@ $(LDLIBS)

ocamlrun.gcc.host : $(GCC_HOST_S) ../clock.gcc.host.o
	$(CC) $(CFLAGS) $+ -o $@ $(LDLIBS)
