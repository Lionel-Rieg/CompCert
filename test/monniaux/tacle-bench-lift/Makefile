ALL_CFLAGS = -include kill_pragma.h

CFILES=lift.c	liftlibcontrol.c  liftlibio.c

HFILES=liftlibcontrol.h  liftlibio.h

K1C_GCC_OFILES=$(CFILES:.c=.gcc.k1c.o)
K1C_GCC_OFILES_O1=$(CFILES:.c=.gcc.o1.k1c.o)
K1C_CCOMP_OFILES=$(CFILES:.c=.ccomp.k1c.o)
K1C_GCC_SFILES=$(CFILES:.c=.gcc.k1c.s)
K1C_CCOMP_SFILES=$(CFILES:.c=.ccomp.k1c.s)

HOST_GCC_OFILES=$(CFILES:.c=.gcc.host.o)
HOST_CCOMP_OFILES=$(CFILES:.c=.ccomp.host.o)
HOST_GCC_SFILES=$(CFILES:.c=.gcc.host.s)
HOST_CCOMP_SFILES=$(CFILES:.c=.ccomp.host.s)

all:	lift.gcc.o1.k1c.out lift.gcc.k1c.out lift.ccomp.k1c.out $(K1C_GCC_SFILES) $(K1C_CCOMP_SFILES)

include ../rules.mk

$(K1C_GCC_SFILES) $(K1C_CCOMP_SFILES) $(HOST_GCC_SFILES) $(HOST_CCOMP_SFILES) : $(HFILES)

lift.gcc.k1c: $(K1C_GCC_OFILES)
	$(K1C_CC) $(K1C_CFLAGS) -o $@ $+ ../clock.gcc.k1c.o

lift.gcc.o1.k1c: $(K1C_GCC_OFILES_O1)
	$(K1C_CC) $(K1C_CFLAGS_O1) -o $@ $+ ../clock.gcc.k1c.o

lift.ccomp.k1c: $(K1C_CCOMP_OFILES)
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) -o $@ $+ ../clock.gcc.k1c.o

lift.gcc.host: $(HOST_GCC_OFILES)
	$(CC) $(CFLAGS) -o $@ $+ ../clock.gcc.host.o

lift.ccomp.host: $(HOST_CCOMP_OFILES)
	$(CCOMP) $(CCOMPFLAGS) -o $@ $+ ../clock.gcc.host.o

.PHONY: clean

clean:
	rm -f *.s *.o *.k1c
