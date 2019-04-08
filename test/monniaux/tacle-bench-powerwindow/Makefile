ALL_CFLAGS = -include kill_pragma.h

CFILES=	powerwindow.c			powerwindow_PW_Control_DRV.c \
	powerwindow_const_params.c	powerwindow_PW_Control_PSG_BackL.c \
	powerwindow_controlexclusion.c	powerwindow_PW_Control_PSG_BackR.c \
	powerwindow_debounce.c		powerwindow_PW_Control_PSG_Front.c \
	powerwindow_inputs.c		wcclib.c \
	powerwindow_powerwindow_control.c

HFILES=	kill_pragma.h  wcclib.h \
	$(wildcard powerwindow_HeaderFiles/*.h)

K1C_GCC_OFILES=$(CFILES:.c=.gcc.k1c.o)
K1C_CCOMP_OFILES=$(CFILES:.c=.ccomp.k1c.o)
K1C_GCC_SFILES=$(CFILES:.c=.gcc.k1c.s)
K1C_CCOMP_SFILES=$(CFILES:.c=.ccomp.k1c.s)

HOST_GCC_OFILES=$(CFILES:.c=.gcc.host.o)
HOST_CCOMP_OFILES=$(CFILES:.c=.ccomp.host.o)
HOST_GCC_SFILES=$(CFILES:.c=.gcc.host.s)
HOST_CCOMP_SFILES=$(CFILES:.c=.ccomp.host.s)

all:	powerwindow.gcc.k1c.out powerwindow.ccomp.k1c.out $(K1C_GCC_SFILES) $(K1C_CCOMP_SFILES)

include ../rules.mk

$(K1C_GCC_SFILES) $(K1C_CCOMP_SFILES) $(HOST_GCC_SFILES) $(HOST_CCOMP_SFILES) : $(HFILES)

powerwindow.gcc.k1c: $(K1C_GCC_OFILES)
	$(K1C_CC) $(K1C_CFLAGS) -o $@ $+ ../clock.gcc.k1c.o

powerwindow.ccomp.k1c: $(K1C_CCOMP_OFILES)
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) -o $@ $+ ../clock.gcc.k1c.o

powerwindow.gcc.host: $(HOST_GCC_OFILES)
	$(CC) $(CFLAGS) -o $@ $+ ../clock.gcc.host.o

powerwindow.ccomp.host: $(HOST_CCOMP_OFILES)
	$(CCOMP) $(CCOMPFLAGS) -o $@ $+ ../clock.gcc.host.o

.PHONY: clean

clean:
	rm -f *.s *.o *.k1c
