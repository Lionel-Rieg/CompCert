include ../rules.mk

all: varargs.ccomp.k1c.s varargs.ccomp.k1c

varargs.ccomp.k1c: varargs.ccomp.k1c.o
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) $+ -o $@

clean:
	$(RM) -f *.k1c *.host *.o *.s
