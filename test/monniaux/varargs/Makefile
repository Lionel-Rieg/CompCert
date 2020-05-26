include ../rules.mk

all: varargs.ccomp.kvx.s varargs.ccomp.kvx

varargs.ccomp.kvx: varargs.ccomp.kvx.o
	$(KVX_CCOMP) $(KVX_CCOMPFLAGS) $+ -o $@

clean:
	$(RM) -f *.kvx *.host *.o *.s
