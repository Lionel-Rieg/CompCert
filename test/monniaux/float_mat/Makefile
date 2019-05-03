include ../rules.mk

PRODUCTS=float_mat.host float_mat.gcc.o1.k1c.out float_mat.gcc.k1c.out float_mat.ccomp.k1c.out float_mat.ccomp.k1c.s float_mat.gcc.k1c.s float_mat.gcc.k1c float_mat.ccomp.k1c

all:	$(PRODUCTS)

float_mat.host: float_mat.c float_mat_run.c float_mat.h
	$(CC) $(CFLAGS) float_mat.c float_mat_run.c -o $@

float_mat.gcc.k1c.s float_mat.ccomp.k1c.s float_mat_run.gcc.k1c.s: float_mat.h

float_mat.gcc.k1c: float_mat.gcc.k1c.o float_mat_run.gcc.k1c.o
	$(K1C_CC) $(K1C_CFLAGS) $+ -o $@

float_mat.gcc.o1.k1c: float_mat.gcc.o1.k1c.o float_mat_run.gcc.o1.k1c.o
	$(K1C_CC) $(K1C_CFLAGS_O1) $+ -o $@

float_mat.ccomp.k1c: float_mat.ccomp.k1c.o float_mat_run.gcc.k1c.o
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) $+ -o $@

clean:
	$(RM) -f *.k1c *.host *.o *.s

.PHONY: clean
