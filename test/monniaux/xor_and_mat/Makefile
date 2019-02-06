include ../rules.mk

PRODUCTS=int_mat.host int_mat.gcc.k1c.out int_mat.ccomp.k1c.out int_mat.ccomp.k1c.s int_mat.gcc.k1c.s int_mat.gcc.k1c int_mat.ccomp.k1c

all:	$(PRODUCTS)

int_mat.host: int_mat.c int_mat_run.c xor_and.h
	$(CC) $(CFLAGS) int_mat.c int_mat_run.c -o $@

int_mat.gcc.k1c.s int_mat.ccomp.k1c.s int_mat_run.gcc.k1c.s: xor_and.h

int_mat.gcc.k1c: int_mat.gcc.k1c.o int_mat_run.gcc.k1c.o
	$(K1C_CC) $(K1C_CFLAGS) $+ -o $@

int_mat.ccomp.k1c: int_mat.ccomp.k1c.o int_mat_run.gcc.k1c.o
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) $+ -o $@

clean:
	$(RM) -f $(PRODUCTS) int_mat.gcc.k1c.o int_mat.ccomp.k1c.o int_mat_run.gcc.k1c.o

.PHONY: clean
