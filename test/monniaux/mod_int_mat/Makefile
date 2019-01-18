CFLAGS=-Wall -O3
K1C_CC=k1-mbr-gcc
K1C_CFLAGS=-Wall -O3 -std=c99
K1C_CCOMP=../../../ccomp
K1C_CCOMPFLAGS=-Wall -O3 -D__thread= -D__int128=int

PRODUCTS=int_mat.host int_mat.gcc.k1c.out int_mat.ccomp.k1c.out int_mat.ccomp.k1c.s int_mat.gcc.k1c.s int_mat.gcc.k1c int_mat.ccomp.k1c

all:	$(PRODUCTS)

%.gcc.k1c.s: %.c
	$(K1C_CC) $(K1C_CFLAGS) -S $< -o $@

%.gcc.k1c.o: %.gcc.k1c.s
	$(K1C_CC) $(K1C_CFLAGS) -c $< -o $@

%.gcc.k1c.o: %.gcc.k1c.c
	$(K1C_CC) $(K1C_CFLAGS) -c $< -o $@

%.ccomp.k1c.s: %.c
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) -S $< -o $@

%.ccomp.k1c.o: %.ccomp.k1c.s
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) -c $< -o $@

%.ccomp.k1c.o: %.ccomp.k1c.c
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) -c $< -o $@

int_mat.host: int_mat.c int_mat_run.c modint.h
	$(CC) $(CFLAGS) int_mat.c int_mat_run.c -o $@

int_mat.gcc.k1c.s int_mat.ccomp.k1c.s: modint.h

int_mat.gcc.k1c: int_mat.gcc.k1c.o int_mat_run.gcc.k1c.o
	$(K1C_CC) $(K1C_CFLAGS) $+ -o $@

int_mat.ccomp.k1c: int_mat.ccomp.k1c.o int_mat_run.gcc.k1c.o
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) $+ -o $@

%.k1c.out: %.k1c
	k1-cluster --cycle-based -- $< | tee $@

clean:
	$(RM) -f $(PRODUCTS) int_mat.gcc.k1c.o int_mat.ccomp.k1c.o int_mat_run.gcc.k1c.o

.PHONY: clean
