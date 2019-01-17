CFLAGS=-Wall -O3
K1C_CC=k1-mbr-gcc
K1C_CFLAGS=-Wall -O3 -std=c99
K1C_CCOMP=../../ccomp
K1C_CCOMPFLAGS=-Wall -O3 -D__thread= -D__int128=int

PRODUCTS=int_mat.host int_mat.k1c int_mat.k1c_ccomp int_mat.k1c_ccomp.s int_mat.k1c.s

all:	$(PRODUCTS)

int_mat.host: int_mat.c int_mat_run.c modint.h
	$(CC) $(CFLAGS) int_mat.c int_mat_run.c -o $@

int_mat.k1c.s: int_mat.c modint.h
	$(K1C_CC) $(K1C_CFLAGS) -S int_mat.c -o $@

int_mat.k1c: int_mat.k1c.s int_mat_run.k1c.o modint.h
	$(K1C_CC) $(K1C_CFLAGS) int_mat.k1c.s int_mat_run.k1c.o -o $@

int_mat_run.k1c.o: int_mat_run.c modint.h
	$(K1C_CC) $(K1C_CFLAGS) -c int_mat_run.c -o $@

int_mat.k1c_ccomp.s: int_mat.c modint.h
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) -S int_mat.c -o $@

int_mat.k1c_ccomp: int_mat.k1c_ccomp.s int_mat_run.k1c.o modint.h
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) int_mat.k1c_ccomp.s int_mat_run.k1c.o -o $@

clean:
	$(RM) -f $(PRODUCTS)

.PHONY: clean
