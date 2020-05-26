CFLAGS=-Wall -O3 -std=c99
KVX_CC=k1-cos-gcc
KVX_CFLAGS=-Wall -O3 -std=c99
KVX_CCOMP=../../../ccomp
KVX_CCOMPFLAGS=-Wall -O3

PRODUCTS=int_mat.host int_mat.gcc.kvx.out int_mat.ccomp.kvx.out int_mat.ccomp.kvx.s int_mat.gcc.kvx.s int_mat.gcc.kvx int_mat.ccomp.kvx

all:	$(PRODUCTS)

%.gcc.kvx.s: %.c
	$(KVX_CC) $(KVX_CFLAGS) -S $< -o $@

%.gcc.kvx.o: %.gcc.kvx.s
	$(KVX_CC) $(KVX_CFLAGS) -c $< -o $@

%.ccomp.kvx.s: %.c
	$(KVX_CCOMP) $(KVX_CCOMPFLAGS) -S $< -o $@

%.ccomp.kvx.o: %.ccomp.kvx.s
	$(KVX_CCOMP) $(KVX_CCOMPFLAGS) -c $< -o $@

int_mat.host: int_mat.c int_mat_run.c modint.h
	$(CC) $(CFLAGS) int_mat.c int_mat_run.c -o $@

int_mat.gcc.kvx.s int_mat.ccomp.kvx.s int_mat_run.gcc.kvx.s: modint.h

int_mat.gcc.kvx: int_mat.gcc.kvx.o int_mat_run.gcc.kvx.o
	$(KVX_CC) $(KVX_CFLAGS) $+ -o $@

int_mat.ccomp.kvx: int_mat.ccomp.kvx.o int_mat_run.gcc.kvx.o
	$(KVX_CCOMP) $(KVX_CCOMPFLAGS) $+ -o $@

%.kvx.out: %.kvx
	k1-cluster --cycle-based -- $< | tee $@

clean:
	$(RM) -f $(PRODUCTS) int_mat.gcc.kvx.o int_mat.ccomp.kvx.o int_mat_run.gcc.kvx.o

.PHONY: clean
