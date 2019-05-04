include ../rules.mk

PRODUCTS=glibc_qsort.gcc.host.out glibc_qsort.ccomp.host.out glibc_qsort.gcc.k1c.out glibc_qsort.gcc.o1.k1c.out glibc_qsort.ccomp.k1c.out glibc_qsort.ccomp.k1c.s glibc_qsort.gcc.k1c.s glibc_qsort.gcc.k1c glibc_qsort.ccomp.k1c

all:	$(PRODUCTS)

glibc_qsort.gcc.host: glibc_qsort.c glibc_qsort_run.gcc.host.o glibc_qsort.h
	$(CC) $(CFLAGS) glibc_qsort.c glibc_qsort_run.gcc.host.o -o $@

glibc_qsort.ccomp.host: glibc_qsort.c glibc_qsort_run.gcc.host.o glibc_qsort.h
	$(CCOMP) $(CCOMPFLAGS) glibc_qsort.c glibc_qsort_run.gcc.host.o -o $@

glibc_qsort.gcc.k1c.s glibc_qsort.ccomp.k1c.s glibc_qsort_run.gcc.k1c.s: glibc_qsort.h

glibc_qsort.gcc.k1c: glibc_qsort.gcc.k1c.o glibc_qsort_run.gcc.k1c.o
	$(K1C_CC) $(K1C_CFLAGS) $+ -o $@

glibc_qsort.gcc.o1.k1c: glibc_qsort.gcc.o1.k1c.o glibc_qsort_run.gcc.o1.k1c.o
	$(K1C_CC) $(K1C_CFLAGS_O1) $+ -o $@

glibc_qsort.ccomp.k1c: glibc_qsort.ccomp.k1c.o glibc_qsort_run.gcc.k1c.o
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) $+ -o $@

clean:
	$(RM) -f $(PRODUCTS) glibc_qsort.gcc.k1c.o glibc_qsort.ccomp.k1c.o glibc_qsort_run.gcc.k1c.o glibc_qsort_run.gcc.k1c.s

.PHONY: clean
