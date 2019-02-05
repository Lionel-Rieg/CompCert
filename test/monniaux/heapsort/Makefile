include ../rules.mk

PRODUCTS=heapsort.gcc.host.out heapsort.ccomp.host.out heapsort.gcc.k1c.out heapsort.ccomp.k1c.out heapsort.ccomp.k1c.s heapsort.gcc.k1c.s heapsort.gcc.k1c heapsort.ccomp.k1c

all:	$(PRODUCTS)

heapsort.gcc.host: heapsort.c heapsort_run.gcc.host.o heapsort.h
	$(CC) $(CFLAGS) heapsort.c heapsort_run.gcc.host.o -o $@

heapsort.ccomp.host: heapsort.c heapsort_run.gcc.host.o heapsort.h
	$(CCOMP) $(CCOMPFLAGS) heapsort.c heapsort_run.gcc.host.o -o $@

heapsort.gcc.k1c.s heapsort.ccomp.k1c.s heapsort_run.gcc.k1c.s: heapsort.h

heapsort.gcc.k1c: heapsort.gcc.k1c.o heapsort_run.gcc.k1c.o
	$(K1C_CC) $(K1C_CFLAGS) $+ -o $@

heapsort.ccomp.k1c: heapsort.ccomp.k1c.o heapsort_run.gcc.k1c.o
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) $+ -o $@

%.k1c.out: %.k1c
	k1-cluster --cycle-based -- $< | tee $@

clean:
	$(RM) -f $(PRODUCTS) heapsort.gcc.k1c.o heapsort.ccomp.k1c.o heapsort_run.gcc.k1c.o heapsort_run.gcc.k1c.s

.PHONY: clean
