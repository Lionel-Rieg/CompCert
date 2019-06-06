
include ../rules.mk


src=int_mat_run.c int_mat.c

PRODUCTS?=xor_and_mat.gcc.host xor_and_mat.ccomp.host xor_and_mat.gcc.k1c xor_and_mat.gcc.o1.k1c xor_and_mat.ccomp.k1c
PRODUCTS_OUT=$(addsuffix .out,$(PRODUCTS))

all: $(PRODUCTS)

.PHONY:
run: measures.csv


xor_and_mat.gcc.host: $(src:.c=.gcc.host.o) ../clock.gcc.host.o 
	$(CC) $(CFLAGS) $+ -o $@
xor_and_mat.ccomp.host: $(src:.c=.ccomp.host.o) ../clock.gcc.host.o 
	$(CCOMP) $(CCOMPFLAGS) $+ -o $@
xor_and_mat.gcc.k1c: $(src:.c=.gcc.k1c.o) ../clock.gcc.k1c.o 
	$(K1C_CC) $(K1C_CFLAGS) $+ -o $@
xor_and_mat.gcc.o1.k1c: $(src:.c=.gcc.o1.k1c.o) ../clock.gcc.k1c.o 
	$(K1C_CC) $(K1C_CFLAGS_O1) $+ -o $@
xor_and_mat.ccomp.k1c: $(src:.c=.ccomp.k1c.o) ../clock.gcc.k1c.o 
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) $+ -o $@
measures.csv: $(PRODUCTS_OUT)
	echo "benches, gcc host,ccomp host,gcc k1c,gcc o1 k1c,ccomp k1c" > $@
	echo "xor_and_mat c2", $$(grep 'c2_time' xor_and_mat.gcc.host.out | cut -d':' -f2), $$(grep 'c2_time' xor_and_mat.ccomp.host.out | cut -d':' -f2), $$(grep 'c2_time' xor_and_mat.gcc.k1c.out | cut -d':' -f2), $$(grep 'c2_time' xor_and_mat.gcc.o1.k1c.out | cut -d':' -f2), $$(grep 'c2_time' xor_and_mat.ccomp.k1c.out | cut -d':' -f2)>> $@
	echo "xor_and_mat c7", $$(grep 'c7_time' xor_and_mat.gcc.host.out | cut -d':' -f2), $$(grep 'c7_time' xor_and_mat.ccomp.host.out | cut -d':' -f2), $$(grep 'c7_time' xor_and_mat.gcc.k1c.out | cut -d':' -f2), $$(grep 'c7_time' xor_and_mat.gcc.o1.k1c.out | cut -d':' -f2), $$(grep 'c7_time' xor_and_mat.ccomp.k1c.out | cut -d':' -f2)>> $@

.SECONDARY:

.PHONY:
clean:
	rm -f *.o *.s *.k1c *.csv

