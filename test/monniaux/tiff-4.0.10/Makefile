ALL_CCOMPFLAGS = -flongdouble

include ../rules.mk

LIBS=-lm

src=$(wildcard *.c)

PRODUCTS?=ppm2tiff.gcc.host ppm2tiff.ccomp.host ppm2tiff.gcc.k1c ppm2tiff.gcc.o1.k1c ppm2tiff.ccomp.k1c
PRODUCTS_OUT=$(addsuffix .out,$(PRODUCTS))

all: $(PRODUCTS)

.PHONY:
run: measures.csv

ppm2tiff.gcc.host: $(src:.c=.gcc.host.o) ../clock.gcc.host.o 
	$(CC) $(CFLAGS) $+ $(LIBS) -o $@
ppm2tiff.ccomp.host: $(src:.c=.ccomp.host.o) ../clock.gcc.host.o 
	$(CCOMP) $(CCOMPFLAGS) $+ $(LIBS) -o $@
ppm2tiff.gcc.k1c: $(src:.c=.gcc.k1c.o) ../clock.gcc.k1c.o 
	$(K1C_CC) $(K1C_CFLAGS) $+ $(LIBS) -o $@
ppm2tiff.gcc.o1.k1c: $(src:.c=.gcc.o1.k1c.o) ../clock.gcc.k1c.o 
	$(K1C_CC) $(K1C_CFLAGS_O1) $+ $(LIBS) -o $@
ppm2tiff.ccomp.k1c: $(src:.c=.ccomp.k1c.o) ../clock.gcc.k1c.o 
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) $+ $(LIBS) -o $@

ppm2tiff.gcc.host.out: ppm2tiff.gcc.host
	bunzip2 < example_bw.pbm.bz2 | ./$< -c g3 $<.g3.tif | tee $@

ppm2tiff.ccomp.host.out: ppm2tiff.ccomp.host
	bunzip2 < example_bw.pbm.bz2 | ./$< -c g3 $<.g3.tif | tee $@

ppm2tiff.gcc.k1c.out: ppm2tiff.gcc.k1c
	bunzip2 < example_bw.pbm.bz2 | $(EXECUTE_CYCLES) ./$< -c g3 $<.g3.tif | tee $@

ppm2tiff.gcc.o1.k1c.out: ppm2tiff.gcc.o1.k1c
	bunzip2 < example_bw.pbm.bz2 | $(EXECUTE_CYCLES) ./$< -c g3 $<.g3.tif | tee $@

ppm2tiff.ccomp.k1c.out: ppm2tiff.ccomp.k1c
	bunzip2 < example_bw.pbm.bz2 | $(EXECUTE_CYCLES) ./$< -c g3 $<.g3.tif | tee $@

measures.csv: $(PRODUCTS_OUT)
	echo "benches, gcc host,ccomp host,gcc k1c,gcc o1 k1c,ccomp k1c" > $@
	echo "ppm2tiff ", $$(grep 'cycles' ppm2tiff.gcc.host.out | cut -d':' -f2), $$(grep 'cycles' ppm2tiff.ccomp.host.out | cut -d':' -f2), $$(grep 'cycles' ppm2tiff.gcc.k1c.out | cut -d':' -f2), $$(grep 'cycles' ppm2tiff.gcc.o1.k1c.out | cut -d':' -f2), $$(grep 'cycles' ppm2tiff.ccomp.k1c.out | cut -d':' -f2)>> $@

.SECONDARY:

.PHONY:
clean:
	rm -f *.o *.s *.k1c *.csv

