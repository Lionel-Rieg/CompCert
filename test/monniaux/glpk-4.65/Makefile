ALL_CFLAGS += -I src/amd -I src/colamd -I src/mpl -I src/simplex -I src/api -I src/intopt -I src/minisat -I src/npp -I src/zlib -I src/bflib -I src/env -I src/misc -I src/draft -I src

include ../rules.mk

LIBS = -lm

src=examples/glpsol.c $(wildcard src/*/*.c)

PRODUCTS?=glpsol.gcc.host glpsol.ccomp.host glpsol.gcc.k1c glpsol.gcc.o1.k1c glpsol.ccomp.k1c
PRODUCTS_OUT=$(addsuffix .out,$(PRODUCTS))

all: $(PRODUCTS)

.PHONY:
run: measures.csv


glpsol.gcc.host: $(src:.c=.gcc.host.o) ../clock.gcc.host.o 
	$(CC) $(CFLAGS) $+ $(LIBS) -o $@
glpsol.ccomp.host: $(src:.c=.ccomp.host.o) ../clock.gcc.host.o 
	$(CCOMP) $(CCOMPFLAGS) $+ $(LIBS) -o $@
glpsol.gcc.k1c: $(src:.c=.gcc.k1c.o) ../clock.gcc.k1c.o 
	$(K1C_CC) $(K1C_CFLAGS) $+  $(LIBS) -o $@
glpsol.gcc.o1.k1c: $(src:.c=.gcc.o1.k1c.o) ../clock.gcc.k1c.o 
	$(K1C_CC) $(K1C_CFLAGS_O1) $+  $(LIBS) -o $@
glpsol.ccomp.k1c: $(src:.c=.ccomp.k1c.o) ../clock.gcc.k1c.o 
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) $+  $(LIBS) -o $@
measures.csv: $(PRODUCTS_OUT)
	echo "benches, gcc host,ccomp host,gcc k1c,gcc o1 k1c,ccomp k1c" > $@

.SECONDARY:

.PHONY:
clean:
	rm -f *.o *.s *.k1c *.csv

