
include ../rules.mk

EXECUTE_ARGS=sudoku.sat

src=main.c solver.c

PRODUCTS?=minisat.gcc.host minisat.ccomp.host minisat.gcc.kvx minisat.gcc.o1.kvx minisat.ccomp.kvx
PRODUCTS_OUT=$(addsuffix .out,$(PRODUCTS))

all: $(PRODUCTS)

.PHONY:
run: measures.csv

LIBS=-lm

minisat.gcc.host: $(src:.c=.gcc.host.o) ../clock.gcc.host.o 
	$(CC) $(CFLAGS) $+ $(LIBS) -o $@
minisat.ccomp.host: $(src:.c=.ccomp.host.o) ../clock.gcc.host.o 
	$(CCOMP) $(CCOMPFLAGS) $+ $(LIBS) -o $@
minisat.gcc.kvx: $(src:.c=.gcc.kvx.o) ../clock.gcc.kvx.o 
	$(KVX_CC) $(KVX_CFLAGS) $+ $(LIBS) -o $@
minisat.gcc.o1.kvx: $(src:.c=.gcc.o1.kvx.o) ../clock.gcc.kvx.o 
	$(KVX_CC) $(KVX_CFLAGS_O1) $+ $(LIBS) -o $@
minisat.ccomp.kvx: $(src:.c=.ccomp.kvx.o) ../clock.gcc.kvx.o 
	$(KVX_CCOMP) $(KVX_CCOMPFLAGS) $+ $(LIBS) -o $@
measures.csv: $(PRODUCTS_OUT)
	echo "benches, gcc host,ccomp host,gcc kvx,gcc o1 kvx,ccomp kvx" > $@

.SECONDARY:

.PHONY:
clean:
	rm -f *.o *.s *.kvx *.csv

