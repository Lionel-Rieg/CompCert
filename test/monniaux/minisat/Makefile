
include ../rules.mk

EXECUTE_ARGS=sudoku.sat

src=main.c solver.c

PRODUCTS?=minisat.gcc.host minisat.ccomp.host minisat.gcc.k1c minisat.gcc.o1.k1c minisat.ccomp.k1c
PRODUCTS_OUT=$(addsuffix .out,$(PRODUCTS))

all: $(PRODUCTS)

.PHONY:
run: measures.csv

LIBS=-lm

minisat.gcc.host: $(src:.c=.gcc.host.o) ../clock.gcc.host.o 
	$(CC) $(CFLAGS) $+ $(LIBS) -o $@
minisat.ccomp.host: $(src:.c=.ccomp.host.o) ../clock.gcc.host.o 
	$(CCOMP) $(CCOMPFLAGS) $+ $(LIBS) -o $@
minisat.gcc.k1c: $(src:.c=.gcc.k1c.o) ../clock.gcc.k1c.o 
	$(K1C_CC) $(K1C_CFLAGS) $+ $(LIBS) -o $@
minisat.gcc.o1.k1c: $(src:.c=.gcc.o1.k1c.o) ../clock.gcc.k1c.o 
	$(K1C_CC) $(K1C_CFLAGS_O1) $+ $(LIBS) -o $@
minisat.ccomp.k1c: $(src:.c=.ccomp.k1c.o) ../clock.gcc.k1c.o 
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) $+ $(LIBS) -o $@
measures.csv: $(PRODUCTS_OUT)
	echo "benches, gcc host,ccomp host,gcc k1c,gcc o1 k1c,ccomp k1c" > $@

.SECONDARY:

.PHONY:
clean:
	rm -f *.o *.s *.k1c *.csv

