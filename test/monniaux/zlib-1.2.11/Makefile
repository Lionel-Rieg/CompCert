ALL_CCOMPFLAGS = -faddx
ALL_CFLAGS = -D_POSIX_C_SOURCE=2 -D_LARGEFILE64_SOURCE=1 -U__STRICT_ANSI__

include ../rules.mk

src=$(wildcard *.c)

PRODUCTS?=minigzip.gcc.host minigzip.ccomp.host minigzip.gcc.k1c minigzip.gcc.o1.k1c minigzip.ccomp.k1c
PRODUCTS_OUT=$(addsuffix .out,$(PRODUCTS))

all: $(PRODUCTS)

.PHONY:
run: measures.csv


minigzip.gcc.host: $(src:.c=.gcc.host.o) ../clock.gcc.host.o 
	$(CC) $(CFLAGS) $+ -lm -o $@
minigzip.ccomp.host: $(src:.c=.ccomp.host.o) ../clock.gcc.host.o 
	$(CCOMP) $(CCOMPFLAGS) $+ -lm -o $@
minigzip.gcc.k1c: $(src:.c=.gcc.k1c.o) ../clock.gcc.k1c.o 
	$(K1C_CC) $(K1C_CFLAGS) $+ -lm -o $@
minigzip.gcc.o1.k1c: $(src:.c=.gcc.o1.k1c.o) ../clock.gcc.k1c.o 
	$(K1C_CC) $(K1C_CFLAGS_O1) $+ -lm -o $@
minigzip.ccomp.k1c: $(src:.c=.ccomp.k1c.o) ../clock.gcc.k1c.o 
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) $+ -lm -o $@
measures.csv: $(PRODUCTS_OUT)
	echo "benches, gcc host,ccomp host,gcc k1c,gcc o1 k1c,ccomp k1c" > $@
	echo "zlib ", $$(grep 'cycles' minigzip.gcc.host.out | cut -d':' -f2), $$(grep 'cycles' minigzip.ccomp.host.out | cut -d':' -f2), $$(grep 'cycles' minigzip.gcc.k1c.out | cut -d':' -f2), $$(grep 'cycles' minigzip.gcc.o1.k1c.out | cut -d':' -f2), $$(grep 'cycles' minigzip.ccomp.k1c.out | cut -d':' -f2)>> $@

SAMPLE_FILE=zlib.h

minigzip.gcc.host.out minigzip.gcc.host.output: minigzip.gcc.host
	./$< < $(SAMPLE_FILE) > $<.output 2> $@

minigzip.ccomp.host.out minigzip.ccomp.host.output: minigzip.ccomp.host
	./$< < $(SAMPLE_FILE) > $<.output 2> $@

minigzip.gcc.k1c.out minigzip.gcc.k1c.output: minigzip.gcc.k1c
	$(EXECUTE_CYCLES) $< < $(SAMPLE_FILE) > $<.output 2> $@

minigzip.gcc.o1.k1c.out minigzip.gcc.o1.k1c.output: minigzip.gcc.o1.k1c
	$(EXECUTE_CYCLES) $< < $(SAMPLE_FILE) > $<.output 2> $@

minigzip.ccomp.k1c.out minigzip.ccomp.k1c.output: minigzip.ccomp.k1c
	$(EXECUTE_CYCLES) $< < $(SAMPLE_FILE) > $<.output 2> $@

.SECONDARY:

.PHONY:
clean:
	rm -f *.o *.s *.k1c *.csv

