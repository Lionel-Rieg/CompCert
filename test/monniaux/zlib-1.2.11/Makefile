TARGET=zlib

ALL_CCOMPFLAGS=-faddx
ALL_CFLAGS=  -D_POSIX_C_SOURCE=2 -D_LARGEFILE64_SOURCE=1 -U__STRICT_ANSI__
EXECUTE_ARGS=< zlib_small.txt > /dev/null 2> __BASE__.out

include ../rules.mk


#ALL_CCOMPFLAGS = -faddx
#ALL_CFLAGS = -D_POSIX_C_SOURCE=2 -D_LARGEFILE64_SOURCE=1 -U__STRICT_ANSI__
#
#include ../rules.mk
#
#src=$(wildcard *.c)
#
#PRODUCTS?=minigzip.gcc.host minigzip.ccomp.host minigzip.gcc.kvx minigzip.gcc.o1.kvx minigzip.ccomp.kvx
#PRODUCTS_OUT=$(addsuffix .out,$(PRODUCTS))
#
#all: $(PRODUCTS)
#
#.PHONY:
#run: measures.csv
#
#
#minigzip.gcc.host: $(src:.c=.gcc.host.o) ../clock.gcc.host.o 
#	$(CC) $(CFLAGS) $+ -lm -o $@
#minigzip.ccomp.host: $(src:.c=.ccomp.host.o) ../clock.gcc.host.o 
#	$(CCOMP) $(CCOMPFLAGS) $+ -lm -o $@
#minigzip.gcc.kvx: $(src:.c=.gcc.kvx.o) ../clock.gcc.kvx.o 
#	$(KVX_CC) $(KVX_CFLAGS) $+ -lm -o $@
#minigzip.gcc.o1.kvx: $(src:.c=.gcc.o1.kvx.o) ../clock.gcc.kvx.o 
#	$(KVX_CC) $(KVX_CFLAGS_O1) $+ -lm -o $@
#minigzip.ccomp.kvx: $(src:.c=.ccomp.kvx.o) ../clock.gcc.kvx.o 
#	$(KVX_CCOMP) $(KVX_CCOMPFLAGS) $+ -lm -o $@
#measures.csv: $(PRODUCTS_OUT)
#	echo "benches, gcc host,ccomp host,gcc kvx,gcc o1 kvx,ccomp kvx" > $@
#	echo "zlib ", $$(grep 'cycles' minigzip.gcc.host.out | cut -d':' -f2), $$(grep 'cycles' minigzip.ccomp.host.out | cut -d':' -f2), $$(grep 'cycles' minigzip.gcc.kvx.out | cut -d':' -f2), $$(grep 'cycles' minigzip.gcc.o1.kvx.out | cut -d':' -f2), $$(grep 'cycles' minigzip.ccomp.kvx.out | cut -d':' -f2)>> $@
#
#SAMPLE_FILE=zlib.h
#
#minigzip.gcc.host.out minigzip.gcc.host.output: minigzip.gcc.host
#	./$< < $(SAMPLE_FILE) > $<.output 2> $@
#
#minigzip.ccomp.host.out minigzip.ccomp.host.output: minigzip.ccomp.host
#	./$< < $(SAMPLE_FILE) > $<.output 2> $@
#
#minigzip.gcc.kvx.out minigzip.gcc.kvx.output: minigzip.gcc.kvx
#	$(EXECUTE_CYCLES) $< < $(SAMPLE_FILE) > $<.output 2> $@
#
#minigzip.gcc.o1.kvx.out minigzip.gcc.o1.kvx.output: minigzip.gcc.o1.kvx
#	$(EXECUTE_CYCLES) $< < $(SAMPLE_FILE) > $<.output 2> $@
#
#minigzip.ccomp.kvx.out minigzip.ccomp.kvx.output: minigzip.ccomp.kvx
#	$(EXECUTE_CYCLES) $< < $(SAMPLE_FILE) > $<.output 2> $@
#
#.SECONDARY:
#
#.PHONY:
#clean:
#	rm -f *.o *.s *.kvx *.csv
#
