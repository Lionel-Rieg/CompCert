YARPGEN=yarpgen
MAX=10
PREFIX=ran%06.f
include ../rules.mk

K1C_CCOMPFLAGS += -funprototyped -fbitfields

TARGETS_C=$(shell seq --format $(PREFIX)/func.c 0 $(MAX)) \
	$(shell seq --format $(PREFIX)/driver.c 0 $(MAX)) \
	$(shell seq --format $(PREFIX)/init.h 0 $(MAX))
TARGETS_CCOMP_S=$(shell seq --format $(PREFIX)/func.ccomp.k1c.s 0 $(MAX)) \
	$(shell seq --format $(PREFIX)/driver.ccomp.k1c.s 0 $(MAX))
TARGETS_GCC_S=$(shell seq --format $(PREFIX)/func.gcc.k1c.s 0 $(MAX)) \
	$(shell seq --format $(PREFIX)/driver.gcc.k1c.s 0 $(MAX))
TARGETS_CCOMP_OUT=$(shell seq --format $(PREFIX)/example.ccomp.k1c.out 0 $(MAX))
TARGETS_GCC_OUT=$(shell seq --format $(PREFIX)/example.gcc.k1c.out 0 $(MAX))
TARGETS_GCC_HOST_OUT=$(shell seq --format $(PREFIX)/example.gcc.host.out 0 $(MAX))

all:	$(TARGETS_CCOMP_OUT) $(TARGETS_GCC_OUT) $(TARGETS_GCC_HOST_OUT)

ran%/example.ccomp.k1c: ran%/func.ccomp.k1c.o ran%/driver.ccomp.k1c.o 
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) $+ -o $@

ran%/example.gcc.k1c: ran%/func.gcc.k1c.o ran%/driver.gcc.k1c.o 
	$(K1C_CC) $(K1C_CFLAGS) $+ -o $@

ran%/example.gcc.host: ran%/func.gcc.host.o ran%/driver.gcc.host.o 
	$(CC) $(CFLAGS) $+ -o $@

ran%/driver.c ran%/func.c ran%/init.h:
	-mkdir ran$*
	$(YARPGEN) --seed=$* --out-dir=ran$*/ --std=c99

.PHONY: all clean

clean:
	-rm -rf ran*
