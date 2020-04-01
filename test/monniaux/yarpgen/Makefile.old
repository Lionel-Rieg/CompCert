YARPGEN=yarpgen
MAX=300
PREFIX=ran%06.f
include ../rules.mk

K1C_CCOMPFLAGS += -funprototyped -fbitfields
CCOMPFLAGS += -funprototyped -fbitfields

TARGETS_C=$(shell seq --format $(PREFIX)/func.c 0 $(MAX)) \
	$(shell seq --format $(PREFIX)/driver.c 0 $(MAX)) \
	$(shell seq --format $(PREFIX)/init.h 0 $(MAX))
TARGETS_CCOMP_K1C_S=$(shell seq --format $(PREFIX)/func.ccomp.k1c.s 0 $(MAX)) \
	$(shell seq --format $(PREFIX)/driver.ccomp.k1c.s 0 $(MAX))
TARGETS_GCC_K1C_S=$(shell seq --format $(PREFIX)/func.gcc.k1c.s 0 $(MAX)) \
	$(shell seq --format $(PREFIX)/driver.gcc.k1c.s 0 $(MAX))
TARGETS_CCOMP_HOST_S=$(shell seq --format $(PREFIX)/func.ccomp.host.s 0 $(MAX)) \
	$(shell seq --format $(PREFIX)/driver.ccomp.host.s 0 $(MAX))
TARGETS_GCC_HOST_S=$(shell seq --format $(PREFIX)/func.gcc.host.s 0 $(MAX)) \
	$(shell seq --format $(PREFIX)/driver.gcc.host.s 0 $(MAX))
TARGETS_CCOMP_K1C_OUT=$(shell seq --format $(PREFIX)/example.ccomp.k1c.out 0 $(MAX))
TARGETS_GCC_K1C_OUT=$(shell seq --format $(PREFIX)/example.gcc.k1c.out 0 $(MAX))
TARGETS_GCC_HOST_OUT=$(shell seq --format $(PREFIX)/example.gcc.host.out 0 $(MAX))
TARGETS_CCOMP_HOST_OUT=$(shell seq --format $(PREFIX)/example.ccomp.host.out 0 $(MAX))
TARGETS_CMP=$(shell seq --format $(PREFIX)/example.k1c.cmp 0 $(MAX))

all:	$(TARGETS_CCOMP_K1C_OUT) $(TARGETS_GCC_K1C_OUT) $(TARGETS_GCC_HOST_OUT) $(TARGETS_CCOMP_HOST_OUT) $(TARGETS_CCOMP_K1C_S) $(TARGETS_GCC_K1C_S) $(TARGETS_GCC_HOST_S) $(TARGETS_CCOMP_HOST_S) $(TARGETS_CMP) $(TARGETS_C)

ran%/func.ccomp.k1c.s ran%/func.gcc.k1c.s ran%/func.ccomp.host.s ran%/func.gcc.host.s : ran%/init.h

ran%/example.ccomp.k1c: ran%/func.ccomp.k1c.o ran%/driver.ccomp.k1c.o 
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) $+ -o $@

ran%/example.gcc.k1c: ran%/func.gcc.k1c.o ran%/driver.gcc.k1c.o 
	$(K1C_CC) $(K1C_CFLAGS) $+ -o $@

ran%/example.gcc.host: ran%/func.gcc.host.o ran%/driver.gcc.host.o 
	$(CC) $(CFLAGS) $+ -o $@

ran%/example.ccomp.host: ran%/func.ccomp.host.o ran%/driver.ccomp.host.o 
	$(CCOMP) $(CCOMPFLAGS) $+ -o $@

ran%/driver.c ran%/func.c ran%/init.h:
	-mkdir ran$*
	$(YARPGEN) --seed=$* --out-dir=ran$*/ --std=c99

ran%/example.k1c.cmp : ran%/example.gcc.k1c.out ran%/example.ccomp.k1c.out
	cmp $+ > $@

.PHONY: all clean

clean:
	-rm -rf ran*
