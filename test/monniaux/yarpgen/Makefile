TARGET_CCOMP=../../../ccomp

YARPGEN=yarpgen
MAX=300
PREFIX=ran%06.f

CCOMPOPTS += -funprototyped -fbitfields

TESTS_C=$(shell seq --format $(PREFIX)/func.c 0 $(MAX)) \
	$(shell seq --format $(PREFIX)/driver.c 0 $(MAX)) \
	$(shell seq --format $(PREFIX)/init.h 0 $(MAX))
TESTS_CCOMP_TARGET_S=$(shell seq --format $(PREFIX)/func.ccomp.target.s 0 $(MAX)) \
	$(shell seq --format $(PREFIX)/driver.ccomp.target.s 0 $(MAX))
TESTS_GCC_TARGET_S=$(shell seq --format $(PREFIX)/func.gcc.target.s 0 $(MAX)) \
	$(shell seq --format $(PREFIX)/driver.gcc.target.s 0 $(MAX))
TESTS_GCC_HOST_S=$(shell seq --format $(PREFIX)/func.gcc.host.s 0 $(MAX)) \
	$(shell seq --format $(PREFIX)/driver.gcc.host.s 0 $(MAX))
TESTS_CCOMP_TARGET_OUT=$(shell seq --format $(PREFIX)/example.ccomp.target.out 0 $(MAX))
TESTS_GCC_TARGET_OUT=$(shell seq --format $(PREFIX)/example.gcc.target.out 0 $(MAX))
TESTS_GCC_HOST_OUT=$(shell seq --format $(PREFIX)/example.gcc.host.out 0 $(MAX))
TESTS_CMP=$(shell seq --format $(PREFIX)/example.target.cmp 0 $(MAX))

all:	$(TESTS_CCOMP_TARGET_OUT) $(TESTS_GCC_TARGET_OUT) $(TESTS_GCC_HOST_OUT) $(TESTS_CCOMP_TARGET_S) $(TESTS_GCC_TARGET_S) $(TESTS_GCC_HOST_S) $(TESTS_CMP) $(TESTS_C)

tests_c: $(TESTS_C)

%.ccomp.target.s : %.c
	$(TARGET_CCOMP) $(CCOMPOPTS) -S -o $@ $<

%.gcc.target.s : %.c
	$(TARGET_CC) $(CCOMPOPTS) -S -o $@ $<

%.gcc.host.s : %.c
	$(CC) $(CFLAGS) -S -o $@ $<

%.target.o : %.target.s
	$(TARGET_CCOMP) $(CCOMPOPTS) -c -o $@ $<

%.target.out : %.target
	$(EXECUTE) $< > $@

%.host.out : %.host
	./$< > $@

ran%/func.ccomp.target.s ran%/func.gcc.target.s ran%/func.ccomp.host.s ran%/func.gcc.host.s : ran%/init.h

ran%/example.ccomp.target: ran%/func.ccomp.target.o ran%/driver.ccomp.target.o 
	$(TARGET_CCOMP) $(CCOMPOPTS) $+ -o $@

ran%/example.gcc.target: ran%/func.gcc.target.o ran%/driver.gcc.target.o 
	$(TARGET_CC) $(TARGET_CFLAGS) $+ -o $@

ran%/example.gcc.host: ran%/func.gcc.host.o ran%/driver.gcc.host.o 
	$(CC) $(CFLAGS) $+ -o $@

ran%/example.ccomp.host: ran%/func.ccomp.host.o ran%/driver.ccomp.host.o 
	$(CCOMP) $(CCOMPFLAGS) $+ -o $@

ran%/driver.c ran%/func.c ran%/init.h:
	-mkdir ran$*
	$(YARPGEN) --seed=$* --out-dir=ran$*/ --std=c99

ran%/example.target.cmp : ran%/example.gcc.target.out ran%/example.ccomp.target.out
	cmp $+ > $@

.PHONY: all clean tests_c

clean:
	-rm -rf ran*
