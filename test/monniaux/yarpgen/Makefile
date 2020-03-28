TARGET_CCOMP=../../../ccomp
TARGET_CC=gcc

all:

ifndef YARPGEN
YARPGEN=./yarpgen
GENERATOR=yarpgen
endif

MAX=170
PREFIX=ran%06.f

CCOMPOPTS=-static
CCOMPFLAGS+=-funprototyped -fbitfields -fno-cse2 -stdlib ../../../runtime # FIXME

TESTS_C=$(shell seq --format $(PREFIX)/func.c 1 $(MAX)) \
	$(shell seq --format $(PREFIX)/driver.c 1 $(MAX)) \
	$(shell seq --format $(PREFIX)/init.c 1 $(MAX)) \
	$(shell seq --format $(PREFIX)/init.h 1 $(MAX))

$(TESTS_C): $(GENERATOR)

TESTS_CCOMP_TARGET_S=$(shell seq --format $(PREFIX)/func.ccomp.target.s 1 $(MAX)) \
	$(shell seq --format $(PREFIX)/driver.ccomp.target.s 1 $(MAX))
TESTS_GCC_TARGET_S=$(shell seq --format $(PREFIX)/func.gcc.target.s 1 $(MAX)) \
	$(shell seq --format $(PREFIX)/driver.gcc.target.s 1 $(MAX))
TESTS_GCC_HOST_S=$(shell seq --format $(PREFIX)/func.gcc.host.s 1 $(MAX)) \
	$(shell seq --format $(PREFIX)/driver.gcc.host.s 1 $(MAX))
TESTS_CCOMP_TARGET_OUT=$(shell seq --format $(PREFIX)/example.ccomp.target.out 1 $(MAX))
TESTS_GCC_TARGET_OUT=$(shell seq --format $(PREFIX)/example.gcc.target.out 1 $(MAX))
TESTS_GCC_HOST_OUT=$(shell seq --format $(PREFIX)/example.gcc.host.out 1 $(MAX))
TESTS_CMP=$(shell seq --format $(PREFIX)/example.host_target.cmp 1 $(MAX)) $(shell seq --format $(PREFIX)/example.target.cmp 1 $(MAX))

all:	$(TESTS_CCOMP_TARGET_OUT) $(TESTS_GCC_TARGET_OUT) $(TESTS_GCC_HOST_OUT) $(TESTS_CCOMP_TARGET_S) $(TESTS_GCC_TARGET_S) $(TESTS_GCC_HOST_S) $(TESTS_CMP) $(TESTS_C)

tests_c: $(TESTS_C)

tests_s: $(TESTS_CCOMP_TARGET_S)

%.ccomp.target.s : %.c
	$(TARGET_CCOMP) $(CCOMPOPTS) $(CCOMPFLAGS) -S -o $@ $<

%.gcc.target.s : %.c
	$(TARGET_CC) $(CCOMPOPTS) -S -o $@ $<

%.gcc.host.s : %.c
	$(CC) $(CFLAGS) -S -o $@ $<

%.target.o : %.target.s
	$(TARGET_CCOMP) $(CCOMPOPTS) $(CCOMPFLAGS) -c -o $@ $<

%.target.out : %.target
	$(EXECUTE) $< > $@

%.host.out : %.host
	./$< > $@

ran%/func.ccomp.target.s ran%/func.gcc.target.s ran%/func.ccomp.host.s ran%/func.gcc.host.s : ran%/init.h

ran%/example.ccomp.target: ran%/func.ccomp.target.o ran%/driver.ccomp.target.o  ran%/init.ccomp.target.o ran%/check.ccomp.target.o ran%/hash.ccomp.target.o
	$(TARGET_CCOMP) $(CCOMPOPTS) $(CCOMPFLAGS) $+ -o $@

ran%/example.gcc.target: ran%/func.gcc.target.o ran%/driver.gcc.target.o ran%/init.ccomp.target.o ran%/check.gcc.target.o ran%/hash.gcc.target.o
	$(TARGET_CC) $(TARGET_CFLAGS) $+ -o $@

ran%/example.gcc.host: ran%/func.gcc.host.o ran%/driver.gcc.host.o ran%/init.gcc.host.o ran%/check.gcc.host.o ran%/hash.gcc.host.o
	$(CC) $(CFLAGS) $+ -o $@

ran%/driver.c ran%/func.c ran%/init.c ran%/check.c ran%/hash.c ran%/init.h:
	mkdir -p ran$*
	$(YARPGEN) --seed=$* --out-dir=ran$*/ --std=c99

ran%/example.target.cmp : ran%/example.gcc.target.out ran%/example.ccomp.target.out
	cmp $+ > $@

ran%/example.host_target.cmp : ran%/example.gcc.host.out ran%/example.ccomp.target.out
	cmp $+ > $@

yarpgen:
	curl -L -o yarpgen_v1.1.tar.gz https://github.com/intel/yarpgen/archive/v1.1.tar.gz
	tar xfz yarpgen_v1.1.tar.gz
	$(MAKE) CXX=g++ -C yarpgen-1.1
	cp yarpgen-1.1/yarpgen $@

.PHONY: all clean tests_c tests_c
.SECONDARY: .s .target .out

clean:
	-rm -rf ran*
