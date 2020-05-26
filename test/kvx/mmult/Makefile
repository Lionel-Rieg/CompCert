KVXC ?= k1-cos-gcc
CC ?= gcc
CCOMP ?= ccomp
CFLAGS ?= -O2
SIMU ?= k1-mppa
TIMEOUT ?= 10s

KVXCPATH=$(shell which $(KVXC))
CCPATH=$(shell which $(CC))
CCOMPPATH=$(shell which $(CCOMP))
SIMUPATH=$(shell which $(SIMU))

PRNG=../prng/prng.c

ALL= mmult-test-gcc-x86 mmult-test-gcc-kvx mmult-test-ccomp-kvx
CCOMP_OUT= mmult-test-ccomp-kvx.out
GCC_OUT= mmult-test-gcc-kvx.out
X86_GCC_OUT= mmult-test-gcc-x86.out
STUB_OUT=.zero

all: $(ALL)

mmult-test-gcc-x86: mmult.c $(PRNG) $(CCPATH)
	$(CC) $(CFLAGS) $(filter-out $(CCPATH),$^) -o $@

mmult-test-gcc-kvx: mmult.c $(PRNG) $(KVXCPATH)
	$(KVXC) $(CFLAGS) $(filter-out $(KVXCPATH),$^) -o $@

mmult-test-ccomp-kvx: mmult.c $(PRNG) $(CCOMPPATH)
	$(CCOMP) $(CFLAGS) $(filter-out $(CCOMPPATH),$^) -o $@

.SECONDARY:
%kvx.out: %kvx $(SIMUPATH)
	ret=0; timeout $(TIMEOUT) $(SIMU) -- $< > $@ || { ret=$$?; }; echo $$ret >> $@

%x86.out: %x86
	ret=0; timeout $(TIMEOUT) ./$< > $@ || { ret=$$?; }; echo $$ret >> $@

.zero:
	@echo "0" > $@

.PHONY:
test: test-x86 test-kvx

.PHONY:
test-x86: $(X86_GCC_OUT) $(STUB_OUT)
	@if ! diff $< $(STUB_OUT); then\
		>&2 echo "ERROR x86: $< failed";\
	else\
		echo "GOOD x86: $< succeeded";\
	fi

.PHONY:
test-kvx: $(GCC_OUT) $(STUB_OUT)
	@if ! diff $< $(STUB_OUT); then\
		>&2 echo "ERROR kvx: $< failed";\
	else\
		echo "GOOD kvx: $< succeeded";\
	fi

.PHONY:
check: $(CCOMP_OUT) $(STUB_OUT)
	@if ! diff $< $(STUB_OUT); then\
		>&2 echo "ERROR kvx: $< failed";\
	else\
		echo "GOOD kvx: $< succeeded";\
	fi
