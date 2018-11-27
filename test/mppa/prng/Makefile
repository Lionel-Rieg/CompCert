K1CC ?= k1-mbr-gcc
CC ?= gcc
CCOMP ?= ccomp
CFLAGS ?= -O2
SIMU ?= k1-mppa
TIMEOUT ?= 10s

K1CCPATH=$(shell which $(K1CC))
CCPATH=$(shell which $(CC))
CCOMPPATH=$(shell which $(CCOMP))
SIMUPATH=$(shell which $(SIMU))

ALL= prng-test-gcc-x86 prng-test-gcc-k1c prng-test-ccomp-k1c
CCOMP_OUT= prng-test-ccomp-k1c.out
GCC_OUT= prng-test-gcc-k1c.out
X86_GCC_OUT= prng-test-gcc-x86.out
STUB_OUT=.zero

all: $(ALL)

prng-test-gcc-x86: prng.c $(CCPATH)
	$(CC) -D__UNIT_TEST_PRNG__ $(CFLAGS) $< -o $@

prng-test-gcc-k1c: prng.c $(K1CCPATH)
	$(K1CC) -D__UNIT_TEST_PRNG__ $(CFLAGS) $< -o $@

prng-test-ccomp-k1c: prng.c $(CCOMPPATH)
	$(CCOMP) -D__UNIT_TEST_PRNG__ $(CFLAGS) $< -o $@

.SECONDARY:
%k1c.out: %k1c $(SIMUPATH)
	ret=0; timeout $(TIMEOUT) $(SIMU) -- $<  > $@ || { ret=$$?; }; echo $$ret >> $@

%x86.out: %x86
	ret=0; timeout $(TIMEOUT) ./$< > $@ || { ret=$$?; }; echo $$ret >> $@

.zero:
	@echo "0" > $@

.PHONY:
test: test-x86 test-k1c

.PHONY:
test-x86: $(X86_GCC_OUT) $(STUB_OUT)
	@if ! diff $< $(STUB_OUT); then\
		>&2 echo "ERROR x86: $< failed";\
	else\
		echo "GOOD x86: $< succeeded";\
	fi

.PHONY:
test-k1c: $(GCC_OUT) $(STUB_OUT)
	@if ! diff $< $(STUB_OUT); then\
		>&2 echo "ERROR k1c: $< failed";\
	else\
		echo "GOOD k1c: $< succeeded";\
	fi

.PHONY:
check: $(CCOMP_OUT) $(STUB_OUT)
	@if ! diff $< $(STUB_OUT); then\
		>&2 echo "ERROR k1c: $< failed";\
	else\
		echo "GOOD k1c: $< succeeded";\
	fi

.PHONY:
clean:
	rm -f prng-test-gcc-x86 prng-test-gcc-k1c prng-test-ccomp-k1c
