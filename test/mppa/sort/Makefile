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

PRNG=../prng/prng.c

CFILES=insertion.c merge.c selection.c main.c

ALL= insertion-gcc-x86 insertion-gcc-k1c insertion-ccomp-k1c\
     selection-gcc-x86 selection-gcc-k1c selection-ccomp-k1c\
     merge-gcc-x86 merge-gcc-k1c merge-ccomp-k1c\
     main-gcc-x86 main-gcc-k1c main-ccomp-k1c

CCOMP_OUT= insertion-ccomp-k1c.out selection-ccomp-k1c.out merge-ccomp-k1c.out\
		   main-ccomp-k1c.out
GCC_OUT= insertion-gcc-k1c.out selection-gcc-k1c.out merge-gcc-k1c.out\
		   main-gcc-k1c.out
X86_GCC_OUT= insertion-gcc-x86.out selection-gcc-x86.out merge-gcc-x86.out\
		   main-gcc-x86.out
STUB_OUT= .zero

all: $(ALL)

main-gcc-x86: $(CFILES) $(PRNG) $(CCPATH)
	$(CC) $(CFLAGS) $(filter-out $(CCPATH),$^) -o $@

%-gcc-x86: %.c $(PRNG) $(CCPATH)
	$(CC) -D__UNIT_TEST_$$(echo $(basename $<) | tr a-z A-Z)__ $(CFLAGS) $(filter-out $(CCPATH),$^) -o $@

main-gcc-k1c: $(CFILES) $(PRNG) $(CCPATH)
	$(K1CC) $(CFLAGS) $(filter-out $(CCPATH),$^) -o $@

%-gcc-k1c: %.c $(PRNG) $(K1CCPATH)
	$(K1CC) -D__UNIT_TEST_$$(echo $(basename $<) | tr a-z A-Z)__ $(CFLAGS) $(filter-out $(K1CCPATH),$^) -o $@

main-ccomp-k1c: $(CFILES) $(PRNG) $(CCOMPPATH)
	$(CCOMP) $(CFLAGS) $(filter-out $(CCOMPPATH),$^) -o $@

%-ccomp-k1c: %.c $(PRNG) $(CCOMPPATH)
	$(CCOMP) -D__UNIT_TEST_$$(echo $(basename $<) | tr a-z A-Z)__ $(CFLAGS) $(filter-out $(CCOMPPATH),$^) -o $@

.SECONDARY:
%x86.out: %x86
	ret=0; timeout $(TIMEOUT) ./$< > $@ || { ret=$$?; }; echo $$ret >> $@

%k1c.out: %k1c $(SIMUPATH)
	ret=0; timeout $(TIMEOUT) $(SIMU) -- $< > $@ || { ret=$$?; }; echo $$ret >> $@

.zero:
	@echo "0" > $@

.PHONY:
test-x86: $(STUB_OUT) $(X86_GCC_OUT)
	@for test in $(wordlist 2,100,$^); do\
		if ! diff $$test $(STUB_OUT); then\
			>&2 echo "ERROR x86: $$test failed";\
		else\
			echo "GOOD x86: $$test succeeded";\
		fi;\
	done

.PHONY:
test-k1c: $(STUB_OUT) $(GCC_OUT)
	@for test in $(wordlist 2,100,$^); do\
		if ! diff $$test $(STUB_OUT); then\
			>&2 echo "ERROR k1c: $$test failed";\
		else\
			echo "GOOD k1c: $$test succeeded";\
		fi;\
	done

.PHONY:
test: test-x86 test-k1c

.PHONY:
check: $(STUB_OUT) $(CCOMP_OUT)
	@for test in $(wordlist 2,100,$^); do\
		if ! diff $$test $(STUB_OUT); then\
			>&2 echo "ERROR k1c: $$test failed";\
		else\
			echo "GOOD k1c: $$test succeeded";\
		fi;\
	done
