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

CFILES=insertion.c merge.c selection.c main.c

ALL= insertion-gcc-x86 insertion-gcc-kvx insertion-ccomp-kvx\
     selection-gcc-x86 selection-gcc-kvx selection-ccomp-kvx\
     merge-gcc-x86 merge-gcc-kvx merge-ccomp-kvx\
     main-gcc-x86 main-gcc-kvx main-ccomp-kvx

CCOMP_OUT= insertion-ccomp-kvx.out selection-ccomp-kvx.out merge-ccomp-kvx.out\
		   main-ccomp-kvx.out
GCC_OUT= insertion-gcc-kvx.out selection-gcc-kvx.out merge-gcc-kvx.out\
		   main-gcc-kvx.out
X86_GCC_OUT= insertion-gcc-x86.out selection-gcc-x86.out merge-gcc-x86.out\
		   main-gcc-x86.out
STUB_OUT= .zero

all: $(ALL)

main-gcc-x86: $(CFILES) $(PRNG) $(CCPATH)
	$(CC) $(CFLAGS) $(filter-out $(CCPATH),$^) -o $@

%-gcc-x86: %.c $(PRNG) $(CCPATH)
	$(CC) -D__UNIT_TEST_$$(echo $(basename $<) | tr a-z A-Z)__ $(CFLAGS) $(filter-out $(CCPATH),$^) -o $@

main-gcc-kvx: $(CFILES) $(PRNG) $(CCPATH)
	$(KVXC) $(CFLAGS) $(filter-out $(CCPATH),$^) -o $@

%-gcc-kvx: %.c $(PRNG) $(KVXCPATH)
	$(KVXC) -D__UNIT_TEST_$$(echo $(basename $<) | tr a-z A-Z)__ $(CFLAGS) $(filter-out $(KVXCPATH),$^) -o $@

main-ccomp-kvx: $(CFILES) $(PRNG) $(CCOMPPATH)
	$(CCOMP) $(CFLAGS) $(filter-out $(CCOMPPATH),$^) -o $@

%-ccomp-kvx: %.c $(PRNG) $(CCOMPPATH)
	$(CCOMP) -D__UNIT_TEST_$$(echo $(basename $<) | tr a-z A-Z)__ $(CFLAGS) $(filter-out $(CCOMPPATH),$^) -o $@

.SECONDARY:
%x86.out: %x86
	ret=0; timeout $(TIMEOUT) ./$< > $@ || { ret=$$?; }; echo $$ret >> $@

%kvx.out: %kvx $(SIMUPATH)
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
test-kvx: $(STUB_OUT) $(GCC_OUT)
	@for test in $(wordlist 2,100,$^); do\
		if ! diff $$test $(STUB_OUT); then\
			>&2 echo "ERROR kvx: $$test failed";\
		else\
			echo "GOOD kvx: $$test succeeded";\
		fi;\
	done

.PHONY:
test: test-x86 test-kvx

.PHONY:
check: $(STUB_OUT) $(CCOMP_OUT)
	@for test in $(wordlist 2,100,$^); do\
		if ! diff $$test $(STUB_OUT); then\
			>&2 echo "ERROR kvx: $$test failed";\
		else\
			echo "GOOD kvx: $$test succeeded";\
		fi;\
	done
