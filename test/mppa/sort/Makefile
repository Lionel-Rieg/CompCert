K1CC ?= k1-mbr-gcc
CC ?= gcc
CCOMP ?= ccomp
CFLAGS ?= -O2

PRNG=../prng/prng.c

CFILES=insertion.c merge.c selection.c main.c

ALL= insertion-test-gcc-x86 insertion-test-gcc-k1c\
     selection-test-gcc-x86 selection-test-gcc-k1c\
     merge-test-gcc-x86     merge-test-gcc-k1c\
     main-test-gcc-x86           main-test-gcc-k1c\
     main-test-ccomp-k1c

all: $(ALL)

main-test-gcc-x86: $(CFILES) $(PRNG)
	$(CC) $(CFLAGS) $^ -o $@

%-test-gcc-x86: %.c $(PRNG)
	$(CC) -D__UNIT_TEST_$$(echo $(basename $<) | tr a-z A-Z)__ $(CFLAGS) $^ -o $@

main-test-gcc-k1c: $(CFILES) $(PRNG)
	$(K1CC) $(CFLAGS) $^ -o $@

%-test-gcc-k1c: %.c $(PRNG)
	$(K1CC) -D__UNIT_TEST_$$(echo $(basename $<) | tr a-z A-Z)__ $(CFLAGS) $^ -o $@

main-test-ccomp-k1c: $(CFILES) $(PRNG)
	$(CCOMP) $(CFLAGS) $^ -o $@

%-test-ccomp-k1c: %.c $(PRNG)
	$(CCOMP) -D__UNIT_TEST_$$(echo $(basename $<) | tr a-z A-Z)__ $(CFLAGS) $^ -o $@

.PHONY:
test-x86: insertion-test-gcc-x86 selection-test-gcc-x86 merge-test-gcc-x86 main-test-gcc-x86
	@for test in $^; do\
		if ! ./$$test; then\
			>&2 echo "ERROR x86: $$test failed";\
		else\
			echo "x86: Test $$test Succeeded";\
		fi;\
	done

.PHONY:
test-k1c: insertion-test-gcc-k1c selection-test-gcc-k1c merge-test-gcc-k1c main-test-gcc-k1c
	@for test in $^; do\
		if ! k1-cluster -- ./$$test; then\
			>&2 echo "ERROR k1c: $$test failed";\
		else\
			echo "k1c: Test $$test Succeeded";\
		fi;\
	done

.PHONY:
test: test-x86 test-k1c

.PHONY:
check: main-test-ccomp-k1c
	@if ! k1-cluster -- ./$<; then\
		>&2 echo "ERROR k1c: sort $< failed";\
	else\
		echo "k1c: Test sort $< succeeded";\
	fi

.PHONY:
clean:
	rm -f $(ALL)
