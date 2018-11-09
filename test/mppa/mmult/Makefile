K1CC ?= k1-mbr-gcc
CC ?= gcc
CCOMP ?= ccomp
CFLAGS ?= -O2

PRNG=../prng/prng.c

ALL= mmult-test-gcc-x86 mmult-test-gcc-k1c mmult-test-ccomp-k1c\

all: $(ALL)

mmult-test-gcc-x86: mmult.c $(PRNG)
	$(CC) $(CFLAGS) $^ -o $@

mmult-test-gcc-k1c: mmult.c $(PRNG)
	$(K1CC) $(CFLAGS) $^ -o $@

mmult-test-ccomp-k1c: mmult.c $(PRNG)
	$(CCOMP) $(CFLAGS) $^ -o $@

.PHONY:
test: test-x86 test-k1c

.PHONY:
test-x86: mmult-test-gcc-x86
	@if ! ./$<; then\
		>&2 echo "ERROR x86: $< failed";\
	else\
		echo "x86: Test $< succeeded";\
	fi

.PHONY:
test-k1c: mmult-test-gcc-k1c
	@if ! k1-cluster -- ./$<; then\
		>&2 echo "ERROR k1c: $< failed";\
	else\
		echo "k1c: Test $< succeeded";\
	fi

.PHONY:
check: mmult-test-ccomp-k1c
	@if ! k1-cluster -- ./$<; then\
		>&2 echo "ERROR k1c: mmult $< failed";\
	else\
		echo "k1c: Test mmult $< succeeded";\
	fi

.PHONY:
clean:
	rm -f $(ALL)
