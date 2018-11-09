K1CC ?= k1-mbr-gcc
CC ?= gcc
CCOMP ?= ccomp
CFLAGS ?= -O2

all: prng-test-gcc-x86 prng-test-gcc-k1c prng-test-ccomp-k1c

prng-test-gcc-x86: prng.c
	$(CC) -D__UNIT_TEST_PRNG__ $(CFLAGS) $< -o $@

prng-test-gcc-k1c: prng.c
	$(K1CC) -D__UNIT_TEST_PRNG__ $(CFLAGS) $< -o $@

prng-test-ccomp-k1c: prng.c
	$(CCOMP) -D__UNIT_TEST_PRNG__ $(CFLAGS) $< -o $@

.PHONY:
test: test-x86 test-k1c

.PHONY:
test-x86: prng-test-gcc-x86
	@if ! ./$<; then\
		>&2 echo "ERROR: $< failed";\
		exit;\
	else\
		echo "$< Succeeded";\
	fi

.PHONY:
test-k1c: prng-test-gcc-k1c
	@if ! k1-cluster -- ./$<; then\
		>&2 echo "ERROR: $< failed";\
		exit;\
	else\
		echo "$< Succeeded";\
	fi

.PHONY:
check: prng-test-ccomp-k1c
	@if ! k1-cluster -- ./$<; then\
		>&2 echo "ERROR: $< failed";\
		exit;\
	else\
		echo "$< Succeeded";\
	fi

.PHONY:
clean:
	rm -f prng-test-gcc-x86 prng-test-gcc-k1c prng-test-ccomp-k1c
