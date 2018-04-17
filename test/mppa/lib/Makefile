prng-test-x86: prng.c
	gcc -D__UNIT_TEST__ -O2 -std=c99 $< -o $@

prng-test-k1c: prng.c
	k1-gcc -D__UNIT_TEST__ -O2 -std=c99 $< -o $@

.PHONY:
test: test-x86 test-k1c

.PHONY:
test-x86: prng-test-x86
	@if ! ./$<; then\
		>&2 echo "ERROR: $< failed";\
		exit;\
	else\
		echo "x86: Test Succeeded";\
	fi

.PHONY:
test-k1c: prng-test-k1c
	@if ! k1-cluster -- ./$<; then\
		>&2 echo "ERROR: $< failed";\
		exit;\
	else\
		echo "k1c: Test Succeeded";\
	fi

.PHONY:
clean:
	rm -f prng-test-x86 prng-test-k1c
