prng-test-x86: prng.c
	gcc -D__UNIT_TEST__ -O2 -std=c99 $< -o $@

.PHONY:
test: test-x86

.PHONY:
test-x86: prng-test-x86
	@if ! ./$<; then\
		>&2 echo "ERROR: $< failed";\
		exit;\
	else\
		echo "Test Succeeded";\
	fi

.PHONY:
clean:
	rm -f prng-test-x86
