PRNG=../lib/prng.c

insertion-test-x86: insertion.c $(PRNG)
	gcc -g -D__UNIT_TEST_INSERTION__ -O2 -std=c99 $^ -o $@

insertion-test-k1c: insertion.c $(PRNG)
	k1-gcc -D__UNIT_TEST_INSERTION__ -O2 -std=c99 $^ -o $@

selection-test-x86: selection.c $(PRNG)
	gcc -g -D__UNIT_TEST_SELECTION__ -O2 -std=c99 $^ -o $@

selection-test-k1c: selection.c $(PRNG)
	k1-gcc -D__UNIT_TEST_SELECTION__ -O2 -std=c99 $^ -o $@

.PHONY:
unittest: unittest-x86 unittest-k1c

.PHONY:
unittest-x86: insertion-test-x86 selection-test-x86
	@for test in $^; do\
		if ! ./$$test; then\
			>&2 echo "ERROR: $$test failed";\
		else\
			echo "x86: Test $$test Succeeded";\
		fi;\
	done

.PHONY:
unittest-k1c: insertion-test-k1c selection-test-k1c
	@for test in $^; do\
		if ! k1-cluster -- ./$$test; then\
			>&2 echo "ERROR: $$test failed";\
		else\
			echo "k1c: Test $$test Succeeded";\
		fi;\
	done

.PHONY:
clean:
	rm -f insertion-test-x86 insertion-test-k1c selection-test-k1c selection-test-x86
