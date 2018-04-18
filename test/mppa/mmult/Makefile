PRNG=../lib/prng.c

ALL= mmult-test-x86 mmult-test-k1c\

all: $(ALL)

%-test-x86: %.c $(PRNG)
	gcc -D__UNIT_TEST_$$(echo $(basename $<) | tr a-z A-Z)__ -O2 -std=c99 $^ -o $@

%-test-k1c: %.c $(PRNG)
	k1-gcc -D__UNIT_TEST_$$(echo $(basename $<) | tr a-z A-Z)__ -O2 -std=c99 $^ -o $@

test-x86: mmult.c $(PRNG)
	gcc -g -O2 -std=c99 $^ -o $@

test-k1c: mmult.c $(PRNG)
	k1-gcc -g -O2 -std=c99 $^ -o $@

%.s: %.c
	ccomp -O2 -S $< -o $@

test-ccomp: mmult.s $(subst .c,.s,$(PRNG))
	k1-gcc $^ -o $@

.PHONY:
unittest: unittest-x86 unittest-k1c

.PHONY:
check: check-x86 check-k1c

.PHONY:
compc-check: test-ccomp
	@if ! k1-cluster -- ./$<; then\
		>&2 echo "ERROR k1c: sort $< failed";\
	else\
		echo "k1c: Test sort $< succeeded";\
	fi

.PHONY:
check-x86: test-x86
	@if ! ./$<; then\
		>&2 echo "ERROR x86: $< failed";\
	else\
		echo "x86: Test $< succeeded";\
	fi

.PHONY:
check-k1c: test-k1c
	@if ! k1-cluster -- ./$<; then\
		>&2 echo "ERROR k1c: $< failed";\
	else\
		echo "k1c: Test $< succeeded";\
	fi

.PHONY:
unittest-x86: mmult-test-x86
	@for test in $^; do\
		if ! ./$$test; then\
			>&2 echo "ERROR x86: $$test failed";\
		else\
			echo "x86: Test $$test Succeeded";\
		fi;\
	done

.PHONY:
unittest-k1c: mmult-test-k1c
	@for test in $^; do\
		if ! k1-cluster -- ./$$test; then\
			>&2 echo "ERROR k1c: $$test failed";\
		else\
			echo "k1c: Test $$test Succeeded";\
		fi;\
	done

.PHONY:
clean:
	rm -f $(ALL)
