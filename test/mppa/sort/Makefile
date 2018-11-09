PRNG=../lib/prng.c
CCOMP=../../../ccomp

ALL= insertion-test-x86 insertion-test-k1c\
     selection-test-x86 selection-test-k1c\
     merge-test-x86     merge-test-k1c\
     test-x86           test-k1c\
     test-ccomp

all: $(ALL)

%-test-x86: %.c $(PRNG)
	gcc -g -D__UNIT_TEST_$$(echo $(basename $<) | tr a-z A-Z)__ -O2 -std=c99 $^ -o $@

%-test-k1c: %.c $(PRNG)
	k1-mbr-gcc -g -D__UNIT_TEST_$$(echo $(basename $<) | tr a-z A-Z)__ -O2 -std=c99 $^ -o $@

test-x86: selection.c merge.c insertion.c test.c $(PRNG)
	gcc -g -O2 -std=c99 $^ -o $@

test-k1c: selection.c merge.c insertion.c test.c $(PRNG)
	k1-mbr-gcc -g -O2 -std=c99 $^ -o $@

%.s: %.c $(CCOMP)
	ccomp -O2 -S $< -o $@

test-ccomp: selection.s merge.s insertion.s test.s $(subst .c,.s,$(PRNG))
	k1-mbr-gcc $^ -o $@

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
unittest-x86: insertion-test-x86 selection-test-x86 merge-test-x86
	@for test in $^; do\
		if ! ./$$test; then\
			>&2 echo "ERROR x86: $$test failed";\
		else\
			echo "x86: Test $$test Succeeded";\
		fi;\
	done

.PHONY:
unittest-k1c: insertion-test-k1c selection-test-k1c merge-test-k1c
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
