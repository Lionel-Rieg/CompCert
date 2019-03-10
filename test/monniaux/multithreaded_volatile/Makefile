all: volatile.ccomp.k1c volatile.gcc.k1c

volatile.ccomp.k1c : volatile.ccomp.k1c.s
	k1-cos-gcc $< -o $@

volatile.gcc.k1c : volatile.gcc.k1c.s
	k1-cos-gcc $< -o $@

volatile.ccomp.k1c.s : volatile.c
	../../../ccomp -O2 -Wall -Wno-c11-extensions -S $< -o $@

volatile.gcc.k1c.s : volatile.c
	k1-cos-gcc -O2 -Wall -Werror=implicit -std=gnu99 -S $< -o $@

clean:
	-rm -f *.k1c *.s

.PHONY: clean
