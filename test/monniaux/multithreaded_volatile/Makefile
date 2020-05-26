all: volatile.ccomp.kvx volatile.gcc.kvx

volatile.ccomp.kvx : volatile.ccomp.kvx.s
	k1-cos-gcc $< -o $@

volatile.gcc.kvx : volatile.gcc.kvx.s
	k1-cos-gcc $< -o $@

volatile.ccomp.kvx.s : volatile.c
	../../../ccomp -O2 -Wall -S $< -o $@

volatile.gcc.kvx.s : volatile.c
	k1-cos-gcc -O2 -Wall -Werror=implicit -std=gnu99 -S $< -o $@

clean:
	-rm -f *.kvx *.s

.PHONY: clean
