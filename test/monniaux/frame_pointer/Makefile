whole : a.o b.o
	../../../ccomp $+ -o $@

a.o : a.c
	k1-mbr-gcc -std=c99 -Wall -c $<

b.o : b.c
	../../../ccomp -Wall -Wno-c11-extensions -c $<

clean:
	-rm -f a.o b.o whole

.PHONY: clean
