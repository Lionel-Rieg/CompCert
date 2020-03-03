whole : a.o b.o
	../../../ccomp $+ -o $@

a.s : a.c
	k1-cos-gcc -std=c99 -Wall -S $<

b.s : b.c
	../../../ccomp -Wall -Wno-c11-extensions -S $<

%.o : %.s
	k1-cos-gcc -c $<

clean:
	-rm -f a.o b.o a.s b.s whole

.PHONY: clean
