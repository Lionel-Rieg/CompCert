CFLAGS=-Wall -O3
CCOMPFLAGS=-Wall -O3 -D_DEFAULT_SOURCE
CCOMP=ccomp
EXECUTE=k1-cluster --syscall=libstd_scalls.so --

K1C_CC=k1-mbr-gcc
K1C_CFLAGS=-Wall -O3 -std=c99
K1C_CCOMP=../../../ccomp
K1C_CCOMPFLAGS=-Wall -O3

all: check

%.gcc.k1c.s: %.c
	$(K1C_CC) $(K1C_CFLAGS) -S $< -o $@

%.gcc.k1c.o: %.gcc.k1c.s
	$(K1C_CC) $(K1C_CFLAGS) -c $< -o $@

%.ccomp.k1c.s: %.c
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) -S $< -o $@

%.ccomp.k1c.o: %.ccomp.k1c.s
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) -c $< -o $@

%.gcc.host.o: %.c
	$(CC) $(CFLAGS) -c $< -o $@

all: compress.gcc.host compress.ccomp.host compress.gcc.k1c compress.ccomp.k1c

compress.gcc.host : compress42.c ../clock.gcc.host.o
	$(CC) $(CFLAGS) $+ -o $@

compress.ccomp.host : compress42.c ../clock.gcc.host.o
	$(CCOMP) $(CCOMPFLAGS) $+ -o $@

compress.gcc.k1c : compress42.gcc.k1c.o ../clock.gcc.k1c.o
	$(K1C_CC) $(K1C_CFLAGS) $+ -o $@

compress.ccomp.k1c : compress42.ccomp.k1c.o ../clock.gcc.k1c.o
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) $+ -o $@

INFILE=Makefile
COMPRESSED=foo.gcc.host.Z

foo.gcc.host.Z: compress.gcc.host $(INFILE)
	./compress.gcc.host <$(INFILE) >foo.gcc.host.Z 2> foo.gcc.host.Z.out

foo.ccomp.k1c.Z: compress.ccomp.k1c $(INFILE)
	$(EXECUTE) ./compress.ccomp.k1c <$(INFILE) >foo.ccomp.k1c.Z 2> foo.ccomp.k1c.Z.out

foo.gcc.k1c.Z: compress.gcc.k1c $(INFILE)
	$(EXECUTE) ./compress.gcc.k1c <$(INFILE) >foo.gcc.k1c.Z 2> foo.gcc.k1c.Z.out

foo.gcc.host.txt: compress.gcc.host $(COMPRESSED)
	./compress.gcc.host -d <$(COMPRESSED) >foo.gcc.host.txt 2> foo.gcc.host.txt.out

foo.ccomp.k1c.txt: compress.gcc.host $(COMPRESSED)
	$(EXECUTE) ./compress.ccomp.k1c -d <$(COMPRESSED) >foo.ccomp.k1c.txt 2> foo.ccomp.k1c.txt.out

foo.gcc.k1c.txt: compress.gcc.host $(COMPRESSED)
	$(EXECUTE) ./compress.gcc.k1c -d <$(COMPRESSED) >foo.gcc.k1c.txt 2> foo.gcc.k1c.txt.out

check: foo.gcc.host.Z foo.gcc.host.txt foo.ccomp.k1c.Z foo.ccomp.k1c.txt foo.gcc.k1c.Z foo.gcc.k1c.txt
	cmp foo.gcc.host.Z foo.ccomp.k1c.Z
	cmp foo.gcc.host.Z foo.gcc.k1c.Z
	cmp foo.gcc.host.txt foo.ccomp.k1c.txt
	cmp foo.gcc.host.txt foo.gcc.k1c.txt

clean:
	rm -f *.Z *.txt *.out *.o *.s *.host *.k1c

.PHONY: clean

.SECONDARY: %.s
