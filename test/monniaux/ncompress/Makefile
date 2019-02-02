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

all: compress.gcc.host compress.ccomp.host compress.gcc.k1c compress.ccomp.k1c

compress.gcc.host : compress42.c
	$(CC) $(CFLAGS) $< -o $@

compress.ccomp.host : compress42.c
	$(CCOMP) $(CCOMPFLAGS) $< -o $@

compress.gcc.k1c : compress42.gcc.k1c.o
	$(K1C_CC) $(K1C_CFLAGS) $< -o $@

compress.ccomp.k1c : compress42.ccomp.k1c.o
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) $< -o $@

INFILE=Makefile
COMPRESSED=foo.gcc.host.Z

foo.gcc.host.Z: compress.gcc.host $(INFILE)
	./compress.gcc.host <$(INFILE) >$@

foo.ccomp.k1c.Z: compress.ccomp.k1c $(INFILE)
	$(EXECUTE) ./compress.ccomp.k1c <$(INFILE) >$@

foo.gcc.host.txt: compress.gcc.host $(COMPRESSED)
	./compress.gcc.host -d <$(COMPRESSED) >$@

foo.ccomp.k1c.txt: compress.gcc.host $(COMPRESSED)
	$(EXECUTE) ./compress.ccomp.k1c -d <$(COMPRESSED) >$@

check: foo.gcc.host.Z foo.ccomp.k1c.Z foo.gcc.host.txt foo.ccomp.k1c.txt
	cmp foo.gcc.host.Z foo.ccomp.k1c.Z
	cmp foo.gcc.host.txt foo.ccomp.k1c.txt
