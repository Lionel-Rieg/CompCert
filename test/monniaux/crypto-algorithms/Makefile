CFLAGS=-Wall -O3
K1C_CC=k1-mbr-gcc
K1C_CFLAGS=-Wall -O3
K1C_CCOMP=../../../ccomp
K1C_CCOMPFLAGS=-Wall -O3 -D__thread= -D__int128=int


all:	md2.all md5.all sha1.all sha256.all blowfish.all des.all
k1c:	md2_test.ccomp.k1c md5_test.ccomp.k1c sha1_test.ccomp.k1c sha256_test.ccomp.k1c blowfish_test.ccomp.k1c des_test.ccomp.k1c

md2.all : md2_test.ccomp.k1c.out md2_test.gcc.k1c.out
md5.all : md5_test.ccomp.k1c.out md5_test.gcc.k1c.out
arcfour.all : arcfour_test.ccomp.k1c.out arcfour_test.gcc.k1c.out
blowfish.all : blowfish_test.ccomp.k1c.out blowfish_test.gcc.k1c.out
rot-13.all : rot-13_test.ccomp.k1c.out rot-13_test.gcc.k1c.out
sha1.all : sha1_test.ccomp.k1c.out sha1_test.gcc.k1c.out
sha256.all : sha256_test.ccomp.k1c.out sha256_test.gcc.k1c.out
des.all: des_test.ccomp.k1c.out des_test.gcc.k1c.out

%.gcc.k1c.s: %.c
	$(K1C_CC) $(K1C_CFLAGS) -S $< -o $@

%.gcc.k1c.o: %.gcc.k1c.s
	$(K1C_CC) $(K1C_CFLAGS) -c $< -o $@

%.ccomp.k1c.s: %.c
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) -S $< -o $@

%.ccomp.k1c.o: %.ccomp.k1c.s
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) -c $< -o $@

%_test.host: %.c %_test.c %.h
	$(CC) $(CFLAGS) $*.c $*_test.c -o $@

%.gcc.k1c.s %.ccomp.k1c.s %_test.gcc.k1c.s: %.h

%_test.gcc.k1c: %.gcc.k1c.o %_test.gcc.k1c.o
	$(K1C_CC) $(K1C_CFLAGS) $+ -o $@

%_test.ccomp.k1c: %.ccomp.k1c.o %_test.gcc.k1c.o modulo_division.gcc.k1c.o 
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) $+ -o $@

%.k1c.out: %.k1c
	k1-cluster --cycle-based -- $< | tee $@

clean:
	$(RM) -f *.s *.o *.out *.k1c *.host

.PHONY: clean all md2.all md5.all rot-13.all sha1.all sha256.all md5.all blowfish.all arcfour.all des.all
