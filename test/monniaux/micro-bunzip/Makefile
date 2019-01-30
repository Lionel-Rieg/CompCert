all: testfile.txt testfile.txt.2ccomp testfile.txt.2gcc testfile.txt.ccomp.out testfile.txt.gcc.out
	cmp testfile.txt testfile.txt.2ccomp
	cmp testfile.txt testfile.txt.2gcc

../clock.gcc.k1c.o : ../clock.c ../cycles.h 
	k1-mbr-gcc -c -Wall -O3 $< -o $@

micro-bunzip.host: micro-bunzip.c ../clock.c
	$(CC) $+ -o $@

micro-bunzip.ccomp.k1c: micro-bunzip.c ../clock.gcc.k1c.o
	../../../ccomp -Wall -O3 $+ -o $@

# TODO: -O3 buggy??
micro-bunzip.gcc.k1c: micro-bunzip.c ../clock.gcc.k1c.o
	k1-mbr-gcc -Wall -O2 $+ -o $@

testfile.txt: micro-bunzip.c
	cat micro-bunzip.c > $@
	sha1sum micro-bunzip.c >> $@
	cat micro-bunzip.c >> $@
	md5sum micro-bunzip.c >> $@
#	cat micro-bunzip.c >> $@
#	sha224sum micro-bunzip.c >> $@
#	cat micro-bunzip.c >> $@
#	sha256sum micro-bunzip.c >> $@
#	cat micro-bunzip.c >> $@
#	sha384sum micro-bunzip.c >> $@
#	cat micro-bunzip.c >> $@
#	sha512sum micro-bunzip.c >> $@
#x	cat micro-bunzip.c >> $@

testfile.txt.2ccomp testfile.txt.ccomp.out: testfile.txt micro-bunzip.ccomp.k1c
	bzip2 <testfile.txt | k1-cluster --cycle-based --syscall=libstd_scalls.so -- micro-bunzip.ccomp.k1c > testfile.txt.2ccomp 2> testfile.txt.ccomp.out

testfile.txt.2gcc testfile.txt.gcc.out: testfile.txt micro-bunzip.gcc.k1c
	bzip2 <testfile.txt | k1-cluster --cycle-based --syscall=libstd_scalls.so -- micro-bunzip.gcc.k1c > testfile.txt.2gcc 2> testfile.txt.gcc.out

testfile.txt.2host: testfile.txt micro-bunzip.host
	bzip2 <testfile.txt | valgrind ./micro-bunzip.host > testfile.txt.2host

clean:
	rm -f *.k1c *.out test*txt*

.PHONY: clean
