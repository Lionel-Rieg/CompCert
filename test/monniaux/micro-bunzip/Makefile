include ../rules.mk

all: testfile.txt testfile.txt.2ccomp testfile.txt.2gcc testfile.ccomp.kvx.out testfile.gcc.kvx.out testfile.ccomp.host.out testfile.gcc.host.out
	cmp testfile.txt testfile.txt.2ccomp
	cmp testfile.txt testfile.txt.2gcc

micro-bunzip.ccomp.host: micro-bunzip.c ../clock.gcc.host.o
	$(CCOMP) $(CCOMPFLAGS) $+ -o $@

micro-bunzip.ccomp.kvx: micro-bunzip.c ../clock.gcc.kvx.o
	$(KVX_CCOMP) $(KVX_CCOMPFLAGS) $+ -o $@

micro-bunzip.gcc.host: micro-bunzip.c ../clock.gcc.host.o
	$(CC) $(CFLAGS) $+ -o $@

# micro-bunzip.gcc.kvx: micro-bunzip.c ../clock.gcc.kvx.o
#	$(KVX_CC) $(KVX_CFLAGS) $+ -o $@

# TODO: -O3 buggy??
micro-bunzip.gcc.kvx: micro-bunzip.c ../clock.gcc.kvx.o
	$(KVX_CC) -Wall -O2 $+ -o $@

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

testfile.txt.2ccomp testfile.ccomp.kvx.out: testfile.txt micro-bunzip.ccomp.kvx
	bzip2 <testfile.txt | k1-cluster --cycle-based --syscall=libstd_scalls.so -- micro-bunzip.ccomp.kvx > testfile.txt.2ccomp 2> testfile.ccomp.kvx.out

testfile.txt.2gcc testfile.gcc.kvx.out: testfile.txt micro-bunzip.gcc.kvx
	bzip2 <testfile.txt | k1-cluster --cycle-based --syscall=libstd_scalls.so -- micro-bunzip.gcc.kvx > testfile.txt.2gcc 2> testfile.gcc.kvx.out

testfile.txt.2host testfile.gcc.host.out: testfile.txt micro-bunzip.gcc.host
	bzip2 <testfile.txt | ./micro-bunzip.gcc.host > testfile.txt.2host 2> testfile.gcc.host.out

testfile.ccomp.host.out: testfile.txt micro-bunzip.ccomp.host
	bzip2 <testfile.txt | ./micro-bunzip.ccomp.host > /dev/null 2> testfile.ccomp.host.out

clean:
	rm -f *.kvx *.out test*txt*

.PHONY: clean
