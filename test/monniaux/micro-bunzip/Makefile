all: testfile.txt testfile.txt.2
	cmp testfile.txt testfile.txt.2

micro-bunzip.k1c: micro-bunzip.c
	../../../ccomp -O3 $< -U __SIZEOF_INT128__ -D __SIZE_TYPE__='long long' -o $@

testfile.txt: micro-bunzip.c
	cat micro-bunzip.c > $@
	sha1sum micro-bunzip.c >> $@
	cat micro-bunzip.c >> $@
	md5sum micro-bunzip.c >> $@
	cat micro-bunzip.c >> $@
	sha224sum micro-bunzip.c >> $@
	cat micro-bunzip.c >> $@
	sha256sum micro-bunzip.c >> $@
	cat micro-bunzip.c >> $@
	sha384sum micro-bunzip.c >> $@
	cat micro-bunzip.c >> $@
	sha512sum micro-bunzip.c >> $@
	cat micro-bunzip.c >> $@

testfile.txt.2: testfile.txt micro-bunzip.k1c
	bzip2 <testfile.txt | k1-cluster --syscall=libstd_scalls.so -- micro-bunzip.k1c > $@

