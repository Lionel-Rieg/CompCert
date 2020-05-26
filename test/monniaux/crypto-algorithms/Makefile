include ../rules.mk

all:	md2.all md5.all sha1.all sha256.all blowfish.all des.all
kvx:	md2_test.ccomp.kvx md5_test.ccomp.kvx sha1_test.ccomp.kvx sha256_test.ccomp.kvx blowfish_test.ccomp.kvx des_test.ccomp.kvx

md2.all : md2_test.ccomp.kvx.out md2_test.gcc.kvx.out
md5.all : md5_test.ccomp.kvx.out md5_test.gcc.kvx.out
arcfour.all : arcfour_test.ccomp.kvx.out arcfour_test.gcc.kvx.out
blowfish.all : blowfish_test.ccomp.kvx.out blowfish_test.gcc.kvx.out
rot-13.all : rot-13_test.ccomp.kvx.out rot-13_test.gcc.kvx.out
sha1.all : sha1_test.ccomp.kvx.out sha1_test.gcc.kvx.out
sha256.all : sha256_test.ccomp.kvx.out sha256_test.gcc.kvx.out
des.all: des_test.ccomp.kvx.out des_test.gcc.kvx.out
base64.all: base64_test.ccomp.kvx.out base64_test.gcc.kvx.out
aes.all : aes_test.ccomp.kvx.out aes_test.gcc.kvx.out

%.gcc.kvx.s %.ccomp.kvx.s %_test.gcc.kvx.s: %.h

%_test.gcc.kvx: %.gcc.kvx.o %_test.gcc.kvx.o
	$(KVX_CC) $(KVX_CFLAGS) $+ -o $@

%_test.ccomp.kvx: %.ccomp.kvx.o %_test.gcc.kvx.o 
	$(KVX_CCOMP) $(KVX_CCOMPFLAGS) $+ -o $@

clean:
	$(RM) -f *.s *.o *.out *.kvx *.host

.PHONY: clean all md2.all md5.all rot-13.all sha1.all sha256.all md5.all blowfish.all arcfour.all des.all base64.all aes.all
