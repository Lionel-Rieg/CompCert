CFLAGS=-Wall -O3
K1C_CC=k1-mbr-gcc
K1C_CFLAGS=-Wall -O3 -std=c99
K1C_CCOMP=../../ccomp
K1C_CCOMPFLAGS=-Wall -O3 -D__thread= -D__int128=int

EXECUTABLES=int_mat.host int_mat.k1c int_mat.k1c_ccomp

all:	$(EXECUTABLES)

int_mat.host: int_mat.c
	$(CC) $(CFLAGS) $+ -o $@

int_mat.k1c: int_mat.c
	$(K1C_CC) $(K1C_CFLAGS) $+ -o $@

int_mat.k1c_ccomp: int_mat.c
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) $+ -o $@

clean:
	$(RM) -f $(EXECUTABLES)

.PHONY: clean
