# Benchmarking CompCert and GCC

rules.mk contains generic rules to compile with gcc and ccomp, with different
optimizations, and producing different binaries. It also produces a
measures.csv file containing the different timings given by the bench.

Up to 5 different optimizations can be used.

To use this rule.mk, create a folder, put inside all the .c/.h source files,
and write a Makefile ressembling:
```make
TARGET=float_mat
MEASURES="c1 c2 c3 c4 c5 c6 c7 c8"

include ../rules.mk
```

This is all that is required to write, the rules.mk handles everything.

There is the possibility to define some variables to finetune what you want.
For instance, `ALL_CFILES` describes the .c source files whose objects are
to be linked.

Here is an exhaustive list of the variables:
- `TARGET`: name of the binary to produce
- `MEASURES`: list of the different timings. This supposes that the program
prints something of the form "c3 cycles: 44131" for instance. In the above
example, the Makefile would generate such a line:
```
float_mat c3,  1504675,  751514,  553235, 1929369,  1372441 
```
- `ALL_CFILES`: list of .c files to compile. By default, `$(wildcard *.c)`
- `CLOCK`: basename of the clock file to compile. Default `../clock`
- `ALL_CFLAGS`: cflags that are to be included for all compilers
- `ALL_GCCFLAGS`: same, but GCC specific
- `ALL_CCOMPFLAGS`: same, but ccomp specific
- `K1C_CC`: GCC compiler (default k1-cos-gcc)
- `K1C_CCOMP`: compcert compiler (default ccomp)
- `EXECUTE_CYCLES`: running command (default `k1-cluster` with some options)
- `GCCiFLAGS` with i from 0 to 4: the wanted optimizations. If one of these flags is empty, nothing is done. Same for `CCOMPiFLAGS`. For now, the default values:
```
# You can define up to GCC4FLAGS and CCOMP4FLAGS
GCC0FLAGS?=
GCC1FLAGS?=$(ALL_GCCFLAGS) -O1
GCC2FLAGS?=$(ALL_GCCFLAGS) -O2
GCC3FLAGS?=$(ALL_GCCFLAGS) -O3
GCC4FLAGS?=
CCOMP0FLAGS?=
CCOMP1FLAGS?=$(ALL_CCOMPFLAGS) -fno-postpass
CCOMP2FLAGS?=$(ALL_CCOMPFLAGS)
CCOMP3FLAGS?=
CCOMP4FLAGS?=

# Prefix names
GCC0PREFIX?=
GCC1PREFIX?=.gcc.o1
GCC2PREFIX?=.gcc.o2
GCC3PREFIX?=.gcc.o3
GCC4PREFIX?=
CCOMP0PREFIX?=
CCOMP1PREFIX?=.ccomp.o1
CCOMP2PREFIX?=.ccomp.o2
CCOMP3PREFIX?=
CCOMP4PREFIX?= 
```

The `PREFIX` are the prefixes to add to the .s, .o, etc.. You should be careful that if a FLAGS is set, then the according PREFIX should be set as well.

Assembly files will be generated in `asm/`, objects in `obj/`, binaries in `bin/` and outputs in `out/`.

To compile and execute all the benches : `make`
