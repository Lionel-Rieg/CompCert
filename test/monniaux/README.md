# Benchmarking `CompCert` and GCC

## Compiling `CompCert`

The first step to benchmark `CompCert` is to compile it - the `INSTALL.md` instructions of the project root folder should guide you on installing it.

For the benchmarks to work, the compiler `ccomp` should be on your `$PATH`, with the runtime libraries installed correctly (with a successful `make install` on the project root directory).

## Using the harness

`rules.mk` contains generic rules to compile with `gcc` and `ccomp`, with different optimizations, and producing different binaries. It also produces a `measures.csv` file containing the different timings given by the bench.

Up to 5 different sets of optimizations per compiler can be used.

To use this `rules.mk`, create a folder, put inside all the .c/.h source files, and write a Makefile resembling:
```make
TARGET=float_mat
MEASURES="c1 c2 c3 c4 c5 c6 c7 c8"

include ../rules.mk
```

This is all that is required to write, the `rules.mk` handles everything.

There is the possibility to define some variables to fine tune what you want. For instance, `ALL_CFILES` describes the .c source files whose objects are to be linked.

Here is an exhaustive list of the variables:
- `TARGET`: name of the binary to produce
- `MEASURES`: list of the different timings. This supposes that the program
prints something of the form `c3 cycles: 44131`.
- `ALL_CFILES`: list of .c files to compile. By default, `$(wildcard *.c)`
- `CLOCK`: `basename` of the clock file to compile. Default `../clock`
- `ALL_CFLAGS`: `cflags` that are to be included for all compilers
- `ALL_GCCFLAGS`: same, but GCC specific
- `ALL_CCOMPFLAGS`: same, but `ccomp` specific
- `KVX_CC`: GCC compiler (default `k1-cos-gcc`)
- `KVX_CCOMP`: `CompCert` compiler (default `ccomp`)
- `EXECUTE_CYCLES`: running command (default is `k1-cluster --syscall=libstd_scalls.so --cycle-based --`)
- `EXECUTE_ARGS`: execution arguments. You can use a macro `__BASE__` which expands to the name of the binary being executed.
- `GCCiFLAGS` with `i` from 0 to 4: the wanted optimizations. If one of these flags is empty, nothing is done. Same for `CCOMPiFLAGS`. Look at `rules.mk` to see the default values. You might find something like this:

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

The `PREFIX` are the prefixes to add to the secondary produced files (assembly, object, executable, ..). You should be careful that if a `FLAGS` is set, then the according `PREFIX` should be set as well.

Assembly files are generated in `asm/`, objects in `obj/`, binaries in `bin/` and outputs in `out/`.

To compile and execute all the benches : `make` while in the `monniaux` directory (without any `-j` flag). Doing so will compile CompCert, install it, and then proceed to execute each bench.

To compile and/or execute a single bench, `cd` to the bench directory, then:
- `make` for compiling the bench
- `make run` for running it

You can use `-j` flag when in a single bench directory.

## Individual scripts

If you want to run the building and running scripts individually without having to use the `Makefile` from `test/monniaux`, you can run the `build_benches.sh` script which builds each bench using all the available cores on your machine.

Once the benches are built, you can then run `run_benches.sh file.csv` where `file.csv` is where you want to store the timings of the benchmarks. `run_benches.sh` also uses all the available cores of your machine.

## Adding timings to a benchmark

If you just add a benchmark without any timing function, the resulting `measures.csv` file will be empty for lack of timing output.

To add a timing, you must use the functions whose prototypes are in `clock.h`

    #include "../clock.h"
    /* ... */
    clock_prepare();
    /* ... */
    clock_start();
    /* .. computations .. */
    clock_stop();
    /* ... */
    print_total_clock(); // print to stdout
    printerr_total_clock(); // print to stderr

If the benchmark doesn't use `stdout` in a binary way you can use `print_total_clock()`. However, some benchmarks like `jpeg-6b` print their binary content to `stdout`, which then messes up the `grep` command when attempting to use it to extract the cycles from `stdout`.

The solution is then to use `printerr_total_clock()` which will print the cycles to `stderr`, and use `EXECUTE_ARGS` ressembling this:

    EXECUTE_ARGS=-dct int -outfile __BASE__.jpg testimg.ppm 2> __BASE__.out

`__BASE__` is a macro that gets expanded to the base name - that is, the `TARGET` concatenated with one of the `GCCiPREFIX` or `CCOMPiPREFIX`. For instance, in `jpeg-6b`, `__BASE__` could be `jpeg-6b.ccomp.o2`.
