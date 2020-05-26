include ../../Makefile.config

CCOMP=../../ccomp
CCOMPFLAGS=$(CCOMPOPTS) -stdlib ../../runtime -dc -dclight -dasm

CFLAGS+=-O2 -Wall
EXECUTE:=timeout --signal=SIGTERM 20s $(EXECUTE)

LIBS=$(LIBMATH)

TIME=time >/dev/null
# FIXME - maybe this is better? From v3.6
# TIME=ocaml unix.cma ../../tools/xtime.ml -o /dev/null -mintime 2.0 -minruns 4

PROGS?=fib integr qsort fft fftsp fftw sha1 sha3 aes almabench \
  lists binarytrees fannkuch mandelbrot nbody \
  nsieve nsievebits spectral vmach \
  chomp perlin siphash24

##
# Kalray NOTE :
# * removed knucleotide from PROGS, it is hard to edit the input
#   to modify its size without resulting in a seg fault, and the base input
#   takes a too long time to complete in the simulator.
# * also removed bisect, who is exhibiting different float values on the Kalray
#   architecture than using x86 GCC (for both CompCert and GCC ports) (tested with n=10)
##
ifeq ($(ARCH),kvx)
	PROGS:=$(filter-out knucleotide,$(PROGS))
	PROGS:=$(filter-out bisect,$(PROGS))
endif

all: $(PROGS:%=%.compcert)

all_s: $(PROGS:%=%.s)

all_gcc: $(PROGS:%=%.gcc)

%.compcert: %.c
	$(CCOMP) $(CCOMPFLAGS) -o $*.compcert $*.c $(LIBS)

%.s: %.c
	$(CCOMP) $(CCOMPFLAGS) -S $*.c

%.gcc: %.c
	$(CC) $(CFLAGS) -o $*.gcc $*.c $(LIBS)

test: all
	@for i in $(PROGS); do \
		 SIMU='$(EXECUTE)' ./Runtest $$i ./$$i.compcert;\
         done

test_gcc: all_gcc
	@for i in $(PROGS); do \
	   SIMU='$(EXECUTE)' ./Runtest $$i ./$$i.gcc;\
         done

bench_gcc: all_gcc
	@for i in $(PROGS); do \
	   $(TIME) -name $$i -- ./$$i.gcc; \
         done

bench: all
	@for i in $(PROGS); do \
	   $(TIME) -name $$i -- ./$$i.compcert; \
         done

clean:
	rm -f *.compcert *.gcc
	rm -f *.compcert.c *.light.c *.parsed.c *.s *.o *.sdump *~ 
	rm -f *.out
