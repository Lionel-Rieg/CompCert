include ../../Makefile.config

CCOMP=../../ccomp
CCOMPFLAGS=$(CCOMPOPTS) -stdlib ../../runtime -dc -dclight -dasm

CFLAGS+=-O1 -Wall

LIBS=$(LIBMATH)

#TIME=xtime -o /dev/null -mintime 2.0     # Xavier's hack
TIME=time >/dev/null                    # Otherwise

PROGS?=fib qsort fftw sha1 sha3 aes \
  lists binarytrees fannkuch \
  nsieve nsievebits vmach \
  chomp perlin siphash24\
  integr fft fftsp almabench knucleotide mandelbrot nbody spectral bisect

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
	   if $(EXECUTE) ./$$i.compcert | cmp -s - Results/$$i; \
           then echo "$$i: passed"; \
           else echo "$$i: FAILED"; exit 2; \
	   fi; \
         done

test_gcc: all_gcc
	@for i in $(PROGS); do \
	   if $(EXECUTE) ./$$i.gcc | cmp -s - Results/$$i; \
           then echo "$$i: passed"; \
           else echo "$$i: FAILED"; \
	   fi; \
         done

bench_gcc: all_gcc
	@for i in $(PROGS); do \
	   echo -n "$$i: "; $(TIME) ./$$i.gcc; \
         done

bench: all
	@for i in $(PROGS); do \
	   echo -n "$$i: "; $(TIME) ./$$i.compcert; \
         done

clean:
	rm -f *.compcert *.gcc
	rm -f *.compcert.c *.light.c *.parsed.c *.s *.o *.sdump *~ 
