CCOMP=ccomp
CCOMPFLAGS=-g -O3 -Wall -fno-unprototyped

CFLAGS=-g -std=c99 -O3 -Wall -Wextra -Werror=implicit

K1C_CC=k1-mbr-gcc
K1C_CFLAGS =-g -std=c99 -O2 -Wall -Wextra -Werror=implicit

K1C_CCOMP = ../../../ccomp
K1C_CCOMPFLAGS=-O3 -Wall -Wno-c11-extensions -fno-unprototyped # -fpostpass-ilp

EXECUTE=k1-cluster --syscall=libstd_scalls.so --
EXECUTE_CYCLES=k1-cluster --syscall=libstd_scalls.so --cycle-based --

%.gcc.host.o : %.gcc.host.s
	$(CC) $(CFLAGS) -c -o $@ $<

%.ccomp.host.o : %.ccomp.host.s
	$(CCOMP) $(CCOMPFLAGS) -c -o $@ $<

%.gcc.host.s : %.c
	$(CC) $(CFLAGS) -S -o $@ $<

%.ccomp.host.s : %.c
	$(CCOMP) $(CCOMPFLAGS) -S -o $@ $<

%.gcc.k1c.s: %.c
	$(K1C_CC) $(K1C_CFLAGS) -S $< -o $@

%.gcc.k1c.o: %.gcc.k1c.s
	$(K1C_CC) $(K1C_CFLAGS) -c $< -o $@

%.ccomp.k1c.s: %.c
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) -S $< -o $@

%.ccomp.k1c.o: %.ccomp.k1c.s
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) -c $< -o $@

%.gcc.k1c : %.gcc.k1c.o
	$(K1C_CC) $(K1C_CFLAGS) $+ -o $@

%.ccomp.k1c : %.ccomp.k1c.o
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) $+ -o $@

%.gcc.host : %.gcc.host.o
	$(CC) $(CFLAGS) $+ -o $@

%.ccomp.host : %.ccomp.host.o
	$(CCOMP) $(CCOMPFLAGS) $+ -o $@

%.k1c.out : %.k1c
	$(EXECUTE_CYCLES) $< $(EXECUTE_ARGS) |tee $@

%.host.out : %.host
	./$< $(EXECUTE_ARGS) |tee $@
