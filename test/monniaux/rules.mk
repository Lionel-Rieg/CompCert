CCOMP=ccomp
CCOMPFLAGS=-g -O3 -Wall -fno-unprototyped

CFLAGS=-g -std=c99 -O3 -Wall -Wextra -Werror=implicit

K1C_CC=k1-mbr-gcc
K1C_CFLAGS =-g -std=c99 -O2 -Wall -Wextra -Werror=implicit

K1C_CCOMP = ../../../ccomp
K1C_CCOMPFLAGS=-O3 -Wall -fno-unprototyped

EXECUTE=k1-cluster --syscall=libstd_scalls.so --

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

%.k1c.out : %.k1c
	k1-cluster --cycle-based -- $< |tee $@

%.host.out : %.host
	./$< |tee $@
