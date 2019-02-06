CCOMP=ccomp
CCOMPFLAGS=-O3 -Wall -fno-unprototyped
CFLAGS= -std=c99 -O3 -Wall -Wextra -Werror=implicit
K1C_CC=k1-mbr-gcc
K1C_CFLAGS = -std=c99 -O3 -Wall -Wextra -Werror=implicit
K1C_CCOMP = ../../../ccomp
K1C_CCOMPFLAGS=-O3 -Wall -fno-unprototyped

EXECUTE=k1-cluster --syscall=libstd_scalls.so --

%.host.gcc.o : %.c
	$(CC) $(CFLAGS) -c -o $@ $<

%.host.ccomp.o : %.c
	$(CCOMP) $(CCOMPFLAGS) -c -o $@ $<

%.gcc.k1c.s: %.c
	$(K1C_CC) $(K1C_CFLAGS) -S $< -o $@

%.gcc.k1c.o: %.gcc.k1c.s
	$(K1C_CC) $(K1C_CFLAGS) -c $< -o $@

%.ccomp.k1c.s: %.c
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) -S $< -o $@

%.ccomp.k1c.o: %.ccomp.k1c.s
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) -c $< -o $@

%.gcc.host.o: %.c
	$(CC) $(CFLAGS) -c $< -o $@

%.ccomp.host.o: %.c
	$(CCOMP) $(CCOMPFLAGS) -c $< -o $@

%.k1c.out : %.k1c
	k1-cluster --cycle-based -- $< |tee $@

%.host.out : %.host
	./$< |tee $@
