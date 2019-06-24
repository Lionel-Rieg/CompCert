ALL_CCOMPFLAGS+=-fno-unprototyped
CCOMP=ccomp-x86
CCOMPFLAGS=-g -O3 -Wall $(ALL_CCOMPFLAGS) $(ALL_CFLAGS)

CFLAGS=-g -std=c99 -O3 -Wall -Wextra -Werror=implicit  $(ALL_CFLAGS)

K1C_CC=k1-cos-gcc
K1C_CFLAGS = -D__K1C_COS__ -std=c99 -O3 -Wall -Wextra -Werror=implicit  $(ALL_CFLAGS)
K1C_CFLAGS_O1 =-std=c99 -O1 -fschedule-insns2 -Wall -Wextra -Werror=implicit  $(ALL_CFLAGS)

K1C_CCOMP = ../../../ccomp
K1C_CCOMPFLAGS=-O3 -Wall $(ALL_CCOMPFLAGS) $(ALL_CFLAGS) # -fpostpass= revlist

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

%.gcc.o1.k1c.s: %.c
	$(K1C_CC) $(K1C_CFLAGS_O1) -S $< -o $@

%.gcc.o1.k1c.o: %.gcc.o1.k1c.s
	$(K1C_CC) $(K1C_CFLAGS_O1) -c $< -o $@

%.gcc.k1c.s: %.c
	$(K1C_CC) $(K1C_CFLAGS) -S $< -o $@

%.gcc.k1c.o: %.gcc.k1c.s
	$(K1C_CC) $(K1C_CFLAGS) -c $< -o $@

%.ccomp.k1c.s: %.c
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) -S $< -o $@

%.ccomp.k1c.o: %.ccomp.k1c.s
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) -c $< -o $@

# %.gcc.k1c : %.gcc.k1c.o
# 	$(K1C_CC) $(K1C_CFLAGS) $+ -o $@

# %.ccomp.k1c : %.ccomp.k1c.o
# 	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) $+ -o $@

# %.gcc.host : %.gcc.host.o
# 	$(CC) $(CFLAGS) $+ -o $@

# %.ccomp.host : %.ccomp.host.o
# 	$(CCOMP) $(CCOMPFLAGS) $+ -o $@

%.k1c.out : %.k1c
	$(EXECUTE_CYCLES) $< $(EXECUTE_ARGS) |tee $@

%.host.out : %.host
	./$< $(EXECUTE_ARGS) |tee $@
