CFILES=$(wildcard *.c)
SFILES=$(subst .c,.s,$(CFILES))

all: $(SFILES)

.SECONDARY:
%.S: %.c
	k1-gcc -O2 -S $< -o $@
