CFILES=$(wildcard *.c)
SFILES=$(subst .c,.s,$(CFILES))

all: $(SFILES)

.SECONDARY:
%.S: %.c
	ccomp -O2 -S $< -o $@
	sed -i -e 's/i64_/__compcert_i64_/g' $@
