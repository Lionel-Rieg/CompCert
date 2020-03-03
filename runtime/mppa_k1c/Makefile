CCOMP ?= ../../ccomp
CFLAGS ?= -O2 -D__K1_TINYK1__

CFILES=$(wildcard *.c)
SFILES=$(subst .c,.s,$(CFILES))

CCOMPPATH=$(shell which $(CCOMP))

all: $(SFILES)

.SECONDARY:
%.s: %.c $(CCOMPPATH)
	$(CCOMP) $(CFLAGS) -S $< -o $@
	sed -i -e 's/i64_/__compcert_i64_/g' -e 's/i32_/__compcert_i32_/g' \
               -e 's/f64_/__compcert_f64_/g' -e 's/f32_/__compcert_f32_/g' $@
