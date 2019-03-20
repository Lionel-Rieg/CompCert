CSMITH=csmith
MAX=100

include ../rules.mk
K1C_CCOMPFLAGS+=-I/usr/include/csmith -fstruct-passing -fbitfields

TARGETS_S=$(shell seq --format src%06.f.ccomp.k1c.s 0 $(MAX))
TARGETS_C=$(shell seq --format src%06.f.c 0 $(MAX))
TARGETS_O=$(shell seq --format src%06.f.ccomp.k1c.o 0 $(MAX))

all: c s o

s: $(TARGETS_S)
c: $(TARGETS_C)
o: $(TARGETS_O)

src%.c :
	$(CSMITH) --output $@ --seed $*

clean:
	-rm -f $(TARGETS_C) $(TARGETS_S) $(TARGETS_O)

.PHONY: s c o clean
