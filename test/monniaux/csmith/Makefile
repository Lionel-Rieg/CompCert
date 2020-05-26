CSMITH?=/local/monniaux/packages/csmith-2.3.0/bin/csmith
MAX=1000

include ../rules.mk
KVX_CCOMPFLAGS+=-I/local/monniaux/packages/csmith-2.3.0/include/csmith-2.3.0 -fstruct-passing -fbitfields

TARGETS_S=$(shell seq --format src%06.f.ccomp.kvx.s 0 $(MAX))
TARGETS_C=$(shell seq --format src%06.f.c 0 $(MAX))
TARGETS_O=$(shell seq --format src%06.f.ccomp.kvx.o 0 $(MAX))

all: c s o

s: $(TARGETS_S)
c: $(TARGETS_C)
o: $(TARGETS_O)

src%.c :
	$(CSMITH) --output $@ --seed $*

clean:
	-rm -f $(TARGETS_C) $(TARGETS_S) $(TARGETS_O)

.PHONY: s c o clean
