# install Quest using: opam install quest
MAX=300

include ../rules.mk

QUEST=quest
K1C_CCOMPFLAGS += -fstruct-passing -fbitfields

PREFIX=ran%06.f
TARGETS_C=$(shell seq --format $(PREFIX).c 0 $(MAX))
TARGETS_OUT=$(shell seq --format $(PREFIX).ccomp.k1c.out 0 $(MAX))

all:	$(TARGETS_C) $(TARGETS_OUT)

ran%.c :
	$(QUEST) -seed $* -test ansi > $@

%.ccomp.k1c : %.ccomp.k1c.s
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) $+ -o $@

clean:
	-rm -f $(TARGETS_C) $(TARGETS_OUT)

.PHONY: all clean
