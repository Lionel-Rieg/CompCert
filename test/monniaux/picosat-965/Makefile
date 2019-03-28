EXECUTE_ARGS=sudoku.sat

include ../rules.mk

ALL_CFLAGS = -DNDEBUG
EMBEDDED_CFLAGS = -DNALARM -DNZIP -DNGETRUSAGE
K1C_CFLAGS += $(EMBEDDED_CFLAGS)
K1C_CCOMPFLAGS += $(EMBEDDED_CFLAGS)
CCOMPFLAGS += -fbitfields
K1C_CCOMPFLAGS += -fbitfields

K1C_CFLAGS += $(ALL_CFLAGS)
K1C_CCOMPFLAGS += $(ALL_CFLAGS)
CCOMPFLAGS += $(ALL_CFLAGS)
CFLAGS += $(ALL_CFLAGS)

all: picosat.ccomp.k1c.s version.ccomp.k1c.s app.ccomp.k1c.s main.ccomp.k1c.s picosat.gcc.k1c.s version.gcc.k1c.s app.gcc.k1c.s main.gcc.k1c.s picosat.ccomp.k1c.out picosat.gcc.k1c.out picosat.ccomp.host.out picosat.gcc.host.out

picosat.ccomp.k1c : picosat.ccomp.k1c.s version.ccomp.k1c.s app.ccomp.k1c.s main.ccomp.k1c.s ../clock.gcc.k1c.o
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) $+ -o $@

picosat.gcc.k1c : picosat.gcc.k1c.s version.gcc.k1c.s app.gcc.k1c.s main.gcc.k1c.s ../clock.gcc.k1c.o
	$(K1C_CC) $(K1C_CFLAGS) $+ -o $@

picosat.ccomp.host : picosat.ccomp.host.s version.ccomp.host.s app.ccomp.host.s main.ccomp.host.s ../clock.gcc.host.o
	$(CCOMP) $(CCOMPFLAGS) $+ -o $@

picosat.gcc.host : picosat.gcc.host.s version.gcc.host.s app.gcc.host.s main.gcc.host.s ../clock.gcc.host.o
	$(CC) $(FLAGS) $+ -o $@

clean:
	-rm -f *.s *.k1c *.out

.PHONY: clean
