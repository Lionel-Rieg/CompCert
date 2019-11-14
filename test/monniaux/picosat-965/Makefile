EXECUTE_ARGS=sudoku.sat
ALL_CFLAGS = -DNALARM -DNZIP -DNGETRUSAGE -DNDEBUG
ALL_CCOMPFLAGS += -fbitfields # -fno-if-conversion
TARGET=picosat
ALL_CFILES=picosat.c version.c app.c main.c

include ../rules.mk

# FIXME - what were these for?
#K1C_CFLAGS += $(EMBEDDED_CFLAGS)
#K1C_CCOMPFLAGS += $(EMBEDDED_CFLAGS)
