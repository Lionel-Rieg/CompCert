ALL_CFLAGS += -I src/amd -I src/colamd -I src/mpl -I src/simplex -I src/api -I src/intopt -I src/minisat -I src/npp -I src/zlib -I src/bflib -I src/env -I src/misc -I src/draft -I src
ALL_CFILES=examples/glpsol.c $(wildcard src/*/*.c)
TARGET=glpk
EXECUTE_ARGS=--math examples/prod.mod

include ../rules.mk
