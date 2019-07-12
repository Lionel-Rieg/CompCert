# This Makefile does not depend on ../rules.mk
SHELL=bash

# You can modify ALL_CFILES to include the files that should be linked
ALL_CFILES=$(wildcard *.c)

# Name of the target
TARGET=toto

# Name of the clock object
CLOCK=../clock.gcc.k1c.o

# Maximum amount of time measures (see cycles.h)
MAX_MEASURES=10

# Flags common to both compilers, then to gcc, then to ccomp
ALL_CFLAGS=-g -Wall -D__K1C_COS__ -DMAX_MEASURES=$(MAX_MEASURES)
ALL_GCCFLAGS=$(ALL_CFLAGS) -std=c99 -Wextra -Werror=implicit
ALL_CCOMPFLAGS=$(ALL_CFLAGS)

# The compilers
K1C_CC=k1-cos-gcc
K1C_CCOMP=ccomp

# Command to execute
EXECUTE_CYCLES=k1-cluster --syscall=libstd_scalls.so --cycle-based --

# You can define up to GCC4FLAGS and CCOMP4FLAGS
GCC0FLAGS=$(ALL_GCCFLAGS) -O0
GCC1FLAGS=$(ALL_GCCFLAGS) -O1
GCC2FLAGS=$(ALL_GCCFLAGS) -O2
GCC3FLAGS=$(ALL_GCCFLAGS) -O3
GCC4FLAGS=
CCOMP0FLAGS=$(ALL_CCOMPFLAGS) -O0
CCOMP1FLAGS=$(ALL_CCOMPFLAGS) -fno-postpass
CCOMP2FLAGS=$(ALL_CCOMPFLAGS)
CCOMP3FLAGS=
CCOMP4FLAGS=

# Prefix names
GCC0PREFIX=.gcc.o0
GCC1PREFIX=.gcc.o1
GCC2PREFIX=.gcc.o2
GCC3PREFIX=.gcc.o3
GCC4PREFIX=
CCOMP0PREFIX=.ccomp.o0
CCOMP1PREFIX=.ccomp.o1
CCOMP2PREFIX=.ccomp.o2
CCOMP3PREFIX=
CCOMP4PREFIX=

# List of outfiles, updated by gen_rules
OUTFILES:=

# First line of the CSV file
FIRSTLINE:=benches

firstrule: all

# $1: compiler
# $2: compilation flags
# $3: extension prefix
define gen_rules

.SECONDARY:
%$(3).s: %.c
	$(1) $(2) -S $$< -o $$@

.SECONDARY:
$(TARGET)$(3).bin: $(ALL_CFILES:.c=$(3).o) $(CLOCK)
	$(K1C_CC) $$+ -lm -o $$@

OUTFILES:=$(OUTFILES) $(TARGET)$(3).out
FIRSTLINE:=$(FIRSTLINE), $(3)

endef

# Generic rules
%.o: %.s
	$(K1C_CC) $< -c -o $@

%.out: %.bin
	$(EXECUTE_CYCLES) $< | tee $@

##
# Generating the rules for all the compiler/flags..
##

ifneq ($(GCC0FLAGS),)
$(eval $(call gen_rules,$(K1C_CC),$(GCC0FLAGS),$(GCC0PREFIX)))
endif
ifneq ($(GCC1FLAGS),)
$(eval $(call gen_rules,$(K1C_CC),$(GCC1FLAGS),$(GCC1PREFIX)))
endif
ifneq ($(GCC2FLAGS),)
$(eval $(call gen_rules,$(K1C_CC),$(GCC2FLAGS),$(GCC2PREFIX)))
endif
ifneq ($(GCC3FLAGS),)
$(eval $(call gen_rules,$(K1C_CC),$(GCC3FLAGS),$(GCC3PREFIX)))
endif
ifneq ($(GCC4FLAGS),)
$(eval $(call gen_rules,$(K1C_CC),$(GCC4FLAGS),$(GCC4PREFIX)))
endif

ifneq ($(CCOMP0FLAGS),)
$(eval $(call gen_rules,$(K1C_CCOMP),$(CCOMP0FLAGS),$(CCOMP0PREFIX)))
endif
ifneq ($(CCOMP1FLAGS),)
$(eval $(call gen_rules,$(K1C_CCOMP),$(CCOMP1FLAGS),$(CCOMP1PREFIX)))
endif
ifneq ($(CCOMP2FLAGS),)
$(eval $(call gen_rules,$(K1C_CCOMP),$(CCOMP2FLAGS),$(CCOMP2PREFIX)))
endif
ifneq ($(CCOMP3FLAGS),)
$(eval $(call gen_rules,$(K1C_CCOMP),$(CCOMP3FLAGS),$(CCOMP3PREFIX)))
endif
ifneq ($(CCOMP4FLAGS),)
$(eval $(call gen_rules,$(K1C_CCOMP),$(CCOMP4FLAGS),$(CCOMP4PREFIX)))
endif

measures.csv: $(OUTFILES)
	@echo $(FIRSTLINE) > $@
	@for ((i=0;i<=$(MAX_MEASURES);i++)) do\
		first=$$(grep "($$i) cycles" $(firstword $(OUTFILES)));\
		if test ! -z "$$first"; then\
			line="$(TARGET) $$i";\
			$(foreach outfile,$(OUTFILES),line="$$line, $$(grep "($$i) cycles" $(outfile) | cut -d':' -f2)"; ):;\
			echo "$$line" >> $@;\
		fi;\
	done;\
	echo "$@ created!"

.PHONY: all clean
all: measures.csv

clean:
	rm -f *.o *.s *.bin *.out

