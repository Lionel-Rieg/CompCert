K1CC ?= k1-mbr-gcc
CC ?= gcc
CCOMP ?= ccomp
CFLAGS ?= -O2
SIMU ?= k1-cluster
TIMEOUT ?= 10s

DIR=./
SRCDIR=$(DIR)
OUTDIR=$(DIR)/out
BINDIR=$(DIR)/bin
ASMDIR=$(DIR)/asm

##
# Intended flow : .c -> .gcc.s -> .gcc.bin -> .gcc.out
#                    -> .ccomp.s -> .ccomp.bin -> .ccomp.out
##

K1CCPATH=$(shell which $(K1CC))
CCPATH=$(shell which $(CC))
CCOMPPATH=$(shell which $(CCOMP))
SIMUPATH=$(shell which $(SIMU))

TESTNAMES=$(notdir $(subst .c,,$(wildcard $(DIR)/*.c)))
X86_GCC_OUT=$(addprefix $(OUTDIR)/,$(addsuffix .x86-gcc.out,$(TESTNAMES)))
GCC_OUT=$(addprefix $(OUTDIR)/,$(addsuffix .gcc.out,$(TESTNAMES)))
CCOMP_OUT=$(addprefix $(OUTDIR)/,$(addsuffix .ccomp.out,$(TESTNAMES)))

OUT=$(X86_GCC_OUT) $(GCC_OUT) $(CCOMP_OUT)
BIN=$(addprefix $(BINDIR)/,$(addsuffix .x86-gcc.bin,$(TESTNAMES)))\
	$(addprefix $(BINDIR)/,$(addsuffix .gcc.bin,$(TESTNAMES)))\
	$(addprefix $(BINDIR)/,$(addsuffix .ccomp.bin,$(TESTNAMES)))

##
# Targets
##

all: $(BIN)

.PHONY:
test: $(X86_GCC_OUT) $(GCC_OUT)
	@echo "Comparing x86 gcc output to k1 gcc.."
	@for test in $(TESTNAMES); do\
		x86out=$(OUTDIR)/$$test.x86-gcc.out;\
		gccout=$(OUTDIR)/$$test.gcc.out;\
		if ! diff $$x86out $$gccout; then\
			>&2 echo "ERROR: $$x86out and $$gccout differ";\
		else\
			echo "GOOD: $$x86out and $$gccout concur";\
		fi;\
	done

.PHONY:
check: $(GCC_OUT) $(CCOMP_OUT)
	@echo "Comparing k1 gcc output to ccomp.."
	@for test in $(TESTNAMES); do\
		gccout=$(OUTDIR)/$$test.gcc.out;\
		ccompout=$(OUTDIR)/$$test.ccomp.out;\
		if ! diff $$ccompout $$gccout; then\
			>&2 echo "ERROR: $$ccompout and $$gccout differ";\
		else\
			echo "GOOD: $$ccompout and $$gccout concur";\
		fi;\
	done

##
# Rules
##

.SECONDARY:
# Generating output

$(OUTDIR)/%.x86-gcc.out: $(BINDIR)/%.x86-gcc.bin
	@mkdir -p $(@D)
	timeout $(TIMEOUT) ./$< || { ret=$$?; } > $@; echo $$ret >> $@

$(OUTDIR)/%.gcc.out: $(BINDIR)/%.gcc.bin $(SIMUPATH)
	@mkdir -p $(@D)
	timeout $(TIMEOUT) $(SIMU) -- $< || { ret=$$?; } > $@; echo $$ret >> $@

$(OUTDIR)/%.ccomp.out: $(BINDIR)/%.ccomp.bin $(SIMUPATH)
	@mkdir -p $(@D)
	timeout $(TIMEOUT) $(SIMU) -- $< || { ret=$$?; } > $@; echo $$ret >> $@

# Assembly to binary

$(BINDIR)/%.x86-gcc.bin: $(ASMDIR)/%.x86-gcc.s $(CCPATH)
	@mkdir -p $(@D)
	$(CC) $(CFLAGS) $< -o $@

$(BINDIR)/%.gcc.bin: $(ASMDIR)/%.gcc.s $(K1CCPATH)
	@mkdir -p $(@D)
	$(K1CC) $(CFLAGS) $< -o $@

$(BINDIR)/%.ccomp.bin: $(ASMDIR)/%.ccomp.s $(CCOMPPATH)
	@mkdir -p $(@D)
	$(CCOMP) $(CFLAGS) $< -o $@

# Source to assembly

$(ASMDIR)/%.x86-gcc.s: $(SRCDIR)/%.c $(CCPATH)
	@mkdir -p $(@D)
	$(CC) $(CFLAGS) -S $< -o $@

$(ASMDIR)/%.gcc.s: $(SRCDIR)/%.c $(K1CCPATH)
	@mkdir -p $(@D)
	$(K1CC) $(CFLAGS) -S $< -o $@

$(ASMDIR)/%.ccomp.s: $(SRCDIR)/%.c $(CCOMPPATH)
	@mkdir -p $(@D)
	$(CCOMP) $(CFLAGS) -S $< -o $@
