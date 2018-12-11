K1CC ?= k1-mbr-gcc
CC ?= gcc
CCOMP ?= ccomp
OPTIM ?= -O2
CFLAGS ?= $(OPTIM) -Wl,--wrap=printf
SIMU ?= k1-mppa
TIMEOUT ?= --signal=SIGTERM 120s

DIR=./
SRCDIR=$(DIR)
OUTDIR=$(DIR)/out
BINDIR=$(DIR)/bin
ASMDIR=$(DIR)/asm
LIB=../lib/system.x86-gcc.a
K1LIB=../lib/system.gcc.a

##
# Intended flow : .c -> .gcc.s -> .gcc.bin -> .gcc.out
#                    -> .ccomp.s -> .ccomp.bin -> .ccomp.out
##

K1CCPATH=$(shell which $(K1CC))
CCPATH=$(shell which $(CC))
CCOMPPATH=$(shell which $(CCOMP))
SIMUPATH=$(shell which $(SIMU))

TESTNAMES?=$(notdir $(subst .c,,$(wildcard $(DIR)/*.c)))
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

GREEN=\033[0;32m
RED=\033[0;31m
NC=\033[0m

.PHONY: 
test: $(X86_GCC_OUT) $(GCC_OUT)
	@echo "Comparing x86 gcc output to k1 gcc.."
	@for test in $(TESTNAMES); do\
		x86out=$(OUTDIR)/$$test.x86-gcc.out;\
		gccout=$(OUTDIR)/$$test.gcc.out;\
		if diff -q $$x86out $$gccout > /dev/null; test $${PIPESTATUS[0]} -ne 0; then\
			>&2 printf "$(RED)ERROR: $$x86out and $$gccout differ$(NC)\n";\
		else\
			printf "$(GREEN)GOOD: $$x86out and $$gccout concur$(NC)\n";\
		fi;\
	done

.PHONY:
check: $(GCC_OUT) $(CCOMP_OUT)
	@echo "Comparing k1 gcc output to ccomp.."
	@for test in $(TESTNAMES); do\
		gccout=$(OUTDIR)/$$test.gcc.out;\
		ccompout=$(OUTDIR)/$$test.ccomp.out;\
		if diff -q $$ccompout $$gccout > /dev/null; test $${PIPESTATUS[0]} -ne 0; then\
			>&2 printf "$(RED)ERROR: $$ccompout and $$gccout differ$(NC)\n";\
		else\
			printf "$(GREEN)GOOD: $$ccompout and $$gccout concur$(NC)\n";\
		fi;\
	done

##
# Rules
##

.SECONDARY:
$(LIB):
	(cd $(dir $(LIB)) && make)

$(K1LIB):
	(cd $(dir $(LIB)) && make)

# Generating output

## Version avec timeout
$(OUTDIR)/%.x86-gcc.out: $(BINDIR)/%.x86-gcc.bin
	@mkdir -p $(@D)
	ret=0; timeout $(TIMEOUT) ./$< > $@ || { ret=$$?; }; echo $$ret >> $@

$(OUTDIR)/%.gcc.out: $(BINDIR)/%.gcc.bin $(SIMUPATH)
	@mkdir -p $(@D)
	ret=0; timeout $(TIMEOUT) $(SIMU) -- $< > $@ || { ret=$$?; }; echo $$ret >> $@

$(OUTDIR)/%.ccomp.out: $(BINDIR)/%.ccomp.bin $(SIMUPATH)
	@mkdir -p $(@D)
	ret=0; timeout $(TIMEOUT) $(SIMU) -- $< > $@ || { ret=$$?; }; echo $$ret >> $@

# Assembly to binary

$(BINDIR)/%.x86-gcc.bin: $(ASMDIR)/%.x86-gcc.s $(LIB) $(CCPATH)
	@mkdir -p $(@D)
	$(CC) $(CFLAGS) $(filter-out $(CCPATH),$^) -o $@

$(BINDIR)/%.gcc.bin: $(ASMDIR)/%.gcc.s $(K1LIB) $(K1CCPATH)
	@mkdir -p $(@D)
	$(K1CC) $(CFLAGS) $(filter-out $(K1CCPATH),$^) -o $@

$(BINDIR)/%.ccomp.bin: $(ASMDIR)/%.ccomp.s $(K1LIB) $(CCOMPPATH)
	@mkdir -p $(@D)
	$(CCOMP) $(CFLAGS) $(filter-out $(CCOMPPATH),$^) -o $@

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
