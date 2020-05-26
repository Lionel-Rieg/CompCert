SHELL := /bin/bash

KVXC ?= k1-cos-gcc
CC ?= gcc
CCOMP ?= ccomp
OPTIM ?= -O2
CFLAGS ?= $(OPTIM)
CCOMPFLAGS ?= $(CFLAGS)
SIMU ?= k1-mppa
TIMEOUT ?= --signal=SIGTERM 120s
DIFF ?= python2.7 floatcmp.py -reltol .00001
HARDRUN ?= k1-jtag-runner

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

KVXCPATH=$(shell which $(KVXC))
CCPATH=$(shell which $(CC))
CCOMPPATH=$(shell which $(CCOMP))
SIMUPATH=$(shell which $(SIMU))

TESTNAMES?=$(notdir $(subst .c,,$(wildcard $(DIR)/*.c)))
X86_GCC_OUT=$(addprefix $(OUTDIR)/,$(addsuffix .x86-gcc.out,$(TESTNAMES)))
GCC_SIMUOUT=$(addprefix $(OUTDIR)/,$(addsuffix .gcc.simu.out,$(TESTNAMES)))
CCOMP_SIMUOUT=$(addprefix $(OUTDIR)/,$(addsuffix .ccomp.simu.out,$(TESTNAMES)))
GCC_HARDOUT=$(addprefix $(OUTDIR)/,$(addsuffix .gcc.hard.out,$(TESTNAMES)))
CCOMP_HARDOUT=$(addprefix $(OUTDIR)/,$(addsuffix .ccomp.hard.out,$(TESTNAMES)))

BIN=$(addprefix $(BINDIR)/,$(addsuffix .x86-gcc.bin,$(TESTNAMES)))\
	$(addprefix $(BINDIR)/,$(addsuffix .gcc.bin,$(TESTNAMES)))\
	$(addprefix $(BINDIR)/,$(addsuffix .ccomp.bin,$(TESTNAMES)))

##
# Targets
##

all: $(BIN)

GREEN=\033[0;32m
RED=\033[0;31m
YELLOW=\033[0;33m
NC=\033[0m

.PHONY:
test: simutest

.PHONY:
check: simucheck

.PHONY: 
simutest: $(X86_GCC_OUT) $(GCC_SIMUOUT)
	@echo "Comparing x86 gcc output to k1 gcc.."
	for test in $(TESTNAMES); do\
		x86out=$(OUTDIR)/$$test.x86-gcc.out;\
		gccout=$(OUTDIR)/$$test.gcc.simu.out;\
		if grep "__KVX__" -q $$test.c; then\
			printf "$(YELLOW)UNTESTED: $$test.c contains an \`#ifdef __KVX__\`\n";\
		elif $(DIFF) $$x86out $$gccout > /dev/null; test $${PIPESTATUS[0]} -ne 0; then\
			>&2 printf "$(RED)ERROR: $$x86out and $$gccout differ$(NC)\n";\
		else\
			printf "$(GREEN)GOOD: $$x86out and $$gccout concur$(NC)\n";\
		fi;\
	done

.PHONY:
simucheck: $(GCC_SIMUOUT) $(CCOMP_SIMUOUT)
	@echo "Comparing k1 gcc output to ccomp.."
	@for test in $(TESTNAMES); do\
		gccout=$(OUTDIR)/$$test.gcc.simu.out;\
		ccompout=$(OUTDIR)/$$test.ccomp.simu.out;\
		if $(DIFF) $$ccompout $$gccout > /dev/null; test $${PIPESTATUS[0]} -ne 0; then\
			>&2 printf "$(RED)ERROR: $$ccompout and $$gccout differ$(NC)\n";\
		else\
			printf "$(GREEN)GOOD: $$ccompout and $$gccout concur$(NC)\n";\
		fi;\
	done

.PHONY: 
hardtest: $(X86_GCC_OUT) $(GCC_HARDOUT)
	@echo "Comparing x86 gcc output to k1 gcc.."
	for test in $(TESTNAMES); do\
		x86out=$(OUTDIR)/$$test.x86-gcc.out;\
		gccout=$(OUTDIR)/$$test.gcc.hard.out;\
		if grep "__KVX__" -q $$test.c; then\
			printf "$(YELLOW)UNTESTED: $$test.c contains an \`#ifdef __KVX__\`\n";\
		elif $(DIFF) $$x86out $$gccout > /dev/null; test $${PIPESTATUS[0]} -ne 0; then\
			>&2 printf "$(RED)ERROR: $$x86out and $$gccout differ$(NC)\n";\
		else\
			printf "$(GREEN)GOOD: $$x86out and $$gccout concur$(NC)\n";\
		fi;\
	done

.PHONY:
hardcheck: $(GCC_HARDOUT) $(CCOMP_HARDOUT)
	@echo "Comparing k1 gcc output to ccomp.."
	@for test in $(TESTNAMES); do\
		gccout=$(OUTDIR)/$$test.gcc.hard.out;\
		ccompout=$(OUTDIR)/$$test.ccomp.hard.out;\
		if $(DIFF) $$ccompout $$gccout > /dev/null; test $${PIPESTATUS[0]} -ne 0; then\
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

$(OUTDIR)/%.gcc.simu.out: $(BINDIR)/%.gcc.bin $(SIMUPATH)
	@mkdir -p $(@D)
	ret=0; timeout $(TIMEOUT) $(SIMU) -- $< > $@ || { ret=$$?; }; echo $$ret >> $@

$(OUTDIR)/%.ccomp.simu.out: $(BINDIR)/%.ccomp.bin $(SIMUPATH)
	@mkdir -p $(@D)
	ret=0; timeout $(TIMEOUT) $(SIMU) -- $< > $@ || { ret=$$?; }; echo $$ret >> $@

$(OUTDIR)/%.gcc.hard.out: $(BINDIR)/%.gcc.bin $(SIMUPATH)
	@mkdir -p $(@D)
	ret=0; timeout $(TIMEOUT) $(HARDRUN) --exec-file=Cluster0:$< > $@ || { ret=$$?; }; echo $$ret >> $@

$(OUTDIR)/%.ccomp.hard.out: $(BINDIR)/%.ccomp.bin $(SIMUPATH)
	@mkdir -p $(@D)
	ret=0; timeout $(TIMEOUT) $(HARDRUN) --exec-file=Cluster0:$< > $@ || { ret=$$?; }; echo $$ret >> $@

# Assembly to binary

$(BINDIR)/%.x86-gcc.bin: $(ASMDIR)/%.x86-gcc.s $(LIB) $(CCPATH)
	@mkdir -p $(@D)
	$(CC) $(CFLAGS) $(filter-out $(CCPATH),$^) -o $@

$(BINDIR)/%.gcc.bin: $(ASMDIR)/%.gcc.s $(K1LIB) $(KVXCPATH)
	@mkdir -p $(@D)
	$(KVXC) $(CFLAGS) $(filter-out $(KVXCPATH),$^) -o $@

$(BINDIR)/%.ccomp.bin: $(ASMDIR)/%.ccomp.s $(K1LIB) $(CCOMPPATH)
	@mkdir -p $(@D)
	$(CCOMP) $(CCOMPFLAGS) $(filter-out $(CCOMPPATH),$^) -o $@

# Source to assembly

$(ASMDIR)/%.x86-gcc.s: $(SRCDIR)/%.c $(CCPATH)
	@mkdir -p $(@D)
	$(CC) $(CFLAGS) -S $< -o $@

$(ASMDIR)/%.gcc.s: $(SRCDIR)/%.c $(KVXCPATH)
	@mkdir -p $(@D)
	$(KVXC) $(CFLAGS) -S $< -o $@

$(ASMDIR)/%.ccomp.s: $(SRCDIR)/%.c $(CCOMPPATH)
	@mkdir -p $(@D)
	$(CCOMP) $(CCOMPFLAGS) -S $< -o $@
