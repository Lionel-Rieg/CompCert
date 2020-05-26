SHELL := /bin/bash

KVXC ?= k1-cos-gcc
CC ?= gcc
CCOMP ?= ccomp
CFLAGS ?= -O2 -Wno-varargs
SIMU ?= k1-mppa
TIMEOUT ?= --signal=SIGTERM 120s
HARDRUN ?= k1-jtag-runner

DIR=./
SRCDIR=$(DIR)
OUTDIR=$(DIR)/out
BINDIR=$(DIR)/bin
ASMDIR=$(DIR)/asm
OBJDIR=$(DIR)/obj
COMMON=common
VAARG_COMMON=vaarg_common

##
# Intended flow : .c -> .gcc.s -> .gcc.o -> .gcc.bin -> .gcc.out
#                    -> .ccomp.s -> .ccomp.o -> .ccomp.bin -> .ccomp.out
#                    -> .x86-gcc.s -> .x86-gcc.o -> .x86-gcc.bin -> .x86-gcc.out
#
# The .o -> .bin part uses $(COMMON).gcc.o or $(COMMON).x86-gcc.o depending on the architecture
# There is also a $(VAARG_COMMON) that is the same than $(COMMON) but with va_arg
##

KVXCPATH=$(shell which $(KVXC))
CCPATH=$(shell which $(CC))
CCOMPPATH=$(shell which $(CCOMP))
SIMUPATH=$(shell which $(SIMU))

TESTNAMES ?= $(filter-out $(VAARG_COMMON),$(filter-out $(COMMON),$(notdir $(subst .c,,$(wildcard $(DIR)/*.c)))))

X86_GCC_OUT=$(addprefix $(OUTDIR)/,$(addsuffix .x86-gcc.out,$(TESTNAMES)))
GCC_SIMUOUT=$(addprefix $(OUTDIR)/,$(addsuffix .gcc.simu.out,$(TESTNAMES)))
GCC_REV_SIMUOUT=$(addprefix $(OUTDIR)/,$(addsuffix .gcc.rev.simu.out,$(TESTNAMES)))
CCOMP_SIMUOUT=$(addprefix $(OUTDIR)/,$(addsuffix .ccomp.simu.out,$(TESTNAMES)))

GCC_HARDOUT=$(addprefix $(OUTDIR)/,$(addsuffix .gcc.hard.out,$(TESTNAMES)))
GCC_REV_HARDOUT=$(addprefix $(OUTDIR)/,$(addsuffix .gcc.rev.hard.out,$(TESTNAMES)))
CCOMP_HARDOUT=$(addprefix $(OUTDIR)/,$(addsuffix .ccomp.hard.out,$(TESTNAMES)))

VAARG_X86_GCC_OUT=$(addprefix $(OUTDIR)/,$(addsuffix .x86-gcc.vaarg.out,$(TESTNAMES)))
VAARG_GCC_SIMUOUT=$(addprefix $(OUTDIR)/,$(addsuffix .gcc.vaarg.simu.out,$(TESTNAMES)))
VAARG_GCC_REV_SIMUOUT=$(addprefix $(OUTDIR)/,$(addsuffix .gcc.rev.vaarg.simu.out,$(TESTNAMES)))
VAARG_CCOMP_SIMUOUT=$(addprefix $(OUTDIR)/,$(addsuffix .ccomp.vaarg.simu.out,$(TESTNAMES)))

VAARG_GCC_HARDOUT=$(addprefix $(OUTDIR)/,$(addsuffix .gcc.vaarg.hard.out,$(TESTNAMES)))
VAARG_GCC_REV_HARDOUT=$(addprefix $(OUTDIR)/,$(addsuffix .gcc.rev.vaarg.hard.out,$(TESTNAMES)))
VAARG_CCOMP_HARDOUT=$(addprefix $(OUTDIR)/,$(addsuffix .ccomp.vaarg.hard.out,$(TESTNAMES)))

BIN=$(addprefix $(BINDIR)/,$(addsuffix .x86-gcc.bin,$(TESTNAMES)))\
	$(addprefix $(BINDIR)/,$(addsuffix .gcc.bin,$(TESTNAMES)))\
	$(addprefix $(BINDIR)/,$(addsuffix .ccomp.bin,$(TESTNAMES)))\
	$(addprefix $(BINDIR)/,$(addsuffix .gcc.rev.bin,$(TESTNAMES)))\
	$(addprefix $(BINDIR)/,$(addsuffix .x86-gcc.vaarg.bin,$(TESTNAMES)))\
	$(addprefix $(BINDIR)/,$(addsuffix .gcc.vaarg.bin,$(TESTNAMES)))\
	$(addprefix $(BINDIR)/,$(addsuffix .ccomp.vaarg.bin,$(TESTNAMES)))\
	$(addprefix $(BINDIR)/,$(addsuffix .gcc.rev.vaarg.bin,$(TESTNAMES)))

##
# Targets
##

all: $(BIN)

GREEN=\033[0;32m
RED=\033[0;31m
NC=\033[0m

.PHONY:
test: simutest

.PHONY:
simutest: $(X86_GCC_OUT) $(GCC_SIMUOUT) $(VAARG_X86_GCC_OUT) $(VAARG_GCC_SIMUOUT)
	@echo "Comparing x86 gcc output to k1 gcc.."
	@for test in $(TESTNAMES); do\
		x86out=$(OUTDIR)/$$test.x86-gcc.out;\
		gccout=$(OUTDIR)/$$test.gcc.simu.out;\
		vaarg_x86out=$(OUTDIR)/$$test.x86-gcc.vaarg.out;\
		vaarg_gccout=$(OUTDIR)/$$test.gcc.vaarg.simu.out;\
		if ! diff $$x86out $$gccout > /dev/null; then\
			>&2 printf "$(RED)ERROR: $$x86out and $$gccout differ$(NC)\n";\
		else\
			printf "$(GREEN)GOOD: $$x86out and $$gccout concur$(NC)\n";\
		fi;\
		if ! diff $$vaarg_x86out $$vaarg_gccout > /dev/null; then\
			>&2 printf "$(RED)ERROR: $$vaarg_x86out and $$vaarg_gccout differ$(NC)\n";\
		else\
			printf "$(GREEN)GOOD: $$vaarg_x86out and $$vaarg_gccout concur$(NC)\n";\
		fi;\
	done

.PHONY:
check: simucheck

.PHONY:
simucheck: $(GCC_SIMUOUT) $(CCOMP_SIMUOUT) $(GCC_REV_SIMUOUT) $(VAARG_GCC_SIMUOUT) $(VAARG_CCOMP_SIMUOUT) $(VAARG_GCC_REV_SIMUOUT)
	@echo "Comparing k1 gcc output to ccomp.."
	@for test in $(TESTNAMES); do\
		gccout=$(OUTDIR)/$$test.gcc.simu.out;\
		ccompout=$(OUTDIR)/$$test.ccomp.simu.out;\
		gccrevout=$(OUTDIR)/$$test.gcc.rev.simu.out;\
		vaarg_gccout=$(OUTDIR)/$$test.gcc.vaarg.simu.out;\
		vaarg_ccompout=$(OUTDIR)/$$test.ccomp.vaarg.simu.out;\
		vaarg_gccrevout=$(OUTDIR)/$$test.gcc.rev.vaarg.simu.out;\
		if ! diff $$ccompout $$gccout > /dev/null; then\
			>&2 printf "$(RED)ERROR: $$ccompout and $$gccout differ$(NC)\n";\
		else\
			printf "$(GREEN)GOOD: $$ccompout and $$gccout concur$(NC)\n";\
		fi;\
		if ! diff $$gccrevout $$gccout > /dev/null; then\
			>&2 printf "$(RED)ERROR: $$gccrevout and $$gccout differ$(NC)\n";\
		else\
			printf "$(GREEN)GOOD: $$gccrevout and $$gccout concur$(NC)\n";\
		fi;\
		if ! diff $$vaarg_ccompout $$vaarg_gccout > /dev/null; then\
			>&2 printf "$(RED)ERROR: $$vaarg_ccompout and $$vaarg_gccout differ$(NC)\n";\
		else\
			printf "$(GREEN)GOOD: $$vaarg_ccompout and $$vaarg_gccout concur$(NC)\n";\
		fi;\
		if ! diff $$vaarg_gccrevout $$vaarg_gccout > /dev/null; then\
			>&2 printf "$(RED)ERROR: $$vaarg_gccrevout and $$vaarg_gccout differ$(NC)\n";\
		else\
			printf "$(GREEN)GOOD: $$vaarg_gccrevout and $$vaarg_gccout concur$(NC)\n";\
		fi;\
	done

.PHONY: 
hardtest: $(X86_GCC_OUT) $(GCC_HARDOUT) $(VAARG_X86_GCC_OUT) $(VAARG_GCC_HARDOUT)
	@echo "Comparing x86 gcc output to k1 gcc.."
	@for test in $(TESTNAMES); do\
		x86out=$(OUTDIR)/$$test.x86-gcc.out;\
		gccout=$(OUTDIR)/$$test.gcc.hard.out;\
		vaarg_x86out=$(OUTDIR)/$$test.x86-gcc.vaarg.out;\
		vaarg_gccout=$(OUTDIR)/$$test.gcc.vaarg.hard.out;\
		if ! diff $$x86out $$gccout > /dev/null; then\
			>&2 printf "$(RED)ERROR: $$x86out and $$gccout differ$(NC)\n";\
		else\
			printf "$(GREEN)GOOD: $$x86out and $$gccout concur$(NC)\n";\
		fi;\
		if ! diff $$vaarg_x86out $$vaarg_gccout > /dev/null; then\
			>&2 printf "$(RED)ERROR: $$vaarg_x86out and $$vaarg_gccout differ$(NC)\n";\
		else\
			printf "$(GREEN)GOOD: $$vaarg_x86out and $$vaarg_gccout concur$(NC)\n";\
		fi;\
	done

.PHONY:
hardcheck: $(GCC_HARDOUT) $(CCOMP_HARDOUT) $(GCC_REV_HARDOUT) $(VAARG_GCC_HARDOUT) $(VAARG_CCOMP_HARDOUT) $(VAARG_GCC_REV_HARDOUT)
	@echo "Comparing k1 gcc output to ccomp.."
	@for test in $(TESTNAMES); do\
		gccout=$(OUTDIR)/$$test.gcc.hard.out;\
		ccompout=$(OUTDIR)/$$test.ccomp.hard.out;\
		gccrevout=$(OUTDIR)/$$test.gcc.rev.hard.out;\
		vaarg_gccout=$(OUTDIR)/$$test.gcc.vaarg.hard.out;\
		vaarg_ccompout=$(OUTDIR)/$$test.ccomp.vaarg.hard.out;\
		vaarg_gccrevout=$(OUTDIR)/$$test.gcc.rev.vaarg.hard.out;\
		if ! diff $$ccompout $$gccout > /dev/null; then\
			>&2 printf "$(RED)ERROR: $$ccompout and $$gccout differ$(NC)\n";\
		else\
			printf "$(GREEN)GOOD: $$ccompout and $$gccout concur$(NC)\n";\
		fi;\
		if ! diff $$gccrevout $$gccout > /dev/null; then\
			>&2 printf "$(RED)ERROR: $$gccrevout and $$gccout differ$(NC)\n";\
		else\
			printf "$(GREEN)GOOD: $$gccrevout and $$gccout concur$(NC)\n";\
		fi;\
		if ! diff $$vaarg_ccompout $$vaarg_gccout > /dev/null; then\
			>&2 printf "$(RED)ERROR: $$vaarg_ccompout and $$vaarg_gccout differ$(NC)\n";\
		else\
			printf "$(GREEN)GOOD: $$vaarg_ccompout and $$vaarg_gccout concur$(NC)\n";\
		fi;\
		if ! diff $$vaarg_gccrevout $$vaarg_gccout > /dev/null; then\
			>&2 printf "$(RED)ERROR: $$vaarg_gccrevout and $$vaarg_gccout differ$(NC)\n";\
		else\
			printf "$(GREEN)GOOD: $$vaarg_gccrevout and $$vaarg_gccout concur$(NC)\n";\
		fi;\
	done

##
# Rules
##

.SECONDARY:

##
# Generating output
##

## Version sans les timeout
#$(OUTDIR)/%.x86-gcc.out: $(BINDIR)/%.x86-gcc.bin
#	@mkdir -p $(@D)
#	./$< > $@; echo $$? >> $@
#
#$(OUTDIR)/%.gcc.out: $(BINDIR)/%.gcc.bin $(SIMUPATH)
#	@mkdir -p $(@D)
#	$(SIMU) -- $< > $@ ; echo $$? >> $@
#
#$(OUTDIR)/%.ccomp.out: $(BINDIR)/%.ccomp.bin $(SIMUPATH)
#	@mkdir -p $(@D)
#	$(SIMU) -- $< > $@ ; echo $$? >> $@

## No vaarg

$(OUTDIR)/%.x86-gcc.out: $(BINDIR)/%.x86-gcc.bin
	@mkdir -p $(@D)
	ret=0; timeout $(TIMEOUT) ./$< > $@ || { ret=$$?; }; echo $$ret >> $@

$(OUTDIR)/%.gcc.simu.out: $(BINDIR)/%.gcc.bin $(SIMUPATH)
	@mkdir -p $(@D)
	ret=0; timeout $(TIMEOUT) $(SIMU) -- $< > $@ || { ret=$$?; }; echo $$ret >> $@

$(OUTDIR)/%.gcc.rev.simu.out: $(BINDIR)/%.gcc.rev.bin $(SIMUPATH)
	@mkdir -p $(@D)
	ret=0; timeout $(TIMEOUT) $(SIMU) -- $< > $@ || { ret=$$?; }; echo $$ret >> $@

$(OUTDIR)/%.ccomp.simu.out: $(BINDIR)/%.ccomp.bin $(SIMUPATH)
	@mkdir -p $(@D)
	ret=0; timeout $(TIMEOUT) $(SIMU) -- $< > $@ || { ret=$$?; }; echo $$ret >> $@

$(OUTDIR)/%.gcc.hard.out: $(BINDIR)/%.gcc.bin $(SIMUPATH)
	@mkdir -p $(@D)
	ret=0; timeout $(TIMEOUT) $(HARDRUN) --exec-file=Cluster0:$< > $@ || { ret=$$?; }; echo $$ret >> $@

$(OUTDIR)/%.gcc.rev.hard.out: $(BINDIR)/%.gcc.rev.bin $(SIMUPATH)
	@mkdir -p $(@D)
	ret=0; timeout $(TIMEOUT) $(HARDRUN) --exec-file=Cluster0:$< > $@ || { ret=$$?; }; echo $$ret >> $@

$(OUTDIR)/%.ccomp.hard.out: $(BINDIR)/%.ccomp.bin $(SIMUPATH)
	@mkdir -p $(@D)
	ret=0; timeout $(TIMEOUT) $(HARDRUN) --exec-file=Cluster0:$< > $@ || { ret=$$?; }; echo $$ret >> $@

## With vaarg

$(OUTDIR)/%.x86-gcc.vaarg.out: $(BINDIR)/%.x86-gcc.vaarg.bin
	@mkdir -p $(@D)
	ret=0; timeout $(TIMEOUT) ./$< > $@ || { ret=$$?; }; echo $$ret >> $@

$(OUTDIR)/%.gcc.vaarg.simu.out: $(BINDIR)/%.gcc.vaarg.bin $(SIMUPATH)
	@mkdir -p $(@D)
	ret=0; timeout $(TIMEOUT) $(SIMU) -- $< > $@ || { ret=$$?; }; echo $$ret >> $@

$(OUTDIR)/%.gcc.rev.vaarg.simu.out: $(BINDIR)/%.gcc.rev.vaarg.bin $(SIMUPATH)
	@mkdir -p $(@D)
	ret=0; timeout $(TIMEOUT) $(SIMU) -- $< > $@ || { ret=$$?; }; echo $$ret >> $@

$(OUTDIR)/%.ccomp.vaarg.simu.out: $(BINDIR)/%.ccomp.vaarg.bin $(SIMUPATH)
	@mkdir -p $(@D)
	ret=0; timeout $(TIMEOUT) $(SIMU) -- $< > $@ || { ret=$$?; }; echo $$ret >> $@

$(OUTDIR)/%.gcc.vaarg.hard.out: $(BINDIR)/%.gcc.vaarg.bin $(SIMUPATH)
	@mkdir -p $(@D)
	ret=0; timeout $(TIMEOUT) $(HARDRUN) --exec-file=Cluster0:$< > $@ || { ret=$$?; }; echo $$ret >> $@

$(OUTDIR)/%.gcc.rev.vaarg.hard.out: $(BINDIR)/%.gcc.rev.vaarg.bin $(SIMUPATH)
	@mkdir -p $(@D)
	ret=0; timeout $(TIMEOUT) $(HARDRUN) --exec-file=Cluster0:$< > $@ || { ret=$$?; }; echo $$ret >> $@

$(OUTDIR)/%.ccomp.vaarg.hard.out: $(BINDIR)/%.ccomp.vaarg.bin $(SIMUPATH)
	@mkdir -p $(@D)
	ret=0; timeout $(TIMEOUT) $(HARDRUN) --exec-file=Cluster0:$< > $@ || { ret=$$?; }; echo $$ret >> $@

##
# Object to binary
##

## common

$(BINDIR)/$(COMMON).x86-gcc.bin: $(OBJDIR)/$(COMMON).x86-gcc.o $(CCPATH)
	@mkdir -p $(@D)
	$(CC) $(CFLAGS) $< -o $@

$(BINDIR)/$(COMMON).gcc.bin: $(OBJDIR)/$(COMMON).gcc.o $(KVXCPATH)
	@mkdir -p $(@D)
	$(KVXC) $(CFLAGS) $< -o $@

$(BINDIR)/$(COMMON).ccomp.bin: $(OBJDIR)/$(COMMON).ccomp.o $(CCOMPPATH)
	@mkdir -p $(@D)
	$(CCOMP) $(CFLAGS) $< -o $@

## vaarg_common

$(BINDIR)/$(VAARG_COMMON).x86-gcc.bin: $(OBJDIR)/$(VAARG_COMMON).x86-gcc.o $(CCPATH)
	@mkdir -p $(@D)
	$(CC) $(CFLAGS) $< -o $@

$(BINDIR)/$(VAARG_COMMON).gcc.bin: $(OBJDIR)/$(VAARG_COMMON).gcc.o $(KVXCPATH)
	@mkdir -p $(@D)
	$(KVXC) $(CFLAGS) $< -o $@

$(BINDIR)/$(VAARG_COMMON).ccomp.bin: $(OBJDIR)/$(VAARG_COMMON).ccomp.o $(CCOMPPATH)
	@mkdir -p $(@D)
	$(CCOMP) $(CFLAGS) $< -o $@

## no vaarg

$(BINDIR)/%.x86-gcc.bin: $(OBJDIR)/%.x86-gcc.o $(OBJDIR)/$(COMMON).x86-gcc.o $(CCPATH)
	@mkdir -p $(@D)
	$(CC) $(CFLAGS) $(wordlist 1,2,$^) -o $@

$(BINDIR)/%.gcc.bin: $(OBJDIR)/%.gcc.o $(OBJDIR)/$(COMMON).gcc.o $(KVXCPATH)
	@mkdir -p $(@D)
	$(KVXC) $(CFLAGS) $(wordlist 1,2,$^) -o $@

$(BINDIR)/%.gcc.rev.bin: $(OBJDIR)/%.gcc.o $(OBJDIR)/$(COMMON).ccomp.o $(KVXCPATH)
	@mkdir -p $(@D)
	$(CCOMP) $(CFLAGS) $(wordlist 1,2,$^) -o $@

$(BINDIR)/%.ccomp.bin: $(OBJDIR)/%.ccomp.o $(OBJDIR)/$(COMMON).gcc.o $(CCOMPPATH)
	@mkdir -p $(@D)
	$(CCOMP) $(CFLAGS) $(wordlist 1,2,$^) -o $@

## with vaarg

$(BINDIR)/%.x86-gcc.vaarg.bin: $(OBJDIR)/%.x86-gcc.o $(OBJDIR)/$(VAARG_COMMON).x86-gcc.o $(CCPATH)
	@mkdir -p $(@D)
	$(CC) $(CFLAGS) $(wordlist 1,2,$^) -o $@

$(BINDIR)/%.gcc.vaarg.bin: $(OBJDIR)/%.gcc.o $(OBJDIR)/$(VAARG_COMMON).gcc.o $(KVXCPATH)
	@mkdir -p $(@D)
	$(KVXC) $(CFLAGS) $(wordlist 1,2,$^) -o $@

$(BINDIR)/%.gcc.rev.vaarg.bin: $(OBJDIR)/%.gcc.o $(OBJDIR)/$(VAARG_COMMON).ccomp.o $(KVXCPATH)
	@mkdir -p $(@D)
	$(CCOMP) $(CFLAGS) $(wordlist 1,2,$^) -o $@

$(BINDIR)/%.ccomp.vaarg.bin: $(OBJDIR)/%.ccomp.o $(OBJDIR)/$(VAARG_COMMON).gcc.o $(CCOMPPATH)
	@mkdir -p $(@D)
	$(CCOMP) $(CFLAGS) $(wordlist 1,2,$^) -o $@

##
# Assembly to object
##

$(OBJDIR)/%.x86-gcc.o: $(ASMDIR)/%.x86-gcc.s $(CCPATH)
	@mkdir -p $(@D)
	$(CC) -c $(CFLAGS) $< -o $@

$(OBJDIR)/%.gcc.o: $(ASMDIR)/%.gcc.s $(KVXCPATH)
	@mkdir -p $(@D)
	$(KVXC) -c $(CFLAGS) $< -o $@

$(OBJDIR)/%.ccomp.o: $(ASMDIR)/%.ccomp.s $(CCOMPPATH)
	@mkdir -p $(@D)
	$(CCOMP) -c $(CFLAGS) $< -o $@


##
# Source to assembly
##

$(ASMDIR)/%.x86-gcc.s: $(SRCDIR)/%.c $(CCPATH)
	@mkdir -p $(@D)
	$(CC) $(CFLAGS) -S $< -o $@

$(ASMDIR)/%.gcc.s: $(SRCDIR)/%.c $(KVXCPATH)
	@mkdir -p $(@D)
	$(KVXC) $(CFLAGS) -S $< -o $@

$(ASMDIR)/%.ccomp.s: $(SRCDIR)/%.c $(CCOMPPATH)
	@mkdir -p $(@D)
	$(CCOMP) $(CFLAGS) -S $< -o $@
