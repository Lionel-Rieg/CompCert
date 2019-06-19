SHELL := /bin/bash

K1CC ?= k1-cos-gcc
CC ?= gcc
CCOMP ?= ccomp
CFLAGS ?= -O2 -Wno-varargs
SIMU ?= k1-mppa
TIMEOUT ?= --signal=SIGTERM 120s

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

K1CCPATH=$(shell which $(K1CC))
CCPATH=$(shell which $(CC))
CCOMPPATH=$(shell which $(CCOMP))
SIMUPATH=$(shell which $(SIMU))

TESTNAMES ?= $(filter-out $(VAARG_COMMON),$(filter-out $(COMMON),$(notdir $(subst .c,,$(wildcard $(DIR)/*.c)))))

X86_GCC_OUT=$(addprefix $(OUTDIR)/,$(addsuffix .x86-gcc.out,$(TESTNAMES)))
GCC_OUT=$(addprefix $(OUTDIR)/,$(addsuffix .gcc.out,$(TESTNAMES)))
GCC_REV_OUT=$(addprefix $(OUTDIR)/,$(addsuffix .gcc.rev.out,$(TESTNAMES)))
CCOMP_OUT=$(addprefix $(OUTDIR)/,$(addsuffix .ccomp.out,$(TESTNAMES)))

VAARG_X86_GCC_OUT=$(addprefix $(OUTDIR)/,$(addsuffix .x86-gcc.vaarg.out,$(TESTNAMES)))
VAARG_GCC_OUT=$(addprefix $(OUTDIR)/,$(addsuffix .gcc.vaarg.out,$(TESTNAMES)))
VAARG_GCC_REV_OUT=$(addprefix $(OUTDIR)/,$(addsuffix .gcc.rev.vaarg.out,$(TESTNAMES)))
VAARG_CCOMP_OUT=$(addprefix $(OUTDIR)/,$(addsuffix .ccomp.vaarg.out,$(TESTNAMES)))

OUT=$(X86_GCC_OUT) $(GCC_OUT) $(CCOMP_OUT) $(GCC_REV_OUT)\
		$(VAARG_GCC_OUT) $(VAARG_GCC_OUT) $(VAARG_CCOMP_OUT) $(VAARG_GCC_REV_OUT)
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
test: $(X86_GCC_OUT) $(GCC_OUT) $(VAARG_X86_GCC_OUT) $(VAARG_GCC_OUT)
	@echo "Comparing x86 gcc output to k1 gcc.."
	@for test in $(TESTNAMES); do\
		x86out=$(OUTDIR)/$$test.x86-gcc.out;\
		gccout=$(OUTDIR)/$$test.gcc.out;\
		vaarg_x86out=$(OUTDIR)/$$test.x86-gcc.vaarg.out;\
		vaarg_gccout=$(OUTDIR)/$$test.gcc.vaarg.out;\
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
check: $(GCC_OUT) $(CCOMP_OUT) $(GCC_REV_OUT) $(VAARG_GCC_OUT) $(VAARG_CCOMP_OUT) $(VAARG_GCC_REV_OUT)
	@echo "Comparing k1 gcc output to ccomp.."
	@for test in $(TESTNAMES); do\
		gccout=$(OUTDIR)/$$test.gcc.out;\
		ccompout=$(OUTDIR)/$$test.ccomp.out;\
		gccrevout=$(OUTDIR)/$$test.gcc.rev.out;\
		vaarg_gccout=$(OUTDIR)/$$test.gcc.vaarg.out;\
		vaarg_ccompout=$(OUTDIR)/$$test.ccomp.vaarg.out;\
		vaarg_gccrevout=$(OUTDIR)/$$test.gcc.rev.vaarg.out;\
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

$(OUTDIR)/%.gcc.out: $(BINDIR)/%.gcc.bin $(SIMUPATH)
	@mkdir -p $(@D)
	ret=0; timeout $(TIMEOUT) $(SIMU) -- $< > $@ || { ret=$$?; }; echo $$ret >> $@

$(OUTDIR)/%.gcc.rev.out: $(BINDIR)/%.gcc.rev.bin $(SIMUPATH)
	@mkdir -p $(@D)
	ret=0; timeout $(TIMEOUT) $(SIMU) -- $< > $@ || { ret=$$?; }; echo $$ret >> $@

$(OUTDIR)/%.ccomp.out: $(BINDIR)/%.ccomp.bin $(SIMUPATH)
	@mkdir -p $(@D)
	ret=0; timeout $(TIMEOUT) $(SIMU) -- $< > $@ || { ret=$$?; }; echo $$ret >> $@

## With vaarg

$(OUTDIR)/%.x86-gcc.vaarg.out: $(BINDIR)/%.x86-gcc.vaarg.bin
	@mkdir -p $(@D)
	ret=0; timeout $(TIMEOUT) ./$< > $@ || { ret=$$?; }; echo $$ret >> $@

$(OUTDIR)/%.gcc.vaarg.out: $(BINDIR)/%.gcc.vaarg.bin $(SIMUPATH)
	@mkdir -p $(@D)
	ret=0; timeout $(TIMEOUT) $(SIMU) -- $< > $@ || { ret=$$?; }; echo $$ret >> $@

$(OUTDIR)/%.gcc.rev.vaarg.out: $(BINDIR)/%.gcc.rev.vaarg.bin $(SIMUPATH)
	@mkdir -p $(@D)
	ret=0; timeout $(TIMEOUT) $(SIMU) -- $< > $@ || { ret=$$?; }; echo $$ret >> $@

$(OUTDIR)/%.ccomp.vaarg.out: $(BINDIR)/%.ccomp.vaarg.bin $(SIMUPATH)
	@mkdir -p $(@D)
	ret=0; timeout $(TIMEOUT) $(SIMU) -- $< > $@ || { ret=$$?; }; echo $$ret >> $@

##
# Object to binary
##

## common

$(BINDIR)/$(COMMON).x86-gcc.bin: $(OBJDIR)/$(COMMON).x86-gcc.o $(CCPATH)
	@mkdir -p $(@D)
	$(CC) $(CFLAGS) $< -o $@

$(BINDIR)/$(COMMON).gcc.bin: $(OBJDIR)/$(COMMON).gcc.o $(K1CCPATH)
	@mkdir -p $(@D)
	$(K1CC) $(CFLAGS) $< -o $@

$(BINDIR)/$(COMMON).ccomp.bin: $(OBJDIR)/$(COMMON).ccomp.o $(CCOMPPATH)
	@mkdir -p $(@D)
	$(CCOMP) $(CFLAGS) $< -o $@

## vaarg_common

$(BINDIR)/$(VAARG_COMMON).x86-gcc.bin: $(OBJDIR)/$(VAARG_COMMON).x86-gcc.o $(CCPATH)
	@mkdir -p $(@D)
	$(CC) $(CFLAGS) $< -o $@

$(BINDIR)/$(VAARG_COMMON).gcc.bin: $(OBJDIR)/$(VAARG_COMMON).gcc.o $(K1CCPATH)
	@mkdir -p $(@D)
	$(K1CC) $(CFLAGS) $< -o $@

$(BINDIR)/$(VAARG_COMMON).ccomp.bin: $(OBJDIR)/$(VAARG_COMMON).ccomp.o $(CCOMPPATH)
	@mkdir -p $(@D)
	$(CCOMP) $(CFLAGS) $< -o $@

## no vaarg

$(BINDIR)/%.x86-gcc.bin: $(OBJDIR)/%.x86-gcc.o $(OBJDIR)/$(COMMON).x86-gcc.o $(CCPATH)
	@mkdir -p $(@D)
	$(CC) $(CFLAGS) $(wordlist 1,2,$^) -o $@

$(BINDIR)/%.gcc.bin: $(OBJDIR)/%.gcc.o $(OBJDIR)/$(COMMON).gcc.o $(K1CCPATH)
	@mkdir -p $(@D)
	$(K1CC) $(CFLAGS) $(wordlist 1,2,$^) -o $@

$(BINDIR)/%.gcc.rev.bin: $(OBJDIR)/%.gcc.o $(OBJDIR)/$(COMMON).ccomp.o $(K1CCPATH)
	@mkdir -p $(@D)
	$(CCOMP) $(CFLAGS) $(wordlist 1,2,$^) -o $@

$(BINDIR)/%.ccomp.bin: $(OBJDIR)/%.ccomp.o $(OBJDIR)/$(COMMON).gcc.o $(CCOMPPATH)
	@mkdir -p $(@D)
	$(CCOMP) $(CFLAGS) $(wordlist 1,2,$^) -o $@

## with vaarg

$(BINDIR)/%.x86-gcc.vaarg.bin: $(OBJDIR)/%.x86-gcc.o $(OBJDIR)/$(VAARG_COMMON).x86-gcc.o $(CCPATH)
	@mkdir -p $(@D)
	$(CC) $(CFLAGS) $(wordlist 1,2,$^) -o $@

$(BINDIR)/%.gcc.vaarg.bin: $(OBJDIR)/%.gcc.o $(OBJDIR)/$(VAARG_COMMON).gcc.o $(K1CCPATH)
	@mkdir -p $(@D)
	$(K1CC) $(CFLAGS) $(wordlist 1,2,$^) -o $@

$(BINDIR)/%.gcc.rev.vaarg.bin: $(OBJDIR)/%.gcc.o $(OBJDIR)/$(VAARG_COMMON).ccomp.o $(K1CCPATH)
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

$(OBJDIR)/%.gcc.o: $(ASMDIR)/%.gcc.s $(K1CCPATH)
	@mkdir -p $(@D)
	$(K1CC) -c $(CFLAGS) $< -o $@

$(OBJDIR)/%.ccomp.o: $(ASMDIR)/%.ccomp.s $(CCOMPPATH)
	@mkdir -p $(@D)
	$(CCOMP) -c $(CFLAGS) $< -o $@


##
# Source to assembly
##

$(ASMDIR)/%.x86-gcc.s: $(SRCDIR)/%.c $(CCPATH)
	@mkdir -p $(@D)
	$(CC) $(CFLAGS) -S $< -o $@

$(ASMDIR)/%.gcc.s: $(SRCDIR)/%.c $(K1CCPATH)
	@mkdir -p $(@D)
	$(K1CC) $(CFLAGS) -S $< -o $@

$(ASMDIR)/%.ccomp.s: $(SRCDIR)/%.c $(CCOMPPATH)
	@mkdir -p $(@D)
	$(CCOMP) $(CFLAGS) -S $< -o $@
