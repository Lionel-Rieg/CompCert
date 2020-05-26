KVXC ?= k1-cos-gcc
K1AR ?= k1-cos-ar
CC ?= gcc
AR ?= gcc-ar
CCOMP ?= ccomp
CFLAGS ?= -O1 -Wl,--wrap=printf
SIMU ?= k1-mppa
TIMEOUT ?= --signal=SIGTERM 60s

DIR=./
SRCDIR=$(DIR)
OUTDIR=$(DIR)/out
BINDIR=$(DIR)/bin
ASMDIR=$(DIR)/asm
OBJDIR=$(DIR)/obj

KVXCPATH=$(shell which $(KVXC))
K1ARPATH=$(shell which $(K1AR))
CCPATH=$(shell which $(CC))
ARPATH=$(shell which $(AR))
SIMUPATH=$(shell which $(SIMU))

TESTNAMES=printf-test
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

all: $(BIN) system.x86-gcc.a system.gcc.a

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

# Object to binary

$(BINDIR)/%.x86-gcc.bin: $(OBJDIR)/%.x86-gcc.o system.x86-gcc.a $(CCPATH)
	@mkdir -p $(@D)
	$(CC) $(CFLAGS) $(filter-out $(CCPATH),$^) -o $@

$(BINDIR)/%.gcc.bin: $(OBJDIR)/%.gcc.o system.gcc.a $(KVXCPATH)
	@mkdir -p $(@D)
	$(KVXC) $(CFLAGS) $(filter-out $(KVXCPATH),$^) -o $@

$(BINDIR)/%.ccomp.bin: $(OBJDIR)/%.ccomp.o system.gcc.a $(CCOMPPATH)
	@mkdir -p $(@D)
	$(CCOMP) $(CFLAGS) $(filter-out $(CCOMPPATH),$^) -o $@

# Generating libraries
system.x86-gcc.a: $(OBJDIR)/printf.x86-gcc.o $(ARPATH)
	$(AR) rcs $@ $<

system.gcc.a: $(OBJDIR)/printf.gcc.o $(K1ARPATH)
	$(K1AR) rcs $@ $<

# Assembly to object

$(OBJDIR)/%.x86-gcc.o: $(ASMDIR)/%.x86-gcc.s $(CCPATH)
	@mkdir -p $(@D)
	$(CC) $(CFLAGS) -c $< -o $@

$(OBJDIR)/%.gcc.o: $(ASMDIR)/%.gcc.s $(KVXCPATH)
	@mkdir -p $(@D)
	$(KVXC) $(CFLAGS) -c $< -o $@

$(OBJDIR)/%.ccomp.o: $(ASMDIR)/%.ccomp.s $(CCOMPPATH)
	$(CCOMP) $(CFLAGS) -c $< -o $@

# Source to assembly

$(ASMDIR)/%.x86-gcc.s: $(SRCDIR)/%.c $(CCPATH)
	@mkdir -p $(@D)
	$(CC) $(CFLAGS) -S $< -o $@

$(ASMDIR)/%.gcc.s: $(SRCDIR)/%.c $(KVXCPATH)
	@mkdir -p $(@D)
	$(KVXC) $(CFLAGS) -S $< -o $@

$(ASMDIR)/%.ccomp.s: $(SRCDIR)/%.c $(CCOMPPATH)
	@mkdir -p $(@D)
	$(CCOMP) $(CFLAGS) -S $< -o $@

