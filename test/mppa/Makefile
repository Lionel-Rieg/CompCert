DIR=general
BINDIR=bin
ASMDIR=asm
TESTNAMES=$(notdir $(subst .c,,$(wildcard $(DIR)/*.c)))

CCOMP=../../ccomp
ELF=$(addprefix $(DIR)/$(BINDIR)/,$(addsuffix .bin,$(TESTNAMES)))
TOK=$(addprefix $(DIR)/$(BINDIR)/,$(addsuffix .tok,$(TESTNAMES)))
ASM=$(addprefix $(DIR)/$(ASMDIR)/,$(addsuffix .s,$(TESTNAMES)))
DEBUG:=$(if $(DEBUG),"-dall",)

.PHONY: all
all: $(ELF)

nobin: $(ASM)

##
# Assembling CompCert's assembly file
##
$(DIR)/$(BINDIR)/%.bin: $(DIR)/$(ASMDIR)/%.s
	@mkdir -p $(@D)
	ccomp $< -o $@

##
# Compiling the C file with CompCert
##
.SECONDARY:
$(DIR)/$(ASMDIR)/%.s: $(DIR)/%.c $(CCOMP)
	@mkdir -p $(@D)
	ccomp $(DEBUG) -O0 -v -S $< -o $@

##
# A token (.tok) is created if the .bin (created by CompCert) yields the same
# result as the .bin.exp (created by executing the binary compiled with gcc)
##
$(DIR)/$(BINDIR)/%.tok: $(DIR)/$(BINDIR)/%.bin $(DIR)/output/%.bin.exp
	@mkdir -p $(@D)
	@bash check.sh $< $@

##
# Generate .bin.exp : compile with gcc, execute, store the result in .bin.exp
##
$(DIR)/output/%.bin.exp: $(DIR)/%.c
	@bash generate.sh $< $@

.PHONY: FORCE
FORCE:

.PHONY: check
check: $(TOK) sort mmult

##
# A utility displaying which of the pseudo-instructions are covered in the tests
##
.PHONY: coverage
coverage: $(ASM)
	bash coverage.sh $(DIR)/$(ASMDIR)

##
# Different versions of a sorting algorithm
##
.PHONY: sort
sort: FORCE
	(cd sort && make compc-check)

##
# Different versions of a matrix multiply
##
.PHONY: mmult
mmult: FORCE
	(cd mmult && make compc-check)

.PHONY: clean
clean:
	rm -f $(DIR)/*.alloctrace
	rm -f $(DIR)/*.cm
	rm -f $(DIR)/*.compcert.c
	rm -f $(DIR)/*.i
	rm -f $(DIR)/*.light.c
	rm -f $(DIR)/*.ltl
	rm -f $(DIR)/*.mach
	rm -f $(DIR)/*.parsed.c
	rm -f $(DIR)/*.rtl.?
	rm -f $(DIR)/$(ASMDIR)/*.s
	rm -f $(DIR)/$(BINDIR)/*.bin
	rm -f $(DIR)/$(BINDIR)/*.tok
	rm -f $(DIR)/output/*.out
	rm -f $(DIR)/output/*.exp
	rm -rf $(DIR)/profile/
	rm -f $(ELF)
