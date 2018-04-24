DIR=general
BINDIR=bin
ASMDIR=asm
TESTNAMES=simple call branch for forvar forvarl branchz branchzu

CCOMP=../../ccomp
#TESTS=$(addprefix $(DIR)/,$(TESTNAMES))
ELF=$(addprefix $(DIR)/$(BINDIR)/,$(addsuffix .bin,$(TESTNAMES)))
TOK=$(addprefix $(DIR)/$(BINDIR)/,$(addsuffix .tok,$(TESTNAMES)))
ASM=$(addprefix $(DIR)/$(ASMDIR)/,$(addsuffix .s,$(TESTNAMES)))
DEBUG:=$(if $(DEBUG),"-dall",)

all: $(ELF)

nobin: $(ASM)

$(DIR)/$(BINDIR)/%.bin: $(DIR)/$(ASMDIR)/%.s
	@mkdir -p $(@D)
	k1-gcc $< -o $@

.SECONDARY:
$(DIR)/$(ASMDIR)/%.s: $(DIR)/%.c $(CCOMP)
	@mkdir -p $(@D)
	ccomp $(DEBUG) -O0 -v -S $< -o $@

$(DIR)/$(BINDIR)/%.tok: $(DIR)/$(BINDIR)/%.bin $(DIR)/output/%.bin.exp
	@mkdir -p $(@D)
	@bash check.sh $< $@

$(DIR)/output/%.bin.exp: $(DIR)/%.c
	@bash generate.sh $< $@

.PHONY: FORCE
FORCE:

.PHONY:
check: $(TOK) sort mmult

.PHONY:
sort: FORCE
	(cd sort && make compc-check)

.PHONY:
mmult: FORCE
	(cd mmult && make compc-check)

.PHONY:
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
