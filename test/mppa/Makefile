DIR=general
TESTNAMES=simple call branch for forvar forvarl branchz branchzu

CCOMP=../../ccomp
TESTS=$(addprefix $(DIR)/,$(TESTNAMES))
ELF=$(addsuffix .bin,$(TESTS))
TOK=$(addsuffix .tok,$(TESTS))
ASM=$(addsuffix .s,$(TESTS))
DEBUG:=$(if $(DEBUG),"-dall",)

all: $(ELF)

nobin: $(ASM)

$(DIR)/%.bin: $(DIR)/%.s
	k1-gcc $< -o $@

.SECONDARY:
$(DIR)/%.s: $(DIR)/%.c $(CCOMP)
	ccomp $(DEBUG) -O0 -v -S $< -o $@

$(DIR)/%.tok: $(DIR)/%.bin
	@bash check.sh $< $@

.PHONY: FORCE
FORCE:

.PHONY:
check: $(TOK)

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
	rm -f $(DIR)/*.s
	rm -f $(DIR)/*.tok
	rm -f $(DIR)/output/*.out
	rm -rf $(DIR)/profile/
	rm -f $(ELF)
