DIR=general
TESTNAMES=simple call branch for forvar forvarl

TESTS=$(addprefix $(DIR)/,$(TESTNAMES))
ELF=$(addsuffix .bin,$(TESTS))
ASM=$(addsuffix .s,$(TESTS))
DEBUG:=$(if $(DEBUG),"-dall",)

all: $(ELF)

nobin: $(ASM)

$(DIR)/%.bin: $(DIR)/%.s
	k1-gcc $< -o $@

.SECONDARY:
$(DIR)/%.s: $(DIR)/%.c
	ccomp $(DEBUG) -O0 -v -S $< -o $@

.PHONY:
check: $(ELF)
	bash check.sh $(ELF)

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
	rm -f $(DIR)/output/*.out
	rm -rf $(DIR)/profile/
	rm -f $(ELF)
