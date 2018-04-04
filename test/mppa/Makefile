ELF=simple.bin call.bin branch.bin for.bin
ASM=$(subst .bin,.s,$(ELF))
DEBUG:=$(if $(DEBUG),"-dall",)

all: $(ELF)

nobin: $(ASM)

%.bin: %.s
	k1-gcc $< -o $@

.SECONDARY:
%.s: %.c
	ccomp $(DEBUG) -O0 -v -S $< -o $@

.PHONY:
clean:
	rm -f *.alloctrace
	rm -f *.cm
	rm -f *.compcert.c
	rm -f *.i
	rm -f *.light.c
	rm -f *.ltl
	rm -f *.mach
	rm -f *.parsed.c
	rm -f *.rtl.?
	rm -f *.s
	rm -rf profile/
	rm -f $(ELF)
