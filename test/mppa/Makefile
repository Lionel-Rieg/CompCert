ELF=simple.bin
DEBUG:=$(if $(DEBUG),"-dall",)

all: $(ELF)

%.bin: %.s
	k1-gcc $< -o $@

.SECONDARY:
%.s: %.c
	ccomp $(DEBUG) -v -S $< -o $@

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
