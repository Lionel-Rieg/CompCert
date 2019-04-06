all:	pcre2test.gcc.k1c.out pcre2test.ccomp.k1c.out

ALL_CFLAGS = -DHAVE_CONFIG_H -DPCRE2_CODE_UNIT_WIDTH=8 
EXECUTE_ARGS = testdata/testinput6

include ../rules.mk

CFILES = \
       pcre2_auto_possess.c \
       pcre2_chartables.c \
       pcre2_compile.c \
       pcre2_config.c \
       pcre2_context.c \
       pcre2_convert.c \
       pcre2_dfa_match.c \
       pcre2_error.c \
       pcre2_extuni.c \
       pcre2_find_bracket.c \
       pcre2_jit_compile.c \
       pcre2_maketables.c \
       pcre2_match.c \
       pcre2_match_data.c \
       pcre2_newline.c \
       pcre2_ord2utf.c \
       pcre2_pattern_info.c \
       pcre2_serialize.c \
       pcre2_string_utils.c \
       pcre2_study.c \
       pcre2_substitute.c \
       pcre2_substring.c \
       pcre2_tables.c \
       pcre2_ucd.c \
       pcre2_valid_utf.c \
       pcre2_xclass.c \
       pcre2posix.c \
       pcre2test.c \
       bsp_frequency.c

HFILES = config.h  pcre2_internal.h    pcre2posix.h \
pcre2.h   pcre2_intmodedep.h  pcre2_ucp.h


K1C_GCC_OFILES=$(CFILES:.c=.gcc.k1c.o)
K1C_CCOMP_OFILES=$(CFILES:.c=.ccomp.k1c.o)

$(K1C_GCC_OFILES) $(K1C_CCOMP_OFILES): $(HFILES)

pcre2test.gcc.k1c: $(K1C_GCC_OFILES)
	$(K1C_CC) $(K1C_CFLAGS) -o $@ $+ ../clock.gcc.k1c.o

pcre2test.ccomp.k1c: $(K1C_CCOMP_OFILES)
	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) -o $@ $+ ../clock.gcc.k1c.o

.PHONY: clean

clean:
	rm -f *.s *.o *.k1c
