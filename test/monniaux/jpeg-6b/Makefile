TARGET=jpeg-6b

ALL_CFILES= jcapimin.c jcapistd.c jccoefct.c jccolor.c jcdctmgr.c jchuff.c \
        jcinit.c jcmainct.c jcmarker.c jcmaster.c jcomapi.c jcparam.c \
        jcphuff.c jcprepct.c jcsample.c jctrans.c jdapimin.c jdapistd.c \
        jdatadst.c jdatasrc.c jdcoefct.c jdcolor.c jddctmgr.c jdhuff.c \
        jdinput.c jdmainct.c jdmarker.c jdmaster.c jdmerge.c jdphuff.c \
        jdpostct.c jdsample.c jdtrans.c jerror.c jfdctflt.c jfdctfst.c \
        jfdctint.c jidctflt.c jidctfst.c jidctint.c jidctred.c jquant1.c \
        jquant2.c jutils.c jmemmgr.c jmemansi.c
ALL_CFILES+=rdppm.c rdgif.c rdtarga.c rdrle.c rdbmp.c rdswitch.c cdjpeg.c wrppm.c wrgif.c wrtarga.c wrrle.c wrbmp.c rdcolmap.c
ALL_CFILES+=cjpeg.c

EXECUTE_ARGS=-dct int -outfile __BASE__.jpg testimg.ppm 2> __BASE__.out

include ../rules.mk

#all: cjpeg.gcc.k1c.out djpeg.gcc.k1c.out cjpeg.gcc.o1.k1c.out djpeg.gcc.o1.k1c.out cjpeg.ccomp.k1c.out djpeg.ccomp.k1c.out
#
#LIBSOURCES= jcapimin.c jcapistd.c jccoefct.c jccolor.c jcdctmgr.c jchuff.c \
#        jcinit.c jcmainct.c jcmarker.c jcmaster.c jcomapi.c jcparam.c \
#        jcphuff.c jcprepct.c jcsample.c jctrans.c jdapimin.c jdapistd.c \
#        jdatadst.c jdatasrc.c jdcoefct.c jdcolor.c jddctmgr.c jdhuff.c \
#        jdinput.c jdmainct.c jdmarker.c jdmaster.c jdmerge.c jdphuff.c \
#        jdpostct.c jdsample.c jdtrans.c jerror.c jfdctflt.c jfdctfst.c \
#        jfdctint.c jidctflt.c jidctfst.c jidctint.c jidctred.c jquant1.c \
#        jquant2.c jutils.c jmemmgr.c jmemansi.c
#CSOURCES=$(LIBSOURCES) rdppm.c rdgif.c rdtarga.c rdrle.c rdbmp.c rdswitch.c cdjpeg.c wrppm.c wrgif.c wrtarga.c wrrle.c wrbmp.c rdcolmap.c
#
#LIB_K1C_GCC_OFILES=$(CSOURCES:.c=.gcc.k1c.o)
#LIB_K1C_GCC_O1_OFILES=$(CSOURCES:.c=.gcc.o1.k1c.o)
#LIB_K1C_CCOMP_OFILES=$(CSOURCES:.c=.ccomp.k1c.o)
#
#include ../rules.mk
#
#cjpeg.gcc.k1c: $(LIB_K1C_GCC_OFILES) cjpeg.gcc.k1c.o
#	$(K1C_CC) $(K1C_CFLAGS) -o $@ $+ ../clock.gcc.k1c.o
#djpeg.gcc.k1c: $(LIB_K1C_GCC_OFILES) djpeg.gcc.k1c.o
#	$(K1C_CC) $(K1C_CFLAGS) -o $@ $+ ../clock.gcc.k1c.o
#
#cjpeg.gcc.o1.k1c: $(LIB_K1C_GCC_O1_OFILES) cjpeg.gcc.k1c.o
#	$(K1C_CC) $(K1C_CFLAGS_O1) -o $@ $+ ../clock.gcc.k1c.o
#djpeg.gcc.o1.k1c: $(LIB_K1C_GCC_O1_OFILES) djpeg.gcc.k1c.o
#	$(K1C_CC) $(K1C_CFLAGS_O1) -o $@ $+ ../clock.gcc.k1c.o
#
#cjpeg.ccomp.k1c: $(LIB_K1C_CCOMP_OFILES) cjpeg.gcc.k1c.o
#	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) -o $@ $+ ../clock.gcc.k1c.o
#djpeg.ccomp.k1c: $(LIB_K1C_CCOMP_OFILES) djpeg.gcc.k1c.o
#	$(K1C_CCOMP) $(K1C_CCOMPFLAGS) -o $@ $+ ../clock.gcc.k1c.o
#
#
#djpeg.%.out: djpeg.%
#	$(EXECUTE_CYCLES) $< -dct int -ppm -outfile $@.ppm testorig.jpg 2> $@
#	cmp $@.ppm testimg.ppm 2>> $@
#
#cjpeg.%.out: cjpeg.%
#	$(EXECUTE_CYCLES) $< -dct int -outfile $@.jpg testimg.ppm 2> $@
#	cmp $@.jpg testimg.jpg 2>> $@
#
#.SECONDARY:
