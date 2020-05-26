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

#all: cjpeg.gcc.kvx.out djpeg.gcc.kvx.out cjpeg.gcc.o1.kvx.out djpeg.gcc.o1.kvx.out cjpeg.ccomp.kvx.out djpeg.ccomp.kvx.out
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
#LIB_KVX_GCC_OFILES=$(CSOURCES:.c=.gcc.kvx.o)
#LIB_KVX_GCC_O1_OFILES=$(CSOURCES:.c=.gcc.o1.kvx.o)
#LIB_KVX_CCOMP_OFILES=$(CSOURCES:.c=.ccomp.kvx.o)
#
#include ../rules.mk
#
#cjpeg.gcc.kvx: $(LIB_KVX_GCC_OFILES) cjpeg.gcc.kvx.o
#	$(KVX_CC) $(KVX_CFLAGS) -o $@ $+ ../clock.gcc.kvx.o
#djpeg.gcc.kvx: $(LIB_KVX_GCC_OFILES) djpeg.gcc.kvx.o
#	$(KVX_CC) $(KVX_CFLAGS) -o $@ $+ ../clock.gcc.kvx.o
#
#cjpeg.gcc.o1.kvx: $(LIB_KVX_GCC_O1_OFILES) cjpeg.gcc.kvx.o
#	$(KVX_CC) $(KVX_CFLAGS_O1) -o $@ $+ ../clock.gcc.kvx.o
#djpeg.gcc.o1.kvx: $(LIB_KVX_GCC_O1_OFILES) djpeg.gcc.kvx.o
#	$(KVX_CC) $(KVX_CFLAGS_O1) -o $@ $+ ../clock.gcc.kvx.o
#
#cjpeg.ccomp.kvx: $(LIB_KVX_CCOMP_OFILES) cjpeg.gcc.kvx.o
#	$(KVX_CCOMP) $(KVX_CCOMPFLAGS) -o $@ $+ ../clock.gcc.kvx.o
#djpeg.ccomp.kvx: $(LIB_KVX_CCOMP_OFILES) djpeg.gcc.kvx.o
#	$(KVX_CCOMP) $(KVX_CCOMPFLAGS) -o $@ $+ ../clock.gcc.kvx.o
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
