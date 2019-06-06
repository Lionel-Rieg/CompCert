all: cjpeg.gcc.k1c djpeg.gcc.k1c

LIBSOURCES= jcapimin.c jcapistd.c jccoefct.c jccolor.c jcdctmgr.c jchuff.c \
        jcinit.c jcmainct.c jcmarker.c jcmaster.c jcomapi.c jcparam.c \
        jcphuff.c jcprepct.c jcsample.c jctrans.c jdapimin.c jdapistd.c \
        jdatadst.c jdatasrc.c jdcoefct.c jdcolor.c jddctmgr.c jdhuff.c \
        jdinput.c jdmainct.c jdmarker.c jdmaster.c jdmerge.c jdphuff.c \
        jdpostct.c jdsample.c jdtrans.c jerror.c jfdctflt.c jfdctfst.c \
        jfdctint.c jidctflt.c jidctfst.c jidctint.c jidctred.c jquant1.c \
        jquant2.c jutils.c jmemmgr.c jmemansi.c
CSOURCES=$(LIBSOURCES) rdppm.c rdgif.c rdtarga.c rdrle.c rdbmp.c rdswitch.c cdjpeg.c wrppm.c wrgif.c wrtarga.c wrrle.c wrbmp.c rdcolmap.c

LIB_K1C_GCC_OFILES=$(CSOURCES:.c=.gcc.k1c.o)

include ../rules.mk

cjpeg.gcc.k1c: $(LIB_K1C_GCC_OFILES) cjpeg.gcc.k1c.o
	$(K1C_CC) $(K1C_CFLAGS) -o $@ $+ ../clock.gcc.k1c.o
djpeg.gcc.k1c: $(LIB_K1C_GCC_OFILES) djpeg.gcc.k1c.o
	$(K1C_CC) $(K1C_CFLAGS) -o $@ $+ ../clock.gcc.k1c.o
