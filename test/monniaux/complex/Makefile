include ../rules.mk

PRODUCTS=complex_mat.gcc.host.out complex_mat.ccomp.host.out \
	complex_mat.gcc.k1c.out complex_mat.ccomp.k1c.out \
	complex_mat.gcc.k1c.s complex_mat.ccomp.k1c.s

all:	$(PRODUCTS)

complex_mat.gcc.host.s complex_mat.ccomp.host.s complex_mat.gcc.k1c.s complex_mat.ccomp.k1c.s : ../clock.h

complex_mat.gcc.host complex_mat.ccomp.host : ../clock.gcc.host.o
complex_mat.gcc.k1c complex_mat.ccomp.k1c : ../clock.gcc.k1c.o
