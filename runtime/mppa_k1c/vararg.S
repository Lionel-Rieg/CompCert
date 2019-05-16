
// typedef void * va_list;
// unsigned int __compcert_va_int32(va_list * ap);
// unsigned long long __compcert_va_int64(va_list * ap);

	.text
	.balign 2
	.globl __compcert_va_int32
__compcert_va_int32:
	ld		$r32 = 0[$r0]	# $r32 <- *ap
;;
	addd	$r32 = $r32, 8	# $r32 <- $r32 + WORDSIZE
;;
	sd		0[$r0] = $r32	# *ap <- $r32
;;
	lws		$r0 = -8[$r32]	# retvalue <- 32-bits at *ap - WORDSIZE
	ret
;;

	.text
	.balign 2
	.globl __compcert_va_int64
	.globl __compcert_va_float64
	.globl __compcert_va_composite
__compcert_va_int64:
__compcert_va_float64:
# FIXME this assumes pass-by-reference
__compcert_va_composite:
# Prologue
	ld		$r32 = 0[$r0]	# $r32 <- *ap
;;
	addd	$r32 = $r32, 8	# $r32 <- $r32 + WORDSIZE
;;
	sd		0[$r0] = $r32	# *ap <- $r32
;;
	ld		$r0 = -8[$r32]	# retvalue <- 64-bits at *ap - WORDSIZE
	ret
;;
	
# FIXME this assumes pass-by-reference
	.globl __compcert_acswapd
__compcert_acswapd:
	acswapd	0[$r1] = $r2r3
	;;
	sq	0[$r0] = $r2r3
	ret
	;;
	.globl __compcert_acswapw
__compcert_acswapw:
	acswapw	0[$r1] = $r2r3
	;;
	sq	0[$r0] = $r2r3
	ret
	;;

	.globl __compcert_i32_sdiv
	.globl __compcert_i32_smod
	.globl __compcert_i32_udiv
	.globl __compcert_i32_umod
__compcert_i32_sdiv:
__compcert_i32_smod:
__compcert_i32_udiv:
__compcert_i32_umod:
	sxwd $r0 = $r0
	sxwd $r1 = $r1
	;; /* Can't issue next in the same bundle */
	make $r2 = 0x3ff0000000000000
	addd $r12 = $r12, -16
	;;
	floatd.rn.s $r0 = $r0, 0
	;;
	floatd.rn.s $r3 = $r1, 0
	;;
	floatw.rn.s $r1 = $r1, 0
	;;
	finvw $r1=$r1
	;;
	fwidenlwd $r1 = $r1
	;;
	fmuld $r0 = $r0, $r1
	;;
	ffmsd $r2 = $r1, $r3
	;;
	sd 8[$r12] = $r0
	;;
	ld $r1 = 8[$r12]
	;;
	ffmad $r1 = $r2, $r0
	;;
	ffmad $r0 = $r2, $r1
	;;
	sd 8[$r12] = $r1
	addd $r12 = $r12, 16
	;;
	fixedd.rz $r0 = $r0, 0
	ret
	;;
