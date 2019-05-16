
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
__compcert_i32_umod:
	sxwd $r0 = $r0
	sxwd $r1 = $r1
	make $r2 = 0x3ff0000000000000
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
	copyd $r1 = $r0
	;;
	ffmad $r1 = $r2, $r0
	;;
	ffmad $r0 = $r2, $r1
	;;
	fixedd.rz $r0 = $r0, 0
	ret
	;;

__compcert_i32_smod:
	sxwd $r4 = $r0
	sxwd $r5 = $r1
	make $r2 = 0x3ff0000000000000
	;;
	copyd $r0 = $r4
	copyd $r1 = $r5
	floatd.rn.s $r4 = $r4, 0
	;;
	floatd.rn.s $r3 = $r5, 0
	;;
	floatw.rn.s $r5 = $r5, 0
	;;
	finvw $r5=$r5
	;;
	fwidenlwd $r5 = $r5
	;;
	fmuld $r4 = $r4, $r5
	;;
	ffmsd $r2 = $r5, $r3
	copyd $r5 = $r4
	;;
	ffmad $r5 = $r2, $r4
	;;
	ffmad $r4 = $r2, $r5
	;;
	fixedd.rz $r4 = $r4, 0
	;;
	msbfd $r0 = $r1, $r4
	ret
	;;

__compcert_i32_udiv:
	zxwd $r0 = $r0
	zxwd $r1 = $r1
	make $r2 = 0x3ff0000000000000
	;;
	floatud.rn.s $r0 = $r0, 0
	;;
	floatud.rn.s $r3 = $r1, 0
	;;
	floatuw.rn.s $r1 = $r1, 0
	;;
	finvw $r1=$r1
	;;
	fwidenlwd $r1 = $r1
	;;
	fmuld $r0 = $r0, $r1
	;;
	ffmsd $r2 = $r1, $r3
	copyd $r1 = $r0
	;;
	ffmad $r1 = $r2, $r0
	;;
	ffmad $r0 = $r2, $r1
	;;
	fixedud.rz $r0 = $r0, 0
	;; 
	ret
	;;
