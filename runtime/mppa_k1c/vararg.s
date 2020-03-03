
# typedef void * va_list;
# unsigned int __compcert_va_int32(va_list * ap);
# unsigned long long __compcert_va_int64(va_list * ap);

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
