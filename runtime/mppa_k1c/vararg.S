
// typedef void * va_list;
// unsigned int __compcert_va_int32(va_list * ap);
// unsigned long long __compcert_va_int64(va_list * ap);

	.text
	.balign 2
	.globl __compcert_va_int32
__compcert_va_int32:
# Prologue
	addd	$r14 = $r12, 0
;;
	addd	$r12 = $r12, -16
;;
	sd		0[$r12] = $r14
;;
	get		$r16 = $ra
;;
	sd		8[$r12] = $r16
;;
# Body
	ld		$r32 = 0[$r0]	# $r32 <- *ap
;;
	addd	$r32 = $r32, 8	# $r32 <- $r32 + WORDSIZE
;;
	sd		0[$r0] = $r32	# *ap <- $r32
;;
	lws		$r0 = -8[$r32]	# retvalue <- 32-bits at *ap - WORDSIZE
;;
# Prologue
	ld		$r16 = 8[$r12]
;;
	set		$ra = $r16
;;
	addd	$r12 = $r12, 16
;;
	ret
;;

	.text
	.balign 2
	.globl __compcert_va_int64
	.globl __compcert_va_float64
__compcert_va_int64:
__compcert_va_float64:
# Prologue
	addd	$r14 = $r12, 0
;;
	addd	$r12 = $r12, -16
;;
	sd		0[$r12] = $r14
;;
	get		$r16 = $ra
;;
	sd		8[$r12] = $r16
;;
# Body
	ld		$r32 = 0[$r0]	# $r32 <- *ap
;;
	addd	$r32 = $r32, 8	# $r32 <- $r32 + WORDSIZE
;;
	sd		0[$r0] = $r32	# *ap <- $r32
;;
	ld		$r0 = -8[$r32]	# retvalue <- 64-bits at *ap - WORDSIZE
;;
# Prologue
	ld		$r16 = 8[$r12]
;;
	set		$ra = $r16
;;
	addd	$r12 = $r12, 16
;;
	ret
;;
