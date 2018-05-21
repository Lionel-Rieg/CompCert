	.text

	.align 8
	.globl __compcert_i64_sdiv
	.type	__compcert_i64_sdiv, @function
__compcert_i64_sdiv:
	addw $r12 = $r12, -16
	get $r8 = $ra
	;;
	sd 20[$r12] = $r10
	make $r10 = 0
	;;
	sw 16[$r12] = $r8
	;;
	cb.dltz $r0? .L6
	;;
	cb.dltz $r1? .L7
	;;
.L3:
	make $r2 = 0
	call udivmoddi4
	;;
	lwz $r8 = 16[$r12]
	negd $r1 = $r10
	;;
	xord $r0 = $r1, $r0
	;;
	addd $r0 = $r0, $r10
	ld $r10 = 20[$r12]
	addw $r12 = $r12, 16
	;;
	set $ra = $r8
	;; /* Can't issue next in the same bundle */
	ret
	;;
.L6:
	negd $r0 = $r0
	make $r10 = 1
	;; /* Can't issue next in the same bundle */
	cb.dgez $r1? .L3
	;;
.L7:
	xorw $r10 = $r10, 1
	negd $r1 = $r1
	;;
	sxwd $r10 = $r10
	goto .L3
	;;
	.size	__compcert_i64_sdiv, .-__compcert_i64_sdiv
	.ident	"GCC: (GNU) 4.9.4"
