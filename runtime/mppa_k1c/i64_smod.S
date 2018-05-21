	.text

	.align 8
	.globl __compcert_i64_smod
	.type	__compcert_i64_smod, @function
__compcert_i64_smod:
	addw $r12 = $r12, -24
	get $r8 = $ra
	;;
	sd 16[$r12] = $r15
	make $r15 = 0
	;;
	sd 28[$r12] = $r10
	copyd $r10 = $r15
	;;
	sw 24[$r12] = $r8
	;;
	cb.dltz $r0? .L5
	;;
.L2:
	absd $r1 = $r1
	;; /* Can't issue next in the same bundle */
	make $r2 = 1
	call udivmoddi4
	;;
	lwz $r8 = 24[$r12]
	xord $r0 = $r0, $r10
	;;
	addd $r0 = $r15, $r0
	ld $r10 = 28[$r12]
	;;
	ld $r15 = 16[$r12]
	addw $r12 = $r12, 24
	;;
	set $ra = $r8
	;; /* Can't issue next in the same bundle */
	ret
	;;
.L5:
	negd $r0 = $r0
	make $r15 = 1
	make $r10 = -1
	goto .L2
	;;
	.size	__compcert_i64_smod, .-__compcert_i64_smod
	.ident	"GCC: (GNU) 4.9.4"
