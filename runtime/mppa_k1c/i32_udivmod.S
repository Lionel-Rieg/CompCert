	.text

	.align 8
	.type	udivmodsi4, @function
udivmodsi4:
	zxwd $r0 = $r0
	;; /* Can't issue next in the same bundle */
	zxwd $r1 = $r1
	;; /* Can't issue next in the same bundle */
	sxwd $r2 = $r2
	make $r4 = 0
	;;
	compw.ltu $r3 = $r0, $r1
	;;
	cb.weqz $r3? .L14
	;;
.L2:
	cmoved.deqz $r2? $r0 = $r4
	ret
	;;
.L14:
	clzw $r3 = $r1
	clzw $r5 = $r0
	;;
	sbfw $r5 = $r5, $r3
	;;
	sllw $r1 = $r1,$r5
	zxwd $r3 = $r5
	;;
	compw.ltu $r6 = $r0, $r1
	;;
	cb.wnez $r6? .L3
	;;
	make $r4 = 1
	sbfw $r0 = $r1, $r0
	;;
	sllw $r4 = $r4,$r5
	;;
	zxwd $r4 = $r4
	;;
.L3:
	cb.deqz $r3? .L2
	;;
	srlw $r1 = $r1,1
	copyd $r3 = $r5
	;;
	loopgtz $r3, .L15
	;;
.L4:
	stsuw $r0 = $r1, $r0
	;;
	zxwd $r0 = $r0
	;;
.L15:
	# HW loop end
	;;
	srlw $r1 = $r0,$r5
	addw $r4 = $r0, $r4
	;;
	sllw $r5 = $r1,$r5
	zxwd $r0 = $r1
	;;
	sbfw $r4 = $r5, $r4
	;;
	cmoved.deqz $r2? $r0 = $r4
	ret
	;;
	.size	udivmodsi4, .-udivmodsi4

	.align 8
	.globl __udivsi3
	.type	__udivsi3, @function
__udivsi3:
	make $r2 = 0
	goto udivmodsi4
	;;
	.size	__udivsi3, .-__udivsi3

	.align 8
	.globl __umodsi3
	.type	__umodsi3, @function
__umodsi3:
	make $r2 = 1
	goto udivmodsi4
	;;
	.size	__umodsi3, .-__umodsi3

	.align 8
	.globl __divsi3
	.type	__divsi3, @function
__divsi3:
	addw $r12 = $r12, -16
	get $r8 = $ra
	sxwd $r0 = $r0
	;;
	sxwd $r1 = $r1
	sd 20[$r12] = $r10
	make $r10 = 0
	;;
	sw 16[$r12] = $r8
	;;
	cb.wltz $r0? .L22
	;;
	cb.wltz $r1? .L23
	;;
.L20:
	make $r2 = 0
	call udivmodsi4
	;;
	lwz $r8 = 16[$r12]
	negw $r1 = $r10
	;;
	xorw $r0 = $r1, $r0
	;;
	addw $r0 = $r0, $r10
	ld $r10 = 20[$r12]
	addw $r12 = $r12, 16
	;;
	set $ra = $r8
	;; /* Can't issue next in the same bundle */
	ret
	;;
.L22:
	negw $r0 = $r0
	make $r10 = 1
	;;
	sxwd $r0 = $r0
	;; /* Can't issue next in the same bundle */
	cb.wgez $r1? .L20
	;;
.L23:
	negw $r1 = $r1
	xorw $r10 = $r10, 1
	;;
	sxwd $r1 = $r1
	sxwd $r10 = $r10
	goto .L20
	;;
	.size	__divsi3, .-__divsi3

	.align 8
	.globl __modsi3
	.type	__modsi3, @function
__modsi3:
	addw $r12 = $r12, -24
	get $r8 = $ra
	sxwd $r0 = $r0
	;;
	sd 16[$r12] = $r15
	make $r15 = 0
	sxwd $r1 = $r1
	;;
	sd 28[$r12] = $r10
	copyd $r10 = $r15
	;;
	sw 24[$r12] = $r8
	;;
	cb.wltz $r0? .L27
	;;
.L25:
	absw $r1 = $r1
	make $r2 = 1
	call udivmodsi4
	;;
	lwz $r8 = 24[$r12]
	xorw $r0 = $r0, $r10
	;;
	addw $r0 = $r0, $r15
	ld $r10 = 28[$r12]
	;;
	ld $r15 = 16[$r12]
	addw $r12 = $r12, 24
	;;
	set $ra = $r8
	;; /* Can't issue next in the same bundle */
	ret
	;;
.L27:
	negw $r2 = $r0
	make $r15 = 1
	make $r10 = -1
	;;
	sxwd $r0 = $r2
	goto .L25
	;;
	.size	__modsi3, .-__modsi3
	.ident	"GCC: (GNU) 4.9.4"
