	.text

	.align 8
	.globl udivmoddi4
	.type	udivmoddi4, @function
udivmoddi4:
	compd.ltu $r3 = $r0, $r1
	;; /* Can't issue next in the same bundle */
	sxwd $r2 = $r2
	make $r5 = 0
	;;
	cb.dnez $r3? .L2
	;;
	clzd $r3 = $r1
	;; /* Can't issue next in the same bundle */
	clzd $r4 = $r0
	;;
	sbfw $r4 = $r4, $r3
	;;
	slld $r1 = $r1,$r4
	zxwd $r3 = $r4
	;;
	compd.ltu $r6 = $r0, $r1
	;;
	cb.dnez $r6? .L3
	;;
	make $r5 = 1
	sbfd $r0 = $r1, $r0
	;;
	slld $r5 = $r5,$r4
	;;
.L3:
	cb.deqz $r3? .L2
	;;
	srld $r1 = $r1,1
	copyd $r3 = $r4
	;;
	loopgtz $r3, .L14
	;;
.L4:
	stsud $r0 = $r1, $r0
	;;
.L14:
	# HW loop end
	;;
	addd $r5 = $r0, $r5
	srld $r0 = $r0,$r4
	;;
	slld $r4 = $r0,$r4
	;;
	sbfd $r5 = $r4, $r5
	;;
.L2:
	cmoved.deqz $r2? $r0 = $r5
	ret
	;;
	.size	udivmoddi4, .-udivmoddi4
	.ident	"GCC: (GNU) 4.9.4"
