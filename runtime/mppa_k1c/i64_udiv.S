	.text

	.align 8
	.globl __compcert_i64_udiv
	.type	__compcert_i64_udiv, @function
__compcert_i64_udiv:
	make $r2 = 0
	goto udivmoddi4
	;;
	.size	__compcert_i64_udiv, .-__compcert_i64_udiv
	.ident	"GCC: (GNU) 4.9.4"
