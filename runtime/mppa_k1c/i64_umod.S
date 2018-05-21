	.text

	.align 8
	.globl __compcert_i64_umod
	.type	__compcert_i64_umod, @function
__compcert_i64_umod:
	make $r2 = 1
	goto udivmoddi4
	;;
	.size	__compcert_i64_umod, .-__compcert_i64_umod
	.ident	"GCC: (GNU) 4.9.4"
