/*
Integer division for K1c

David Monniaux, CNRS / Verimag
	*/
	
	.globl dm_udivmoddi4
dm_udivmoddi4:
	sxwd $r2 = $r2
	make $r5 = 0
	compd.ltu $r3 = $r0, $r1
	;;

	clzd $r3 = $r1
	clzd $r4 = $r0
	cb.dnez $r3? .L74
	;;

	sbfw $r4 = $r4, $r3
	;;

	zxwd $r3 = $r4
	slld $r1 = $r1, $r4
	;;

	compd.ltu $r6 = $r0, $r1
	;;

	cb.dnez $r6? .L4C
	;;

	make $r5 = 1
	sbfd $r0 = $r1, $r0
	;;

	slld $r5 = $r5, $r4
	;;

.L4C:
	cb.deqz $r3? .L74
	;;

	srld $r1 = $r1, 1
	zxwd $r3 = $r4
	;;

	loopdo $r3, .LOOP
	;;

	stsud $r0 = $r1, $r0
	;;

.LOOP:
	addd $r5 = $r0, $r5
	srld $r0 = $r0, $r4
	;;

	slld $r4 = $r0, $r4
	;;

	sbfd $r5 = $r4, $r5
	;;

.L74:
	cmoved.deqz $r2? $r0 = $r5
	ret
	;;

/*
r0 : a
r1 : b
r2 : negate result?
r3 : return mod?
*/

	.globl __compcert_i32_sdiv_stsud
__compcert_i32_sdiv_stsud:
	compw.lt $r2 = $r0, 0
	compw.lt $r3 = $r1, 0
	absw $r0 = $r0
	absw $r1 = $r1
	;;
	zxwd $r0 = $r0
	zxwd $r1 = $r1
	xord $r2 = $r2, $r3
	make $r3 = 0
	goto __compcert_i64_divmod_stsud
	;;
	
	.globl __compcert_i32_smod_stsud
__compcert_i32_smod_stsud:
	compw.lt $r2 = $r0, 0
	absw $r0 = $r0
	absw $r1 = $r1
	make $r3 = 1
	;;
	zxwd $r0 = $r0
	zxwd $r1 = $r1
	goto __compcert_i64_divmod_stsud
	;;
	
	.globl __compcert_i32_umod_stsud
__compcert_i32_umod_stsud:
	make $r2 = 0
	make $r3 = 1
	zxwd $r0 = $r0
	zxwd $r1 = $r1
	goto __compcert_i64_divmod_stsud
	;;

	.globl __compcert_i32_udiv_stsud
__compcert_i32_udiv_stsud:
	make $r2 = 0
	make $r3 = 0
	zxwd $r0 = $r0
	zxwd $r1 = $r1
	goto __compcert_i64_divmod_stsud
	;;
	
	.globl __compcert_i64_umod_stsud
__compcert_i64_umod_stsud:
	make $r2 = 0
	make $r3 = 1
	goto __compcert_i64_divmod_stsud
	;;

	.globl __compcert_i64_udiv_stsud
__compcert_i64_udiv_stsud:
	make $r2 = 0
	make $r3 = 0
	goto __compcert_i64_divmod_stsud
	;;

	.globl __compcert_i64_sdiv_stsud
__compcert_i64_sdiv_stsud:
	compd.lt $r2 = $r0, 0
	compd.lt $r3 = $r1, 0
	absd $r0 = $r0
	absd $r1 = $r1
	;;
	xord $r2 = $r2, $r3
	make $r3 = 0
	goto __compcert_i64_divmod_stsud
	;;
	
	.globl __compcert_i64_smod_stsud
__compcert_i64_smod_stsud:
	compd.lt $r2 = $r0, 0
	absd $r0 = $r0
	absd $r1 = $r1
	make $r3 = 1
	goto __compcert_i64_divmod_stsud
	;;

	.globl __compcert_i64_divmod_stsud
__compcert_i64_divmod_stsud:
	make $r5 = 0
	compd.ltu $r7 = $r0, $r1
	;;

	clzd $r7 = $r1
	clzd $r4 = $r0
	cb.dnez $r7? .ZL74
	;;

	sbfw $r4 = $r4, $r7
	;;

	zxwd $r7 = $r4
	slld $r1 = $r1, $r4
	;;

	compd.ltu $r6 = $r0, $r1
	;;

	cb.dnez $r6? .ZL4C
	;;

	make $r5 = 1
	sbfd $r0 = $r1, $r0
	;;

	slld $r5 = $r5, $r4
	;;

.ZL4C:
	cb.deqz $r7? .ZL74
	;;

	srld $r1 = $r1, 1
	zxwd $r7 = $r4
	;;

	loopdo $r7, .ZLOOP
	;;

	stsud $r0 = $r1, $r0
	;;

.ZLOOP:
	addd $r5 = $r0, $r5
	srld $r0 = $r0, $r4
	;;

	slld $r4 = $r0, $r4
	;;

	sbfd $r5 = $r4, $r5
	;;

.ZL74:
	cmoved.weqz $r3? $r0 = $r5
	;;
	negd $r5 = $r0
	;;
	cmoved.wnez $r2? $r0 = $r5
	ret
	;;
