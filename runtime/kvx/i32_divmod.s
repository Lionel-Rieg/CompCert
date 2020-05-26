/* KVX
32-bit unsigned/signed integer division/modulo (udiv5)

D. Monniaux, CNRS, VERIMAG */

	
	.globl __compcert_i32_sdiv_fp
__compcert_i32_sdiv_fp:
	compw.lt $r2 = $r0, 0
	compw.lt $r3 = $r1, 0
	absw $r0 = $r0
	absw $r1 = $r1
	;;
	xord $r2 = $r2, $r3
	make $r3 = 0
	goto __compcert_i32_divmod_fp
	;;
	
	.globl __compcert_i32_smod_fp
__compcert_i32_smod_fp:
	compw.lt $r2 = $r0, 0
	absw $r0 = $r0
	absw $r1 = $r1
	make $r3 = 1
	goto __compcert_i32_divmod_fp
	;;
	
	.globl __compcert_i32_umod_fp
__compcert_i32_umod_fp:
	make $r2 = 0
	make $r3 = 1
	goto __compcert_i32_divmod_fp
	;;

	.globl __compcert_i32_udiv_fp
__compcert_i32_udiv_fp:
	make $r2 = 0
	make $r3 = 0
	;;

/*
r0 : a
r1 : b
r2 : negate result?
r3 : return mod?
*/

	.globl __compcert_i32_divmod_fp
__compcert_i32_divmod_fp:
	zxwd $r7 = $r1
	zxwd $r1 = $r0
#ifndef NO_SHORTCUT
	compw.ltu $r8 = $r0, $r1
	cb.weqz $r1? .ERR # return 0 if divide by 0
#endif
	;;
# a in r1, b in r7
	floatud.rn.s $r5 = $r7, 0
#ifndef NO_SHORTCUT
	compd.eq $r8 = $r7, 1
	cb.wnez $r8? .LESS # shortcut if a < b
#endif
	;;
# b (double) in r5
	make $r6 = 0x3ff0000000000000 # 1.0
	fnarrowdw.rn.s $r11 = $r5
#	cb.wnez $r8, .RET1 # if b=1
	;;
# b (single) in r11
	floatud.rn.s $r10 = $r1, 0
	finvw.rn.s $r11 = $r11
	;;
	fwidenlwd.s $r11 = $r11
	;;
# invb0 in r11
	copyd $r9 = $r11
	ffmsd.rn.s $r6 = $r11, $r5
# alpha in r6
	;;
	ffmad.rn.s $r9 = $r11, $r6
# 1/b in r9
	;;
	fmuld.rn.s $r0 = $r10, $r9
# a/b in r1
	;;
	fixedud.rn.s $r0 = $r0, 0
	;;
	msbfd $r1 = $r0, $r7
	;;
	addd $r6 = $r0, -1
	addd $r8 = $r1, $r7
	;;
	cmoved.dltz $r1? $r0 = $r6
	cmoved.dltz $r1? $r1 = $r8
	;;
	negw $r4 = $r0
	negw $r5 = $r1
	;;
	cmoved.wnez $r2? $r0 = $r4
	cmoved.wnez $r2? $r1 = $r5
	;;
.END:
	cmoved.wnez $r3? $r0 = $r1
	ret
	;;
#ifndef NO_SHORTCUT

.LESS:
	make $r0 = 0
	negw $r5 = $r1
	;;
	cmoved.wnez $r2? $r1 = $r5
	goto .END
	;;
	
.ERR:
	make $r0 = 0
	ret
	;;
#endif
