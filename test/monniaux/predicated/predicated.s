	.text
	
	.globl predicated_write
predicated_write:
	sd.wnez $r0? 8[$r1] = $r2
	ret
	;;

	.globl predicated_read
predicated_read:
	ld.wnez $r1? $r0 = 8[$r2]
	ret
	;;
