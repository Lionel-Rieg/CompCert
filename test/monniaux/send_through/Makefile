send_through: send_through_gcc.kvx.o send_through_ccomp.kvx.o
	../../../ccomp -Wall $+ -o $@ -lm

send_through_gcc.kvx.o  send_through_ccomp.kvx.o: send_through.h

send_through_gcc.kvx.o : send_through_gcc.c
	k1-cos-gcc -Wall -Wextra -std=c99 -Werror=implicit -c $< -o $@

send_through_ccomp.kvx.o : send_through_ccomp.c
	../../../ccomp -Wall -fnone -fvararg-calls -c $< -o $@
