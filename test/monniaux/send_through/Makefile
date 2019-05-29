send_through: send_through_gcc.k1c.o send_through_ccomp.k1c.o
	../../../ccomp -Wall $+ -o $@ -lm

send_through_gcc.k1c.o  send_through_ccomp.k1c.o: send_through.h

send_through_gcc.k1c.o : send_through_gcc.c
	k1-cos-gcc -Wall -Wextra -std=c99 -Werror=implicit -c $< -o $@

send_through_ccomp.k1c.o : send_through_ccomp.c
	../../../ccomp -Wall -fnone -fvararg-calls -c $< -o $@
