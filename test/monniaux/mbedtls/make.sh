CCOMP=`pwd`/../../../ccomp
cd mbedtls
make CC=$CCOMP CFLAGS="-fstruct-passing -fbitfields -Dvolatile= -U__STRICT_ANSI__" WARNING_CFLAGS="-Wall -fno-unprototyped" "$@"
