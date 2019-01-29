exec /home/monniaux/work/Kalray/CompCert/ccomp -U __SIZEOF_INT128__ -U __SIZE_TYPE__ -D __SIZE_TYPE__='unsigned long long' "$@"
