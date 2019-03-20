test: byterun/ocamlrun
	k1-cluster --syscall=libstd_scalls.so -- byterun/ocamlrun examples/quicksort

byterun/ocamlrun:
	(cd byterun ; $(MAKE))

.PHONY: test
