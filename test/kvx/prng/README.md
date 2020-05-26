PRNG
====

This is a simple Pseudo Random Number Generator.

`prng.c` contains a simple unitary test that compares the sum of the "bytewise sum"
of 1000 generated numbers to a hardcoded result, that is the one obtained with
`gcc -O2` on a x86 processor, and returns 0 if the result is correct.

The following commands can be run inside that folder:

- `make`: produces the unitary test binaries
  - `prng-test-gcc-x86` : binary from gcc on x86
  - `prng-test-kvx-x86` : binary from gcc on kvx
  - `prng-test-ccomp-x86` : binary from ccomp on kvx
- `make test`: tests the return value of the binaries produced by gcc.
- `make check`: tests the return value of the binary produced by CompCert.
