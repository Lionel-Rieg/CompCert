MMULT
=====

Examples of matrix multiplication using different methods.

We compute matrix multiplication using column-based matrix multiplication, then row-based, and finally block based.

The test verifies that the result is the same on the three methods. If it is the same, 0 will be returned.

The following commands can be run inside the folder:

- `make`: produces the unitary test binaries
  - `mmult-test-gcc-x86` : binary from gcc on x86
  - `mmult-test-k1c-x86` : binary from gcc on k1c
  - `mmult-test-ccomp-x86` : binary from ccomp on k1c
- `make test`: tests the return value of the binaries produced by gcc.
- `make check`: tests the return value of the binary produced by CompCert.
