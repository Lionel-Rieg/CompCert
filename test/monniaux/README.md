## Folders with just source code
- acswap
- bitfields
- crypto-algorithms
- des
- fill_buffer
- jumptable
- k1_builtins
- latency
- longjmp
- loop
- madd
- math
- memcpy
- multithreaded_volatile
- nand
- predicated
- regalloc
- rotate
- send_through
- sizeof
- slow_globals
- ternary_builtin
- tiny-AES-c
- uzlib
- varargs
- volatile
- xor_and_mat

## Special folders
- csmith
- jpeg-6b
- mbedtls
- quest
- yarpgen

## Just to be compiled
- frame_pointer

## Benches to fix
- BearSSL : does not compile (to fix)
- ncompress : error on comparing
- ocaml : error during postpass scheduling
- micro-bunzip : -O3 buggy with gcc ?
- mod_int_mat : does not include rules.mk
- pcre2test : Trap MEMORY ACCESS VIOLATION sur le binaire ccomp
- picosat : compilation error : implicit declaration

## Benches that work
- binary_search
- bitsliced-aes
- bitsliced-tea
- complex
- float_mat
- glibc_qsort
- heapsort
- idea
- number_theoretic_transform
- quicksort
- sha-2
- tacle-bench-lift
- tacle-bench-powerwindow
- ternary
- too_slow
