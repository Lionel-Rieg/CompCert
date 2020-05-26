# CompCert Kalray port
The verified C compiler ported to Kalray.

## Features

This delivery contains (in addition to features from CompCert master branch):
- A fully functional port of CompCert to Coolidge kvx VLIW core
- Postpass scheduling optimization, only for kvx. Activated by default, it can be deactivated with the compiler flag `-fno-postpass`
- Some experimental features that are work in progress:
  - Slightly better subexpression eliminations, called CSE2 and CSE3. Both go through loops and feature a small alias analysis.
  - `-fduplicate 0` to activate static branch prediction information. The branch prediction is basic, it annotates each `Icond` node by an `option bool`. A `Some true` annotation indicates we predict the branch will be taken. `Some false` indicates the fallthrough case is predicted. `None` indicates we could not predict anything, and are not sure about which control will be preferred.
  - It is also possible to provide a number to perform tail duplication: `-fduplicate 5` will tail duplicate, stopping when more than 5 RTL instructions have been duplicated. This feature offers very variable performance (from -20% up to +20%) because of variations in the later register allocation phase that impacts the postpass scheduling. We intend to work on fine tuning the tail duplication phase once we have the prepass superblock scheduling.
  - `-ftracelinearize` uses the branch prediction information to linearize LTL basic blocks in a slightly better way (in the `Linearize` phase).

## Installing

Please follow the instructions in `INSTALL.md`

## Testing

We modified most of the CompCert tests of the `c` folder in order for them to be executable in reasonable time by the simulator.

To pass the testsuite, first, build and install CompCert using the instructions in `INSTALL.md`, then:
```
cd test/c
make
make test
```

The reference files were generated using `k1-cos-gcc -O1`.

We also have our own tests in `test/mppa/` - to run them, execute the script `simucheck.sh` located in that folder. These consist in comparing `compcert` output to `k1-cos-gcc` output.
