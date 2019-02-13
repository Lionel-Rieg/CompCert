# Coq sources of AbstractBasicBlocks 

- [AbstractBasicBlocksDef](AbstractBasicBlocksDef.v): syntax and sequential semantics of abstract basic blocks (on which we define our analyzes).
This syntax and semantics is parametrized in order to adapt the language for different concrete basic block languages.

- [Parallelizability](Parallelizability.v): define the parallel semantics and the 'is_parallelizable' function which tests whether the sequential run of a given abstract basic block is the same than a parallel run.

- [DepTreeTheory](DepTreeTheory.v): defines a theory of dependency trees, such that two basic blocks with the same dependency tree have the same sequential semantics. In practice, permuting the instructions inside a basic block while perserving the dependencies of assignments should not change the dependency tree. The idea is to verify list schedulings, following ideas of [Formal verification of translation validators proposed by Tristan and Leroy](https://hal.inria.fr/inria-00289540/).

- [ImpDep](ImpDep.v): adds a hash-consing mechanism to trees of [DepTreeTheory](DepTreeTheory.v), and thus provides an efficient "equality" test (a true answer ensures that the two basic blocks in input have the same sequential semantics) in order to check the correctness of list schedulings.

- [DepExample](DepExample.v) defines a toy language (syntax and semantics); [DepExampleEqTest](DepExampleEqTest.v) defines a compiler of the toy language into abstract basic blocks and derives an equality test for the toy language; [DepExampleParallelTest](DepExampleParallelTest.v) derives a parallelizability test from the previous compiler; [DepExampleDemo](DepExampleDemo.v) is a test-suite for both tetsts.
