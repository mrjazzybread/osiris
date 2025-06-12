List of tests taken from the directory `testsuite/tests/effects` of the [OCaml
repository](https://github.com/ocaml/ocaml).

Some files were removed because of features we do not support:

- `backtrace.ml` removed because we do not support backtraces
- `cmphash.ml` this test checks that comparing two effect continuations raises
  `Invalid_argument` but can be hashed. We removed this test because we choose
  to make this comparison crash and have not implemented hashing.
- `issue479.ml` removed: deals with the continuation-already-resumed exception and its interaction with the toplevel
- `marshal.ml` removed, Marshal is not implemented
- `shallow_state_io.ml` and `shallow_state.ml` the interpreter does not support shallow handlers yet
- `test6.ml` removed because we crash instead of raising `Unhandled`
- `test_lazy.ml` lazy is not supported yet
- `unhandled_effects.ml` and `unhandled_unlinked.ml` test unhandled effects

We adapted the following remaining files to use the syntax for effects, rather
than the `try_with` and `match_with` functions. We modified some of them in
additional ways that we describe below.

- `evenodd.ml` : reduced the main number to speed up the test
- `manylive.ml` : implemented a trivial `Random` module, reduced the main number to speed up the test
- `overflow.ml`
- `partial.ml`
- `reperform.ml` : part 2 removed because we crash instead of raising an exception for unhandled effects
- `sched.ml` : avoided polymorphic variants, added an implementation of `Queue`
- `test1.ml`
- `test2.ml`
- `test3.ml`
- `test4.ml`
- `test5.ml`
- `test10.ml` : removed `Deep.get_callstack`, implemented a trivial `Random` module
- `test11.ml`
- `used_cont.ml` : removed the interaction with GC, because we have no GC

Some of the tests above test subtle features of effects, or their performance,
and may not be relevant for the validation of the semantics, but we still
included what we support.
