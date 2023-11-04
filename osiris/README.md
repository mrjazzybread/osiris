# The Osiris translator

## Purpose

## Usage

The basic usage is

```
  osiris --root <project directory> --out <output directory> all
  osiris --root <project directory> --out <output directory> <OCaml module names>
```

Osiris assumes that `dune build` has been executed already, so the OCaml code
has been compiled and the required `.cmt` files can be found somewhere inside
the `_build` subdirectory.

For each module `A` whose name is passed on the command line,
the source file (say `A.ml`) is located somewhere inside
the project directory. Then, a corresponding Coq file (`A.v`) is created, at
the same relative path, inside the output directory.

If the list of module names consists of just the word `all`
then all modules found in the project are processed.

If the command line option `--mark <mark>` is passed then the prefix `<mark>`
is prepended to the name of every generated file.
