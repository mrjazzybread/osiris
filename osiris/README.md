# The Osiris translator

## Purpose

This tool translates [OCaml](https://ocaml.org/) source code
(an `. ml` file)
into an Osiris abstract syntax tree
that can be read by
the [Rocq](https://rocq-prover.org/) proof assistant
(a `.v` file).

This allows using Rocq
and
[Iris](https://iris-project.org/)
to specify and verify this OCaml source code.

## Assumptions

We assume that the OCaml code has been compiled using the
[dune](https://dune.build/) build system.

The flag `-bin-annot` must be passed to the OCaml compiler.
To this end, the `dune` file should contain a line that resembles this:

```
  (flags (:standard -bin-annot))
```

This flag causes the OCaml compiler to create `.cmt` files,
which the Osiris translator reads.

We assume that `dune` is in the PATH. The translator invokes `dune describe`
to obtain a description of the project.

## Usage

The basic usage is

```
  osiris \
    --root <project directory> \
    --out <output directory> \
    <OCaml module names>
```

Passing `--root <project directory>` and `--out <output directory>` is mandatory.

The project directory is the root of the OCaml project;
this is where the `dune-project` file resides.

The output directory is where the translated files should be produced.
An OCaml file whose path relative to the project directory is `foo/bar/baz.ml`
is translated to
a Rocq file whose path relative to the output directory is `foo/bar/baz.v`.
This file contains the definition of an abstract syntax tree, named `__main`,
for this OCaml module. (It usually also contains auxiliary definitions
whose names are not predictable.)

If a list of OCaml module names is passed on the command line,
as shown above,
then only these modules are translated.

If instead, the word `all` is passed on the command line,
as follows,
then all OCaml modules found in the project are processed:

```
  osiris \
    --root <project directory> \
    --out <output directory> \
    all
```
