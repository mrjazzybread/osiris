# Osiris

## Compilation

### Dependencies

The project depends on `ocaml`, `pprint`, `ocaml-compiler-libs`, `dune`, `coq`,
`iris`, `coq-equations`, and `std++`.

It is known to compile with the following versions of the packages:

| Package     | Version | Repo                                         |
|-------------|:-------:|:--------------------------------------------:|
| `ocaml`     | 5.3.0   | -                                            |
| `pprint`    | -       | -                                            |
| `ocaml-compiler-libs` | -  | -                                       |
| `dune`      | 3.17.2  | -                                            |
| `coq`       | 8.17.1  | https://coq.inria.fr/opam/released           |
| `coq-iris`  | dev     | git+https://gitlab.mpi-sws.org/iris/opam.git |
| `coq-stdpp` | dev     | git+https://gitlab.mpi-sws.org/iris/opam.git |
| `coq-equations` | 1.3+8.17 | -                                       |
| `ppx_sexp_conv` | v0.17.0 | -                                        |
| `ppx_deriving` | 6.0.3 | -                                           |
| `coq-serapi` | >=8.10.0+0.7.0 | -                                    |

*Notes*:
- `coq-serapi` is only necessary to build the (currently unmaintained) tutorial,
- you also need to install the python package `alectryon` to build the tutorial.


`make init` creates a new `opam` switch with all the required dependencies at
the right version.


### Build

Run `make`.

## Tutorial

The tutorial is not currently available.