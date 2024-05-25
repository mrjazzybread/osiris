# Osiris

## Compilation

### Dependencies

The project depends on `ocaml`, `pprint`, `ocaml-compiler-libs`, `dune`, `coq`,
`iris`, and `std++`.

It is known to compile with the following versions of the packages:

| Package     | Version | Repo                                         |
|-------------|:-------:|:--------------------------------------------:|
| `ocaml`     | 5.2.0   | -                                            |
| `pprint`    | -       | -                                            |
| `ocaml-compiler-libs` | -  | -                                       |
| `dune`      | 3.11.0  | -                                            |
| `coq`       | 8.17.1  | https://coq.inria.fr/opam/released           |
| `coq-iris`  | dev     | git+https://gitlab.mpi-sws.org/iris/opam.git |
| `coq-stdpp` | dev     | git+https://gitlab.mpi-sws.org/iris/opam.git |
| `coq-serapi` | >=8.10.0+0.7.0 | - |

*Notes*:
- `coq-serapi` is only necessary to build the tutorial,
- you also need to install the python package `alectryon` to build the tutorial.


`make init` creates a new `opam` switch with all the required dependencies at
the right version.


### Build

Run `make`.

## Tutorial

The tutorial is available at <https://fpottier.gitlabpages.inria.fr/osiris/tutorial.html>
