# Osiris

## Compilation

### Dependencies

The project depends on `ocaml`, `dune`, `coq`, `iris`, and `std++`.

It is known to compile with the following versions of the packages:

| Package     | Version | Repo                                         |
|-------------|:-------:|:--------------------------------------------:|
| `ocaml`     | 4.14.1  | -                                            |
| `dune`      | 3.11.0  | -                                            |
| `coq`       | 8.17.1  | https://coq.inria.fr/opam/released           |
| `coq-iris`  | dev     | git+https://gitlab.mpi-sws.org/iris/opam.git |
| `coq-stdpp` | dev     | git+https://gitlab.mpi-sws.org/iris/opam.git |

`make init` creates a new `opam` switch with all the required dependencies at 
the right version.


### Build

Run `make`.
