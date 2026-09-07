FROM ocaml/opam:debian-ocaml-5.5

# System dependencies pulled in by the opam packages we install below.
# The base image ships opam 2.0, which cannot auto-install depexts, so we
# install them explicitly: pkg-config for conf-pkg-config, libgmp-dev for
# zarith (a transitive dep of rocq-runtime).
USER root
RUN apt-get update \
 && apt-get install -y --no-install-recommends \
      pkg-config \
      libgmp-dev \
 && rm -rf /var/lib/apt/lists/*
USER opam

# Install the project's opam dependencies into the base image's existing
# switch (which already has OCaml 5.4 compiled). Skipping `make init` avoids
# a ~5–10 min OCaml recompile.
WORKDIR /tmp/osiris-deps
COPY --chown=opam:opam Makefile ./Makefile
RUN opam repo set-url default https://opam.ocaml.org --yes \
 && make pin SWITCH_NAME=$(opam switch show) \
 && rm -rf /tmp/osiris-deps

WORKDIR /home/opam
