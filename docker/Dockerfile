FROM ocaml/opam:debian-ocaml-5.4

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

# Install the project's opam dependencies into a switch named "osiris".
# We only need the Makefile for this — copying the full source would bust
# the dependency-install cache on every source change.
WORKDIR /tmp/osiris-deps
COPY --chown=opam:opam Makefile ./Makefile
RUN make init \
 && rm -rf /tmp/osiris-deps

# Make the osiris switch the default for containers using this image.
ENV OPAMSWITCH=osiris
WORKDIR /home/opam
