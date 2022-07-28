# VLSM

A validating labelled state transition and message production system
(VLSM) abstractly models a distributed system with faults. This project
contains a formalization of VLSMs and their theory in the Coq proof assistant.

## Meta

- License: [BSD 3-Clause "New" or "Revised" License](LICENSE.md)
- Compatible Coq versions: 8.15 or later
- Additional dependencies:
  - [Coq-std++](https://gitlab.mpi-sws.org/iris/stdpp/) 1.7.0
  - [Itauto](https://gitlab.inria.fr/fbesson/itauto)
- Coq namespace: `VLSM`
- Related publication(s):
  - [VLSM: Validating Labelled State Transition and Message Production Systems](https://arxiv.org/abs/2202.12662) doi:[10.48550/arXiv.2202.12662](https://doi.org/10.48550/arXiv.2202.12662)

## Working with the project online

The simplest way of working with this project without needing to install anything is by doing so online:

[![Open in Papillon](https://papillon.unbounded.network/github-badge.svg)](https://papillon.unbounded.network/projects/github/runtimeverification/vlsm/master)

## Building instructions

We recommend using [opam](https://opam.ocaml.org) to install project dependencies.
Besides the basic building instructions below, we also provide a more detailed
[building guide](BUILDING.md), with special recommendations for Windows users.

To install the project dependencies via opam, do:

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq.8.15.2 coq-stdpp.1.7.0 coq-itauto
```

To build the project when you have all dependencies installed, do:

```shell
git clone https://github.com/runtimeverification/vlsm.git
cd vlsm
make   # or make -j <number-of-cores-on-your-machine>
```

## Coq file organization

- `theories/VLSM/Lib`: Various extensions to the Coq standard library and Coq-std++.
- `theories/VLSM/Core`: Core VLSM definitions and theory.

## Documentation

- [latest coqdoc presentation of the Coq files](https://runtimeverification.github.io/vlsm-docs/latest/coqdoc/toc.html)
- [latest Alectryon presentation the Coq files](https://runtimeverification.github.io/vlsm-docs/latest/alectryon/toc.html)
