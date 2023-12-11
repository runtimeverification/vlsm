# VLSM

[![Docker CI][docker-action-shield]][docker-action-link]
[![coqdoc][coqdoc-shield]][coqdoc-link]

[docker-action-shield]: https://github.com/runtimeverification/vlsm/actions/workflows/test-pr.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/runtimeverification/vlsm/actions/workflows/test-pr.yml


[coqdoc-shield]: https://img.shields.io/badge/docs-coqdoc-blue.svg
[coqdoc-link]: https://runtimeverification.github.io/vlsm-docs/latest/coqdoc/toc.html


The theory of Validating Labelled State transition and Message
production systems (VLSMs) enables describing and proving properties
of distributed systems executing in the presence of faults. This
project contains a formalization of this theory in the Coq proof
assistant along with several examples of distributed protocols
modeled and verified using VLSMs, including the ELMO
(Equivocation-Limited Message Observer) family of message
validating protocols and the Paxos protocol for crash-tolerant
distributed consensus.

## Meta

- License: [BSD 3-Clause "New" or "Revised" License](LICENSE.md)
- Compatible Coq versions: 8.16 and later
- Additional dependencies:
  - [Coq-std++](https://gitlab.mpi-sws.org/iris/stdpp/) 1.9.0 and later
  - [Itauto](https://gitlab.inria.fr/fbesson/itauto)
  - [Coq-Equations](https://github.com/mattam82/Coq-Equations)
- Coq namespace: `VLSM`
- Related publication(s):
  - [Validating Labelled State Transition and Message Production Systems: A Theory for Modelling Faulty Distributed Systems](https://arxiv.org/abs/2202.12662) doi:[10.48550/arXiv.2202.12662](https://doi.org/10.48550/arXiv.2202.12662)

## Building instructions

We recommend using [opam](https://opam.ocaml.org) to install project dependencies.
Besides the basic building instructions below, we also provide a more detailed
[building guide](BUILDING.md), with special recommendations for Windows users.

To install the project dependencies via opam, do:

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq.8.18.0 coq-stdpp.1.9.0 coq-itauto coq-equations
```

To build the project when you have all dependencies installed, do:

```shell
git clone https://github.com/runtimeverification/vlsm.git
cd vlsm
make   # or make -j <number-of-cores-on-your-machine>
```

## Documentation

### File organization

- [Lib](theories/Lib): Extensions to the [Coq standard library](https://coq.inria.fr/stdlib/) and [Coq-std++](https://gitlab.mpi-sws.org/iris/stdpp/).
- [Core](theories/Core): Core VLSM definitions and results.
- [Examples](theories/Examples): Applications of VLSMs, including tutorials.

### Source documentation

- [latest coqdoc presentation of the Coq files](https://runtimeverification.github.io/vlsm-docs/latest/coqdoc/toc.html)
- [latest Alectryon presentation the Coq files](https://runtimeverification.github.io/vlsm-docs/latest/alectryon/toc.html)

### VLSM tutorials

- [VLSMs that Generate Logical Formulas](theories/Examples/Tutorial/Formulas.v): construction of VLSMs corresponding to propositional logic symbols, with their composition having well-formed propositional formulas as valid messages.
- [VLSMs that Multiply](theories/Examples/Tutorial/Multiply.v): construction of VLSMs that perform arithmetic operations, with their composition having products of powers as valid messages.
- [Primes Composition of VLSMs](theories/Examples/Tutorial/PrimesComposition.v): construction of an infinite family of VLSMs that multiply and their composition based on primes.
- [Round-based Asynchronous Muddy Children Puzzle](theories/Examples/Tutorial/MuddyChildrenRounds.v): the [muddy children puzzle](https://plato.stanford.edu/entries/dynamic-epistemic/appendix-B-solutions.html#muddy) as a constrained composition of VLSMs that communicate asynchronously in rounds.

### VLSM application: ELMO

ELMO (Equivocation-Limited Message Observer) is a family of protocols that demonstrates gradual refinement of a specification to make it validating for increasingly more complex constraints.

- [BaseELMO](theories/Examples/ELMO/BaseELMO.v): basic definitions and results related to ELMO.
- [UMO](theories/Examples/ELMO/UMO.v): definition and properties of UMO (Unvalidating Message Observer) components and the UMO protocol.
- [MO](theories/Examples/ELMO/UMO.v): definition and properties of MO (Message Observer) components and the MO protocol.
- [ELMO](theories/Examples/ELMO/ELMO.v): definition and properties of ELMO components and the ELMO protocol.

### VLSM application: Paxos

[Paxos](https://en.wikipedia.org/wiki/Paxos_(computer_science)) is a protocol for achieving distributed consensus among network nodes in the presence of crash faults and message loss.

- [Abstract Specification of Consensus](theories/Examples/Paxos/Consensus.v): specification of consensus as a set of values that can be agreed on by nodes.
- [Specification of Consensus by Voting](theories/Examples/Paxos/Voting.v): specification of consensus where nodes agree on a value by voting.
- [A Basic Paxos Protocol](theories/Examples/Paxos/Paxos.v): specification of consensus by votes from a quorum of acceptor nodes and using a leader node for each ballot.
