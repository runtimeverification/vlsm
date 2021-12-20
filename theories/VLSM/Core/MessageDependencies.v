From stdpp Require Import prelude.
From Coq Require Import FinFun.
From VLSM Require Import Lib.Preamble Lib.StdppListSet Lib.Measurable.
From VLSM Require Import Core.VLSM Core.Composition Core.Equivocation.

(** * VLSM Message Dependencies

An abstract framework for the full-node condition.
Assumes that each message has an associated set of [message_dependencies].

*)

Section message_dependencies.

Context
  {message : Type}
  (message_dependencies : message -> set message)
  (X : VLSM message)
  {Hbo : HasBeenObservedCapability X}
  .

(**
[MessageDependencies] characterize a @message_dependencies@ function
through two properties:

- Necessity: All dependent messeges for a message @m@m are required to be
observed by any state emitting the message @m@.

- Sufficiency: A message can be produced by the machine pre-loaded with its
dependencies.
*)
Class MessageDependencies
  :=
  { message_dependencies_are_necessary (m : message)
      `(protocol_generated_prop (pre_loaded_with_all_messages_vlsm X) s m)
      : forall (dm : message),
        dm ∈ message_dependencies m ->
        has_been_observed X s dm
  ; message_dependencies_are_sufficient (m : message)
      `(can_emit (pre_loaded_with_all_messages_vlsm X) m)
      : can_emit (pre_loaded_vlsm X (fun msg => msg ∈ message_dependencies m)) m
  }.

(** The (local) full node condition for a given @message_dependencies@ function
requires that a state (receiving the message) has previously
observed all of @m@'s dependencies.
*)
Definition message_dependencies_full_node_condition
  (s : vstate X)
  (m : message)
  : Prop
  := forall dm, dm ∈ message_dependencies m ->
    has_been_observed X s dm.

(** A VLSM has the [message_dependencies_full_node_condition_prop]
if the validity of receiving a message in a state implies the
[message_dependencies_full_node_condition] for that state and message
*)
Definition message_dependencies_full_node_condition_prop : Prop :=
  forall l s m,
  vvalid X l (s, Some m) -> message_dependencies_full_node_condition s m.

End message_dependencies.
