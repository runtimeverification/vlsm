From stdpp Require Import prelude.
From Coq Require Import FinFun Relations.Relation_Operators.
From VLSM.Lib Require Import Preamble ListExtras StdppListSet Measurable.
From VLSM.Core Require Import VLSM Composition Equivocation.

(** * VLSM Message Dependencies

An abstract framework for the full-node condition.
Assumes that each message has an associated set of [message_dependencies].

*)

Section sec_message_dependencies.

Context
  {message : Type}
  (message_dependencies : message -> set message)
  (X : VLSM message)
  {Hbo : HasBeenObservedCapability X}
  .

(**
[MessageDependencies] characterize a <<message_dependencies>> function
through two properties:

- Necessity: All dependent messeges for a message <<m>>m are required to be
observed by any state emitting the message <<m>>.

- Sufficiency: A message can be produced by the machine pre-loaded with its
dependencies.

Together with [message_dependencies_full_node_condition_prop], it
constitutes the _full node assumption_.
*)
Class MessageDependencies
  :=
  { message_dependencies_are_necessary (m : message)
      `(can_produce (pre_loaded_with_all_messages_vlsm X) s m)
      : forall (dm : message),
        dm ∈ message_dependencies m ->
        has_been_observed X s dm
  ; message_dependencies_are_sufficient (m : message)
      `(can_emit (pre_loaded_with_all_messages_vlsm X) m)
      : can_emit (pre_loaded_vlsm X (fun msg => msg ∈ message_dependencies m)) m
  }.

(** The (local) full node condition for a given <<message_dependencies>> function
requires that a state (receiving the message) has previously
observed all of <<m>>'s dependencies.
*)
Definition message_dependencies_full_node_condition
  (s : vstate X)
  (m : message)
  : Prop :=
  forall dm, dm ∈ message_dependencies m -> has_been_observed X s dm.

(** A VLSM has the [message_dependencies_full_node_condition_prop]
if the validity of receiving a message in a state implies the
[message_dependencies_full_node_condition] for that state and message
*)
Definition message_dependencies_full_node_condition_prop : Prop :=
  forall l s m,
  vvalid X l (s, Some m) -> message_dependencies_full_node_condition s m.

(** Membership to the message_dependencies of a message induces a dependency
relation.
*)
Definition msg_dep_rel : relation message :=
  fun m1 m2 => m1 ∈ message_dependencies m2.

(** The transitive closure of the [msg_dep_rel]ation is a happens-before
relation.
*)
Definition msg_dep_happens_before : relation message := flip (clos_trans _ (flip msg_dep_rel)).

(** Unrolling one the [msg_dep_happens_before] relation one step. *)
Lemma msg_dep_happens_before_iff_one x z
  : msg_dep_happens_before x z <->
    msg_dep_rel x z \/ exists y, msg_dep_happens_before x y /\ msg_dep_rel y z.
Proof.
  split.
  - intros Hhb.
    apply Operators_Properties.clos_trans_t1n in Hhb.
    inversion Hhb; subst.
    + left. assumption.
    + right.
      exists y.
      split; [|assumption].
      apply Operators_Properties.clos_t1n_trans.
      assumption.
  - intros Hhb.
    apply Operators_Properties.clos_t1n_trans.
    destruct Hhb as [Hone | [y [Hhb Hone]]].
    + apply t1n_step. assumption.
    + apply t1n_trans with y; [assumption|].
      apply Operators_Properties.clos_trans_t1n.
      assumption.
Qed.

Global Instance msg_dep_happens_before_transitive : Transitive msg_dep_happens_before.
Proof.
  apply flip_Transitive.
  intros m1 m2 m3.
  apply t_trans.
Qed.

(** If the [msg_dep_rel]ation reflects a predicate <<P>> and the induced
[msg_dep_happens_before] is [well_founded], then if <<P>> holds for a message,
it will hold for all its dependencies. *)
Lemma msg_dep_happens_before_reflect
  (P : message -> Prop)
  (Hreflects : forall dm m, msg_dep_rel dm m -> P m -> P dm)
  : forall dm m, msg_dep_happens_before dm m -> P m -> P dm.
Proof.
  intros dm m Hdm.
  apply Operators_Properties.clos_trans_t1n in Hdm.
  induction Hdm; [apply Hreflects; assumption|].
  intro Hpx.
  apply IHHdm.
  revert Hpx.
    apply Hreflects.
    assumption.
Qed.

End sec_message_dependencies.
      assumption.
Qed.

End sec_message_dependencies.

