From VLSM.Lib Require Import Itauto.
From stdpp Require Import prelude finite.
From Coq Require Import Streams FunctionalExtensionality Eqdep_dec.
From VLSM.Lib Require Import Preamble ListExtras.
From VLSM.Core Require Import VLSM Plans VLSMProjections.

(** * Paxos: Abstract Specification of Consensus

  A very high-level specification of the consensus problem,
  following Lamport.

  It does not even explicitly model multiple nodes, just
  the set of values which any node thinks have been agreed
  upon as the consensus value.

  The only allowed transition is moving from an empty set
  to a singleton set.

  Note that this captures the safety and liveness properties
  of never thinking multiple (distinct) values have been selected
  and eventually selecting a value, but cannot specify any
  properties about if and when correct nodes learn of the consensus.
*)

Section sec_consensus_spec.

Context
  (V VSet : Type)
  `{FinSet V VSet}
  .

Definition consensus_state : Type := VSet.
Definition consensus_message : Type := False.

(**
  This type can be seen as a degenerate case when
  defining a sum type for expressing different steps
  in a transition system.
*)
Inductive consensus_action : Type :=
| Decided (v : V).

(**
  To enable TLA-style refinement, we need to allow stutter actions
  in our transition system. Hence, we use [None] to express stuttering,
  i.e., a no-op transition.
*)
Definition consensus_label : Type := option consensus_action.

Definition consensus_type : VLSMType False :=
{|
  state := consensus_state;
  label := consensus_label;
|}.

(**
  A [consensus_state] is initial when the the consensus set is empty.
*)
Definition consensus_initial_state_prop (s : consensus_state) : Prop := s ≡ ∅.

(** There are no initial messages. *)
Definition consensus_initial_message_prop (m : consensus_message) : Prop := False.

Definition consensus_valid (l : consensus_label) :
  consensus_state * option consensus_message -> Prop :=
  fun '(s, _) =>
  match l with
  | None => True
  | Some (Decided _) => s ≡ ∅
  end.

Definition consensus_transition (l : consensus_label) :
  consensus_state * option consensus_message -> consensus_state * option consensus_message :=
  fun '(s, _) =>
  match l with
  | None => (s, None)
  | Some (Decided v) => ({[ v ]} ∪ s, None)
  end.

Definition consensus_vlsm_machine : VLSMMachine consensus_type :=
{|
  initial_state_prop := consensus_initial_state_prop;
  s0 := populate (_ ↾ (reflexivity _ : consensus_initial_state_prop ∅));
  initial_message_prop := consensus_initial_message_prop;
  transition := consensus_transition;
  valid := consensus_valid;
|}.

Definition consensus_vlsm := mk_vlsm consensus_vlsm_machine.

Lemma consensus_invariant :
  forall (s : state consensus_vlsm),
    valid_state_prop _ s ->
    s ≡ ∅ \/ exists v : V, s ≡ {[ v ]}.
Proof.
  intros s Hs.
  induction Hs using valid_state_prop_ind; [by left |].
  destruct Ht as [(_ & _ & Hvalid) Hstep]; cbn in Hvalid.
  destruct l as [[v] |]; inversion Hstep; subst s'; [| done].
  right; exists v.
  by rewrite Hvalid, (right_id ∅ (∪)).
Qed.

End sec_consensus_spec.
