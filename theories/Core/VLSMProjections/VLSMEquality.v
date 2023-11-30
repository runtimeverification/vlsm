From VLSM.Lib Require Import Itauto.
From stdpp Require Import prelude.
From VLSM.Core Require Import VLSM.
From VLSM.Core.VLSMProjections Require Import VLSMInclusion VLSMEmbedding.

(** * Core: VLSM Trace Equality

  In this module, we define VLSM _equality_ in terms of traces.
  When both VLSMs have the same state and label types they also share the
  same [Trace] type, and sets of traces can be compared without conversion.
  Then VLSM <<X>> and VLSM <<Y>> are _equal_ if their [valid_trace]s are exactly the same.
*)

Section sec_VLSM_equality.

Context
  {message : Type}
  {T : VLSMType message}
  .

Definition VLSM_eq_part
  (MX MY : VLSMMachine T)
  (X := mk_vlsm MX) (Y := mk_vlsm MY) : Prop :=
    VLSM_incl X Y /\ VLSM_incl Y X.

End sec_VLSM_equality.

Notation VLSM_eq X Y := (VLSM_eq_part (vlsm_machine X) (vlsm_machine Y)).

Lemma VLSM_eq_refl
  {message : Type}
  {T : VLSMType message}
  (MX : VLSMMachine T)
  (X := mk_vlsm MX)
  : VLSM_eq X X.
Proof.
  by firstorder.
Qed.

Lemma VLSM_eq_sym
  {message : Type}
  {T : VLSMType message}
  (MX MY : VLSMMachine T)
  (X := mk_vlsm MX) (Y := mk_vlsm MY)
  : VLSM_eq X Y -> VLSM_eq Y X.
Proof.
  by firstorder.
Qed.

Lemma VLSM_eq_trans
  {message : Type}
  {T : VLSMType message}
  (MX MY MZ : VLSMMachine T)
  (X := mk_vlsm MX) (Y := mk_vlsm MY) (Z := mk_vlsm MZ)
  : VLSM_eq X Y -> VLSM_eq Y Z -> VLSM_eq X Z.
Proof.
  by firstorder.
Qed.

Section sec_VLSM_eq_properties.

(** ** VLSM equality properties *)

Context
  {message : Type} [T : VLSMType message]
  [MX MY : VLSMMachine T]
  (Hincl : VLSM_eq_part MX MY)
  (X := mk_vlsm MX)
  (Y := mk_vlsm MY)
  .

(** VLSM equality specialized to finite trace. *)

Lemma VLSM_eq_finite_valid_trace
  (s : state X)
  (tr : list (transition_item X))
  : finite_valid_trace X s tr <-> finite_valid_trace Y s tr.
Proof.
  by split; apply VLSM_incl_finite_valid_trace, Hincl.
Qed.

Lemma VLSM_eq_finite_valid_trace_init_to
  (s f : state X)
  (tr : list (transition_item X))
  : finite_valid_trace_init_to X s f tr <->
    finite_valid_trace_init_to Y s f tr.
Proof.
  by split; apply VLSM_incl_finite_valid_trace_init_to, Hincl.
Qed.

Lemma VLSM_eq_valid_state
  (s : state X)
  : valid_state_prop X s <-> valid_state_prop Y s.
Proof.
  by split; apply VLSM_incl_valid_state, Hincl.
Qed.

Lemma VLSM_eq_initial_state
  (is : state X)
  : initial_state_prop X is <-> initial_state_prop Y is.
Proof.
  by split; apply VLSM_incl_initial_state, Hincl.
Qed.

Lemma VLSM_eq_finite_valid_trace_from
  (s : state X)
  (tr : list (transition_item X))
  : finite_valid_trace_from X s tr <->
    finite_valid_trace_from Y s tr.
Proof.
  by split; apply VLSM_incl_finite_valid_trace_from, Hincl.
Qed.

Lemma VLSM_eq_finite_valid_trace_from_to
  (s f : state X)
  (tr : list (transition_item X))
  : finite_valid_trace_from_to X s f tr <-> finite_valid_trace_from_to Y s f tr.
Proof.
  by split; apply VLSM_incl_finite_valid_trace_from_to, Hincl.
Qed.

Lemma VLSM_eq_in_futures
  (s1 s2 : state X)
  : in_futures X s1 s2 <-> in_futures Y s1 s2.
Proof.
  by split; apply VLSM_incl_in_futures, Hincl.
Qed.

Lemma VLSM_eq_input_valid_transition
  : forall l s im s' om,
  input_valid_transition X l (s, im) (s', om) <->
  input_valid_transition Y l (s, im) (s', om).
Proof.
  by split; apply @VLSM_incl_input_valid_transition, Hincl.
Qed.

Lemma VLSM_eq_input_valid
  : forall l s im,
  input_valid X l (s, im) <-> input_valid Y l (s, im).
Proof.
  by split; apply @VLSM_incl_input_valid, Hincl.
Qed.

Lemma VLSM_eq_can_produce
  (s : state T)
  (om : option message)
  : option_can_produce X s om <-> option_can_produce Y s om.
Proof.
  by split; apply VLSM_incl_can_produce, Hincl.
Qed.

Lemma VLSM_eq_can_emit
  (m : message)
  : can_emit X m <-> can_emit Y m.
Proof.
  by split; apply VLSM_incl_can_emit, Hincl.
Qed.

Lemma VLSM_eq_infinite_valid_trace_from
  s ls
  : infinite_valid_trace_from X s ls <->
    infinite_valid_trace_from Y s ls.
Proof.
  by split; apply VLSM_incl_infinite_valid_trace_from, Hincl.
Qed.

Lemma VLSM_eq_infinite_valid_trace
  s ls
  : infinite_valid_trace X s ls <-> infinite_valid_trace Y s ls.
Proof.
  by split; apply VLSM_incl_infinite_valid_trace, Hincl.
Qed.

Lemma VLSM_eq_valid_trace
  : forall t, valid_trace_prop X t <-> valid_trace_prop Y t.
Proof.
  by split; apply VLSM_incl_valid_trace, Hincl.
Qed.

End sec_VLSM_eq_properties.
