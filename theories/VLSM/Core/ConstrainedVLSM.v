From VLSM.Lib Require Import Itauto.
From stdpp Require Import prelude.
From Coq Require Import Streams.
From VLSM.Lib Require Import Preamble.
From VLSM.Core Require Import VLSM PreloadedVLSM VLSMInclusion VLSMEmbedding VLSMEquality.

(** * Constrained VLSM

  Given a base VLSM <<X>>, we can further constrain its validity
  condition with the given predicate, producing a new VLSM.
*)

Section sec_constrained_vlsm.

Context
  {message : Type}
  (X : VLSM message)
  (constraint : label X -> state X * option message -> Prop).

Definition constrained_vlsm_type : VLSMType message :=
  vtype X.

Definition constrained_vlsm_machine : VLSMMachine X :=
{|
  initial_state_prop := @initial_state_prop _ _ X;
  initial_message_prop := @initial_message_prop _ _ X;
  s0 := @s0 _ _ X;
  transition := @transition _ _ X;
  valid := fun l som => valid X l som /\ constraint l som;
|}.

Definition constrained_vlsm : VLSM message :=
{|
  vtype := vtype X;
  vmachine := constrained_vlsm_machine;
|}.

End sec_constrained_vlsm.

Lemma VLSM_embedding_constrained_vlsm :
  forall `(X : VLSM message) (constraint : label X -> state X * option message -> Prop),
    VLSM_embedding (constrained_vlsm X constraint) X id id.
Proof.
  intros.
  apply basic_VLSM_strong_embedding; red; cbn; [| done..].
  by itauto.
Qed.

Lemma VLSM_incl_constrained_vlsm :
  forall `(X : VLSM message) (constraint : label X -> state X * option message -> Prop),
    VLSM_incl (constrained_vlsm X constraint) X.
Proof.
  intros message X.
  rewrite <- (mk_vlsm_machine X); cbn.
  intros constraint.
  apply (VLSMInclusion.VLSM_incl_embedding_iff (constrained_vlsm_machine X constraint)).
  by apply (VLSM_embedding_constrained_vlsm {| vtype := X; vmachine := X; |}).
Qed.

Section sec_constrained_vlsm_lemmas.

Context
  {message : Type}
  (X : VLSM message)
  (constraint : label X -> state X * option message -> Prop).

Lemma option_initial_message_prop_constrained_vlsm :
  forall om : option message,
    @option_initial_message_prop _ _ (constrained_vlsm X constraint) om
      <->
    @option_initial_message_prop _ _ X om.
Proof.
  done.
Qed.

Lemma valid_state_message_prop_constrained_vlsm :
  forall
    (constraint : label X -> state X * option message -> Prop)
    (s : state _) (om : option message),
      valid_state_message_prop (constrained_vlsm X constraint) s om ->
        valid_state_message_prop X s om.
Proof.
  intros cstr s om H.
  destruct X.
  eapply VLSM_incl_valid_state_message; [.. | by do 2 red | done].
  by apply (VLSM_incl_constrained_vlsm {| vtype := vtype; vmachine := vmachine; |}).
Qed.

Lemma valid_state_prop_constrained_vlsm :
  forall (s : state _),
    valid_state_prop (constrained_vlsm X constraint) s ->
      valid_state_prop X s.
Proof.
  intros s [om Hvsmp].
  exists om.
  by apply valid_state_message_prop_constrained_vlsm.
Qed.

Lemma valid_message_prop_constrained_vlsm :
  forall (m : message),
    valid_message_prop (constrained_vlsm X constraint) m ->
      valid_message_prop X m.
Proof.
  intros m [s Hvsmp].
  exists s.
  by apply valid_state_message_prop_constrained_vlsm.
Qed.

Lemma option_valid_message_prop_constrained_vlsm :
  forall (om : option message),
    option_valid_message_prop (constrained_vlsm X constraint) om ->
      option_valid_message_prop X om.
Proof.
  intros om [s Hvsmp].
  exists s.
  by apply valid_state_message_prop_constrained_vlsm.
Qed.

Lemma input_valid_constrained_vlsm :
  forall (l : label _) (som : state _ * option message),
    input_valid (constrained_vlsm X constraint) l som ->
      input_valid X l som.
Proof.
  intros l [s om] Hiv.
  destruct X.
  apply VLSM_incl_input_valid; [| done].
  by apply (VLSM_incl_constrained_vlsm {| vtype := vtype; vmachine := vmachine; |}).
Qed.

Lemma input_valid_transition_constrained_vlsm :
  forall (l : label _) (som som' : state _ * option message),
    input_valid_transition (constrained_vlsm X constraint) l som som' ->
      input_valid_transition X l som som'.
Proof.
  intros l [s om] [s' om'] Hivt.
  destruct X.
  apply VLSM_incl_input_valid_transition; [| done].
  by apply (VLSM_incl_constrained_vlsm {| vtype := vtype; vmachine := vmachine; |}).
Qed.

Lemma option_can_produce_constrained_vlsm :
  forall (s : state _) (om : option message),
    option_can_produce (constrained_vlsm X constraint) s om ->
      option_can_produce X s om.
Proof.
  intros s om Hocp.
  destruct X.
  eapply VLSM_incl_can_produce; [| done].
  by apply (VLSM_incl_constrained_vlsm {| vtype := vtype; vmachine := vmachine; |}).
Qed.

Lemma can_produce_constrained_vlsm :
  forall (s : state _) (m : message),
    can_produce (constrained_vlsm X constraint) s m ->
      can_produce X s m.
Proof.
  by intros; apply option_can_produce_constrained_vlsm.
Qed.

Lemma can_emit_constrained_vlsm :
  forall (m : message),
    can_emit (constrained_vlsm X constraint) m ->
      can_emit X m.
Proof.
  intros m Hce.
  destruct X.
  eapply VLSM_incl_can_emit; [| done].
  by apply (VLSM_incl_constrained_vlsm {| vtype := vtype; vmachine := vmachine; |}).
Qed.

Lemma finite_valid_trace_from_constrained_vlsm :
  forall (s : state _) (tr : list transition_item),
    finite_valid_trace_from (constrained_vlsm X constraint) s tr ->
      finite_valid_trace_from X s tr.
Proof.
  intros s tr Hfvtf.
  destruct X.
  apply VLSM_incl_finite_valid_trace_from; [| done].
  by apply (VLSM_incl_constrained_vlsm {| vtype := vtype; vmachine := vmachine; |}).
Qed.

Lemma finite_valid_trace_constrained_vlsm :
  forall (s : state _) (tr : list transition_item),
    finite_valid_trace (constrained_vlsm X constraint) s tr ->
      finite_valid_trace X s tr.
Proof.
  intros s tr Hfvt.
  destruct X.
  apply VLSM_incl_finite_valid_trace; [| done].
  by apply (VLSM_incl_constrained_vlsm {| vtype := vtype; vmachine := vmachine; |}).
Qed.

Lemma finite_valid_trace_from_to_constrained_vlsm :
  forall (s1 s2 : state _) (tr : list transition_item),
    finite_valid_trace_from_to (constrained_vlsm X constraint) s1 s2 tr ->
      finite_valid_trace_from_to X s1 s2 tr.
Proof.
  intros s1 s2 tr Hfvtft.
  destruct X.
  apply VLSM_incl_finite_valid_trace_from_to; [| done].
  by apply (VLSM_incl_constrained_vlsm {| vtype := vtype; vmachine := vmachine; |}).
Qed.

Lemma finite_valid_trace_init_to_constrained_vlsm :
  forall (s1 s2 : state _) (tr : list transition_item),
    finite_valid_trace_init_to (constrained_vlsm X constraint) s1 s2 tr ->
      finite_valid_trace_init_to X s1 s2 tr.
Proof.
  intros s1 s2 tr Hfvtit.
  destruct X.
  apply VLSM_incl_finite_valid_trace_init_to; [| done].
  by apply (VLSM_incl_constrained_vlsm {| vtype := vtype; vmachine := vmachine; |}).
Qed.

Lemma finite_valid_trace_init_to_emit_constrained_vlsm :
  forall (s1 s2 : state _) (om : option message) (tr : list transition_item),
    finite_valid_trace_init_to_emit (constrained_vlsm X constraint) s1 s2 om tr ->
      finite_valid_trace_init_to_emit X s1 s2 om tr.
Proof.
  induction 1; cbn; [by constructor |].
  by destruct Hv; econstructor.
Qed.

Lemma empty_initial_message_or_final_output_constrained_vlsm :
  forall (tr : list transition_item) (om : option message),
    empty_initial_message_or_final_output (constrained_vlsm X constraint) tr om ->
      empty_initial_message_or_final_output X tr om.
Proof.
  intros tr om.
  unfold empty_initial_message_or_final_output; cbn.
  by case_match.
Qed.

Lemma infinite_valid_trace_from_constrained_vlsm :
  forall (s : state _) (tr : Stream transition_item),
    infinite_valid_trace_from (constrained_vlsm X constraint) s tr ->
      infinite_valid_trace_from X s tr.
Proof.
  intros s tr Hivtf.
  destruct X.
  apply VLSM_incl_infinite_valid_trace_from; [| done].
  by apply (VLSM_incl_constrained_vlsm {| vtype := vtype; vmachine := vmachine; |}).
Qed.

Lemma infinite_valid_trace_constrained_vlsm :
  forall (s : state _) (tr : Stream transition_item),
    infinite_valid_trace (constrained_vlsm X constraint) s tr ->
      infinite_valid_trace X s tr.
Proof.
  intros s tr Hivt.
  destruct X.
  apply VLSM_incl_infinite_valid_trace; [| done].
  by apply (VLSM_incl_constrained_vlsm {| vtype := vtype; vmachine := vmachine; |}).
Qed.

Lemma valid_trace_from_prop_constrained_vlsm :
  forall (tr : Trace),
    valid_trace_from_prop (constrained_vlsm X constraint) tr ->
      valid_trace_from_prop X tr.
Proof.
  intros [] Hvtfp; cbn.
  - by apply finite_valid_trace_from_constrained_vlsm.
  - by apply infinite_valid_trace_from_constrained_vlsm.
Qed.

Lemma valid_trace_prop_constrained_vlsm :
  forall (tr : Trace),
    valid_trace_prop (constrained_vlsm X constraint) tr ->
      valid_trace_prop X tr.
Proof.
  intros tr Hvtp.
  destruct X.
  apply VLSM_incl_valid_trace; [| done].
  by apply (VLSM_incl_constrained_vlsm {| vtype := vtype; vmachine := vmachine; |}).
Qed.

Lemma in_futures_constrained_vlsm :
  forall (s1 s2 : state _),
    in_futures (constrained_vlsm X constraint) s1 s2 ->
      in_futures X s1 s2.
Proof.
  intros s1 s2 Hif.
  destruct X.
  apply VLSM_incl_in_futures; [| done].
  by apply (VLSM_incl_constrained_vlsm {| vtype := vtype; vmachine := vmachine; |}).
Qed.

End sec_constrained_vlsm_lemmas.

Section sec_constrained_vlsm_commutation_lemmas.

Lemma constrained_preloaded_comm :
  forall `(X : VLSM message) (constraint : label X -> state X * option message -> Prop)
    (initial : message -> Prop),
      VLSM_eq
        (constrained_vlsm (pre_loaded_vlsm X initial) constraint)
        (pre_loaded_vlsm (constrained_vlsm X constraint) initial).
Proof.
  intros message X.
  rewrite <- (mk_vlsm_machine X); cbn.
  intros constraint initial.
  by split; apply (VLSM_incl_embedding_iff (constrained_vlsm_machine
    (pre_loaded_vlsm X initial) constraint)), basic_VLSM_strong_embedding; red; cbn.
Qed.

Lemma VLSM_incl_constrained_preloaded :
  forall `(X : VLSM message) (constraint : label X -> state X * option message -> Prop)
    (initial : message -> Prop),
      VLSM_incl
        (constrained_vlsm (pre_loaded_vlsm X initial) constraint)
        (pre_loaded_vlsm (constrained_vlsm X constraint) initial).
Proof.
  by intros; apply constrained_preloaded_comm.
Qed.

Lemma VLSM_incl_preloaded_constrained :
  forall `(X : VLSM message) (constraint : label X -> state X * option message -> Prop)
    (initial : message -> Prop),
      VLSM_incl
        (pre_loaded_vlsm (constrained_vlsm X constraint) initial)
        (constrained_vlsm (pre_loaded_vlsm X initial) constraint).
Proof.
  by intros; apply constrained_preloaded_comm.
Qed.

End sec_constrained_vlsm_commutation_lemmas.
