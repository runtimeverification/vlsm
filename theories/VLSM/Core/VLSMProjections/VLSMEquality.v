From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From VLSM.Core Require Import VLSM VLSMProjections.VLSMInclusion VLSMProjections.VLSMEmbedding.

(** * VLSM Trace Equality

  We can also define VLSM _equality_ in terms of traces.
  When both VLSMs have the same state and label types they also share the
  same [Trace] type, and sets of traces can be compared without conversion.
  Then VLSM <<X>> and VLSM <<Y>> are _equal_ if their [valid_trace]s are exactly the same.
*)

Section sec_VLSM_equality.

Context
  {message : Type}
  {vtype : VLSMType message}
  .

Definition VLSM_eq_part
  (MX MY : VLSMMachine vtype)
  (X := mk_vlsm MX) (Y := mk_vlsm MY)
  :=
  forall t : Trace,
    valid_trace_prop X t <-> valid_trace_prop Y t .
#[local] Notation VLSM_eq X Y := (VLSM_eq_part (machine X) (machine Y)).

Lemma VLSM_eq_incl_l
  (MX MY : VLSMMachine vtype)
  (X := mk_vlsm MX) (Y := mk_vlsm MY)
  : VLSM_eq X Y -> VLSM_incl X Y.
Proof.
  intros Heq t Hxt. by apply Heq.
Qed.

Lemma VLSM_eq_incl_r
  (MX MY : VLSMMachine vtype)
  (X := mk_vlsm MX) (Y := mk_vlsm MY)
  : VLSM_eq X Y -> VLSM_incl Y X.
Proof.
  intros Heq t Hyt. by apply Heq.
Qed.

Lemma VLSM_eq_incl_iff
  (MX MY : VLSMMachine vtype)
  (X := mk_vlsm MX) (Y := mk_vlsm MY)
  : VLSM_eq X Y <-> VLSM_incl X Y /\ VLSM_incl Y X.
Proof. firstorder. Qed.

End sec_VLSM_equality.

Notation VLSM_eq X Y := (VLSM_eq_part (machine X) (machine Y)).

Lemma VLSM_eq_refl
  {message : Type}
  {vtype : VLSMType message}
  (MX : VLSMMachine vtype)
  (X := mk_vlsm MX)
  : VLSM_eq X X.
Proof.
  firstorder.
Qed.

Lemma VLSM_eq_sym
  {message : Type}
  {vtype : VLSMType message}
  (MX MY : VLSMMachine vtype)
  (X := mk_vlsm MX) (Y := mk_vlsm MY)
  : VLSM_eq X Y -> VLSM_eq Y X.
Proof.
  firstorder.
Qed.

Lemma VLSM_eq_trans
  {message : Type}
  {vtype : VLSMType message}
  (MX MY MZ : VLSMMachine vtype)
  (X := mk_vlsm MX) (Y := mk_vlsm MY) (Z := mk_vlsm MZ)
  : VLSM_eq X Y -> VLSM_eq Y Z -> VLSM_eq X Z.
Proof.
  firstorder.
Qed.

Section sec_VLSM_eq_properties.

(** ** VLSM equality properties *)

Context
  {message : Type} [vtype : VLSMType message]
  [MX MY : VLSMMachine vtype]
  (Hincl : VLSM_eq_part MX MY)
  (X := mk_vlsm MX)
  (Y := mk_vlsm MY)
  .

(** VLSM equality specialized to finite trace. *)

Lemma VLSM_eq_proj1 : VLSM_incl X Y.
Proof.
  apply VLSM_eq_incl_iff in Hincl.
  apply Hincl.
Qed.

Lemma VLSM_eq_proj2 : VLSM_incl Y X.
Proof.
  apply VLSM_eq_incl_iff in Hincl.
  apply Hincl.
Qed.

Lemma VLSM_eq_finite_valid_trace
  (s : vstate X)
  (tr : list (vtransition_item X))
  : finite_valid_trace X s tr <-> finite_valid_trace Y s tr.
Proof.
  split.
  - apply (VLSM_incl_finite_valid_trace VLSM_eq_proj1).
  - apply (VLSM_incl_finite_valid_trace VLSM_eq_proj2).
Qed.

Lemma VLSM_eq_finite_valid_trace_init_to
  (s f : vstate X)
  (tr : list (vtransition_item X))
  : finite_valid_trace_init_to X s f tr <->
    finite_valid_trace_init_to Y s f tr.
Proof.
  split.
  - apply (VLSM_incl_finite_valid_trace_init_to VLSM_eq_proj1).
  - apply (VLSM_incl_finite_valid_trace_init_to VLSM_eq_proj2).
Qed.

Lemma VLSM_eq_valid_state
  (s : vstate X)
  : valid_state_prop X s <-> valid_state_prop Y s.
Proof.
  split.
  - apply (VLSM_incl_valid_state VLSM_eq_proj1).
  - apply (VLSM_incl_valid_state VLSM_eq_proj2).
Qed.

Lemma VLSM_eq_initial_state
  (is : vstate X)
  : vinitial_state_prop X is <-> vinitial_state_prop Y is.
Proof.
  split.
  - apply (VLSM_incl_initial_state VLSM_eq_proj1).
  - apply (VLSM_incl_initial_state VLSM_eq_proj2).
Qed.

Lemma VLSM_eq_finite_valid_trace_from
  (s : vstate X)
  (tr : list (vtransition_item X))
  : finite_valid_trace_from X s tr <->
    finite_valid_trace_from Y s tr.
Proof.
  split.
  - apply (VLSM_incl_finite_valid_trace_from VLSM_eq_proj1).
  - apply (VLSM_incl_finite_valid_trace_from VLSM_eq_proj2).
Qed.

Lemma VLSM_eq_finite_valid_trace_from_to
  (s f : vstate X)
  (tr : list (vtransition_item X))
  : finite_valid_trace_from_to X s f tr <-> finite_valid_trace_from_to Y s f tr.
Proof.
  split.
  - apply (VLSM_incl_finite_valid_trace_from_to VLSM_eq_proj1).
  - apply (VLSM_incl_finite_valid_trace_from_to VLSM_eq_proj2).
Qed.

Lemma VLSM_eq_in_futures
  (s1 s2 : vstate X)
  : in_futures X s1 s2 <-> in_futures Y s1 s2.
Proof.
  split.
  - apply (VLSM_incl_in_futures VLSM_eq_proj1).
  - apply (VLSM_incl_in_futures VLSM_eq_proj2).
Qed.

Lemma VLSM_eq_input_valid_transition
  : forall l s im s' om,
  input_valid_transition X l (s,im) (s',om) <->
  input_valid_transition Y l (s,im) (s',om).
Proof.
  split.
  - apply (VLSM_incl_input_valid_transition VLSM_eq_proj1).
  - apply (VLSM_incl_input_valid_transition VLSM_eq_proj2).
Qed.

Lemma VLSM_eq_input_valid
  : forall l s im,
  input_valid X l (s,im) <-> input_valid Y l (s,im).
Proof.
  split.
  - apply (VLSM_incl_input_valid VLSM_eq_proj1).
  - apply (VLSM_incl_input_valid VLSM_eq_proj2).
Qed.

Lemma VLSM_eq_can_produce
  (s : state)
  (om : option message)
  : option_can_produce X s om <-> option_can_produce Y s om.
Proof.
  split.
  - apply (VLSM_incl_can_produce VLSM_eq_proj1).
  - apply (VLSM_incl_can_produce VLSM_eq_proj2).
Qed.

Lemma VLSM_eq_can_emit
  (m : message)
  : can_emit X m <-> can_emit Y m.
Proof.
  split.
  - apply (VLSM_incl_can_emit VLSM_eq_proj1).
  - apply (VLSM_incl_can_emit VLSM_eq_proj2).
Qed.

Lemma VLSM_eq_infinite_valid_trace_from
  s ls
  : infinite_valid_trace_from X s ls <->
    infinite_valid_trace_from Y s ls.
Proof.
  split.
  - apply (VLSM_incl_infinite_valid_trace_from VLSM_eq_proj1).
  - apply (VLSM_incl_infinite_valid_trace_from VLSM_eq_proj2).
Qed.

Lemma VLSM_eq_infinite_valid_trace
  s ls
  : infinite_valid_trace X s ls <-> infinite_valid_trace Y s ls.
Proof.
  split.
  - apply (VLSM_incl_infinite_valid_trace VLSM_eq_proj1).
  - apply (VLSM_incl_infinite_valid_trace VLSM_eq_proj2).
Qed.

Lemma VLSM_eq_valid_trace
  : forall t, valid_trace_prop X t <-> valid_trace_prop Y t.
Proof.
  split.
  - apply (VLSM_incl_valid_trace VLSM_eq_proj1).
  - apply (VLSM_incl_valid_trace VLSM_eq_proj2).
Qed.

End sec_VLSM_eq_properties.

Section sec_VLSM_incl_preloaded_properties.

(** ** Inclusion properties for pre-loaded VLSMs *)

Context
  {message : Type}
  (X : VLSM message)
  .

Lemma pre_loaded_vlsm_with_valid_eq
  (P Q : message -> Prop)
  (QimpliesValid : forall m, Q m -> valid_message_prop (pre_loaded_vlsm X P) m)
  : VLSM_eq (pre_loaded_vlsm X (fun m => P m \/ Q m)) (pre_loaded_vlsm X P).
Proof.
  apply VLSM_eq_incl_iff; split; cbn.
  - apply pre_loaded_vlsm_incl_relaxed; itauto.
  - apply pre_loaded_vlsm_incl; itauto.
Qed.

Lemma pre_loaded_vlsm_idem
  (P : message -> Prop)
  : VLSM_eq (pre_loaded_vlsm (pre_loaded_vlsm X P) P) (pre_loaded_vlsm X P).
Proof.
  apply VLSM_eq_incl_iff; split; cbn.
  - apply pre_loaded_vlsm_idem_l.
  - apply pre_loaded_vlsm_idem_r.
Qed.

Lemma pre_loaded_with_all_messages_vlsm_is_pre_loaded_with_True
  : VLSM_eq (pre_loaded_with_all_messages_vlsm X) (pre_loaded_vlsm X (fun m => True)).
Proof.
  apply VLSM_eq_incl_iff; split; cbn.
  - apply pre_loaded_with_all_messages_vlsm_is_pre_loaded_with_True_l.
  - apply pre_loaded_with_all_messages_vlsm_is_pre_loaded_with_True_r.
Qed.

Lemma pre_loaded_with_all_messages_eq_validating_pre_loaded_vlsm
  (P : message -> Prop)
  (Hvalidating :
    forall (l : label) (s : state) (m : message)
      (Hv : input_valid (pre_loaded_with_all_messages_vlsm X) l (s, Some m)),
      valid_message_prop (pre_loaded_vlsm X P) m)
  : VLSM_eq (pre_loaded_with_all_messages_vlsm X) (pre_loaded_vlsm X P).
Proof.
  apply VLSM_eq_incl_iff; split; cbn;
    [| apply pre_loaded_vlsm_incl_pre_loaded_with_all_messages].
  apply basic_VLSM_incl.
  - by intro; intros **.
  - by intros l s m Hv _ _; eapply Hvalidating.
  - by intros l s om (_ & _ & ?).
  - by intros l s om s' om' [_ Ht].
Qed.

Lemma vlsm_is_pre_loaded_with_False
  : VLSM_eq X (pre_loaded_vlsm X (fun m => False)).
Proof.
  destruct X as (T, M). intro Hpp.
  apply VLSM_eq_incl_iff. simpl.
  split; apply basic_VLSM_strong_incl; cbv; itauto.
Qed.

Lemma vlsm_is_pre_loaded_with_False_initial_message
  : strong_full_projection_initial_message_preservation X (pre_loaded_vlsm X (fun m => False)).
Proof.
  by intros m Hm; left.
Qed.

Lemma vlsm_is_pre_loaded_with_False_initial_message_rev
  : strong_full_projection_initial_message_preservation (pre_loaded_vlsm X (fun m => False)) X.
Proof.
  by intros m [Hm | Hfalse].
Qed.

Lemma pre_loaded_with_all_messages_vlsm_idem
  : VLSM_eq (pre_loaded_with_all_messages_vlsm (pre_loaded_with_all_messages_vlsm X)) (pre_loaded_with_all_messages_vlsm X).
Proof.
  apply VLSM_eq_incl_iff; split; cbn.
  - apply pre_loaded_with_all_messages_vlsm_idem_l.
  - apply pre_loaded_with_all_messages_vlsm_idem_r.
Qed.

Lemma vlsm_is_pre_loaded_with_False_valid_state_message s om
  : valid_state_message_prop X s om <-> valid_state_message_prop (pre_loaded_vlsm X (fun m => False)) s om.
Proof.
  pose proof vlsm_is_pre_loaded_with_False as Heq.
  apply VLSM_eq_incl_iff in Heq.
  destruct X as (T, M); simpl in *.
  split; (apply VLSM_incl_valid_state_message; [|cbv;tauto]); apply Heq.
Qed.

End sec_VLSM_incl_preloaded_properties.
