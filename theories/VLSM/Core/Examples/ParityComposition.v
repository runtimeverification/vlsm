From VLSM.Lib Require Import Itauto.
From Coq Require Import FunctionalExtensionality.
From Coq Require Import ZArith.Znumtheory.
From stdpp Require Import prelude.
From VLSM.Lib Require Import Preamble StdppExtras FinSuppFn NatExtras ListExtras.
From VLSM.Core Require Import VLSM PreloadedVLSM ConstrainedVLSM Composition.
From VLSM.Core Require Import VLSMProjections ProjectionTraces.

(** * Parity VLSM Composition

  This module demonstrates advanced concepts of the VLSM framework. We define
  a generalized parity VLSM parameterized on a multiplier and a composition
  of such VLSMs. We then construct the composition consisting of a component 
  for each prime number, characterize the valid messages, and show that any
  component in the composition is a validator.
*)

#[local] Open Scope Z_scope.

(** ** General automation *)

(** Custom tactic used to simplify proofs of valid VLSM transitions. *)

Ltac app_valid_tran :=
  repeat split; cbn;
  match goal with
  | |- option_valid_message_prop _ _ => by apply initial_message_is_valid
  | |- option_valid_message_prop _ _ => eapply emitted_messages_are_valid
  | |- valid_state_prop _ _ => by apply initial_state_is_valid
  | |- valid_state_prop _ _ => eapply input_valid_transition_destination
  end.

Section sec_parity_vlsm.

Context
 (multiplier : Z)
 (multiplier_gt_1 : multiplier > 1)
 (index : Type)
 `{Inhabited index}
 .

(** ** Definition of Parity VLSM

  The Parity VLSM will only have one label, indicating a decrement.
  For this reason, the [unit] type can be used.
*)

Definition ParityLabel : Type := unit.

(** The state will hold an integer. *)

Definition ParityState : Type := Z.

(** Messages are integers. *)

Definition ParityMessage : Type := Z.

(** A VLSM Type is defined using ParityState and ParityLabel. *)

Definition ParityType : VLSMType ParityMessage :=
{|
  state := ParityState;
  label := ParityLabel;
|}.

(**
  The specifications for the initial state, transition
  and guard predicate are as follows:
*)

Definition ParityComponent_initial_state_prop (st : ParityState) : Prop := st >= 1.

Definition ParityComponent_transition
  (l : ParityLabel) (st : ParityState) (om : option ParityMessage)
  : ParityState * option ParityMessage :=
  match om with
  | Some j  => (st - j, Some (multiplier * j))
  | None    => (st, None)
  end.

Definition ParityComponent_valid
  (l : ParityLabel) (st : ParityState) (om : option ParityMessage) : Prop :=
  match om with
  | Some msg => msg <= st /\ 2 <= msg
  | None     => False
  end.

(**
  We must also provide a proof that the intial state type
  is inhabited as the set of initial states is non-empty.
*)

Definition ParityComponent_initial_state_type : Type :=
  {st : ParityState | ParityComponent_initial_state_prop st}.

Program Definition ParityComponent_initial_state :
  ParityComponent_initial_state_type := exist _ 1 _.
Next Obligation.
Proof. done. Defined.

#[export] Instance ParityComponent_Inhabited_initial_state_type :
  Inhabited (ParityComponent_initial_state_type) :=
    populate (ParityComponent_initial_state).

(**
  An intermediate representation for the VLSM is required.
  It uses the previously defined specifications.
*)

Definition ParityMachine : VLSMMachine ParityType :=
{|
  initial_state_prop := ParityComponent_initial_state_prop;
  initial_message_prop := fun (ms : ParityMessage) => ms = multiplier;
  s0 := ParityComponent_Inhabited_initial_state_type;
  transition := fun l '(st, om) => ParityComponent_transition l st om;
  valid := fun l '(st, om) => ParityComponent_valid l st om;
|}.

(** The definition of the Parity VLSM. *)

Definition ParityVLSM : VLSM ParityMessage :=
{|
  vtype := ParityType;
  vmachine := ParityMachine;
|}.

(**
  To improve readability, we explicitly define [parity_label] as the value of
  the unit type.
*)

Definition parity_label : label ParityType := ().

(** ** Parity VLSM Examples *)

(** *** Example of an arbitrary transition *)

Lemma parity_example_transition_1 `(X : VLSM ParityMessage) :
  transition ParityVLSM parity_label (4, Some 10) = (-6, Some (multiplier * 10)).
Proof. done. Qed.

(** *** Example of a valid trace *)

(**
  The initial state cannot be included in this definition, because, since there
  is no transition reaching this state, it cannot be expressed in the manner below.
  Regarding the transition which leads to the final state, it technically could be
  included, but we choose to model this way, in order to be consistent
  with the subsequent example, where adding the last transition makes a qualitative
  difference to the trace.
*)

Definition parity_trace1_init : list (transition_item ParityVLSM) :=
  [ Build_transition_item parity_label (Some (multiplier ^ 2))
     (multiplier ^ 3 - multiplier ^ 2) (Some (multiplier ^ 3))
  ; Build_transition_item parity_label (Some multiplier)
     (multiplier ^ 3 - multiplier ^ 2 - multiplier) (Some (multiplier ^ 2)) ].

Definition parity_trace1_last_item : transition_item ParityVLSM :=
  Build_transition_item parity_label (Some multiplier)
    (multiplier ^ 3 - multiplier ^ 2 - multiplier - multiplier) (Some (multiplier ^ 2)).

Definition parity_trace1 : list (transition_item ParityVLSM) :=
  parity_trace1_init ++ [parity_trace1_last_item].

Definition parity_trace1_first_state : ParityState := multiplier ^ 3.

Definition parity_trace1_last_state : ParityState :=
  destination parity_trace1_last_item.

(** The trace we defined is valid: *)

Example parity_valid_message_prop_mult :
  valid_message_prop ParityVLSM multiplier.
Proof. by apply initial_message_is_valid. Qed.

Example parity_can_emit_square_mult :
  can_emit ParityVLSM (multiplier ^ 2).
Proof.
  exists (multiplier, Some multiplier), parity_label, 0.
  repeat split; [| | by lia.. | by cbn; do 2 f_equal; lia].
  - by apply initial_state_is_valid; cbn; unfold ParityComponent_initial_state_prop; lia.
  - by app_valid_tran.
Qed.

Example parity_valid_message_prop_square_mult :
  valid_message_prop ParityVLSM (multiplier ^ 2).
Proof.
  by eapply emitted_messages_are_valid, parity_can_emit_square_mult.
Qed.

Proposition parity_valid_transition_1 :
  input_valid_transition ParityVLSM parity_label
   (parity_trace1_first_state, Some (multiplier ^ 2))
   (multiplier ^ 3 - multiplier ^ 2, Some (multiplier ^ 3)).
Proof.
  repeat split; [| | | by lia].
  - by apply initial_state_is_valid; cbn;
      unfold ParityComponent_initial_state_prop, parity_trace1_first_state; lia.
  - by app_valid_tran; eapply parity_can_emit_square_mult.
  - by unfold parity_trace1_first_state; nia.
Qed.

Proposition parity_valid_transition_2 :
  multiplier >= 2 ->
  input_valid_transition ParityVLSM parity_label
   (multiplier ^ 3 - multiplier ^ 2, Some multiplier)
   (multiplier ^ 3 - multiplier ^ 2 - multiplier, Some (multiplier ^ 2)).
Proof.
  repeat split; [| | | by lia |].
  - by app_valid_tran; eapply parity_valid_transition_1; lia.
  - by app_valid_tran; apply parity_can_emit_square_mult.
  - by nia.
  - by cbn; do 2 f_equal; lia.
Qed.

Proposition parity_valid_transition_3 :
  multiplier >= 2 ->
  input_valid_transition ParityVLSM parity_label
   (multiplier ^ 3 - multiplier ^ 2 - multiplier, Some multiplier)
   (multiplier ^ 3 - multiplier ^ 2 - multiplier - multiplier, Some (multiplier ^ 2)).
Proof.
  repeat split; [| | | by lia |].
  - by app_valid_tran; apply parity_valid_transition_2.
  - by app_valid_tran; apply parity_can_emit_square_mult.
  - by nia.
  - by cbn; do 2 f_equal; lia.
Qed.

Example parity_valid_trace1 :
  multiplier >= 2 ->
  finite_valid_trace_init_to ParityVLSM
    parity_trace1_first_state parity_trace1_last_state parity_trace1.
Proof.
  constructor; unfold parity_trace1_first_state;
    [| by cbn; unfold ParityComponent_initial_state_prop; lia].
  repeat apply finite_valid_trace_from_to_extend.
  - by eapply finite_valid_trace_from_to_empty, input_valid_transition_destination,
      parity_valid_transition_3.
  - by apply parity_valid_transition_3.
  - by apply parity_valid_transition_2.
  - by apply parity_valid_transition_1; lia.
Qed.

Example parity_valid_trace1_alt :
  multiplier >= 2 ->
  finite_valid_trace_init_to_alt ParityVLSM
    parity_trace1_first_state parity_trace1_last_state parity_trace1.
Proof.
  constructor; [| by unfold parity_trace1_first_state; cbn; red; lia].
  repeat apply mvt_extend; [.. | by apply mvt_empty].
  - by eapply parity_valid_message_prop_square_mult; lia.
  - by eapply parity_valid_transition_1; lia.
  - cbn; split; [| by lia].
    by unfold parity_trace1_first_state; nia.
  - by apply parity_valid_message_prop_mult.
  - by apply parity_valid_transition_2.
  - by cbn; split; [nia | lia].
  - by apply parity_valid_message_prop_mult.
  - by apply parity_valid_transition_3.
  - by cbn; split; [nia | lia].
Qed.

(** *** Example of a constrained trace *)

(** The previously defined trace is obviously constrained, since it's valid. *)
Lemma parity_constrained_trace1 :
  multiplier >= 2 ->
  finite_constrained_trace_init_to_direct ParityVLSM
    parity_trace1_first_state parity_trace1_last_state parity_trace1.
Proof.
  constructor; [| by unfold parity_trace1_first_state; cbn; red; lia].
  repeat apply ct_extend; [.. | by apply ct_empty].
  - by eapply parity_valid_transition_1; lia.
  - cbn; split; [| by lia].
    by unfold parity_trace1_first_state; nia.
  - by apply parity_valid_transition_2.
  - by cbn; split; [nia | lia].
  - by apply parity_valid_transition_3.
  - by cbn; split; [nia | lia].
Qed.

Definition parity_trace2_init : list (transition_item ParityVLSM) :=
  [ Build_transition_item parity_label (Some multiplier) (2 * multiplier + 1) (Some (multiplier ^ 2))
  ; Build_transition_item parity_label (Some multiplier) (multiplier + 1) (Some (multiplier ^ 2)) ].

Definition parity_trace2_last_item : transition_item ParityVLSM :=
  Build_transition_item parity_label (Some (multiplier + 1)) 0 (Some (multiplier ^ 2 + multiplier) ).

Definition parity_trace2 : list (transition_item ParityVLSM) :=
  parity_trace2_init ++ [parity_trace2_last_item].

Definition parity_trace2_init_first_state : ParityState := 3 * multiplier + 1.

Definition parity_trace2_init_last_state : ParityState := multiplier + 1.

Definition parity_trace2_last_state : ParityState :=
  destination parity_trace2_last_item.

(** The given trace is valid without the last transition. *)

Proposition parity_valid_transition_1' :
  input_valid_transition ParityVLSM parity_label
    (parity_trace2_init_first_state, Some multiplier) (2 * multiplier + 1, Some (multiplier ^ 2)).
Proof.
  repeat split; [| | | by lia |].
  - apply initial_state_is_valid.
    by unfold parity_trace2_init_first_state; cbn; red; lia.
  - by app_valid_tran; apply parity_can_emit_square_mult.
  - by unfold parity_trace2_init_first_state; lia.
  - by cbn; do 2 f_equal; unfold parity_trace2_init_first_state; lia.
Qed.

Proposition parity_valid_transition_2' :
  input_valid_transition ParityVLSM parity_label
    (2 * multiplier + 1, Some multiplier) (multiplier + 1, Some (multiplier ^ 2)).
Proof.
  repeat split; [| | | by lia |].
  - apply initial_state_is_valid.
    by unfold parity_trace2_init_first_state; cbn; red; lia.
  - by app_valid_tran; apply parity_can_emit_square_mult.
  - by unfold parity_trace2_init_first_state; lia.
  - by cbn; do 2 f_equal; unfold parity_trace2_init_first_state; lia.
Qed.

Example parity_valid_trace2_init :
  finite_valid_trace_init_to ParityVLSM
    parity_trace2_init_first_state parity_trace2_init_last_state parity_trace2_init.
Proof.
  constructor; [| by unfold parity_trace2_init_first_state; cbn; red; lia].
  repeat apply finite_valid_trace_from_to_extend.
  - by eapply finite_valid_trace_from_to_empty, input_valid_transition_destination,
      parity_valid_transition_2'.
  - by apply parity_valid_transition_2'.
  - by apply parity_valid_transition_1'.
Qed.

Example parity_valid_trace2_init_alt :
  finite_valid_trace_init_to_alt ParityVLSM
    parity_trace2_init_first_state parity_trace2_init_last_state parity_trace2_init.
Proof.
  constructor; [| by unfold parity_trace2_init_first_state; cbn; red; lia].
  repeat apply mvt_extend; [.. | by apply mvt_empty].
  - by apply parity_valid_message_prop_mult.
  - by apply parity_valid_transition_1'.
  - by cbn; split; unfold parity_trace2_init_first_state; lia.
  - by apply parity_valid_message_prop_mult.
  - by apply parity_valid_transition_2'.
  - by cbn; split; unfold parity_trace2_init_first_state; lia.
Qed.

(**
  From the previous lemmas, it follows that the given trace
  without its last transition is constrained.
*)

Example parity_constrained_trace2_init :
  finite_constrained_trace_init_to ParityVLSM
    parity_trace2_init_first_state parity_trace2_init_last_state parity_trace2_init.
Proof.
  intros.
  apply VLSM_incl_finite_valid_trace_init_to.
  - by apply vlsm_incl_pre_loaded.
  - by apply parity_valid_trace2_init; lia.
Qed.

(**
  The trace is valid (in the preloaded Parity VLSM) without
  its last element and appending it to the end also gives
  a valid trace (in the preloaded Parity VLSM).
  It follows that the full trace is constrained in
  the original Parity VLSM.
*)

Example parity_constrained_trace2 :
  finite_constrained_trace_init_to ParityVLSM
    parity_trace2_init_first_state parity_trace2_last_state parity_trace2.
Proof.
  destruct parity_constrained_trace2_init as [Hfvt Hisp].
  split; [| done].
  eapply (extend_right_finite_trace_from_to _ Hfvt).
  repeat split.
  - by eapply finite_valid_trace_from_to_last_pstate.
  - by apply any_message_is_valid_in_preloaded.
  - by unfold parity_trace2_init_last_state.
  - by lia.
  - cbn; f_equal.
    + by unfold parity_trace2_init_last_state; lia.
    + by f_equal; nia.
Qed.

(** *** Example of a valid transition

  The last transition of a valid trace is valid.
*)

Lemma parity_example_valid_transition :
  input_valid_transition ParityVLSM parity_label
    (multiplier, Some multiplier) (0, Some (multiplier ^ 2)).
Proof.
  repeat split; [| | by lia.. |].
  - apply initial_state_is_valid.
    by unfold parity_trace2_init_first_state; cbn; red; lia.
  - by apply parity_valid_message_prop_mult.
  - by cbn; do 2 f_equal; lia.
Qed.

(** *** Example of a constrained transition

  The last transition of a constrained trace is constrained.
*)

Example parity_example_constrained_transition :
  input_valid_transition (pre_loaded_with_all_messages_vlsm ParityVLSM) parity_label
    (multiplier + 1, Some (multiplier + 1)) (0, Some (multiplier ^ 2 + multiplier)).
Proof.
  apply (finite_valid_trace_from_to_last_transition
    (pre_loaded_with_all_messages_vlsm ParityVLSM)
    parity_trace2_init_first_state parity_trace2_last_state parity_trace2_init
    parity_trace2 parity_trace2_last_item); [| done].
  by apply parity_constrained_trace2.
Qed.

(** ** Parity VLSM Properties *)

(** *** Inclusion into preloaded with all messages *)

Lemma parity_valid_is_constrained :
  VLSM_incl ParityVLSM (pre_loaded_with_all_messages_vlsm ParityVLSM).
Proof.
  by apply vlsm_incl_pre_loaded_with_all_messages_vlsm.
Qed.

(** *** Constrained messages are positive even integers *)

Lemma parity_constrained_messages_left :
  multiplier > 0 ->
  forall (m : ParityMessage),
    constrained_message_prop ParityVLSM m ->
    exists (j : Z), m = multiplier * j /\ j > 1.
Proof.
  intros Hgt0 m ([s []] & [] & s' & (_ & _ & []) & Ht).
  inversion Ht; subst.
  by exists p; split; lia.
Qed.

Lemma parity_constrained_messages_right :
  multiplier > 0 ->
  forall (m : ParityMessage),
    (exists (j : Z), m = multiplier * j) -> m > multiplier ->
    constrained_message_prop ParityVLSM m.
Proof.
  intros Hgt0 m (j & Hj) Hmgt0.
  unfold constrained_message_prop_direct, can_emit.
  exists (j, Some j), parity_label, 0.
  repeat split.
  - by apply initial_state_is_valid; cbn; red; nia.
  - by apply any_message_is_valid_in_preloaded.
  - by lia.
  - by nia.
  - by cbn; do 2 f_equal; lia.
Qed.

Lemma parity_constrained_messages :
  multiplier > 0 ->
  forall (m : ParityMessage),
    constrained_message_prop ParityVLSM m <-> (exists (j : Z), m = multiplier * j /\ j > 1).
Proof.
  split.
  - by apply parity_constrained_messages_left.
  - by intros [? []]; apply parity_constrained_messages_right; [| exists x | nia].
Qed.

(** *** Constrained states property *)

Lemma parity_constrained_states_right :
  forall (st : ParityState),
    constrained_state_prop ParityVLSM st -> st >= 0.
Proof.
  induction 1 using valid_state_prop_ind.
  - by cbn in Hs; unfold ParityComponent_initial_state_prop in Hs; lia.
  - destruct l, om, Ht as [(Hs & _ & []) Ht].
    by inversion Ht; subst; cbn in *; lia.
Qed.

Lemma parity_constrained_states_left :
  forall (st : ParityState),
    st >= 0 -> constrained_state_prop ParityVLSM st.
Proof.
  intros st Hst.
  apply input_valid_transition_destination
    with (l := parity_label) (s := st + 2) (om := Some 2) (om' := Some (2 * multiplier)).
  repeat split; [| | by lia.. | by cbn; do 2 f_equal; lia].
  - by apply initial_state_is_valid; cbn; unfold ParityComponent_initial_state_prop; lia.
  - by apply any_message_is_valid_in_preloaded.
Qed.

Lemma parity_constrained_states :
  forall (st : ParityState),
    constrained_state_prop ParityVLSM st <-> st >= 0.
Proof.
  split.
  - by apply parity_constrained_states_right.
  - by apply parity_constrained_states_left.
Qed.

(** *** Positive powers of the multiplier are valid messages *)

Lemma parity_valid_messages_powers_of_mult_right :
  forall (m : ParityMessage),
    valid_message_prop ParityVLSM m ->
    exists p : Z, p >= 1 /\ m = multiplier ^ p.
Proof.
  intros m [s Hvsm].
  assert (Hom : is_Some (Some m)) by (eexists; done).
  replace m with (is_Some_proj Hom) by done.
  revert Hvsm Hom; generalize (Some m) as om; intros.
  clear m; induction Hvsm using valid_state_message_prop_ind.
  - unfold option_initial_message_prop, from_option in Hom; cbn in Hom.
    destruct Hom as [m ->]; cbn in *.
    by exists 1; split; [lia | f_equal; lia].
  - destruct om as [m |]; [| done].
    unshelve edestruct IHHvsm2 as [x Hx]; [done |].
    inversion Ht; subst; clear Ht.
    cbn in Hx |- *; destruct Hx as [Hgeq1 ->].
    exists (x + 1).
    split; [by lia |].
    by rewrite <- Z.pow_succ_r; [| lia].
Qed.

Lemma parity_valid_messages_powers_of_mult_left :
  forall (p : Z),
    p >= 1 -> valid_message_prop ParityVLSM (multiplier ^ p).
Proof.
  intros p Hp.
  assert (Hle : 0 <= p - 1) by lia.
  replace p with (p - 1 + 1) by lia.
  remember (p - 1) as x.
  clear p Hp Heqx.
  revert x Hle.
  apply natlike_ind; [by apply initial_message_is_valid; cbn; lia |].
  intros x Hxgt0 Hindh.
  pose (msgin := multiplier ^ (x + 1)).
  apply emitted_messages_are_valid.
  exists (msgin, Some (multiplier ^ (x + 1))), parity_label, 0.
  repeat split.
  - by apply initial_state_is_valid; cbn; red; lia.
  - by apply Hindh.
  - by lia.
  - replace (x + 1) with (Z.succ x) by lia.
    by rewrite Z.pow_succ_r; lia.
  - by cbn; rewrite <- Z.pow_succ_r, Z.add_succ_l; [do 2 f_equal; lia | lia].
Qed.

Lemma parity_valid_messages_powers_of_mult :
  forall (m : ParityMessage),
    valid_message_prop ParityVLSM m
      <->
    exists p : Z, p >= 1 /\ m = multiplier ^ p.
Proof.
  split.
  - by intros; apply parity_valid_messages_powers_of_mult_right.
  - by intros (p & Hpgt0 & [= ->]); apply parity_valid_messages_powers_of_mult_left.
Qed.

(**
  The constrained transition from [parity_example_constrained_transition]
  is not also valid.
*)
Example parity_example_constrained_transition_not_valid :
  ~ input_valid_transition ParityVLSM parity_label
    (multiplier + 1, Some (multiplier + 1)) (0, Some (multiplier ^ 2 + multiplier)).
Proof.
  intros [(_ & Hm & _) _].
  apply parity_valid_messages_powers_of_mult in Hm as (p & Hp & Heq).
  rewrite <- (Z.succ_pred p) in Heq.
  rewrite Z.pow_succ_r in Heq by lia.
  assert (Hmul : multiplier * (multiplier ^ Z.pred p - 1) = 1) by lia.
  by apply Z.eq_mul_1_nonneg in Hmul as []; lia.
Qed.

End sec_parity_vlsm.

Section sec_composition.

Context
  {index : Type}
  (multipliers : index -> Z)
  (Hmultipliers : forall (i : index), multipliers i <> 0)
  `{FinSet index indexSet}
  .

Definition indexed_parity_vlsms (i : index) : VLSM ParityMessage :=
  ParityVLSM (multipliers i).

Context
  (parity_constraint : composite_label indexed_parity_vlsms ->
    composite_state indexed_parity_vlsms * option ParityMessage -> Prop)
  .

Definition parity_composite_vlsm : VLSM ParityMessage :=
  composite_vlsm indexed_parity_vlsms parity_constraint.

Lemma composite_state_pos
  (s : composite_state indexed_parity_vlsms)
  (Hs : valid_state_prop parity_composite_vlsm s) :
    forall (i : index), s i >= 0.
Proof.
  intros i.
  apply parity_constrained_states_right with (multipliers i).
  by apply (valid_state_project_preloaded ParityMessage indexed_parity_vlsms parity_constraint).
Qed.

(**
  Any valid message can be expressed as a non-empty product of powers
  of the multipliers associated to the components.
*)
Lemma composition_valid_messages_powers_of_mults_right (m : ParityMessage) :
  valid_message_prop parity_composite_vlsm m ->
  exists (f : fsfun index 0%nat),
    fin_supp f <> [] /\ m = fsfun_prod multipliers f.
Proof.
  intros [s Hvsm].
  remember (Some m) as om.
  revert m Heqom.
  induction Hvsm using valid_state_message_prop_ind; intros; subst.
  - destruct Hom as (n & (mielem & mi) & Hmi); cbn in mi, Hmi.
    exists (delta_nat_fsfun n).
    split; [by eapply elem_of_not_nil, elem_of_delta_nat_fsfun |].
    by rewrite <- Hmi, mi, prod_powers_delta.
  - destruct l as (k & lk).
    destruct om; [| done].
    destruct (IHHvsm2 p) as (f & Hdomf & ->); [done |].
    inversion Ht.
    exists (succ_fsfun f k).
    split; [| by rewrite fsfun_prod_succ].
    apply not_null_element in Hdomf; destruct_dec_sig Hdomf i Hi Heq.
    by eapply elem_of_not_nil, elem_of_succ_fsfun; right.
Qed.

End sec_composition.

Section sec_free_composition.

Context
  `{EqDecision index}
  (multipliers : index -> Z)
  `{Inhabited index}
  .

Definition free_parity_composite_vlsm : VLSM ParityMessage :=
  free_composite_vlsm (indexed_parity_vlsms multipliers).

#[local] Lemma free_parity_composite_vlsm_emits_multiplier :
  forall (m : ParityMessage),
    valid_message_prop free_parity_composite_vlsm m ->
    m >= 2 ->
  forall (n : index),
  input_valid_transition free_parity_composite_vlsm (existT n parity_label)
(update (const 1) n (m + 1), Some m)
(const 1, Some (multipliers n * m)).
Proof.
  repeat split.
  - apply initial_state_is_valid.
    intros j; cbn; red.
    by destruct (decide (n = j)) as [-> |];
      [rewrite update_eq; lia | rewrite update_neq].
  - done.
  - by rewrite update_eq; lia.
  - by lia.
  - cbn; f_equal; rewrite update_eq.
    extensionality j; cbn.
    destruct (decide (n =j)) as [-> |]; state_update_simpl; [by lia |].
    by rewrite update_neq.
Qed.

Lemma composition_valid_messages_powers_of_mults_left
  (Hmpos : forall (i : index), multipliers i > 1) (m : ParityMessage)
  (f : fsfun index 0%nat) :
    fin_supp f <> [] /\ m = fsfun_prod multipliers f ->
    valid_message_prop free_parity_composite_vlsm m.
Proof.
  intros [Hpowgeq1 Hm]; revert f Hpowgeq1 m Hm.
  apply (nat_fsfun_ind (fun (f : fsfun index 0%nat) => fin_supp f <> [] ->
    forall m : ParityMessage, m = fsfun_prod multipliers f ->
    valid_message_prop free_parity_composite_vlsm m)); [| done |].
  - intros f1 f2 Heq Hall Hi m Hm.
    eapply Hall; [| by rewrite Heq].
    contradict Hi.
    apply Permutation_nil.
    by rewrite <- Hi, Heq.
  - intros n f0 IHf0 Hi m Hm.
    destruct (nat_fsfun_inv f0) as [Heq | (n' & f0' & Heq)].
    + rewrite fsfun_prod_succ, Heq, fsfun_prod_zero in Hm.
      apply initial_message_is_valid. exists n.
      by unshelve eexists (exist _ m _); cbn; lia.
    + assert (Hmvalid : valid_message_prop free_parity_composite_vlsm (fsfun_prod multipliers f0)).
      {
        apply IHf0; [| done].
        assert (Hinh : fin_supp (succ_fsfun f0' n') <> []).
        {
          by eapply elem_of_not_nil, elem_of_succ_fsfun; left.
        }
        contradict Hinh; apply Permutation_nil.
        by rewrite <- Hinh, Heq.
      }
      subst m; rewrite fsfun_prod_succ.
      assert (Hpos : fsfun_prod multipliers f0 >= multipliers n').
      {
        rewrite Heq, fsfun_prod_succ.
        cut (fsfun_prod multipliers f0' > 0); [by specialize (Hmpos n'); nia |].
        destruct (decide (fin_supp f0' = [])) as [Hz |].
        - eapply empty_fsfun_supp_inv in Hz as ->.
          by setoid_rewrite fsfun_prod_zero; lia.
        - apply prod_powers_gt; [by lia | | done].
          by intro i; specialize (Hmpos i); lia.
      }
      specialize (Hmpos n').
      by eapply input_valid_transition_out,
        free_parity_composite_vlsm_emits_multiplier; [| lia].
Qed.

Lemma composition_valid_messages_powers_of_mults
  (Hmpos : forall (i : index), multipliers i > 1) (m : ParityMessage) :
    valid_message_prop free_parity_composite_vlsm m <->
  exists (f : fsfun index 0%nat),
    fin_supp f <> [] /\ m = fsfun_prod multipliers f.
Proof.
  split.
  - intros Hvm.
    eapply VLSM_incl_valid_message in Hvm; cycle 1.
    + by apply free_composite_vlsm_spec.
    + by do 2 red.
    + by cbn in Hvm; eapply composition_valid_messages_powers_of_mults_right.
  - by intros [? []]; eapply composition_valid_messages_powers_of_mults_left.
Qed.

Lemma composition_valid_message_ge_2
  (Hmpos : forall (i : index), multipliers i > 1) (m : ParityMessage) :
  valid_message_prop free_parity_composite_vlsm m -> m >= 2.
Proof.
  intro Hv.
  apply composition_valid_messages_powers_of_mults in Hv
    as (i & Hsupp & ->); [| done].
  cut (fsfun_prod multipliers i > 1); [by lia |].
  by apply prod_powers_gt; [lia | ..].
Qed.

End sec_free_composition.

Section sec_parity23.

Inductive index23 := two | three.

Definition multipliers23 (n : index23) : Z :=
  match n with
  | two => 2
  | three => 3
  end.

#[local] Instance inhabited_index23 : Inhabited index23 := populate two.

#[local] Instance eq_dec_index23 : EqDecision index23.
Proof. by intros x y; unfold Decision; decide equality. Qed.

#[local] Instance finite_index23 : finite.Finite index23.
Proof.
  exists [two; three].
  - by repeat constructor; set_solver.
  - by intros []; set_solver.
Qed.

Definition parity_constraint
  (l : composite_label (indexed_parity_vlsms multipliers23))
  (sm : composite_state (indexed_parity_vlsms multipliers23) * option ParityMessage) : Prop :=
    let i := projT1 l in
    let (s', _) := composite_transition (indexed_parity_vlsms multipliers23) l sm in
    Z.Even (((fst sm) i) + (s' i)).

Definition parity_composite_vlsm23 :=
  parity_composite_vlsm multipliers23 parity_constraint.

Definition final_state (s : composite_state (indexed_parity_vlsms multipliers23)) :=
  valid_state_prop parity_composite_vlsm23 s /\
  ~ exists
    (l : composite_label (indexed_parity_vlsms multipliers23))
    (om : option ParityMessage)
    (som' : composite_state (indexed_parity_vlsms multipliers23) * option ParityMessage),
      input_valid_transition parity_composite_vlsm23 l (s, om) som'.

Definition statenm (n m : Z) : composite_state (indexed_parity_vlsms multipliers23) :=
  fun (i : index23) => match i with two => n | three => m end.

Definition state00 := statenm 0 0.

Definition state01 := statenm 0 1.

Definition state10 := statenm 1 0.

Definition state11 := statenm 1 1.

Definition state12 := statenm 1 2.

Definition state21 := statenm 2 1.

Definition state22 := statenm 2 2.

Definition state02 := statenm 0 2.

Example valid_statenm_geq1 (n m : Z) (Hn : n >= 1) (Hm : m >= 1) :
  valid_state_prop parity_composite_vlsm23 (statenm n m).
Proof.
  by apply initial_state_is_valid; intros []; cbn; red.
Qed.

Example valid_state11 : valid_state_prop parity_composite_vlsm23 state11.
Proof. by apply (valid_statenm_geq1 1 1); lia. Qed.

Example valid_state00 : valid_state_prop parity_composite_vlsm23 state00.
Proof.
  apply input_valid_transition_destination
    with (l := existT three parity_label) (s := state02) (om := Some 2) (om' := Some 6).
  repeat split.
  - apply input_valid_transition_destination
      with (l := existT two parity_label) (s := state22) (om := Some 2) (om' := Some 4).
    repeat split.
    + by apply valid_statenm_geq1.
    + apply initial_message_is_valid.
      exists two.
      assert (Hinit : initial_message_prop (indexed_parity_vlsms multipliers23 two) 2) by done.
      by exists (exist _ 2 Hinit).
    + by cbn; lia.
    + by lia.
    + by cbn; state_update_simpl; exists 1; lia.
    + by cbn; f_equal; extensionality i; destruct i; cbn; state_update_simpl; cbn; lia.
  - apply initial_message_is_valid.
    exists two.
    assert (Hinit : initial_message_prop (indexed_parity_vlsms multipliers23 two) 2) by done.
    by exists (exist _ 2 Hinit).
  - by unfold state02; cbn; lia.
  - by lia.
  - by cbn; state_update_simpl; exists 1; lia.
  - by cbn; f_equal; extensionality i; destruct i; cbn; state_update_simpl; cbn; lia.
Qed.

Example valid_state01 : valid_state_prop parity_composite_vlsm23 state01.
Proof.
  apply input_valid_transition_destination
    with (l := existT two parity_label) (s := state21) (om := Some 2) (om' := Some 4).
  repeat split.
  - by apply valid_statenm_geq1.
  - apply initial_message_is_valid.
    exists two.
    assert (Hinit : initial_message_prop (indexed_parity_vlsms multipliers23 two) 2) by done.
    by exists (exist _ 2 Hinit).
  - by cbn; lia.
  - by lia.
  - by cbn; state_update_simpl; exists 1; lia.
  - by cbn; f_equal; extensionality i; destruct i; cbn; state_update_simpl; cbn; lia.
Qed.

Example valid_state10 : valid_state_prop parity_composite_vlsm23 state10.
Proof.
  apply input_valid_transition_destination
    with (l := existT three parity_label) (s := state12) (om := Some 2) (om' := Some 6).
  repeat split.
  - by apply valid_statenm_geq1.
  - apply initial_message_is_valid.
    exists two.
    assert (Hinit : initial_message_prop (indexed_parity_vlsms multipliers23 two) 2) by done.
    by exists (exist _ 2 Hinit).
  - by cbn; lia.
  - by lia.
  - by cbn; state_update_simpl; exists 1; lia.
  - by cbn; f_equal; extensionality i; destruct i; cbn; state_update_simpl; cbn; lia.
Qed.

Lemma final_state_prop23_left (s : composite_state (indexed_parity_vlsms multipliers23)) :
  (s = state00 \/ s = state01 \/ s = state10 \/ s = state11) -> final_state s.
Proof.
  intros Hcases.
  split.
  - destruct Hcases as [Hst | [Hst | [Hst | Hst]]]; subst.
    + by apply valid_state00.
    + by apply valid_state01.
    + by apply valid_state10.
    + by apply valid_state11.
  - intros ([i li] & om & som' & (Hs & Hom & Hv & Hc) & Ht).
    unfold parity_constraint in Hc.
    replace (composite_transition _ _ _) with som' in Hc.
    destruct om; [| done].
    cbn in *; subst.
    state_update_simpl.
    assert (Z.Even p) as [n Hp] by (destruct Hc as [n Hc]; exists (s i - n); lia).
    by destruct Hcases as [Hst |[Hst |[Hst | Hst]]]; subst; destruct i; cbn in *; lia.
Qed.

Lemma final_state_prop23_right (s : composite_state (indexed_parity_vlsms multipliers23)) :
  final_state s ->
    (s two = 0 /\ s three = 0) \/ (s two = 0 /\ s three = 1) \/
    (s two = 1 /\ s three = 0) \/ (s two = 1 /\ s three = 1).
Proof.
  intros [Hs Hfinal].
  destruct (decide ((s two = 0 /\ s three = 0) \/ (s two = 0 /\ s three = 1) \/
    (s two = 1 /\ s three = 0) \/ (s two = 1 /\ s three = 1))); [done |].
  assert (exists (i : index23), s i > 1) as [i Hi].
  {
    cut (s two > 1 \/ s three > 1).
    - by intros []; eexists.
    - assert (s two >= 0) by (eapply composite_state_pos; done).
      assert (s three >= 0) by (eapply composite_state_pos; done).
      by lia.
  }
  contradict Hfinal.
  clear n.
  exists (existT i parity_label), (Some 2),
    (state_update (indexed_parity_vlsms multipliers23) s i (s i - 2), Some (multipliers23 i * 2)).
  repeat split; [done | ..].
  - apply initial_message_is_valid.
    exists two.
    assert (Hinit : initial_message_prop (indexed_parity_vlsms multipliers23 two) 2) by done.
    by exists (exist _ 2 Hinit).
  - by lia.
  - by lia.
  - by cbn; state_update_simpl; exists (s i - 1); lia.
Qed.

End sec_parity23.

(** ** A VLSM composition for all primes

  In the following section we give an example of a composition with an infinite
  number of [ParityVLSM] components, one for each prime number.

  Then we characterize the valid messages for this composition to be precisely
  all natural numbers larger than 1.

  Finally, we show that in this composition any component is a validator.
*)

Section sec_primes_vlsm_composition.

Definition primes_vlsm_composition : VLSM Z :=
  free_parity_composite_vlsm (fun p : primes => `p).

Lemma primes_vlsm_composition_valid_message_char :
  forall (m : Z),
    valid_message_prop primes_vlsm_composition m <-> (m > 1)%Z.
Proof.
  assert (Hprime_pos : forall i : primes, `i > 1).
  {
    intro i.
    destruct_dec_sig i n Hn Heq; subst; cbn.
    by destruct Hn; lia.
  }
  intros m; unfold primes_vlsm_composition.
  rewrite composition_valid_messages_powers_of_mults;
    [| by intro i; specialize (Hprime_pos i); lia..].
  split.
  - intros (fp & Hdom_fp & ->).
    by apply prod_powers_gt.
  - by apply primes_factorization.
Qed.

(**
  For any prime number, its corresponding component in the [primes_vlsm_composition]
  is a validator for that composition, i.e., all of its constrained transitions
  can be lifted to valid transitions for the composition.
*)
Theorem component_projection_validator_prop_primes :
  forall (p : primes),
    component_projection_validator_prop
      (indexed_parity_vlsms (fun p : primes => ` p))
      (fun _ _ => True) p.
Proof.
  intros p lp sp [m|] (Hsp & _ & []).
  exists (lift_to_composite_state' (indexed_parity_vlsms (fun p : primes => `p)) p sp).
  repeat split; [by state_update_simpl | | | by state_update_simpl | done].
  - apply initial_state_is_valid.
    intros p'; cbn; red.
    by destruct (decide (p = p')); subst; state_update_simpl; cbn; [lia |].
  - eapply VLSM_incl_valid_message; [by apply free_composite_vlsm_spec | ..].
    + by do 2 red.
    + by apply primes_vlsm_composition_valid_message_char; lia.
Qed.

(** *** A (slightly) constrained composition of primes *)

(**
  To show how a composition constraint affects validation, we here add a very
  simple constraint, that the received message must be even, to the composition.
*)
Inductive EvenConstraint :
  label primes_vlsm_composition -> state primes_vlsm_composition * option Z -> Prop :=
| even_constraint : forall l s m, Z.Even m -> EvenConstraint l (s, Some m).

Definition even_constrained_primes_composition : VLSM Z :=
  constrained_vlsm primes_vlsm_composition EvenConstraint.

#[local] Lemma even_constrained_primes_composition_emits_multiplier :
  forall (m : ParityMessage),
    valid_message_prop even_constrained_primes_composition m ->
    m >= 2 ->
    Z.Even m ->
  forall (n : primes),
  input_valid_transition even_constrained_primes_composition (existT n parity_label)
  (update (const 1) n (m + 1), Some m)
  (const 1, Some (` n * m)).
Proof.
  repeat split.
  - apply initial_state_is_valid.
    intros j; cbn; red.
    by destruct (decide (n = j)) as [-> |];
      [rewrite update_eq; lia | rewrite update_neq].
  - done.
  - by rewrite update_eq; lia.
  - by lia.
  - done.
  - cbn; f_equal; extensionality j; cbn.
    destruct (decide (n = j)); subst; state_update_simpl.
    + by rewrite update_eq; lia.
    + by rewrite update_neq.
Qed.

Lemma even_constrained_primes_composition_valid_messages_left (m : Z) :
  m > 1 -> Z.Even m -> valid_message_prop even_constrained_primes_composition m.
Proof.
  intros Hm1 Hmeven.
  assert (Hinit : composite_initial_message_prop (indexed_parity_vlsms (fun p : primes => `p)) 2)
    by (unshelve eexists (dexist 2 prime_2), (exist _ 2 _); done).
  destruct (decide (m = 2)) as [-> | Hm2]; [by apply initial_message_is_valid |].
  destruct Hmeven as [n ->].
  assert (Hn : 2 <= n) by lia.
  pose (P := fun n => valid_message_prop even_constrained_primes_composition (2 * n)).
  cut (P n); [done |].
  clear -Hn Hinit; revert n Hn; apply Zlt_lower_bound_ind; subst P; cbn; intros n Hind Hn.
  destruct (decide (prime n)) as [Hp | Hnp].
  - replace (2 * n) with (` (dexist n Hp) * 2) by (cbn; lia).
    eapply input_valid_transition_out,
      even_constrained_primes_composition_emits_multiplier;
        [| done | by exists 1].
    by apply initial_message_is_valid.
  - apply not_prime_divide_prime in Hnp as (m & Hp & q & Hq & ->); [| by lia].
    replace (2 * (q * m)) with (` (dexist m Hp) * (2 * q)) by (cbn; lia).
    eapply input_valid_transition_out,
      even_constrained_primes_composition_emits_multiplier;
      [| by lia | by eexists].
    by apply Hind.
Qed.

(**
  The valid messages of the [even_constrained_primes_composition] are precisely
  all positive even numbers.
*)
Lemma even_constrained_primes_composition_valid_message_char (m : Z) :
  valid_message_prop even_constrained_primes_composition m
    <->
  (m > 1)%Z /\ Z.Even m \/ prime m.
Proof.
  split.
  - intros Hm.
    cut ((m > 1)%Z /\ (Z.Even m \/ prime m)).
    {
      by destruct (decide (prime m)); [right | left; itauto].
    }
    split.
    + apply primes_vlsm_composition_valid_message_char.
      eapply VLSM_incl_valid_message; [..| done].
      * by apply (VLSM_incl_constrained_vlsm primes_vlsm_composition).
      * by do 2 red.
    + apply emitted_messages_are_valid_iff in Hm
        as [([p Hp] & [i Hi] & <-) | ([s [im |]] & [i li] & s' & (_ & _ & _ & Hc) & Ht)];
        cbn in *; [by subst; right; apply bool_decide_spec in Hp | | done].
      inversion Hc; subst; clear Hc.
      inversion Ht; subst; clear Ht.
      by left; apply Zeven_equiv, Zeven_mult_Zeven_r, Zeven_equiv.
  - intros [[] | Hprime].
    + by apply even_constrained_primes_composition_valid_messages_left.
    + apply initial_message_is_valid.
      by unshelve eexists (dexist m Hprime), (exist _ m _).
Qed.

(** No component is validating for the [even_constrained_primes_composition]. *)
Lemma even_constrained_primes_composition_no_validator :
  forall (p : primes),
    ~ component_projection_validator_prop
        (indexed_parity_vlsms (fun p : primes => ` p))
        EvenConstraint p.
Proof.
  intros p Hnv.
  cut (input_valid
    (pre_loaded_with_all_messages_vlsm
      (indexed_parity_vlsms (λ p0 : primes, `p0) p)) () (3, Some 3)).
  {
    intro Hiv.
    apply Hnv in Hiv as (s & _ & _ & _ & _ & Hc).
    by inversion Hc as [? ? ? []]; lia.
  }
  repeat split; [| by apply any_message_is_valid_in_preloaded | by lia..].
  apply initial_state_is_valid; cbn.
  by red; lia.
Qed.

(**
  Now we show that if we constrain each component with a local condition
  equivalent to the global constraint we can recover validation.
*)
Inductive LocalEvenConstraint (mult : Z) :
  label (ParityVLSM mult) -> state (ParityVLSM mult) * option Z -> Prop :=
| local_even_constraint : forall l s m, Z.Even m ->
    LocalEvenConstraint mult l (s, Some m).

Definition even_prime_vlsms (p : primes) : VLSM ParityMessage :=
  constrained_vlsm (ParityVLSM (`p)) (LocalEvenConstraint (`p)).

(**
  Adding the local constraint to each component does not change the behavior
  of the composition.
*)
Lemma even_constrained_primes_composition_incl_left :
  VLSM_incl
    even_constrained_primes_composition
    (composite_vlsm even_prime_vlsms EvenConstraint).
Proof.
  apply basic_VLSM_strong_incl; cycle 3; [by intros ? **.. |].
  intros [p []] s [m |] [Hv Hc]; [| by inversion Hc]; cbn.
  split; [| done].
  split; [| by inversion Hc].
  by destruct Hv.
Qed.

(**
  The validation result is recovered for the new constrained components and composition.
*)
Lemma even_constrained_primes_composition_all_validators :
  forall (p : primes),
    component_projection_validator_prop even_prime_vlsms EvenConstraint p.
Proof.
  intros p lp sp [m |] (Hsp & _ & [[] Hc]).
  inversion Hc as [? ? ? Heven]; subst.
  exists (lift_to_composite_state' (indexed_parity_vlsms (fun p : primes => `p)) p sp).
  repeat split; [by state_update_simpl | | | by state_update_simpl | done..].
  - apply initial_state_is_valid.
    intro p'; cbn; red.
    by destruct (decide (p = p')); subst; state_update_simpl; cbn; [lia |].
  - apply option_valid_message_Some.
    eapply VLSM_incl_valid_message;
      [by apply even_constrained_primes_composition_incl_left | ..].
    + by do 2 red.
    + apply even_constrained_primes_composition_valid_message_char.
      by left; split; [lia |].
Qed.

End sec_primes_vlsm_composition.
