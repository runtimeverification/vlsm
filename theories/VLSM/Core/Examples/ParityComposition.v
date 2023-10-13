From VLSM.Lib Require Import Itauto.
From Coq Require Import FunctionalExtensionality.
From stdpp Require Import prelude.
From VLSM.Lib Require Import Preamble StdppExtras FinSuppFn Primes.
From VLSM.Core Require Import VLSM PreloadedVLSM VLSMProjections Composition.

(** * Parity VLSM

  This module demonstrates some basic notions of the VLSM framework.
  The idea of the parity VLSM is to store an integer and continually decrement it,
  while a constraint is checked at each step. The definitions and lemmas tap into
  concepts such as valid and constrained traces, transitions, states, and messages.
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
 (multiplier_geq_0 : multiplier <> 0)
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
  | Some msg => msg <= st /\ 1 <= msg
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
  multiplier > 0 -> can_emit ParityVLSM (multiplier ^ 2).
Proof.
  exists (multiplier, Some multiplier), parity_label, 0.
  repeat split; [| | by lia.. | by cbn; do 2 f_equal; lia].
  - by apply initial_state_is_valid; cbn; unfold ParityComponent_initial_state_prop; lia.
  - by app_valid_tran.
Qed.

Example parity_valid_message_prop_square_mult :
  multiplier > 0 -> valid_message_prop ParityVLSM (multiplier ^ 2).
Proof.
  intros Hgt0.
  by eapply (emitted_messages_are_valid ParityVLSM (multiplier ^ 2)
    (parity_can_emit_square_mult Hgt0)).
Qed.

Proposition parity_valid_transition_1 :
  multiplier > 0 ->
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
  finite_constrained_trace_init_to ParityVLSM
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
  [ Build_transition_item parity_label (Some multiplier) (multiplier + 1) (Some (multiplier ^ 2))
  ; Build_transition_item parity_label (Some multiplier) 1 (Some (multiplier ^ 2)) ].

Definition parity_trace2_last_item : transition_item ParityVLSM :=
  Build_transition_item parity_label (Some 1) 0 (Some multiplier).

Definition parity_trace2 : list (transition_item ParityVLSM) :=
  parity_trace2_init ++ [parity_trace2_last_item].

Definition parity_trace2_init_first_state : ParityState := 2 * multiplier + 1.

Definition parity_trace2_init_last_state : ParityState := 1.

Definition parity_trace2_last_state : ParityState :=
  destination parity_trace2_last_item.

(** The given trace is valid without the last transition. *)

Proposition parity_valid_transition_1' :
  multiplier > 0 ->
  input_valid_transition ParityVLSM parity_label
    (parity_trace2_init_first_state, Some multiplier) (multiplier + 1, Some (multiplier ^ 2)).
Proof.
  repeat split; [| | | by lia |].
  - apply initial_state_is_valid.
    by unfold parity_trace2_init_first_state; cbn; red; lia.
  - by app_valid_tran; apply parity_can_emit_square_mult.
  - by unfold parity_trace2_init_first_state; lia.
  - by cbn; do 2 f_equal; unfold parity_trace2_init_first_state; lia.
Qed.

Proposition parity_valid_transition_2' :
  multiplier > 0 ->
  input_valid_transition ParityVLSM parity_label
    (multiplier + 1, Some multiplier) (1, Some (multiplier ^ 2)).
Proof.
  repeat split; [| | | by lia |].
  - apply initial_state_is_valid.
    by unfold parity_trace2_init_first_state; cbn; red; lia.
  - by app_valid_tran; apply parity_can_emit_square_mult.
  - by unfold parity_trace2_init_first_state; lia.
  - by cbn; do 2 f_equal; unfold parity_trace2_init_first_state; lia.
Qed.

Example parity_valid_trace2_init :
  multiplier > 0 ->
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
  multiplier > 0 ->
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
  multiplier > 0 ->
  finite_constrained_trace_init_to_alt ParityVLSM
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
  multiplier > 0 ->
  finite_constrained_trace_init_to_alt ParityVLSM
    parity_trace2_init_first_state parity_trace2_last_state parity_trace2.
Proof.
  intros Hgt0.
  destruct parity_constrained_trace2_init as [Hfvt Hisp]; [done |].
  split; [| done].
  eapply (extend_right_finite_trace_from_to _ Hfvt).
  repeat split; [| | | by lia |].
  - by eapply finite_valid_trace_from_to_last_pstate.
  - by apply any_message_is_valid_in_preloaded.
  - by unfold parity_trace2_init_last_state.
  - by cbn; do 2 f_equal; lia.
Qed.

(** *** Example of a valid transition

  The last transition of a valid trace is valid.
*)

Lemma parity_example_valid_transition :
  multiplier > 0 ->
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
  multiplier > 0 ->
  input_valid_transition (pre_loaded_with_all_messages_vlsm ParityVLSM) parity_label
    (1, Some 1) (0, Some multiplier).
Proof.
  intros Hgt0.
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
    constrained_message_prop_alt ParityVLSM m ->
    exists (j : Z), m = multiplier * j /\ m > 0.
Proof.
  intros Hgt0 m ([s []] & [] & s' & (_ & _ & []) & Ht).
  inversion Ht; subst.
  by exists p; split; lia.
Qed.

Lemma parity_constrained_messages_right :
  multiplier > 0 ->
  forall (m : ParityMessage),
    (exists (j : Z), m = multiplier * j) -> m > 0 ->
    constrained_message_prop_alt ParityVLSM m.
Proof.
  intros Hgt0 m (j & Hj) Hmgt0.
  unfold constrained_message_prop_alt, can_emit.
  exists (j, Some j), parity_label, 0.
  repeat split; [| | by lia.. | by cbn; do 2 f_equal; lia]; cycle 1.
  - by apply any_message_is_valid_in_preloaded.
  - apply input_valid_transition_destination
      with (l := parity_label) (s := j + 1) (om := Some 1) (om' := Some multiplier).
    repeat split; [| | by lia.. |].
    + apply initial_state_is_valid.
      by unfold parity_trace2_init_first_state; cbn; red; lia.
    + by apply any_message_is_valid_in_preloaded.
    + by cbn; do 2 f_equal; lia.
Qed.

Lemma parity_constrained_messages :
  multiplier > 0 ->
  forall (m : ParityMessage),
    constrained_message_prop_alt ParityVLSM m <-> (exists (j : Z), m = multiplier * j /\ m > 0).
Proof.
  split.
  - by apply parity_constrained_messages_left.
  - by intros [? []]; apply parity_constrained_messages_right; [| exists x |].
Qed.

(** *** Constrained states property *)

Lemma parity_constrained_states_right :
  forall (st : ParityState),
    constrained_state_prop_alt ParityVLSM st -> st >= 0.
Proof.
  induction 1 using valid_state_prop_ind.
  - by cbn in Hs; unfold ParityComponent_initial_state_prop in Hs; lia.
  - destruct l, om, Ht as [(Hs & _ & []) Ht].
    by inversion Ht; subst; cbn in *; lia.
Qed.

Lemma parity_constrained_states_left :
  forall (st : ParityState),
    st >= 0 -> constrained_state_prop_alt ParityVLSM st.
Proof.
  intros st Hst.
  unfold constrained_state_prop_alt.
  apply input_valid_transition_destination
    with (l := parity_label) (s := st + 1) (om := Some 1) (om' := Some multiplier).
  repeat split; [| | by lia.. | by cbn; do 2 f_equal; lia].
  - by apply initial_state_is_valid; cbn; unfold ParityComponent_initial_state_prop; lia.
  - by apply any_message_is_valid_in_preloaded.
Qed.

Lemma parity_constrained_states :
  forall (st : ParityState),
    constrained_state_prop_alt ParityVLSM st <-> st >= 0.
Proof.
  split.
  - by apply parity_constrained_states_right.
  - by apply parity_constrained_states_left.
Qed.

(** *** Powers of 2 greater or equal than 2 are valid messages *)

Lemma parity_valid_messages_powers_of_mult_right :
  forall (m : option ParityMessage),
    option_valid_message_prop ParityVLSM m -> m <> None ->
      exists p : Z, p >= 1 /\ m = Some (multiplier ^ p).
Proof.
  intros m [s Hvsm] Hmnn.
  induction Hvsm using valid_state_message_prop_ind.
  - unfold option_initial_message_prop, from_option in Hom; cbn in Hom.
    destruct om; [| done].
    by exists 1; split; [lia | f_equal; lia].
  - destruct om, IHHvsm2 as [x Hx]; inversion Ht; cycle 1; [| done..].
    exists (x + 1).
    split; [by lia |].
    destruct Hx as [Hgeq1 [= ->]].
    by rewrite <- Z.pow_succ_r; [| lia].
Qed.

Lemma parity_valid_messages_powers_of_mult_left :
  multiplier > 0 ->
  forall (p : Z),
    p >= 1 -> option_valid_message_prop ParityVLSM (Some (multiplier ^ p)).
Proof.
  intros Hgt0 p Hp.
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
  repeat split; [| by apply Hindh | by lia.. |].
  - by apply initial_state_is_valid; cbn; unfold ParityComponent_initial_state_prop; lia.
  - by cbn; rewrite <- Z.pow_succ_r, Z.add_succ_l; [do 2 f_equal; lia | lia].
Qed.

Lemma parity_valid_messages_powers_of_mult :
  forall (om : option ParityMessage), multiplier > 0 ->
    om <> None -> ((option_valid_message_prop ParityVLSM om) <->
    (exists p : Z, p >= 1 /\ om = Some (multiplier ^ p))).
Proof.
  split.
  - by intros; apply parity_valid_messages_powers_of_mult_right.
  - by intros (p & Hpgt0 & [= ->]); apply parity_valid_messages_powers_of_mult_left.
Qed.

End sec_parity_vlsm.

(*
Definition ls_fin_supp_nat_fn (index : Type) :=
  fin_supp_nat_fn (index := index) (indexSet := listset index).
Definition ls_powers_ind (index : Type) `{EqDecision index} :=
  powers_ind (index := index) (indexSet := listset index).
*)

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

Lemma composition_valid_messages_powers_of_mults_right (m : ParityMessage) :
  valid_message_prop parity_composite_vlsm m ->
  exists (fp : fin_supp_nat_fn index indexSet) (i : index),
    (fin_supp_f fp i >= 1)%nat /\ m = prod_fin_supp_nat_fn multipliers fp.
Proof.
  intros [s Hvsm].
  remember (Some m) as om.
  revert m Heqom.
  induction Hvsm using valid_state_message_prop_ind; intros; subst.
  - destruct Hom as (n & (mielem & mi) & Hmi); cbn in mi, Hmi.
    exists (delta_fin_supp_nat_fn n), n.
    unfold delta_fin_supp_nat_fn at 1; cbn.
    split; [by rewrite increment_fn_eq; cbn; lia |].
    by rewrite <- Hmi, mi, prod_powers_delta.
  - destruct l as (k & lk).
    destruct om; [| done].
    destruct (IHHvsm2 p) as [fp (i & Hi)]; [done |].
    inversion Ht.
    exists (increment_fin_supp_nat_fn fp k), k; cbn.
    split; [by rewrite increment_fn_eq; cbn; lia |].
    destruct Hi as [Hgeq1 ->].
    by rewrite prod_fin_supp_nat_fn_increment.
Qed.

End sec_composition.

Section sec_free_composition.

Context
  `{EqDecision index}
  (multipliers : index -> Z)
  (Hmultipliers : forall (i : index), multipliers i <> 0)
  `{Inhabited index}
  .

Definition free_parity_composite_vlsm : VLSM ParityMessage :=
  free_composite_vlsm (indexed_parity_vlsms multipliers).

Lemma composition_valid_messages_powers_of_mults_left
  (Hmpos : forall (i : index), multipliers i > 0) (m : ParityMessage) :
  forall (fp : fin_supp_nat_fn index (listset index)) (i : index),
    (fin_supp_f fp i >= 1)%nat /\ m = prod_fin_supp_nat_fn multipliers fp ->
    valid_message_prop free_parity_composite_vlsm m.
Proof.
  intros fp i [Hpowgeq1 Hm]; revert i Hpowgeq1 m Hm.
  pose (P := fun (fp : fin_supp_nat_fn index (listset index)) =>
    forall i : index, (fin_supp_f fp i >= 1)%nat ->
    forall m : ParityMessage, m = prod_fin_supp_nat_fn multipliers fp ->
    valid_message_prop free_parity_composite_vlsm m).
  cut (P fp); [done |].
  revert fp; apply fin_supp_nat_fn_ind; subst P.
  - intros fp1 fp2 Heq Hall i Hi m Hm.
    eapply Hall with (i := i); [| by rewrite Heq].
    by replace (fin_supp_f fp1) with (fin_supp_f fp2) by (rewrite Heq; done).
  - by cbn; lia.
  - intros n fp0 IHfp0 i Hi m Hm.
    pose proof (Hfp0 := FinSuppNatFn_complete fp0).
    inversion Hfp0 as [_fp Heqv Heq | n' fp0' _fp Hfp0' Heqv Heq]; subst _fp;
      rewrite Heqv in *.
    + rewrite prod_fin_supp_nat_fn_increment, prod_fin_supp_nat_fn_zero in Hm by done.
      apply initial_message_is_valid. exists n.
      by unshelve eexists (exist _ m _); cbn; lia.
    + assert (Hmvalid : valid_message_prop free_parity_composite_vlsm (prod_fin_supp_nat_fn multipliers fp0)).
      {
        apply IHfp0 with (i := n'); [| done].
        replace (fin_supp_f fp0) with (fin_supp_f (increment_fin_supp_nat_fn fp0' n'))
          by (rewrite Heqv; done).
        by cbn; rewrite increment_fn_eq; lia.
      }
      subst m; rewrite prod_fin_supp_nat_fn_increment by done.
      pose proof (Hpos := prod_powers_pos multipliers Hmpos fp0).
      replace (prod_fin_supp_nat_fn _ _) with (prod_fin_supp_nat_fn multipliers fp0)
        by (rewrite Heqv; done).
      clear - Hmvalid Hpos.
      remember (prod_fin_supp_nat_fn _ _) as m; clear Heqm.
      apply input_valid_transition_out with
        (l := existT n parity_label)
        (s := fun j => if decide (n = j) then m + 1 else 1) (s' := fun _ => 1)
        (om := Some m).
      repeat split.
      * apply initial_state_is_valid.
        intros j; cbn; unfold ParityComponent_initial_state_prop.
        by case_decide; lia.
      * done.
      * by rewrite decide_True; [lia |].
      * by lia.
      * cbn; f_equal; extensionality j.
        rewrite decide_True by done.
        destruct (decide (n = j)); subst; state_update_simpl; [by lia |].
        by rewrite decide_False.
Qed.

Lemma composition_valid_messages_powers_of_mults
  (Hmpos : forall (i : index), multipliers i > 0) (m : ParityMessage) :
    valid_message_prop free_parity_composite_vlsm m <->
  exists (fp : fin_supp_nat_fn index (listset index)) (i : index),
    (fin_supp_f fp i >= 1)%nat /\ m = prod_fin_supp_nat_fn multipliers fp.
Proof.
  split.
  - intros Hvm.
    eapply VLSM_incl_valid_message in Hvm; cycle 1.
    + by apply free_composite_vlsm_spec.
    + by do 2 red.
    + by cbn in Hvm; eapply composition_valid_messages_powers_of_mults_right.
  - by intros [? []]; eapply composition_valid_messages_powers_of_mults_left.
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
