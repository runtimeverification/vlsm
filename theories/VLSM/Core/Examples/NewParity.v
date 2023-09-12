From stdpp Require Import prelude finite.
From VLSM.Core Require Import VLSM PreloadedVLSM VLSMProjections Composition.

(** * Parity VLSM

  This module demonstrates some basic notions of the VLSM framework.
  The idea of the parity VLSM is to store an integer and continually decrement it,
  while a constraint is checked at each step. The name originates from the
  property of this VLSM to accept as constrained messages even numbers.
  The definitions and lemmas tap into concepts such as valid and constrained traces,
  transitions, states, and messages.
*)

#[local] Open Scope Z_scope.

(** ** General arithmetic results

  These lemmas will be helpful in subsequent proofs.
*)

(** Parity is preserved by taking opposite *)
Lemma Zeven_unary_minus :
  forall n : Z, Z.Even n <-> Z.Even (-n).
Proof. by intros n; split; intros [p Hp]; exists (-p); lia. Qed.

(** Even right-hand side and difference implies even left-hand side 
    This lemma will be useful when proving the final result of this section, because of the way 
    we defined the transitions in the Parity VLSM
*)
Lemma Zeven_sub_preserve_parity :
  forall (n m : Z), Z.Even n -> Z.Even (m - n) -> Z.Even m.
Proof. by intros m n [m'] [n']; exists (m' + n'); lia. Qed.

(** Parity is preserved by addition *)
Lemma Zeven_equiv_plus :
  forall (n m : Z), (Z.Even n <-> Z.Even m) -> Z.Even (m + n).
Proof.
  intros n m Hparity.
  destruct (Zeven_odd_dec m).
  - apply Zeven_equiv, Zeven_plus_Zeven; [done |].
    by rewrite Zeven_equiv, Hparity, <- Zeven_equiv.
  - apply Zeven_equiv, Zodd_plus_Zodd; [done |].
    destruct (Zeven_odd_dec n); [| done].
    exfalso.
    eapply Zodd_not_Zeven; [done |].
    by rewrite Zeven_equiv, <- Hparity, <- Zeven_equiv.
Qed.

(** Parity is preserved by subtraction *)
Lemma Zeven_equiv_minus :
  forall (n m : Z), (Z.Even n <-> Z.Even m) -> Z.Even (m - n).
Proof.
  intros n m **.
  replace (m - n) with (m + (-n)) by lia.
  apply Zeven_equiv_plus.
  etransitivity; [| done].
  symmetry.
  by apply Zeven_unary_minus.
Qed.

Lemma Zeven_plus_equiv :
  forall (n m : Z), Z.Even n -> (Z.Even m <-> Z.Even (m + n)).
Proof.
  split; intros.
  - by apply Zeven_equiv, Zeven_plus_Zeven; rewrite Zeven_equiv.
  - apply Zeven_sub_preserve_parity with (m + n); [done |].
    replace (m - (m + n)) with (-n) by lia.
    by rewrite <- Zeven_unary_minus.
Qed.

(** ** General automation *)

(** Custom tactic used to simplify proofs on valid VLSM transitions *)

Ltac app_valid_tran :=
  repeat split; cbn; try done;
  match goal with
  | |- option_valid_message_prop _ _ => by apply initial_message_is_valid
  | |- option_valid_message_prop _ _ => eapply emitted_messages_are_valid
  | |- valid_state_prop _ _ => by apply initial_state_is_valid
  | |- valid_state_prop _ _ => eapply input_valid_transition_destination
  end.

Section sec_parity_vlsm.

Context (multiplier : Z)
        (multiplier_geq_2 : multiplier >= 2)
        (index : Type)
        `{finite.Finite index}
        `{Inhabited index}
        .

(** ** Definition of Parity VLSM

  The Parity VLSM will only have one label, indicating a decrement.
  For this reason, the [unit] type can be used.
*)

Definition ParityLabel : Type := unit.

(** The state will hold an integer. *)

Definition ParityState : Type := Z.

(** The VLSM handles integer messages. *)

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
  | Some j  => ((st - j), Some (multiplier * j))
  | None    => (st, None)
  end.

Definition ParityComponentValid (l : ParityLabel) (st : ParityState)
(om : option ParityMessage) : Prop :=
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
  ParityComponent_initial_state_type := exist _ (1) _.
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
  valid := fun l '(st, om) => ParityComponentValid l st om;
|}.

(** The definition of the Parity VLSM. *)

Definition ParityVLSM : VLSM ParityMessage :=
{|
  vtype := ParityType;
  vmachine := ParityMachine;
|}.

Definition parity_label : label ParityVLSM := ().

(** ** Parity VLSM Examples *)

(** *** Example of an arbitrary transition *)

Lemma parity_example_transition_1 `(X : VLSM ParityMessage) :
  transition ParityVLSM parity_label (4, Some 10) = (-6, Some (multiplier * 10)).
Proof. done. Qed.

(** *** Example of a valid trace *)

(** The initial state cannot be included to this definition, because, since there is no
    transition reaching this state, it cannot be expressed in the below manner
    Regarding the transition which leads to the final state, it technically could be
    included, but we choose to model this way, in order to be consistent
    with the subsequent example, where adding the last transition makes a qualitative
    difference to the trace
*)

Definition parity_trace1_init : list (transition_item ParityVLSM) :=
  [ Build_transition_item parity_label (Some (multiplier ^ 2))
                                           (multiplier ^ 3 - multiplier ^ 2)
                                           (Some (multiplier ^ 3))
  ; Build_transition_item parity_label (Some multiplier)
                                           (multiplier ^ 3 - multiplier ^ 2 - multiplier)
                                           (Some (multiplier ^ 2)) ].

Definition parity_trace1_last_item : transition_item ParityVLSM :=
  Build_transition_item parity_label (Some multiplier)
  (multiplier ^ 3 - multiplier ^ 2 - multiplier - multiplier)
  (Some (multiplier ^ 2)).

Definition parity_trace1 : list (transition_item ParityVLSM) :=
  parity_trace1_init ++ [parity_trace1_last_item].

Definition parity_trace1_first_state : ParityState := multiplier ^ 3.

Definition parity_trace1_last_state : ParityState :=
   destination parity_trace1_last_item.

(** Defined trace is valid: *)

Example parity_valid_message_prop_mult : valid_message_prop ParityVLSM multiplier.
Proof. by apply initial_message_is_valid. Qed.

Example parity_can_emit_square_mult : can_emit ParityVLSM (multiplier ^ 2).
Proof.
  exists (multiplier, Some multiplier), parity_label, 0.
  repeat split; [| | lia.. | cbn; do 2 f_equal; lia].
  - by apply initial_state_is_valid; cbn; unfold ParityComponent_initial_state_prop; lia.
  - by app_valid_tran.
Qed.

Example parity_valid_message_prop_square_mult : valid_message_prop ParityVLSM (multiplier ^ 2).
Proof.
  by apply (emitted_messages_are_valid ParityVLSM (multiplier ^ 2) parity_can_emit_square_mult).
Qed.

Proposition parity_valid_transition_1 :
  input_valid_transition ParityVLSM parity_label
   (parity_trace1_first_state, Some (multiplier ^ 2))
   (multiplier ^ 3 - multiplier ^ 2, Some (multiplier ^ 3)).
Proof.
  repeat split; [| | | lia].
  - apply initial_state_is_valid; cbn;
      unfold ParityComponent_initial_state_prop, parity_trace1_first_state; lia.
  - by app_valid_tran; apply parity_can_emit_square_mult.
  - by unfold parity_trace1_first_state; nia.
Qed.

Proposition parity_valid_transition_2 :
  input_valid_transition ParityVLSM parity_label
   (multiplier ^ 3 - multiplier ^ 2, Some multiplier)
   (multiplier ^ 3 - multiplier ^ 2 - multiplier, Some (multiplier ^ 2)).
Proof.
  repeat split; [| | | lia |].
  - by app_valid_tran; apply parity_valid_transition_1.
  - by app_valid_tran; apply parity_can_emit_square_mult.
  - by nia.
  - by cbn; do 2 f_equal; lia.
Qed.

Proposition parity_valid_transition_3 : 
  input_valid_transition ParityVLSM parity_label
  (multiplier ^ 3 - multiplier ^ 2 - multiplier, Some multiplier)
  (multiplier ^ 3 - multiplier ^ 2 - multiplier - multiplier, Some (multiplier ^ 2)).
Proof.
  repeat split; [| | | lia |].
  - by app_valid_tran; apply parity_valid_transition_2.
  - by app_valid_tran; apply parity_can_emit_square_mult.
  - by nia.
  - by cbn; do 2 f_equal; lia.
Qed.

Example parity_valid_trace1 :
  finite_valid_trace_init_to ParityVLSM
   parity_trace1_first_state parity_trace1_last_state parity_trace1.
Proof.
  constructor; [| unfold parity_trace1_first_state; cbn;
                  unfold ParityComponent_initial_state_prop; lia].
  unfold parity_trace1_first_state.
  repeat apply finite_valid_trace_from_to_extend.
  - by eapply finite_valid_trace_from_to_empty, input_valid_transition_destination, parity_valid_transition_3.
  - by apply parity_valid_transition_3.
  - by apply parity_valid_transition_2.
  - by apply parity_valid_transition_1.
Qed.

Example parity_valid_trace1_alt :
  finite_valid_trace_init_to_alt ParityVLSM
   parity_trace1_first_state parity_trace1_last_state parity_trace1.
Proof.
  constructor; [| unfold parity_trace1_first_state; cbn;
                  unfold ParityComponent_initial_state_prop; lia].
  repeat apply mvt_extend; [.. | apply mvt_empty].
  - by apply parity_valid_message_prop_square_mult.
  - by apply parity_valid_transition_1.
  - cbn; split; [| lia].
    by unfold parity_trace1_first_state; nia.
  - by apply parity_valid_message_prop_mult.
  - by apply parity_valid_transition_2.
  - by cbn; split; [nia|lia].
  - by apply parity_valid_message_prop_mult.
  - by apply parity_valid_transition_3.
  - by cbn; split; [nia|lia].
Qed.

(** *** Example of a constrained trace *)

(** Previously defined trace is obviously constrained, since it's valid *)
Lemma parity_constrained_trace1 :
  finite_constrained_trace_init_to ParityVLSM
   parity_trace1_first_state parity_trace1_last_state parity_trace1.
Proof.
  constructor; [| unfold parity_trace1_first_state; cbn;
                  unfold ParityComponent_initial_state_prop; lia].
  repeat apply ct_extend; [..| apply ct_empty].
  - by apply parity_valid_transition_1.
  - cbn. split; [| lia]. 
    by unfold parity_trace1_first_state; nia.
  - by apply parity_valid_transition_2.
  - cbn; split; [nia|lia].
  - by apply parity_valid_transition_3.
  - cbn; split; [nia| lia].
Qed.

Definition parity_trace2_init : list (transition_item ParityVLSM) :=
  [ Build_transition_item parity_label (Some multiplier) (multiplier + 1)
                                           (Some (multiplier ^ 2))
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
  input_valid_transition ParityVLSM parity_label
   (parity_trace2_init_first_state, Some multiplier) (multiplier + 1, Some (multiplier ^ 2)).
Proof.
  repeat split; [| | | lia |].
  - unfold parity_trace2_init_first_state; apply initial_state_is_valid; cbn;
     unfold ParityComponent_initial_state_prop; lia.
  - by app_valid_tran; apply parity_can_emit_square_mult.
  - by unfold parity_trace2_init_first_state; lia.
  - by cbn; do 2 f_equal; unfold parity_trace2_init_first_state; lia.
Qed.

Proposition parity_valid_transition_2' :
  input_valid_transition ParityVLSM parity_label
  (multiplier + 1, Some multiplier) (1, Some (multiplier ^ 2)).
Proof. 
  repeat split; [| | | lia |].
  - unfold parity_trace2_init_first_state; apply initial_state_is_valid; cbn;
     unfold ParityComponent_initial_state_prop; lia.
  - by app_valid_tran; apply parity_can_emit_square_mult.
  - by unfold parity_trace2_init_first_state; lia.
  - by cbn; do 2 f_equal; unfold parity_trace2_init_first_state; lia.
Qed.

Example parity_valid_trace2_init :
  finite_valid_trace_init_to ParityVLSM
   parity_trace2_init_first_state parity_trace2_init_last_state parity_trace2_init.
Proof.
  constructor; [| unfold parity_trace2_init_first_state; cbn;
                  unfold ParityComponent_initial_state_prop; lia].
  repeat apply finite_valid_trace_from_to_extend.
  - eapply finite_valid_trace_from_to_empty, input_valid_transition_destination, parity_valid_transition_2'.
  - by apply parity_valid_transition_2'.
  - by apply parity_valid_transition_1'.
Qed.

Example parity_valid_trace2_init_alt :
  finite_valid_trace_init_to_alt ParityVLSM
   parity_trace2_init_first_state parity_trace2_init_last_state parity_trace2_init.
Proof.
  constructor; [| unfold parity_trace2_init_first_state; cbn;
                  unfold ParityComponent_initial_state_prop; lia].
  repeat apply mvt_extend; [..| apply mvt_empty].
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
  finite_constrained_trace_init_to_alt ParityVLSM
   parity_trace2_init_first_state parity_trace2_init_last_state parity_trace2_init.
Proof.
  apply VLSM_incl_finite_valid_trace_init_to.
  - by apply vlsm_incl_pre_loaded.
  - by apply parity_valid_trace2_init.
Qed.

(**
  The trace is valid (in the preloaded Parity VLSM) without
  its last element and appending it to the end also gives
  a valid trace (in the preloaded Parity VLSM).
  It follows that the full trace is constrained in
  the original Parity VLSM.
*)

Example parity_constrained_trace2 :
  finite_constrained_trace_init_to_alt ParityVLSM
    parity_trace2_init_first_state parity_trace2_last_state parity_trace2.
Proof.
  destruct parity_constrained_trace2_init.
  split; [| done].
  eapply (extend_right_finite_trace_from_to (pre_loaded_with_all_messages_vlsm ParityVLSM));
    [done |].
  repeat split; [| | | lia |].
  - by eapply finite_valid_trace_from_to_last_pstate.
  - by apply any_message_is_valid_in_preloaded.
  - by unfold parity_trace2_init_last_state; lia.
  - by cbn; do 2 f_equal; lia.
Qed.

(** *** Example of a valid transition

  The last transition of a valid trace is valid.
*)

Lemma parity_example_valid_transition :
  input_valid_transition ParityVLSM parity_label
   (multiplier, Some multiplier) (0, Some (multiplier ^ 2)).
Proof.
  repeat split; [| | lia.. |].
  - unfold parity_trace2_init_first_state; apply initial_state_is_valid; cbn;
     unfold ParityComponent_initial_state_prop; lia.
  - by apply parity_valid_message_prop_mult.
  - by cbn; do 2 f_equal; lia.
Qed.

(** *** Example of a constrained transition

  The last transition of a constrained trace is constrained.
*)

Example parity_example_constrained_transition :
  input_valid_transition (pre_loaded_with_all_messages_vlsm ParityVLSM) parity_label
   (1, Some 1) (0, Some multiplier).
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
  forall (m : ParityMessage), constrained_message_prop_alt ParityVLSM m ->
   exists (j : Z), m = multiplier * j /\ m > 0.
Proof.
  intros m Hm.
  destruct Hm as ([s []] & [] & s' & (_ & _ & []) & Ht).
  inversion Ht; subst.
  by exists p; split; lia.
Qed.

Lemma parity_constrained_messages_right :
  forall (m : ParityMessage), (exists (j : Z), m = multiplier * j) -> m > 0 ->
   constrained_message_prop_alt ParityVLSM m.
Proof.
  intros m (j & Hj) Hmgt0.
  unfold constrained_message_prop_alt, can_emit.
  exists (j, Some j), parity_label, 0.
  repeat split; [| | by lia.. | by cbn; do 2 f_equal; lia].
  - apply input_valid_transition_destination with (l := parity_label) (s := j + 1)
      (om := Some 1) (om' := Some multiplier).
    repeat split; [| | lia.. |].
    + unfold parity_trace2_init_first_state; apply initial_state_is_valid; cbn;
        unfold ParityComponent_initial_state_prop; lia.
    + by apply any_message_is_valid_in_preloaded.
    + cbn; do 2 f_equal; lia.
  - by apply any_message_is_valid_in_preloaded.
Qed.

Lemma parity_constrained_messages :
  forall (m : ParityMessage), constrained_message_prop_alt ParityVLSM m <->
    (exists (j : Z), m = multiplier * j /\ m > 0).
Proof.
  split.
  - apply parity_constrained_messages_left.
  - by intros [? [? ?]]; apply parity_constrained_messages_right; [exists x |].
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
  forall (st : ParityState), st >= 0 ->
    constrained_state_prop_alt ParityVLSM st.
Proof.
  intros st Hst.
  unfold constrained_state_prop_alt.
  apply input_valid_transition_destination with (l := parity_label) (s := st + 1)
    (om := Some 1) (om' := Some multiplier).
  repeat split; [| | lia.. | cbn; do 2 f_equal; lia].
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
  - unfold option_initial_message_prop, from_option in Hom.
    destruct om; [| done].
    unfold initial_message_prop in Hom; cbn in Hom.
    by exists 1; subst; split; [lia | f_equal; lia].
  - destruct om, IHHvsm2 as [x Hx]; inversion Ht; cycle 1; [| done ..].
    inversion H as [Hxgt1 Hsmx].
    exists (x + 1).
    split; [by lia | f_equal].
    destruct Hx as [Hgeq1 Hsome]; apply Some_inj in Hsome; rewrite Hsome.
    rewrite <- Z.pow_succ_r; [f_equal | lia].
Qed.

Lemma parity_valid_messages_powers_of_mult_left :
  forall (p : Z),
    p >= 1 -> option_valid_message_prop ParityVLSM (Some (multiplier ^ p)).
Proof.
  intros p Hp.
  assert (0 <= p - 1) by lia.
  replace p with (p - 1 + 1) by lia.
  remember (p - 1) as x.
  clear p Hp Heqx.
  revert x H1.
  apply natlike_ind.
  - apply initial_message_is_valid; cbn; unfold ParityComponent_initial_state_prop; lia.
  - intros x Hxgt0 Hindh.
    pose (msgin := multiplier ^ (x + 1)).
    apply emitted_messages_are_valid.
    exists (msgin, Some (multiplier ^ (x + 1))), parity_label, 0. subst msgin; cbn.
    repeat split.
    + by apply initial_state_is_valid; cbn; unfold ParityComponent_initial_state_prop; lia.
    + by apply Hindh.
    + by lia.
    + by lia.
    + cbn; rewrite <- Z.pow_succ_r, Z.add_succ_l; [do 2 f_equal; lia | lia].
Qed.

Lemma parity_valid_messages_powers_of_mult : forall (om : option ParityMessage),
  om <> None -> ((option_valid_message_prop ParityVLSM om) <->
    (exists p : Z, p >= 1 /\ om = Some (multiplier ^ p))).
Proof.
  split.
  - by intros; apply parity_valid_messages_powers_of_mult_right.
  - by intros (p & Hpgt0 & [= ->]); apply parity_valid_messages_powers_of_mult_left.
Qed.

End sec_parity_vlsm.

Section sec_composition.

Context {index : Type}
        (multipliers : index -> Z)
        `{finite.Finite index}
        `{Inhabited index}.

Definition indexed_parity_vlsms (i : index) : VLSM ParityMessage :=
  ParityVLSM (multipliers i).

Definition parity_constraint
  (l : composite_label indexed_parity_vlsms) (sm : composite_state indexed_parity_vlsms * option ParityMessage) : Prop :=
  let i := projT1 l in
  let (s', _) := composite_transition indexed_parity_vlsms l sm in
  Z.even (((fst sm) i) + (s' i)).

Definition parity_composite_vlsm : VLSM ParityMessage :=
  composite_vlsm indexed_parity_vlsms parity_constraint.

End sec_composition.
