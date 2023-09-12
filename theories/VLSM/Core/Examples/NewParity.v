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
        `{FinSet index indexSet}
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
  (i : index) (l : ParityLabel) (st : ParityState) (om : option ParityMessage)
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

Definition ParityMachine (i : index) : VLSMMachine ParityType :=
{|
  initial_state_prop := ParityComponent_initial_state_prop;
  initial_message_prop := fun (ms : ParityMessage) => ms = multiplier;
  s0 := ParityComponent_Inhabited_initial_state_type;
  transition := fun l '(st, om) => ParityComponent_transition i l st om;
  valid := fun l '(st, om) => ParityComponentValid l st om;
|}.

(** The definition of the Parity VLSM. *)

Definition ParityVLSM (i : index) : VLSM ParityMessage :=
{|
  vtype := ParityType;
  vmachine := ParityMachine i;
|}.

Definition parity_label (i : index) : label (ParityVLSM i) := ().

(** ** Parity VLSM Examples *)

(** *** Example of an arbitrary transition *)

Lemma parity_example_transition_1 (i : index) `(X : VLSM ParityMessage) :
  transition (ParityVLSM i) (parity_label i) (4, Some 10) = (-6, Some (multiplier * 10)).
Proof. done. Qed.

(** *** Example of a valid trace *)

(** The initial state cannot be included to this definition, because, since there is no
    transition reaching this state, it cannot be expressed in the below manner
    Regarding the transition which leads to the final state, it technically could be
    included, but we choose to model this way, in order to be consistent
    with the subsequent example, where adding the last transition makes a qualitative
    difference to the trace
*)

Definition parity_trace1_init (i : index) : list (transition_item (ParityVLSM i)) :=
  [ Build_transition_item (parity_label i) (Some (multiplier ^ 2))
                                           (multiplier ^ 3 - multiplier ^ 2)
                                           (Some (multiplier ^ 3))
  ; Build_transition_item (parity_label i) (Some multiplier)
                                           (multiplier ^ 3 - multiplier ^ 2 - multiplier)
                                           (Some (multiplier ^ 2)) ].

Definition parity_trace1_last_item (i : index) : transition_item (ParityVLSM i) :=
  Build_transition_item (parity_label i) (Some multiplier)
  (multiplier ^ 3 - multiplier ^ 2 - multiplier - multiplier)
  (Some (multiplier ^ 2)).

Definition parity_trace1 (i : index) : list (transition_item (ParityVLSM i)) :=
  parity_trace1_init i ++ [parity_trace1_last_item i].

Definition parity_trace1_first_state : ParityState := multiplier ^ 3.

Definition parity_trace1_last_state (i : index) : ParityState :=
   destination (parity_trace1_last_item i).

(** Defined trace is valid: *)

Example parity_valid_message_prop_mult (i : index) : valid_message_prop (ParityVLSM i) (multiplier).
Proof. by apply initial_message_is_valid. Qed.

Example parity_can_emit_square_mult (i : index) : can_emit (ParityVLSM i) (multiplier ^ 2).
Proof.
  exists (multiplier, Some multiplier), (parity_label i), 0.
  repeat split; [| | lia.. | cbn; do 2 f_equal; lia].
  - by apply initial_state_is_valid; cbn; unfold ParityComponent_initial_state_prop; lia.
  - by app_valid_tran.
Qed.

Example parity_valid_message_prop_square_mult (i : index) : valid_message_prop (ParityVLSM i) (multiplier ^ 2).
Proof.
  by apply (emitted_messages_are_valid (ParityVLSM i) (multiplier ^ 2) (parity_can_emit_square_mult i)).
Qed.

Proposition parity_valid_transition_1 (i : index) :
  input_valid_transition (ParityVLSM i) (parity_label i)
   (parity_trace1_first_state, Some (multiplier ^ 2))
   (multiplier ^ 3 - multiplier ^ 2, Some (multiplier ^ 3)).
Proof.
  repeat split; [| | | lia].
  - apply initial_state_is_valid; cbn;
      unfold ParityComponent_initial_state_prop, parity_trace1_first_state; lia.
  - by app_valid_tran; apply parity_can_emit_square_mult.
  - by unfold parity_trace1_first_state; nia.
Qed.

Proposition parity_valid_transition_2 (i : index) :
  input_valid_transition (ParityVLSM i) (parity_label i)
   (multiplier ^ 3 - multiplier ^ 2, Some multiplier)
   (multiplier ^ 3 - multiplier ^ 2 - multiplier, Some (multiplier ^ 2)).
Proof.
  repeat split; [| | | lia |].
  - by app_valid_tran; apply parity_valid_transition_1.
  - by app_valid_tran; apply parity_can_emit_square_mult.
  - by nia.
  - by cbn; do 2 f_equal; lia.
Qed.

Proposition parity_valid_transition_3(i : index) : 
  input_valid_transition (ParityVLSM i) (parity_label i)
  (multiplier ^ 3 - multiplier ^ 2 - multiplier, Some multiplier)
  (multiplier ^ 3 - multiplier ^ 2 - multiplier - multiplier, Some (multiplier ^ 2)).
Proof.
  repeat split; [| | | lia |].
  - by app_valid_tran; apply parity_valid_transition_2.
  - by app_valid_tran; apply parity_can_emit_square_mult.
  - by nia.
  - by cbn; do 2 f_equal; lia.
Qed.

Example parity_valid_trace1 (i : index) :
  finite_valid_trace_init_to (ParityVLSM i)
   parity_trace1_first_state (parity_trace1_last_state i) (parity_trace1 i).
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

Example parity_valid_trace1_alt (i : index) :
  finite_valid_trace_init_to_alt (ParityVLSM i)
   parity_trace1_first_state (parity_trace1_last_state i) (parity_trace1 i).
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
Lemma parity_constrained_trace1 (i : index) :
  finite_constrained_trace_init_to (ParityVLSM i)
   parity_trace1_first_state (parity_trace1_last_state i) (parity_trace1 i).
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

Definition parity_trace2_init (i : index) : list (transition_item (ParityVLSM i)) :=
  [ Build_transition_item (parity_label i) (Some multiplier) (multiplier + 1)
                                           (Some (multiplier ^ 2))
  ; Build_transition_item (parity_label i) (Some multiplier) 1 (Some (multiplier ^ 2)) ].

Definition parity_trace2_last_item (i : index) : transition_item (ParityVLSM i) :=
  Build_transition_item (parity_label i) (Some 1) 0 (Some multiplier).

Definition parity_trace2 (i : index) : list (transition_item (ParityVLSM i)) :=
  parity_trace2_init i ++ [parity_trace2_last_item i].

Definition parity_trace2_init_first_state : ParityState := 2 * multiplier + 1.

Definition parity_trace2_init_last_state : ParityState := 1.

Definition parity_trace2_last_state (i : index) : ParityState :=
  destination (parity_trace2_last_item i).

(** The given trace is valid without the last transition. *)

Proposition parity_valid_transition_1' (i : index) :
  input_valid_transition (ParityVLSM i) (parity_label i)
   (parity_trace2_init_first_state, Some multiplier) (multiplier + 1, Some (multiplier ^ 2)).
Proof.
  repeat split; [| | | lia |].
  - unfold parity_trace2_init_first_state; apply initial_state_is_valid; cbn;
     unfold ParityComponent_initial_state_prop; lia.
  - by app_valid_tran; apply parity_can_emit_square_mult.
  - by unfold parity_trace2_init_first_state; lia.
  - by cbn; do 2 f_equal; unfold parity_trace2_init_first_state; lia.
Qed.

Proposition parity_valid_transition_2' (i : index) :
  input_valid_transition (ParityVLSM i) (parity_label i)
  (multiplier + 1, Some multiplier) (1, Some (multiplier ^ 2)).
Proof. 
  repeat split; [| | | lia |].
  - unfold parity_trace2_init_first_state; apply initial_state_is_valid; cbn;
     unfold ParityComponent_initial_state_prop; lia.
  - by app_valid_tran; apply parity_can_emit_square_mult.
  - by unfold parity_trace2_init_first_state; lia.
  - by cbn; do 2 f_equal; unfold parity_trace2_init_first_state; lia.
Qed.

Example parity_valid_trace2_init (i : index) :
  finite_valid_trace_init_to (ParityVLSM i)
   parity_trace2_init_first_state parity_trace2_init_last_state (parity_trace2_init i).
Proof.
  constructor; [| unfold parity_trace2_init_first_state; cbn;
                  unfold ParityComponent_initial_state_prop; lia].
  repeat apply finite_valid_trace_from_to_extend.
  - eapply finite_valid_trace_from_to_empty, input_valid_transition_destination, parity_valid_transition_2'.
  - by apply parity_valid_transition_2'.
  - by apply parity_valid_transition_1'.
Qed.

Example parity_valid_trace2_init_alt (i : index) :
  finite_valid_trace_init_to_alt (ParityVLSM i)
   parity_trace2_init_first_state parity_trace2_init_last_state (parity_trace2_init i).
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

Example parity_constrained_trace2_init (i : index) :
  finite_constrained_trace_init_to_alt (ParityVLSM i)
   parity_trace2_init_first_state parity_trace2_init_last_state (parity_trace2_init i).
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

Example parity_constrained_trace2 (i : index) :
  finite_constrained_trace_init_to_alt (ParityVLSM i)
    parity_trace2_init_first_state (parity_trace2_last_state i) (parity_trace2 i).
Proof.
  destruct (parity_constrained_trace2_init i).
  split; [| done].
  eapply (extend_right_finite_trace_from_to (pre_loaded_with_all_messages_vlsm (ParityVLSM i)));
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

Lemma parity_example_valid_transition (i : index) :
  input_valid_transition (ParityVLSM i) (parity_label i)
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

Example parity_example_constrained_transition (i : index) :
  input_valid_transition (pre_loaded_with_all_messages_vlsm (ParityVLSM i)) (parity_label i)
   (1, Some 1) (0, Some multiplier).
Proof.
  apply (finite_valid_trace_from_to_last_transition
    (pre_loaded_with_all_messages_vlsm (ParityVLSM i))
    parity_trace2_init_first_state (parity_trace2_last_state i) (parity_trace2_init i)
    (parity_trace2 i) (parity_trace2_last_item i)); [| done].
  by apply parity_constrained_trace2.
Qed.

(** ** Parity VLSM Properties *)

(** *** Inclusion into preloaded with all messages *)

Lemma parity_valid_is_constrained (i : index) :
  VLSM_incl (ParityVLSM i) (pre_loaded_with_all_messages_vlsm (ParityVLSM i)).
Proof.
  by apply vlsm_incl_pre_loaded_with_all_messages_vlsm.
Qed.

(** *** Constrained messages are positive even integers *)

Lemma parity_constrained_messages_left (i : index) :
  forall (m : ParityMessage), constrained_message_prop_alt (ParityVLSM i) m ->
   exists (j : Z), m = multiplier * j /\ m > 0.
Proof.
  intros m Hm.
  destruct Hm as ([s []] & [] & s' & (_ & _ & []) & Ht).
  inversion Ht; subst.
  by exists p; split; lia.
Qed.

Lemma parity_constrained_messages_right (i : index) :
  forall (m : ParityMessage), (exists (j : Z), m = multiplier * j) -> m > 0 ->
   constrained_message_prop_alt (ParityVLSM i) m.
Proof.
  intros m (j & Hj) Hmgt0.
  unfold constrained_message_prop_alt, can_emit.
  exists (j, Some j), (parity_label i), 0.
  repeat split; [| | by lia.. | by cbn; do 2 f_equal; lia].
  - apply input_valid_transition_destination with (l := (parity_label i)) (s := j + 1)
      (om := Some 1) (om' := Some multiplier).
    repeat split; [| | lia.. |].
    + unfold parity_trace2_init_first_state; apply initial_state_is_valid; cbn;
        unfold ParityComponent_initial_state_prop; lia.
    + by apply any_message_is_valid_in_preloaded.
    + cbn; do 2 f_equal; lia.
  - by apply any_message_is_valid_in_preloaded.
Qed.

Lemma parity_constrained_messages (i : index) :
  forall (m : ParityMessage), constrained_message_prop_alt (ParityVLSM i) m <->
    (exists (j : Z), m = multiplier * j /\ m > 0).
Proof.
  split.
  - apply parity_constrained_messages_left.
  - by intros [? [? ?]]; apply parity_constrained_messages_right; [exists x |].
Qed.

(** *** Constrained states property *)

Lemma parity_constrained_states_right (i : index) :
 forall (st : ParityState),
  constrained_state_prop_alt (ParityVLSM i) st -> st >= 0.
Proof.
  induction 1 using valid_state_prop_ind.
  - by cbn in Hs; unfold ParityComponent_initial_state_prop in Hs; lia.
  - destruct l, om, Ht as [(Hs & _ & []) Ht].
    by inversion Ht; subst; cbn in *; lia.
Qed.

Lemma parity_constrained_states_left (i : index) :
  forall (st : ParityState), st >= 0 ->
    constrained_state_prop_alt (ParityVLSM i) st.
Proof.
  intros st Hst.
  unfold constrained_state_prop_alt.
  apply input_valid_transition_destination with (l := (parity_label i)) (s := st + 1)
    (om := Some 1) (om' := Some multiplier).
  repeat split; [| | lia.. | cbn; do 2 f_equal; lia].
  - by apply initial_state_is_valid; cbn; unfold ParityComponent_initial_state_prop; lia.
  - by apply any_message_is_valid_in_preloaded.
Qed.

Lemma parity_constrained_states (i : index) :
  forall (st : ParityState),
    constrained_state_prop_alt (ParityVLSM i) st <-> (st >= 0).
Proof.
  split.
  - by apply parity_constrained_states_right.
  - by apply parity_constrained_states_left.
Qed.

(** *** Powers of 2 greater or equal than 2 are valid messages *)

Lemma parity_valid_messages_powers_of_mult_right (i : index) :
  forall (m : option ParityMessage),
    option_valid_message_prop (ParityVLSM i) m -> m <> None ->
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

Lemma parity_valid_messages_powers_of_mult_left (i : index) :
  forall (p : Z),
    p >= 1 -> option_valid_message_prop (ParityVLSM i) (Some (multiplier ^ p)).
Proof.
  intros p Hp.
  assert (0 <= p - 1) by lia.
  replace p with (p - 1 + 1) by lia.
  remember (p - 1) as x.
  clear p Hp Heqx.
  revert x H9.
  apply natlike_ind.
  - apply initial_message_is_valid; cbn; unfold ParityComponent_initial_state_prop; lia.
  - intros x Hxgt0 Hindh.
    pose (msgin := multiplier ^ (x + 1)).
    apply emitted_messages_are_valid.
    exists (msgin, Some (multiplier ^ (x + 1))), (parity_label i), 0. subst msgin; cbn.
    repeat split.
    + by apply initial_state_is_valid; cbn; unfold ParityComponent_initial_state_prop; lia.
    + by apply Hindh.
    + by lia.
    + by lia.
    + cbn; rewrite <- Z.pow_succ_r, Z.add_succ_l; [do 2 f_equal; lia | lia].
Qed.

Lemma parity_valid_messages_powers_of_mult : forall (om : option ParityMessage) (i : index),
  om <> None -> ((option_valid_message_prop (ParityVLSM i) om) <->
    (exists p : Z, p >= 1 /\ om = Some (multiplier ^ p))).
Proof.
  split.
  - by intros; apply (parity_valid_messages_powers_of_mult_right i).
  - by intros (p & Hpgt0 & [= ->]); apply parity_valid_messages_powers_of_mult_left.
Qed.

Definition composite_transition_MC := composite_transition ParityVLSM.

Definition parity_composite_valid
  (l : composite_label ParityVLSM) (som : composite_state ParityVLSM * option ParityMessage) : Prop :=
  let (s, om) := som in
  let (i, li) := l in
    valid (ParityVLSM i) li (s i, om).

Definition parity_constraint
  (l : composite_label ParityVLSM) (sm : composite_state ParityVLSM * option ParityMessage) : Prop :=
  forall (i : index), (exists (s' : ParityState) (om' : option ParityMessage),
    ParityComponent_transition i (parity_label i) ((fst sm) i) (snd sm) = (s', om') ->
    Z.even (((fst sm) i) + s')).

Definition parity_composite_vlsm : VLSM ParityMessage :=
  composite_vlsm ParityVLSM parity_constraint.

End sec_parity_vlsm.
