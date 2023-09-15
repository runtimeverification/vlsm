From stdpp Require Import prelude finite.
From Coq Require Import FunctionalExtensionality.
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
        (multiplier_geq_0 : multiplier <> 0)
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

Definition parity_label : label ParityType := ().

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

Example parity_can_emit_square_mult : multiplier > 0 -> can_emit ParityVLSM (multiplier ^ 2).
Proof.
  exists (multiplier, Some multiplier), parity_label, 0.
  repeat split; [| | lia.. | cbn; do 2 f_equal; lia].
  - by apply initial_state_is_valid; cbn; unfold ParityComponent_initial_state_prop; lia.
  - by app_valid_tran.
Qed.

Example parity_valid_message_prop_square_mult : multiplier > 0 -> valid_message_prop ParityVLSM (multiplier ^ 2).
Proof.
  intros Hgeq0.
  by eapply (emitted_messages_are_valid ParityVLSM (multiplier ^ 2) (parity_can_emit_square_mult Hgeq0)).
Qed.

Proposition parity_valid_transition_1 : multiplier > 0 ->
  input_valid_transition ParityVLSM parity_label
   (parity_trace1_first_state, Some (multiplier ^ 2))
   (multiplier ^ 3 - multiplier ^ 2, Some (multiplier ^ 3)).
Proof.
  repeat split; [| | | lia].
  - apply initial_state_is_valid; cbn;
      unfold ParityComponent_initial_state_prop, parity_trace1_first_state; lia.
  - by app_valid_tran; eapply parity_can_emit_square_mult.
  - by unfold parity_trace1_first_state; nia.
Qed.

Proposition parity_valid_transition_2 : multiplier >= 2 ->
  input_valid_transition ParityVLSM parity_label
   (multiplier ^ 3 - multiplier ^ 2, Some multiplier)
   (multiplier ^ 3 - multiplier ^ 2 - multiplier, Some (multiplier ^ 2)).
Proof.
  repeat split; [| | | lia |].
  - by app_valid_tran; eapply parity_valid_transition_1; lia.
  - by app_valid_tran; apply parity_can_emit_square_mult.
  - by nia.
  - by cbn; do 2 f_equal; lia.
Qed.

Proposition parity_valid_transition_3 : multiplier >= 2 ->
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

Example parity_valid_trace1 : multiplier >= 2 ->
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
  - by apply parity_valid_transition_1; lia.
Qed.

Example parity_valid_trace1_alt : multiplier >= 2 ->
  finite_valid_trace_init_to_alt ParityVLSM
   parity_trace1_first_state parity_trace1_last_state parity_trace1.
Proof.
  constructor; [| unfold parity_trace1_first_state; cbn;
                  unfold ParityComponent_initial_state_prop; lia].
  repeat apply mvt_extend; [.. | apply mvt_empty].
  - by eapply parity_valid_message_prop_square_mult; lia.
  - by eapply parity_valid_transition_1; lia.
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
Lemma parity_constrained_trace1 : multiplier >= 2 ->
  finite_constrained_trace_init_to ParityVLSM
   parity_trace1_first_state parity_trace1_last_state parity_trace1.
Proof.
  constructor; [| unfold parity_trace1_first_state; cbn;
                  unfold ParityComponent_initial_state_prop; lia].
  repeat apply ct_extend; [..| apply ct_empty].
  - by eapply parity_valid_transition_1; lia.
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

Proposition parity_valid_transition_1' : multiplier > 0 ->
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

Proposition parity_valid_transition_2' : multiplier > 0 ->
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

Example parity_valid_trace2_init : multiplier > 0 ->
  finite_valid_trace_init_to ParityVLSM
   parity_trace2_init_first_state parity_trace2_init_last_state parity_trace2_init.
Proof.
  constructor; [| unfold parity_trace2_init_first_state; cbn;
                  unfold ParityComponent_initial_state_prop; lia].
  repeat apply finite_valid_trace_from_to_extend.
  - by eapply finite_valid_trace_from_to_empty, input_valid_transition_destination,
      parity_valid_transition_2'.
  - by apply parity_valid_transition_2'.
  - by apply parity_valid_transition_1'.
Qed.

Example parity_valid_trace2_init_alt : multiplier > 0 ->
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

Example parity_constrained_trace2_init : multiplier > 0 ->
  finite_constrained_trace_init_to_alt ParityVLSM
   parity_trace2_init_first_state parity_trace2_init_last_state parity_trace2_init.
Proof.
  intros Hgeq0.
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

Example parity_constrained_trace2 : multiplier > 0 ->
  finite_constrained_trace_init_to_alt ParityVLSM
    parity_trace2_init_first_state parity_trace2_last_state parity_trace2.
Proof.
  intros Hgeq0.
  destruct parity_constrained_trace2_init; [done |].
  split; [| done].
  eapply (extend_right_finite_trace_from_to (pre_loaded_with_all_messages_vlsm ParityVLSM));
    [done |].
  repeat split; [| | | lia |].
  - by eapply finite_valid_trace_from_to_last_pstate.
  - by apply any_message_is_valid_in_preloaded.
  - by unfold parity_trace2_init_last_state.
  - by cbn; do 2 f_equal; lia.
Qed.

(** *** Example of a valid transition

  The last transition of a valid trace is valid.
*)

Lemma parity_example_valid_transition : multiplier > 0 ->
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

Example parity_example_constrained_transition : multiplier > 0 ->
  input_valid_transition (pre_loaded_with_all_messages_vlsm ParityVLSM) parity_label
   (1, Some 1) (0, Some multiplier).
Proof.
  intros Hgeq0.
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

Lemma parity_constrained_messages_left : multiplier > 0 ->
  forall (m : ParityMessage), constrained_message_prop_alt ParityVLSM m ->
   exists (j : Z), m = multiplier * j /\ m > 0.
Proof.
  intros Hgeq0 m Hm.
  destruct Hm as ([s []] & [] & s' & (_ & _ & []) & Ht).
  inversion Ht; subst.
  by exists p; split; lia.
Qed.

Lemma parity_constrained_messages_right : multiplier > 0 ->
  forall (m : ParityMessage), (exists (j : Z), m = multiplier * j) -> m > 0 ->
   constrained_message_prop_alt ParityVLSM m.
Proof.
  intros Hgeq0 m (j & Hj) Hmgt0.
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

Lemma parity_constrained_messages : multiplier > 0 ->
  forall (m : ParityMessage), constrained_message_prop_alt ParityVLSM m <->
    (exists (j : Z), m = multiplier * j /\ m > 0).
Proof.
  intros Hgeq0.
  split.
  - by apply parity_constrained_messages_left.
  - by intros [? [? ?]]; apply parity_constrained_messages_right; [| exists x |].
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
    cbn in Hom.
    by exists 1; split; [lia | f_equal; lia].
  - destruct om, IHHvsm2 as [x Hx]; inversion Ht; cycle 1; [| done..].
    exists (x + 1).
    split; [by lia | f_equal].
    destruct Hx as [Hgeq1 Hsome]; apply Some_inj in Hsome; rewrite Hsome.
    rewrite <- Z.pow_succ_r; [f_equal | lia].
Qed.

Lemma parity_valid_messages_powers_of_mult_left : multiplier > 0 ->
  forall (p : Z),
    p >= 1 -> option_valid_message_prop ParityVLSM (Some (multiplier ^ p)).
Proof.
  intros Hgeq0 p Hp.
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
    exists (msgin, Some (multiplier ^ (x + 1))), parity_label, 0. cbn.
    repeat split; [| by apply Hindh | lia.. |].
    + by apply initial_state_is_valid; cbn; unfold ParityComponent_initial_state_prop; lia.
    + cbn; rewrite <- Z.pow_succ_r, Z.add_succ_l; [do 2 f_equal; lia | lia].
Qed.

Lemma parity_valid_messages_powers_of_mult : forall (om : option ParityMessage), multiplier > 0 ->
  om <> None -> ((option_valid_message_prop ParityVLSM om) <->
    (exists p : Z, p >= 1 /\ om = Some (multiplier ^ p))).
Proof.
  split.
  - by intros; apply parity_valid_messages_powers_of_mult_right.
  - by intros (p & Hpgt0 & [= ->]); apply parity_valid_messages_powers_of_mult_left.
Qed.

End sec_parity_vlsm.

Section sec_powers_ind.

Context `{finite.Finite index}.

Definition update_powers (powers : index -> nat) (n : index) (nr : nat) (x : index): nat :=
  if decide (n = x) then nr
  else powers x.

Lemma update_powers_eq (powers : index -> nat) (n : index) (nr : nat) :
  update_powers powers n nr n = nr.
Proof.
  unfold update_powers. by rewrite decide_True.
Qed.

Lemma update_powers_neq (powers : index -> nat) (n : index) (x : index) (nr : nat) : n <> x ->
  update_powers powers n nr x = powers x.
Proof.
  intros Hn.
  unfold update_powers. by rewrite decide_False.
Qed.

Definition increment_powers (powers : index -> nat) (n : index) :=
  update_powers powers n (S (powers n)).

Lemma increment_powers_eq (powers : index -> nat) (n : index) :
  increment_powers powers n n = S (powers n).
Proof.
  apply update_powers_eq.
Qed.

Lemma increment_powers_neq (powers : index -> nat) (n : index) (x : index) : n <> x ->
  increment_powers powers n x = powers x.
Proof.
  apply update_powers_neq.
Qed.

Definition sum_powers_aux (powers : index -> nat) (l : list index) : nat :=
  foldr plus 0%nat (map powers l).

Lemma sum_powers_aux_zero (powers : index -> nat) (l : list index) :
  Forall (fun n => powers n = 0%nat) l -> sum_powers_aux powers l = 0%nat.
Proof.
  unfold sum_powers_aux; intros Hforall.
  induction Hforall; [done |].
  by cbn; rewrite IHHforall, H0.
Qed.

Lemma sum_powers_aux_zero_rev (powers : index -> nat) (l : list index) :
  sum_powers_aux powers l = 0%nat -> Forall (fun n => powers n = 0%nat) l.
Proof.
  unfold sum_powers_aux; induction l; [done |].
  cbn in *.
  intros Hzero.
  constructor; [by lia |].
  by apply IHl; lia.
Qed.

Definition sum_powers (powers : index -> nat) : nat := sum_powers_aux powers (enum index).

Definition zero_powers (x : index) : nat := 0.

Inductive Powers : (index -> nat) -> Prop :=
| P_zero : Powers zero_powers
| P_succ : forall (i : index) (powers : index -> nat), Powers powers -> Powers (increment_powers powers i).

Lemma sum_powers_zero_iff (powers : index -> nat) :
  sum_powers powers = 0%nat <-> powers = zero_powers.
Proof.
  split.
  - intros Hzero.
    apply sum_powers_aux_zero_rev in Hzero.
    rewrite Forall_forall in Hzero.
    by extensionality x; apply Hzero, elem_of_enum.
  - intros ->.
    by apply sum_powers_aux_zero, Forall_forall.
Qed.

Lemma sum_increment_powers (powers : index -> nat) (n : index) :
  sum_powers (increment_powers powers n) = S (sum_powers powers).
Proof.
  unfold sum_powers.
  pose proof (Hnodup := NoDup_enum index).
  pose proof (Hn := elem_of_enum n).
  revert Hnodup Hn.
  generalize (enum index) as l.
  induction l; [by inversion 2 |].
  rewrite NoDup_cons, elem_of_cons; cbn.
  intros [Ha Hnodup] [Hn | Hn].
  - subst. rewrite increment_powers_eq; cbn.
    do 2 f_equal.
    clear IHl Hnodup.
    induction l; [done |].
    apply not_elem_of_cons in Ha as [Ha0 Ha]; cbn.
    by rewrite IHl, increment_powers_neq.
  - unfold sum_powers_aux in IHl; rewrite IHl by done.
    rewrite increment_powers_neq by set_solver.
    by lia.
Qed.

Lemma Powers_powers (powers : index -> nat) : Powers powers.
Proof.
  remember (sum_powers powers) as n.
  revert powers Heqn.
  induction n; intros.
  - symmetry in Heqn. apply sum_powers_zero_iff in Heqn as ->.
    by constructor.
  - assert (Hnz : exists (i : index), powers i <> 0%nat).
    {
      apply Exists_finite, not_Forall_Exists; [by typeclasses eauto |].
      intros Hall.
      by unfold sum_powers in Heqn; rewrite sum_powers_aux_zero in Heqn.
    }
    destruct Hnz as (x & Hx).
    destruct (powers x) as [| px] eqn : Heqx; [done |]. clear Hx.
    pose (powers' := update_powers powers x px).
    assert (Heq : powers = increment_powers powers' x).
    {
      extensionality y; unfold increment_powers, powers'.
      destruct (decide (x = y)); [by subst; rewrite !update_powers_eq |].
      by rewrite !update_powers_neq.
    }
    rewrite Heq.
    constructor.
    apply IHn.
    rewrite Heq, sum_increment_powers in Heqn.
    by congruence.
Qed.

Lemma powers_ind
  (P : (index -> nat) -> Prop)
  (Hzero : P zero_powers)
  (Hsucc : forall (i : index) (powers : index -> nat),
    P powers -> P (increment_powers powers i)) :
  forall (powers : index -> nat), P powers.
Proof.
  intro powers.
  pose proof (Hpowers := Powers_powers powers).
  induction Hpowers; [done |].
  by apply Hsucc.
Qed.

End sec_powers_ind.

Section sec_composition.

Context {index : Type}
        (multipliers : index -> Z)
        (Hmultipliers : forall (i : index), multipliers i <> 0)
        `{finite.Finite index}
        `{Inhabited index}.

Definition indexed_parity_vlsms (i : index) : VLSM ParityMessage :=
  ParityVLSM (multipliers i).

Context (parity_constraint : composite_label indexed_parity_vlsms ->
                             composite_state indexed_parity_vlsms * option ParityMessage -> Prop).

Definition parity_composite_vlsm : VLSM ParityMessage :=
  composite_vlsm indexed_parity_vlsms parity_constraint.

Definition prod_powers_aux (powers : index -> nat) (l : list index) : Z :=
  foldr Z.mul 1 (zip_with Z.pow (map multipliers l) (map (Z.of_nat ∘ powers) l)).

Lemma prod_powers_aux_cons (powers : index -> nat) (a : index) (l : list index) :
  prod_powers_aux powers (a :: l) = multipliers a ^ Z.of_nat (powers a) * prod_powers_aux powers l.
Proof. done. Qed.

Lemma prod_powers_aux_zero (powers : index -> nat) (l : list index) :
  Forall (fun n => powers n = 0%nat) l -> prod_powers_aux powers l = 1.
Proof.
  intros Hforall.
  induction Hforall; [done |].
  by rewrite prod_powers_aux_cons, IHHforall, H1.
Qed.

Definition prod_powers (powers : index -> nat) : Z := prod_powers_aux powers (enum index).

Lemma prod_powers_zero : prod_powers zero_powers = 1.
Proof.
  apply prod_powers_aux_zero. by rewrite Forall_forall.
Qed.


Lemma prod_increment_powers (powers : index -> nat) (n : index) :
  prod_powers (increment_powers powers n) = multipliers n * prod_powers powers.
Proof.
  unfold prod_powers.
  pose proof (Hnodup := NoDup_enum index).
  pose proof (Hn := elem_of_enum n).
  revert Hnodup Hn.
  generalize (enum index) as l.
  induction l; [by inversion 2 |].
  rewrite NoDup_cons, elem_of_cons, !prod_powers_aux_cons.
  intros [Ha Hnodup] [Hn | Hn].
  - subst. rewrite increment_powers_eq.
    rewrite Zmult_assoc, <- Z.pow_succ_r; [| lia].
    cut (prod_powers_aux (increment_powers powers a) l = prod_powers_aux powers l); [by intros ->; lia |].
    clear IHl Hnodup.
    induction l; [done |].
    apply not_elem_of_cons in Ha as [Ha0 Ha].
    by rewrite !prod_powers_aux_cons, IHl, increment_powers_neq by done.
  - rewrite IHl by done. rewrite increment_powers_neq by set_solver.
    by lia.
Qed.

Definition delta_powers (n : index) :=
  increment_powers zero_powers n.

Lemma prod_powers_delta (n : index) : prod_powers (delta_powers n) = multipliers n.
Proof.
  unfold delta_powers.
  rewrite prod_increment_powers, prod_powers_zero.
  by lia.
Qed.

Lemma prod_powers_pos (Hmpos : forall (i : index), multipliers i > 0) :
forall (powers : index -> nat), prod_powers powers > 0.
Proof.
  intros powers.
  induction powers using powers_ind; [by rewrite prod_powers_zero |].
  rewrite prod_increment_powers.
  by specialize (Hmpos i); lia.
Qed.

Lemma composition_valid_messages_powers_of_mults_right (m : ParityMessage) :
  valid_message_prop parity_composite_vlsm m ->
  exists (powers : index -> nat) (i : index), Z.of_nat (powers i) >= 1 /\ m = prod_powers powers.
  intros [s Hvsm]. remember (Some m) as om.
  revert m Heqom.
  induction Hvsm using valid_state_message_prop_ind; intros; subst.
  - unfold option_initial_message_prop, from_option in Hom.
    cbn in Hom.
    unfold composite_initial_message_prop in Hom.
    destruct Hom as (n & (mielem & mi) & Hmi).
    cbn in mi, Hmi.
    exists (delta_powers n), n.
    unfold delta_powers at 1.
    split; [by rewrite increment_powers_eq |].
    f_equal. rewrite <- Hmi, mi. symmetry.
    by apply prod_powers_delta.
  - destruct l as (k & lk).
    destruct om; [| done].
    destruct (IHHvsm2 p) as [powers (i & Hi)]; [done |]; inversion Ht.
    exists (increment_powers powers k), k.
    split; [by rewrite increment_powers_eq; lia |].
    f_equal.
    destruct Hi as [Hgeq1 ->].
    by rewrite prod_increment_powers.
Qed.

End sec_composition.

Print powers_ind.

Section sec_free_composition.

Context {index : Type}
        (multipliers : index -> Z)
        (Hmultipliers : forall (i : index), multipliers i <> 0)
        `{finite.Finite index}
        `{Inhabited index}.

Definition free_parity_composite_vlsm : VLSM ParityMessage :=
  free_composite_vlsm (indexed_parity_vlsms multipliers).

Lemma composition_valid_messages_powers_of_mults_left
(Hmpos : forall (i : index), multipliers i > 0) (m : ParityMessage) :
  forall (powers : index -> nat) (i : index), Z.of_nat (powers i) >= 1 /\ m = prod_powers multipliers powers ->
  valid_message_prop free_parity_composite_vlsm m.
Proof.
  intros powers i [Hpowgeq1 Hm].
  revert i Hpowgeq1 m Hm.
  induction powers using powers_ind; [done |].
  pose proof (Hpowers := Powers_powers powers).
  inversion Hpowers.
  - subst. clear Hpowers IHpowers.
    intros _ _ m Hm.
    rewrite prod_increment_powers, prod_powers_zero in Hm by done.
    apply initial_message_is_valid. exists i.
    cut (initial_message_prop (indexed_parity_vlsms multipliers i) m).
    {
      intros Him. by exists (exist _ m Him).
    }
    by subst; cbn; lia.
  - assert (Hmvalid : valid_message_prop free_parity_composite_vlsm (prod_powers multipliers powers)).
    {
      eapply IHpowers with (i := i0); [| done].
      by subst; rewrite increment_powers_eq; lia.
    }
    rewrite prod_increment_powers.
    pose proof (Hpos := prod_powers_pos multipliers Hmultipliers Hmpos powers).
    intros. subst. clear - Hmvalid Hpos.
    remember (prod_powers _ _) as m. clear Heqm.
    unshelve eapply input_valid_transition_out.
    + by exists i; exact parity_label.
    + by intros j; destruct (decide (i = j)); [exact (m + 1) | exact 1].
    + by intros j; exact 1.
    + by exact (Some m).
    + repeat split.
      * apply initial_state_is_valid. intros j. unfold initial_state_prop. cbn.
        unfold ParityComponent_initial_state_prop. by case_decide; lia.
      * done.
      * by rewrite decide_True; [lia |].
      * by lia.
      * cbn. f_equal. extensionality j.
        rewrite decide_True by done.
        destruct (decide (i = j)); subst; state_update_simpl; [lia |].
        by rewrite decide_False.
    + done.
Qed.

Lemma composition_valid_messages_powers_of_mults
(Hmpos : forall (i : index), multipliers i > 0) (m : ParityMessage) :
  (exists (powers : index -> nat) (i : index), Z.of_nat (powers i) >= 1 /\ m = prod_powers multipliers powers) <->
  valid_message_prop free_parity_composite_vlsm m.
Proof.
  split.
  - cut (forall (powers : index → nat) (i : index),
         Z.of_nat (powers i) >= 1 ∧ m = prod_powers multipliers powers ->
         valid_message_prop free_parity_composite_vlsm m);
      [| by apply composition_valid_messages_powers_of_mults_left].
      intros Hforall (powers & i & Hpowersm).
      apply (Hforall powers i Hpowersm).
  - intros Hvm.
    eapply VLSM_incl_valid_message in Hvm; cycle 1.
    + by apply free_composite_vlsm_spec.
    + by do 2 red.
    + cbn in Hvm.
      by eapply composition_valid_messages_powers_of_mults_right.
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
Proof.
  intros x y.
  unfold Decision.
  decide equality.
Qed.

#[local] Instance finite_index23 : finite.Finite index23.
Proof.
  exists [two; three].
  - repeat constructor; set_solver.
  - intros []; set_solver.
Qed.

Definition parity_constraint
  (l : composite_label (indexed_parity_vlsms multipliers23)) (sm : composite_state (indexed_parity_vlsms multipliers23) * option ParityMessage) : Prop :=
  let i := projT1 l in
  let (s', _) := composite_transition (indexed_parity_vlsms multipliers23) l sm in
  Z.even (((fst sm) i) + (s' i)).

Definition parity_composite_vlsm23 := parity_composite_vlsm multipliers23 parity_constraint.

End sec_parity23.
