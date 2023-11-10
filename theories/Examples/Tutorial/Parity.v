From stdpp Require Import prelude finite.
From VLSM.Core Require Import VLSM PreloadedVLSM VLSMProjections Composition.
From Coq Require Import FunctionalExtensionality.

(** * Parity VLSM

  This module demonstrates some basic notions of the VLSM framework. We define
  a (single) parity VLSM that stores a tuple and continually decrements one of the
  tuple's elements while a constraint is checked at each step. The name originates
  from the property of this VLSM to preserve the evenness of the tuple elements
  difference ([parity_valid_states_same_parity]). The definitions and lemmas tap into
  concepts such as valid and constrained traces, transitions, states, and messages.
*)

#[local] Open Scope Z_scope.

(** ** Definition of the Parity VLSM

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

Definition Parity_initial_state_prop (st : ParityState) : Prop :=
  st >= 1.

Definition Parity_transition
  (l : ParityLabel) (st : ParityState) (om : option ParityMessage)
  : ParityState * option ParityMessage :=
  match om with
  | Some j  => (st - j, Some (2 * j))
  | None    => (st, None)
  end.

Definition Parity_valid
  (l : ParityLabel) (st : ParityState) (om : option ParityMessage) : Prop :=
  match om with
  | Some msg => msg <= st /\ 2 <= msg
  | None     => False
  end.

(**
  We must also provide a proof that the intial state type
  is inhabited as the set of initial states is non-empty.
*)

Definition Parity_initial_state_type : Type :=
  {st : ParityState | Parity_initial_state_prop st}.

Program Definition Parity_initial_state :
  Parity_initial_state_type := exist _ 1 _.
Next Obligation.
Proof. done. Defined.

#[export] Instance Parity_Inhabited_initial_state_type :
 Inhabited (Parity_initial_state_type) :=
  populate (Parity_initial_state).

(**
  An intermediate representation for the VLSM is required.
  It uses the previously defined specifications.
*)

Definition ParityMachine : VLSMMachine ParityType :=
{|
  initial_state_prop := Parity_initial_state_prop;
  initial_message_prop := fun (ms : ParityMessage) => ms = 2;
  s0 := Parity_Inhabited_initial_state_type;
  transition := fun l '(st, om) => Parity_transition l st om;
  valid := fun l '(st, om) => Parity_valid l st om;
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

Definition parity_label : label ParityVLSM := ().

(** ** Parity VLSM Examples *)

(** *** Example of an arbitrary transition *)

Lemma parity_example_transition_1 `(X : VLSM ParityMessage) :
  transition ParityVLSM parity_label (4, Some 10) = (-6, Some 20).
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
  [ Build_transition_item parity_label (Some 4)
     4 (Some 8)
  ; Build_transition_item parity_label (Some 2)
     2 (Some 4) ].

Definition parity_trace1_last_item : transition_item ParityVLSM :=
  Build_transition_item parity_label (Some 2)
    0 (Some 4).

Definition parity_trace1 : list (transition_item ParityVLSM) :=
  parity_trace1_init ++ [parity_trace1_last_item].

Definition parity_trace1_first_state : ParityState := 8.

Definition parity_trace1_last_state : ParityState :=
  destination parity_trace1_last_item.

(** Defined trace is valid: *)

Example parity_valid_message_prop_2 : valid_message_prop ParityVLSM 2.
Proof. by apply initial_message_is_valid. Qed.

Example parity_can_emit_4 : can_emit ParityVLSM 4.
Proof.
  exists (2, Some 2), parity_label, 0.
  repeat split; [| | by lia.. | by cbn; do 2 f_equal; lia].
  - by apply initial_state_is_valid; cbn; unfold Parity_initial_state_prop; lia.
  - by app_valid_tran.
Qed.

Example parity_valid_message_prop_4 : valid_message_prop ParityVLSM 4.
Proof.
  by apply (emitted_messages_are_valid ParityVLSM 4 parity_can_emit_4).
Qed.

Proposition parity_valid_transition_1 :
  input_valid_transition ParityVLSM parity_label (8, Some 4) (4, Some 8).
Proof.
  repeat split; [| | | by lia].
  - by apply initial_state_is_valid; cbn;
      unfold Parity_initial_state_prop, parity_trace1_first_state; lia.
  - by apply parity_valid_message_prop_4.
  - by unfold parity_trace1_first_state; nia.
Qed.

Proposition parity_valid_transition_2 :
  input_valid_transition ParityVLSM parity_label (4, Some 2) (2, Some 4).
Proof.
  repeat split; [| | by lia..].
  - by app_valid_tran; eapply parity_valid_transition_1; lia.
  - by apply parity_valid_message_prop_2.
Qed.

Proposition parity_valid_transition_3 :
  input_valid_transition ParityVLSM parity_label (2, Some 2) (0, Some 4).
Proof.
  repeat split; [| | by lia..].
  - by app_valid_tran; apply parity_valid_transition_2.
  - by apply parity_valid_message_prop_2.
Qed.

Example parity_valid_trace1 :
  finite_valid_trace_init_to ParityVLSM
   parity_trace1_first_state parity_trace1_last_state parity_trace1.
Proof.
  constructor; [| done].
  repeat apply finite_valid_trace_from_to_extend.
  - by eapply finite_valid_trace_from_to_empty,
      input_valid_transition_destination, parity_valid_transition_3.
  - by apply parity_valid_transition_3.
  - by apply parity_valid_transition_2.
  - by apply parity_valid_transition_1.
Qed.

Example parity_valid_trace1_alt :
  finite_valid_trace_init_to_alt ParityVLSM
   parity_trace1_first_state parity_trace1_last_state parity_trace1.
Proof.
  constructor; [| done].
  by repeat apply mvt_extend; [.. | apply mvt_empty]; try done;
    [apply parity_valid_message_prop_4 | apply parity_valid_message_prop_2 ..].
Qed.

(** *** Example of a constrained trace *)

(** Previously defined trace is obviously constrained, since it's valid *)
Lemma parity_constrained_trace1 :
  finite_constrained_trace_init_to_direct ParityVLSM
   parity_trace1_first_state parity_trace1_last_state parity_trace1.
Proof.
  constructor; [| done].
  by repeat apply ct_extend; [.. | apply ct_empty].
Qed.

Definition parity_trace2_init : list (transition_item ParityVLSM) :=
  [ Build_transition_item parity_label (Some 2) 5 (Some 4)
  ; Build_transition_item parity_label (Some 2) 3 (Some 4) ].

Definition parity_trace2_last_item : transition_item ParityVLSM :=
  Build_transition_item parity_label (Some 3) 0 (Some 6).

Definition parity_trace2 : list (transition_item ParityVLSM) :=
  parity_trace2_init ++ [parity_trace2_last_item].

Definition parity_trace2_init_first_state : ParityState := 7.

Definition parity_trace2_init_last_state : ParityState := 3.

Definition parity_trace2_last_state : ParityState :=
  destination parity_trace2_last_item.

(** The given trace is valid without the last transition. *)

Proposition parity_valid_transition_1' :
  input_valid_transition ParityVLSM parity_label
   (parity_trace2_init_first_state, Some 2) (5, Some 4).
Proof. by app_valid_tran. Qed.

Proposition parity_valid_transition_2' :
  input_valid_transition ParityVLSM parity_label
   (5, Some 2) (3, Some 4).
Proof. by app_valid_tran; apply parity_valid_transition_1'. Qed.

Example parity_valid_trace2_init :
  finite_valid_trace_init_to ParityVLSM
   parity_trace2_init_first_state parity_trace2_init_last_state parity_trace2_init.
Proof.
  constructor; [| done].
  repeat apply finite_valid_trace_from_to_extend.
  - by eapply finite_valid_trace_from_to_empty,
      input_valid_transition_destination, parity_valid_transition_2'.
  - by apply parity_valid_transition_2'.
  - by apply parity_valid_transition_1'.
Qed.

Example parity_valid_trace2_init_alt :
  finite_valid_trace_init_to_alt ParityVLSM
   parity_trace2_init_first_state parity_trace2_init_last_state parity_trace2_init.
Proof.
  constructor; [| done].
  by repeat apply mvt_extend; [..| apply mvt_empty]; try done;
    apply parity_valid_message_prop_2.
Qed.

(**
  From the previous lemmas, it follows that the given trace
  without its last transition is constrained.
*)

Example parity_constrained_trace2_init :
  finite_constrained_trace_init_to ParityVLSM
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
  finite_constrained_trace_init_to ParityVLSM
    parity_trace2_init_first_state parity_trace2_last_state parity_trace2.
Proof.
  destruct parity_constrained_trace2_init.
  split; [| done].
  eapply (extend_right_finite_trace_from_to (pre_loaded_with_all_messages_vlsm ParityVLSM));
    [done |].
  repeat split; [| | done..].
  - by eapply finite_valid_trace_from_to_last_pstate.
  - by apply any_message_is_valid_in_preloaded.
Qed.

(** *** Example of a valid transition

  The last transition of a valid trace is valid.
*)

Lemma parity_example_valid_transition :
  input_valid_transition ParityVLSM parity_label
   (2, Some 2) (0, Some 4).
Proof.
  apply (finite_valid_trace_from_to_last_transition ParityVLSM
    parity_trace1_first_state parity_trace1_last_state
    parity_trace1_init parity_trace1 parity_trace1_last_item); [| done].
  by apply parity_valid_trace1.
Qed.

(** *** Example of a constrained transition

  The last transition of a constrained trace is constrained.
*)

Example parity_example_constrained_transition :
  input_valid_transition (pre_loaded_with_all_messages_vlsm ParityVLSM) parity_label
   (3, Some 3) (0, Some 6).
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
  forall (m : ParityMessage), constrained_message_prop ParityVLSM m ->
   Z.Even m /\ m >= 4.
Proof.
  intros m ([s []] & [] & s' & (_ & _ & []) & Ht).
  inversion Ht; subst.
  by split; [eexists | lia].
Qed.

Lemma parity_constrained_messages_right :
  forall (m : ParityMessage), Z.Even m -> m >= 4 ->
   constrained_message_prop ParityVLSM m.
Proof.
  intros m [n ->] Hmgt0.
  exists (n, Some n), parity_label, 0.
  repeat split; [| | by lia.. | by cbn; do 2 f_equal; lia].
  - apply initial_state_is_valid; cbn; red; lia.
  - by apply any_message_is_valid_in_preloaded.
Qed.

Lemma parity_constrained_messages :
  forall (m : ParityMessage),
   constrained_message_prop ParityVLSM m <-> (Z.Even m /\ m >= 4).
Proof.
  split.
  - by apply parity_constrained_messages_left.
  - by intros [? ?]; apply parity_constrained_messages_right.
Qed.

(** *** Constrained states property *)

Lemma parity_constrained_states_right :
 forall (st : ParityState),
  constrained_state_prop ParityVLSM st ->
   st >= 0.
Proof.
  induction 1 using valid_state_prop_ind.
  - cbn in Hs; red in Hs; lia.
  - destruct l, om, Ht as [(Hs & _ & []) Ht].
    by inversion Ht; subst; cbn in *; lia.
Qed.

Lemma parity_constrained_states_left :
  forall (st : ParityState), st >= 0 ->
    constrained_state_prop ParityVLSM st.
Proof.
  intros st Hst.
  apply input_valid_transition_destination
    with (l := parity_label) (s := st + 2) (om := Some 2) (om' := Some 4).
  repeat split; [| | by lia.. | by cbn; do 2 f_equal; lia].
  - apply initial_state_is_valid; cbn; red; lia.
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

(** *** Powers of 2 greater or equal than 2 are valid messages *)

Lemma parity_valid_messages_powers_of_2_right :
  forall (m : ParityMessage),
    valid_message_prop ParityVLSM m ->
      exists p : Z, p >= 1 /\ m = 2 ^ p.
Proof.
  intros m [s Hvsm].
  assert (Hom : is_Some (Some m)) by (eexists; done).
  replace m with (is_Some_proj Hom) by done.
  revert Hvsm Hom; generalize (Some m) as om; intros.
  clear m; induction Hvsm using valid_state_message_prop_ind.
  - destruct Hom as [m ->]; cbn in *; subst.
    by exists 1; split; lia.
  - destruct om as [m |]; [| done].
    unshelve edestruct IHHvsm2 as [x Hx]; [done |].
    inversion Ht; subst; clear Ht.
    cbn in Hx |- *; destruct Hx as [Hgeq1 ->].
    exists (x + 1).
    split; [by lia |].
    by rewrite <- Z.pow_succ_r; [| lia].
Qed.

Lemma parity_valid_messages_powers_of_2_left :
  forall (p : Z),
    p >= 1 -> valid_message_prop ParityVLSM (2 ^ p).
Proof.
  intros p Hp.
  assert (Hle : 0 <= p - 1) by lia.
  replace p with (p - 1 + 1) by lia.
  remember (p - 1) as x.
  clear p Hp Heqx.
  revert x Hle.
  apply natlike_ind; [by apply initial_message_is_valid; cbn; lia |].
  intros x Hxgt0 Hindh.
  apply emitted_messages_are_valid.
  exists (2 ^ (x + 1), Some (2 ^ (x + 1))), parity_label, 0.
  repeat split.
  - by apply initial_state_is_valid; cbn; red; lia.
  - by apply Hindh.
  - by lia.
  - replace (x + 1) with (Z.succ x) by lia.
    by rewrite Z.pow_succ_r; lia.
  - by cbn; rewrite <- Z.pow_succ_r, Z.add_succ_l; [do 2 f_equal; lia | lia].
Qed.

Lemma parity_valid_messages_powers_of_2 : forall (m : ParityMessage),
  valid_message_prop ParityVLSM m <->
    exists p : Z, p >= 1 /\ m = 2 ^ p.
Proof.
  split.
  - by intros; apply parity_valid_messages_powers_of_2_right.
  - by intros (p & Hpgt0 & [= ->]); apply parity_valid_messages_powers_of_2_left.
Qed.

(**
  The constrained transition from [parity_example_constrained_transition]
  is not also valid.
*)
Example parity_example_constrained_transition_not_valid :
  ~ input_valid_transition ParityVLSM parity_label
    (3, Some 3) (0, Some 6).
Proof.
  intros [(_ & Hm & _) _].
  apply parity_valid_messages_powers_of_2 in Hm as (p & Hp & Heq).
  rewrite <- (Z.succ_pred p) in Heq.
  by rewrite Z.pow_succ_r in Heq; lia.
Qed.

(** *** Valid states hold non-negative integers *)

Lemma parity_valid_states_right (s : ParityState) :
  valid_state_prop ParityVLSM s -> s >= 0.
Proof.
  induction 1 using valid_state_prop_ind;
    [by cbn in Hs; red in Hs; lia |].
  destruct om, l, Ht as [(Hs & Hm & Hv) Ht]; [| done].
  inversion Ht; subst.
  by destruct Hv; lia.
Qed.

Lemma parity_valid_states_left (s : ParityState) :
  s >= 0 -> valid_state_prop ParityVLSM s.
Proof.
  intro.
  destruct (decide (s = 0)) as [-> |];
    [| by apply initial_state_is_valid; cbn; red; lia].
  apply input_valid_transition_destination
      with (l := parity_label) (s := 2) (om := Some 2) (om' := Some 4).
  repeat split; cbn; [| | by lia..].
  - by apply initial_state_is_valid; cbn; red; lia.
  - by apply initial_message_is_valid.
Qed.

Lemma parity_valid_states :
  forall (s : ParityState),
  valid_state_prop ParityVLSM s <-> s >= 0.
Proof.
  split.
  - by apply parity_valid_states_right.
  - by apply parity_valid_states_left.
Qed.


Section sec_radix23.

Inductive index23 := two | three.


#[local] Instance eq_dec_index23 : EqDecision index23.
Proof. by intros x y; unfold Decision; decide equality. Qed.


Definition Triple_transition
  (l : ParityLabel) (st : ParityState) (om : option ParityMessage)
  : ParityState * option ParityMessage :=
  match om with
  | Some j  => (st - j, Some (3 * j))
  | None    => (st, None)
  end.

Definition TripleMachine : VLSMMachine ParityType :=
{|
  initial_state_prop := Parity_initial_state_prop;
  initial_message_prop := fun (ms : ParityMessage) => ms = 3;
  s0 := Parity_Inhabited_initial_state_type;
  transition := fun l '(st, om) => Triple_transition l st om;
  valid := fun l '(st, om) => Parity_valid l st om;
|}.

Definition TripleVLSM : VLSM ParityMessage := mk_vlsm TripleMachine.

Definition components_23 (i : index23) : VLSM ParityMessage :=
  match i with
  | two => ParityVLSM
  | three => TripleVLSM
  end.

Definition composite_state_23_sum (s : composite_state components_23) : Z :=
  s two + s three.

Definition zproj (s : composite_state components_23) (i : index23) : Z :=
  match i with
  | two => s two
  | three => s three
  end.

Definition constraint_23
  (l : composite_label components_23)
  (sm : composite_state components_23 * option ParityMessage) : Prop :=
  let sm' := composite_transition components_23 l sm in
  Z.Even (composite_state_23_sum sm.1 + composite_state_23_sum sm'.1).

Definition composition_23 : VLSM ParityMessage :=
  composite_vlsm components_23 constraint_23.

Definition final_state (s : composite_state components_23) :=
  valid_state_prop composition_23 s /\
  ~ exists
    (l : composite_label components_23)
    (om : option ParityMessage)
    (som' : composite_state components_23 * option ParityMessage),
      input_valid_transition composition_23 l (s, om) som'.

Definition statenm (n m : Z) : composite_state components_23 :=
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
  valid_state_prop composition_23 (statenm n m).
Proof.
  by apply initial_state_is_valid; intros []; cbn; red.
Qed.

Example valid_state11 : valid_state_prop composition_23 state11.
Proof. by apply (valid_statenm_geq1 1 1); lia. Qed.

Example valid_state00 : valid_state_prop composition_23 state00.
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
      assert (Hinit : initial_message_prop (components_23 two) 2) by done.
      by exists (exist _ 2 Hinit).
    + by cbn; lia.
    + by lia.
    + by red; cbn; unfold composite_state_23_sum; state_update_simpl; cbn; exists 3.
    + by cbn; f_equal; extensionality i; destruct i; cbn; state_update_simpl; cbn.
  - apply initial_message_is_valid.
    exists two.
    assert (Hinit : initial_message_prop (components_23 two) 2) by done.
    by exists (exist _ 2 Hinit).
  - by unfold state02; cbn; lia.
  - by lia.
  - by red; cbn; unfold composite_state_23_sum; state_update_simpl; cbn; exists 1.
  - by cbn; f_equal; extensionality i; destruct i; cbn; state_update_simpl; cbn.
Qed.

Example valid_state01 : valid_state_prop composition_23 state01.
Proof.
  apply input_valid_transition_destination
    with (l := existT two parity_label) (s := state21) (om := Some 2) (om' := Some 4).
  repeat split.
  - by apply valid_statenm_geq1.
  - apply initial_message_is_valid.
    exists two.
    assert (Hinit : initial_message_prop (components_23 two) 2) by done.
    by exists (exist _ 2 Hinit).
  - by cbn; lia.
  - by lia.
  - by red; cbn; unfold composite_state_23_sum; state_update_simpl; cbn; exists 2.
  - by cbn; f_equal; extensionality i; destruct i; cbn; state_update_simpl; cbn.
Qed.

Example valid_state10 : valid_state_prop composition_23 state10.
Proof.
  apply input_valid_transition_destination
    with (l := existT three parity_label) (s := state12) (om := Some 2) (om' := Some 6).
  repeat split.
  - by apply valid_statenm_geq1.
  - apply initial_message_is_valid.
    exists two.
    assert (Hinit : initial_message_prop (components_23 two) 2) by done.
    by exists (exist _ 2 Hinit).
  - by cbn; lia.
  - by lia.
  - by red; cbn; unfold composite_state_23_sum; state_update_simpl; cbn; exists 2.
  - by cbn; f_equal; extensionality i; destruct i; cbn; state_update_simpl; cbn.
Qed.

Lemma final_state_prop23_left (s : composite_state components_23) :
  (s = state00 \/ s = state01 \/ s = state10 \/ s = state11) -> final_state s.
Proof.
  intros Hcases.
  split.
  - destruct Hcases as [Hst | [Hst | [Hst | Hst]]]; subst.
    + by apply valid_state00.
    + by apply valid_state01.
    + by apply valid_state10.
    + by apply valid_state11.
  - intros ([i li] & om & som' & (Hs & Hom & Hv & Hc) & _).
    destruct Hc as [n Hc].
    destruct i; (destruct om ; [| done]); unfold composite_state_23_sum in Hc;
      cbn in *; state_update_simpl;
      by destruct Hcases as [| [| []]]; subst; cbn in *; lia.
Qed.

Lemma valid_state_23_pos :
  forall (s : composite_state components_23), valid_state_prop composition_23 s ->
  forall (i : index23), zproj s i >= 0.
Proof.
  intros s Hs; induction Hs using valid_state_prop_ind;
    [by intros i; specialize (Hs i); destruct i; cbn in *; red in Hs; lia |].
  destruct l as [j lj], Ht as [(_ & _ & Hv & Hc) Ht].
  intro i; specialize (IHHs i).
  by destruct j; (destruct om ; [| done]); inversion Ht; subst; clear Ht; cbn in *;
    destruct i; cbn in *; state_update_simpl; lia.
Qed.

Lemma final_state_prop23_right (s : composite_state components_23) :
  final_state s ->
    (s two = 0 /\ s three = 0) \/ (s two = 0 /\ s three = 1) \/
    (s two = 1 /\ s three = 0) \/ (s two = 1 /\ s three = 1).
Proof.
  intros [Hs Hfinal].
  destruct (decide ((s two = 0 /\ s three = 0) \/ (s two = 0 /\ s three = 1) \/
    (s two = 1 /\ s three = 0) \/ (s two = 1 /\ s three = 1))); [done |].
  contradict Hfinal.
  assert (s two > 1 \/ s three > 1) as [Hs1 | Hs1].
  {
    pose proof (valid_state_23_pos _ Hs two).
    pose proof (valid_state_23_pos _ Hs three).
    by cbn in *; lia.
  }
  - exists (existT two ()), (Some 2),
      (state_update components_23 s two (s two - 2), Some 4).
    repeat split; [done | ..].
    + apply initial_message_is_valid.
      exists two.
      assert (Hinit : initial_message_prop (components_23 two) 2) by done.
      by exists (exist _ 2 Hinit).
    + by lia.
    + by lia.
    + red; cbn; unfold composite_state_23_sum; state_update_simpl.
      by exists (s two + s three - 1); lia.
  - exists (existT three ()), (Some 2),
      (state_update components_23 s three (s three - 2), Some 6).
    repeat split; [done | ..].
    + apply initial_message_is_valid.
      exists two.
      assert (Hinit : initial_message_prop (components_23 two) 2) by done.
      by exists (exist _ 2 Hinit).
    + by lia.
    + by lia.
    + red; cbn; unfold composite_state_23_sum; state_update_simpl.
      by exists (s two + s three - 1); lia.
Qed.

End sec_radix23.

