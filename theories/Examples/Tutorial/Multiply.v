From stdpp Require Import prelude finite.
From VLSM.Core Require Import VLSM PreloadedVLSM VLSMProjections Composition.
From Coq Require Import FunctionalExtensionality.

(** * Tutorial: VLSMs that Multiply

  This module demonstrates some basic notions of the VLSM framework.

  We define a family of VLSMs that store an integer and continually decrement it
  using input messages (also integers), while a constraint is checked at each step.
  The definitions and lemmas tap into concepts such as valid and constrained
  traces, transitions, states, and messages.

  The "doubling" VLSM has 2 as its only initial message and as output doubles
  the messages it receives as input. Therefore, constrained messages are
  positive even numbers ([doubling_constrained_messages]) and valid messages are
  powers of 2 ([doubling_valid_messages_powers_of_2]). Similarly, the "tripling"
  VLSM has 3 as its only initial message and as output triples the messages it
  receives as input.

  When composing the doubling and tripling VLSMs, they become more than
  the sum of their parts: the free composition's valid messages are
  all integers which can be decomposed as a product of powers of 2 and 3.
*)

#[local] Open Scope Z_scope.

(** ** Definition of common features of the multiplying VLSMs

  The multiplying VLSMs have only one type of transition, decrementing their
  state and multiplying their input message as an output.
  For this reason, the [unit] type can be used as a label.
*)

Definition multiplying_label : Type := unit.

(** The state will hold an integer. *)

Definition multiplying_state : Type := Z.

(** Messages are integers. *)

Definition multiplying_message : Type := Z.

(** A VLSM Type is defined using [multiplying_state] and [multiplying_label]. *)

Definition multiplying_type : VLSMType multiplying_message :=
{|
  state := multiplying_state;
  label := multiplying_label;
|}.

(**
  To improve readability, we explicitly define [multiply_label] as the value of
  the unit type.
*)

Definition multiply_label : label multiplying_type := ().

(** The initial states of multiplying VLSMs will be positive integers. *)

Definition multiplying_initial_state_prop (st : multiplying_state) : Prop :=
  st >= 1.

(**
  We must also provide a proof that the intial state type
  is inhabited as the set of initial states is non-empty.
*)

Definition multiplying_initial_state_type : Type :=
  {st : multiplying_state | multiplying_initial_state_prop st}.

Program Definition multiplying_initial_state :
  multiplying_initial_state_type := exist _ 1 _.
Next Obligation.
Proof. done. Defined.

#[export] Instance multiplying_initial_state_type_inhabited :
 Inhabited (multiplying_initial_state_type) :=
  populate (multiplying_initial_state).

(**
  The transition validity predicate is also common for all multiplying VLSMs:
  the message must exist, must be larger than 1, and not larger than the current state.
*)

Definition multiplying_valid
  (l : multiplying_label) (st : multiplying_state) (om : option multiplying_message) : Prop :=
  match om with
  | Some msg => 2 <= msg <= st
  | None     => False
  end.

(** ** Definition of the doubling VLSM

  The doubling VLSM is a multiplying VLSM whose initial message is 2 and which
  outputs the double of the received input, while using it to decrement the
  current state; the [multiplying_valid] constraint ensures that the valid/constraines
  states don't become negative.

  Not that, since the transition function must be total, it must also be defined
  for the case in which no input is provided, although that case will be
  filtered out by the transition validity predicate.
*)

Definition doubling_transition
  (l : multiplying_label) (st : multiplying_state) (om : option multiplying_message)
  : multiplying_state * option multiplying_message :=
  match om with
  | Some j  => (st - j, Some (2 * j))
  | None    => (st, None)
  end.

(**
  An intermediate representation for the VLSM is required.
  It uses the previously defined specifications with the addition that it
  states that 2 is the only initial message.
*)

Definition doubling_machine : VLSMMachine multiplying_type :=
{|
  initial_state_prop := multiplying_initial_state_prop;
  initial_message_prop := fun (ms : multiplying_message) => ms = 2;
  s0 := multiplying_initial_state_type_inhabited;
  transition := fun l '(st, om) => doubling_transition l st om;
  valid := fun l '(st, om) => multiplying_valid l st om;
|}.

(** The definition of the doubling VLSM *)

Definition doubling_vlsm : VLSM multiplying_message :=
{|
  vlsm_type := multiplying_type;
  vlsm_machine := doubling_machine;
|}.

(** *** Doubling VLSM examples *)

(** **** Example of an arbitrary transition *)

Lemma doubling_example_transition_1 `(X : VLSM multiplying_message) :
  transition doubling_vlsm multiply_label (4, Some 10) = (-6, Some 20).
Proof. done. Qed.

(** **** Example of a valid trace *)

(** The initial state cannot be included to this definition, because, since there is no
    transition reaching this state, it cannot be expressed in the below manner
    Regarding the transition which leads to the final state, it technically could be
    included, but we choose to model this way, in order to be consistent
    with the subsequent example, where adding the last transition makes a qualitative
    difference to the trace
*)

Definition doubling_trace1_init : list (transition_item doubling_vlsm) :=
  [ Build_transition_item multiply_label (Some 4)
     4 (Some 8)
  ; Build_transition_item multiply_label (Some 2)
     2 (Some 4) ].

Definition doubling_trace1_last_item : transition_item doubling_vlsm :=
  Build_transition_item multiply_label (Some 2)
    0 (Some 4).

Definition doubling_trace1 : list (transition_item doubling_vlsm) :=
  doubling_trace1_init ++ [doubling_trace1_last_item].

Definition doubling_trace1_first_state : multiplying_state := 8.

Definition doubling_trace1_last_state : multiplying_state :=
  destination doubling_trace1_last_item.

(** Defined trace is valid: *)

Example doubling_valid_message_prop_2 : valid_message_prop doubling_vlsm 2.
Proof. by apply initial_message_is_valid. Qed.

Example doubling_can_emit_4 : can_emit doubling_vlsm 4.
Proof.
  exists (2, Some 2), multiply_label, 0.
  repeat split; [| | by lia.. | by cbn; do 2 f_equal; lia].
  - by apply initial_state_is_valid; cbn; unfold multiplying_initial_state_prop; lia.
  - by app_valid_tran.
Qed.

Example doubling_valid_message_prop_4 : valid_message_prop doubling_vlsm 4.
Proof.
  by apply (emitted_messages_are_valid doubling_vlsm 4 doubling_can_emit_4).
Qed.

Proposition doubling_valid_transition_1 :
  input_valid_transition doubling_vlsm multiply_label (8, Some 4) (4, Some 8).
Proof.
  repeat split; [| | | by lia].
  - by apply initial_state_is_valid; cbn;
      unfold multiplying_initial_state_prop, doubling_trace1_first_state; lia.
  - by apply doubling_valid_message_prop_4.
  - by unfold doubling_trace1_first_state; nia.
Qed.

Proposition doubling_valid_transition_2 :
  input_valid_transition doubling_vlsm multiply_label (4, Some 2) (2, Some 4).
Proof.
  repeat split; [| | by lia..].
  - by app_valid_tran; eapply doubling_valid_transition_1; lia.
  - by apply doubling_valid_message_prop_2.
Qed.

Proposition doubling_valid_transition_3 :
  input_valid_transition doubling_vlsm multiply_label (2, Some 2) (0, Some 4).
Proof.
  repeat split; [| | by lia..].
  - by app_valid_tran; apply doubling_valid_transition_2.
  - by apply doubling_valid_message_prop_2.
Qed.

Example doubling_valid_trace1 :
  finite_valid_trace_init_to doubling_vlsm
   doubling_trace1_first_state doubling_trace1_last_state doubling_trace1.
Proof.
  constructor; [| done].
  repeat apply finite_valid_trace_from_to_extend.
  - by eapply finite_valid_trace_from_to_empty,
      input_valid_transition_destination, doubling_valid_transition_3.
  - by apply doubling_valid_transition_3.
  - by apply doubling_valid_transition_2.
  - by apply doubling_valid_transition_1.
Qed.

Example doubling_valid_trace1_alt :
  finite_valid_trace_init_to_alt doubling_vlsm
   doubling_trace1_first_state doubling_trace1_last_state doubling_trace1.
Proof.
  constructor; [| done].
  by repeat apply mvt_extend; [.. | apply mvt_empty]; try done;
    [apply doubling_valid_message_prop_4 | apply doubling_valid_message_prop_2 ..].
Qed.

(** **** Example of a constrained trace *)

(** Previously defined trace is obviously constrained, since it's valid *)
Lemma doubling_constrained_trace1 :
  finite_constrained_trace_init_to_direct doubling_vlsm
   doubling_trace1_first_state doubling_trace1_last_state doubling_trace1.
Proof.
  constructor; [| done].
  by repeat apply ct_extend; [.. | apply ct_empty].
Qed.

Definition doubling_trace2_init : list (transition_item doubling_vlsm) :=
  [ Build_transition_item multiply_label (Some 2) 5 (Some 4)
  ; Build_transition_item multiply_label (Some 2) 3 (Some 4) ].

Definition doubling_trace2_last_item : transition_item doubling_vlsm :=
  Build_transition_item multiply_label (Some 3) 0 (Some 6).

Definition doubling_trace2 : list (transition_item doubling_vlsm) :=
  doubling_trace2_init ++ [doubling_trace2_last_item].

Definition doubling_trace2_init_first_state : multiplying_state := 7.

Definition doubling_trace2_init_last_state : multiplying_state := 3.

Definition doubling_trace2_last_state : multiplying_state :=
  destination doubling_trace2_last_item.

(** The given trace is valid without the last transition. *)

Proposition doubling_valid_transition_1' :
  input_valid_transition doubling_vlsm multiply_label
   (doubling_trace2_init_first_state, Some 2) (5, Some 4).
Proof. by app_valid_tran. Qed.

Proposition doubling_valid_transition_2' :
  input_valid_transition doubling_vlsm multiply_label
   (5, Some 2) (3, Some 4).
Proof. by app_valid_tran; apply doubling_valid_transition_1'. Qed.

Example doubling_valid_trace2_init :
  finite_valid_trace_init_to doubling_vlsm
   doubling_trace2_init_first_state doubling_trace2_init_last_state doubling_trace2_init.
Proof.
  constructor; [| done].
  repeat apply finite_valid_trace_from_to_extend.
  - by eapply finite_valid_trace_from_to_empty,
      input_valid_transition_destination, doubling_valid_transition_2'.
  - by apply doubling_valid_transition_2'.
  - by apply doubling_valid_transition_1'.
Qed.

Example doubling_valid_trace2_init_alt :
  finite_valid_trace_init_to_alt doubling_vlsm
   doubling_trace2_init_first_state doubling_trace2_init_last_state doubling_trace2_init.
Proof.
  constructor; [| done].
  by repeat apply mvt_extend; [..| apply mvt_empty]; try done;
    apply doubling_valid_message_prop_2.
Qed.

(**
  From the previous lemmas, it follows that the given trace
  without its last transition is constrained.
*)

Example doubling_constrained_trace2_init :
  finite_constrained_trace_init_to doubling_vlsm
   doubling_trace2_init_first_state doubling_trace2_init_last_state doubling_trace2_init.
Proof.
  apply VLSM_incl_finite_valid_trace_init_to.
  - by apply vlsm_incl_pre_loaded.
  - by apply doubling_valid_trace2_init.
Qed.

(**
  The trace is valid (in the preloaded doubling VLSM) without
  its last element and appending it to the end also gives
  a valid trace (in the preloaded doubling VLSM).
  It follows that the full trace is constrained in
  the original doubling VLSM.
*)

Example doubling_constrained_trace2 :
  finite_constrained_trace_init_to doubling_vlsm
    doubling_trace2_init_first_state doubling_trace2_last_state doubling_trace2.
Proof.
  destruct doubling_constrained_trace2_init.
  split; [| done].
  eapply (extend_right_finite_trace_from_to (pre_loaded_with_all_messages_vlsm doubling_vlsm));
    [done |].
  repeat split; [| | done..].
  - by eapply finite_valid_trace_from_to_last_pstate.
  - by apply any_message_is_valid_in_preloaded.
Qed.

(** **** Example of a valid transition

  The last transition of a valid trace is valid.
*)

Lemma doubling_example_valid_transition :
  input_valid_transition doubling_vlsm multiply_label
   (2, Some 2) (0, Some 4).
Proof.
  apply (finite_valid_trace_from_to_last_transition doubling_vlsm
    doubling_trace1_first_state doubling_trace1_last_state
    doubling_trace1_init doubling_trace1 doubling_trace1_last_item); [| done].
  by apply doubling_valid_trace1.
Qed.

(** **** Example of a constrained transition

  The last transition of a constrained trace is constrained.
*)

Example doubling_example_constrained_transition :
  input_constrained_transition doubling_vlsm multiply_label
   (3, Some 3) (0, Some 6).
Proof.
  apply (finite_valid_trace_from_to_last_transition
    (pre_loaded_with_all_messages_vlsm doubling_vlsm)
    doubling_trace2_init_first_state doubling_trace2_last_state doubling_trace2_init
    doubling_trace2 doubling_trace2_last_item); [| done].
  by apply doubling_constrained_trace2.
Qed.

(** *** Doubling VLSM properties *)

(** **** Inclusion into preloaded with all messages *)

Lemma doubling_valid_is_constrained :
  VLSM_incl doubling_vlsm (pre_loaded_with_all_messages_vlsm doubling_vlsm).
Proof.
  by apply vlsm_incl_pre_loaded_with_all_messages_vlsm.
Qed.

(** *** Constrained messages are positive even integers *)

Lemma doubling_constrained_messages_left :
  forall (m : multiplying_message), constrained_message_prop doubling_vlsm m ->
   Z.Even m /\ m >= 4.
Proof.
  intros m ([s []] & [] & s' & (_ & _ & []) & Ht).
  inversion Ht; subst.
  by split; [eexists | lia].
Qed.

Lemma doubling_constrained_messages_right :
  forall (m : multiplying_message), Z.Even m -> m >= 4 ->
   constrained_message_prop doubling_vlsm m.
Proof.
  intros m [n ->] Hmgt0.
  exists (n, Some n), multiply_label, 0.
  repeat split; [| | by lia.. | by cbn; do 2 f_equal; lia].
  - apply initial_state_is_valid; cbn; red; lia.
  - by apply any_message_is_valid_in_preloaded.
Qed.

Lemma doubling_constrained_messages :
  forall (m : multiplying_message),
   constrained_message_prop doubling_vlsm m <-> (Z.Even m /\ m >= 4).
Proof.
  split.
  - by apply doubling_constrained_messages_left.
  - by intros [? ?]; apply doubling_constrained_messages_right.
Qed.

(** *** Constrained states property *)

Lemma doubling_constrained_states_right :
 forall (st : multiplying_state),
  constrained_state_prop doubling_vlsm st ->
   st >= 0.
Proof.
  induction 1 using valid_state_prop_ind.
  - cbn in Hs; red in Hs; lia.
  - destruct l, om, Ht as [(Hs & _ & []) Ht].
    by inversion Ht; subst; cbn in *; lia.
Qed.

Lemma doubling_constrained_states_left :
  forall (st : multiplying_state), st >= 0 ->
    constrained_state_prop doubling_vlsm st.
Proof.
  intros st Hst.
  apply input_valid_transition_destination
    with (l := multiply_label) (s := st + 2) (om := Some 2) (om' := Some 4).
  repeat split; [| | by lia.. | by cbn; do 2 f_equal; lia].
  - apply initial_state_is_valid; cbn; red; lia.
  - by apply any_message_is_valid_in_preloaded.
Qed.

Lemma doubling_constrained_states :
  forall (st : multiplying_state),
    constrained_state_prop doubling_vlsm st <-> st >= 0.
Proof.
  split.
  - by apply doubling_constrained_states_right.
  - by apply doubling_constrained_states_left.
Qed.

(** *** Powers of 2 greater than or equal to 2 are valid messages *)

Lemma doubling_valid_messages_powers_of_2_right :
  forall (m : multiplying_message),
    valid_message_prop doubling_vlsm m ->
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

Lemma doubling_valid_messages_powers_of_2_left :
  forall (p : Z),
    p >= 1 -> valid_message_prop doubling_vlsm (2 ^ p).
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
  exists (2 ^ (x + 1), Some (2 ^ (x + 1))), multiply_label, 0.
  repeat split.
  - by apply initial_state_is_valid; cbn; red; lia.
  - by apply Hindh.
  - replace (x + 1) with (Z.succ x) by lia.
    by rewrite Z.pow_succ_r; lia.
  - by lia.
  - by cbn; rewrite <- Z.pow_succ_r, Z.add_succ_l; [do 2 f_equal; lia | lia].
Qed.

Lemma doubling_valid_messages_powers_of_2 : forall (m : multiplying_message),
  valid_message_prop doubling_vlsm m <->
    exists p : Z, p >= 1 /\ m = 2 ^ p.
Proof.
  split.
  - by intros; apply doubling_valid_messages_powers_of_2_right.
  - by intros (p & Hpgt0 & [= ->]); apply doubling_valid_messages_powers_of_2_left.
Qed.

(**
  The constrained transition from [doubling_example_constrained_transition]
  is not also valid.
*)
Example doubling_example_constrained_transition_not_valid :
  ~ input_valid_transition doubling_vlsm multiply_label
    (3, Some 3) (0, Some 6).
Proof.
  intros [(_ & Hm & _) _].
  apply doubling_valid_messages_powers_of_2 in Hm as (p & Hp & Heq).
  rewrite <- (Z.succ_pred p) in Heq.
  by rewrite Z.pow_succ_r in Heq; lia.
Qed.

(** **** Valid states hold non-negative integers *)

Lemma doubling_valid_states_right (s : multiplying_state) :
  valid_state_prop doubling_vlsm s -> s >= 0.
Proof.
  induction 1 using valid_state_prop_ind;
    [by cbn in Hs; red in Hs; lia |].
  destruct om, l, Ht as [(Hs & Hm & Hv) Ht]; [| done].
  inversion Ht; subst.
  by destruct Hv; lia.
Qed.

Lemma doubling_valid_states_left (s : multiplying_state) :
  s >= 0 -> valid_state_prop doubling_vlsm s.
Proof.
  intro.
  destruct (decide (s = 0)) as [-> |];
    [| by apply initial_state_is_valid; cbn; red; lia].
  apply input_valid_transition_destination
      with (l := multiply_label) (s := 2) (om := Some 2) (om' := Some 4).
  repeat split; cbn; [| | by lia..].
  - by apply initial_state_is_valid; cbn; red; lia.
  - by apply initial_message_is_valid.
Qed.

Lemma doubling_valid_states :
  forall (s : multiplying_state),
  valid_state_prop doubling_vlsm s <-> s >= 0.
Proof.
  split.
  - by apply doubling_valid_states_right.
  - by apply doubling_valid_states_left.
Qed.

(** ** Definition of the tripling VLSM

  Similarly to the doubling VLSM, the tripling VLSM is a multiplying VLSM,
  differing only by the fact that its initial message is 3 and that it
  outputs the triple of the received input.

  It can be shown that its constrained messages are multiples of three and that
  its valid messages are powers of three, but the proofs will be similar to
  those for the doubling VLSM so we will omit them. The development in module
  [PrimesComposition] will make the results for the doubling and tripling VLSM be
  particular instances of more general results.
*)

Definition tripling_transition
  (l : multiplying_label) (st : multiplying_state) (om : option multiplying_message)
  : multiplying_state * option multiplying_message :=
  match om with
  | Some j  => (st - j, Some (3 * j))
  | None    => (st, None)
  end.

Definition tripling_machine : VLSMMachine multiplying_type :=
{|
  initial_state_prop := multiplying_initial_state_prop;
  initial_message_prop := fun (ms : multiplying_message) => ms = 3;
  s0 := multiplying_initial_state_type_inhabited;
  transition := fun l '(st, om) => tripling_transition l st om;
  valid := fun l '(st, om) => multiplying_valid l st om;
|}.

Definition tripling_vlsm : VLSM multiplying_message := mk_vlsm tripling_machine.

(** ** Composition of doubling and tripling VLSMs *)

Section sec_23_composition.

(**
  Since our notion of [composite_vlsm] is based on an indexed set of components,
  we need to define a base index type
*)

Inductive index23 := two | three.

#[local] Instance eq_dec_index23 : EqDecision index23.
Proof. by intros x y; unfold Decision; decide equality. Qed.

Definition components_23 (i : index23) : VLSM multiplying_message :=
  match i with
  | two => doubling_vlsm
  | three => tripling_vlsm
  end.

(** We define a helper function to make composite state easier to write. *)
Definition state_23 (n m : Z) : composite_state components_23 :=
  fun (i : index23) => match i with two => n | three => m end.

Definition state00 := state_23 0 0.

Definition state01 := state_23 0 1.

Definition state10 := state_23 1 0.

Definition state11 := state_23 1 1.

Definition state12 := state_23 1 2.

Definition state21 := state_23 2 1.

Definition state22 := state_23 2 2.

Definition state02 := state_23 0 2.

Definition zproj (s : composite_state components_23) (i : index23) : Z :=
  match i with
  | two => s two
  | three => s three
  end.

Definition free_composition_23 : VLSM multiplying_message :=
  free_composite_vlsm components_23.

Lemma composition_23_2_initial :
  composite_initial_message_prop components_23 2.
Proof.
  by exists two; unshelve eexists (exist _ 2 _); cbn; lia.
Qed.

Lemma composition_23_3_initial :
  composite_initial_message_prop components_23 3.
Proof.
  by exists three; unshelve eexists (exist _ 3 _); cbn; lia.
Qed.

Lemma free_composition_23_valid_messages_powers_of_23_right :
  forall (m : multiplying_message),
    valid_message_prop free_composition_23 m ->
      exists p2 p3 : Z, p2 >= 0 /\ p3 >= 0 /\ p2 + p3 >= 1 /\
        m = 2 ^ p2 * 3 ^ p3.
Proof.
  intros m [s Hvsm].
  assert (Hom : is_Some (Some m)) by (eexists; done).
  replace m with (is_Some_proj Hom) by done.
  revert Hvsm Hom; generalize (Some m) as om; intros.
  clear m; induction Hvsm using valid_state_message_prop_ind.
  - destruct Hom as [m ->]; cbn in *; subst.
    destruct Hom0 as ([] & [] & <-); cbn in *.
    + by exists 1, 0; split; lia.
    + by exists 0, 1; split; lia.
  - destruct l as [[] []];
      (destruct om as [m |]; [| done]);
      (unshelve edestruct IHHvsm2 as (p2 & p3 & Hgt1 & Heq); [done |]);
      cbn in *; inversion Ht; subst; cbn in *.
    + exists (Z.succ p2), p3.
      split; [by lia |].
      by rewrite Z.pow_succ_r; lia.
    + exists p2, (Z.succ p3).
      split; [by lia |].
      by rewrite Z.pow_succ_r; lia.
Qed.

Lemma free_composition_23_valid_messages_powers_of_23_left :
  forall (p2 p3 : Z), p2 >= 0 -> p3 >= 0 -> 1 <= p2 + p3 ->
    valid_message_prop free_composition_23 (2 ^ p2 * 3 ^ p3).
Proof.
  intros p2 p3 Hp2 Hp3 Hp.
  remember (p2 + p3) as p.
  revert p2 p3 Hp2 Hp3 Heqp.
  pose (P (p : Z) := forall (p2 p3 : Z), p2 >= 0 -> p3 >= 0 -> p = p2 + p3 ->
    valid_message_prop free_composition_23 (2 ^ p2 * 3 ^ p3)).
  cut (P p); [done |].
  revert p Hp; apply Zlt_lower_bound_ind; subst P; cbn.
  intros p Hind Hp p2 p3 Hp2 Hp3 ->.
  destruct (decide (p2 = 0)) as [-> |], (decide (p3 = 0)) as [-> |];
    [by lia |..].
  - destruct (decide (p3 = 1)) as [-> |];
      [by apply initial_message_is_valid, composition_23_3_initial |].
    apply emitted_messages_are_valid.
    exists (state_23 1 (3 ^ (p3 - 1)), Some (3 ^ (p3 - 1))),
      (existT three multiply_label), state10.
    repeat split.
    + by apply initial_state_is_valid; intros []; cbn; red; lia.
    + replace (3 ^ (p3 - 1)) with (2 ^ 0 * 3 ^ (p3 - 1)) by lia.
      by eapply Hind; cycle 3; [done | lia..].
    + replace (p3 - 1) with (Z.succ (p3 - 2)) by lia.
      by rewrite Z.pow_succ_r; lia.
    + by cbn; lia.
    + cbn; f_equal.
      * by extensionality i; destruct i; state_update_simpl; cbn; lia.
      * replace p3 with (Z.succ (p3 - 1)) at 2 by lia.
        by f_equal; rewrite Z.pow_succ_r; lia.
  - destruct (decide (p2 = 1)) as [-> |];
      [by apply initial_message_is_valid, composition_23_2_initial |].
    apply emitted_messages_are_valid.
    exists (state_23 (2 ^ (p2 - 1)) 1, Some (2 ^ (p2 - 1))),
      (existT two multiply_label), state01.
    repeat split.
    + by apply initial_state_is_valid; intros []; cbn; red; lia.
    + replace (2 ^ (p2 - 1)) with (2 ^ (p2 - 1) * 3 ^ 0)
        by lia.
      by eapply Hind; cycle 3; [done | lia..].
    + replace (p2 - 1) with (Z.succ (p2 - 2)) by lia.
      by rewrite Z.pow_succ_r; lia.
    + by cbn; lia.
    + cbn; f_equal.
      * by extensionality i; destruct i; state_update_simpl; cbn; lia.
      * replace p2 with (Z.succ (p2 - 1)) at 2 by lia.
        by f_equal; rewrite Z.pow_succ_r; lia.
  - apply emitted_messages_are_valid.
    exists
      (state_23 (2 ^ (p2 - 1) * 3 ^ p3) 1, Some (2 ^ (p2 - 1) * 3 ^ p3)),
      (existT two multiply_label), state01.
    repeat split.
    + by apply initial_state_is_valid; intros []; cbn; red; lia.
    + by eapply Hind; cycle 3; [done | lia..].
    + replace p3 with (Z.succ (p3 - 1)) by lia.
      by rewrite Z.pow_succ_r; lia.
    + by cbn; lia.
    + cbn; f_equal.
      * by extensionality i; destruct i; state_update_simpl; cbn; lia.
      * replace p2 with (Z.succ (p2 - 1)) at 2 by lia.
        by f_equal; rewrite Z.pow_succ_r; lia.
Qed.

(**
  The valid messages of the [free_composition_23] VLSM consist of all integers
  larger than 1 which can be decomposed as a product of powers of 2 and 3.
*)
Theorem free_composition_23_valid_messages_powers_of_23 :
  forall (m : multiplying_message),
    valid_message_prop free_composition_23 m <->
      exists p2 p3 : Z, p2 >= 0 /\ p3 >= 0 /\ p2 + p3 >= 1 /\
        m = 2 ^ p2 * 3 ^ p3.
Proof.
  split.
  - by apply free_composition_23_valid_messages_powers_of_23_right.
  - intros (? & ? & ? & ? & ? & ->).
    by eapply free_composition_23_valid_messages_powers_of_23_left; lia.
Qed.

Section sec_state_update_23_def.

Context
  (s : composite_state components_23)
  (i : index23)
  (z : Z)
  .

Definition state_update_23 (j : index23) : state (components_23 j) :=
  if (decide (i = j)) then
    match j with
    | two => z
    | three  => z
    end
  else s j.

Lemma state_update_23_eq :
  zproj state_update_23 i = z.
Proof.
  by unfold state_update_23; destruct i; cbn; rewrite decide_True.
Qed.

Lemma state_update_23_neq :
  forall (j : index23), j <> i -> state_update_23 j = s j.
Proof.
  by intros; unfold state_update_23; rewrite decide_False.
Qed.

End sec_state_update_23_def.

Lemma state_update_23_twice :
  forall (s : composite_state components_23) (i : index23) (z z' : Z),
    state_update_23 (state_update_23 s i z) i z' = state_update_23 s i z'.
Proof.
  by intros; extensionality j; unfold state_update_23; case_decide; subst.
Qed.

Lemma state_update_23_two (s : composite_state components_23) (z : Z) :
  state_update_23 s two z = state_update components_23 s two z.
Proof.
  extensionality i; destruct i; unfold state_update_23; state_update_simpl.
  - by rewrite decide_True.
  - by rewrite decide_False.
Qed.

Lemma state_update_23_three (s : composite_state components_23) (z : Z) :
  state_update_23 s three z = state_update components_23 s three z.
Proof.
  extensionality i; destruct i; unfold state_update_23; state_update_simpl.
  - by rewrite decide_False.
  - by rewrite decide_True.
Qed.

Definition label_23 (i : index23) : composite_label components_23.
Proof.
  exists i.
  by destruct i; exact ().
Defined.

Definition multiplier_23 (i : index23) : Z :=
  match i with
  | two => 2
  | three => 3
  end.

Lemma free_composition_23_reachable_0 :
  forall (s : composite_state components_23),
    valid_state_prop free_composition_23 s ->
  forall (i : index23), 2 <= zproj s i ->
    in_futures free_composition_23 s (state_update_23 s i 0).
Proof.
  intros s Hs i Hi.
  remember (zproj s i) as si; revert s Hs Heqsi.
  pose (P (si : Z) :=
    forall (s : composite_state components_23),
      valid_state_prop free_composition_23 s ->
      si = zproj s i ->
    in_futures free_composition_23 s (state_update_23 s i 0)).
  cut (P si); [done |].
  revert si Hi; apply Zlt_lower_bound_ind; subst P; cbn.
  intros si Hind Hlt s Hs Heqsi.
  destruct (decide (4 <= si)); [| destruct (decide (si = 3))].
  - pose (s' := state_update_23 s i (si - 2)).
    cut (input_valid_transition free_composition_23 (label_23 i)
      (s, Some 2) (s', Some (2 * multiplier_23 i))).
    {
      transitivity s'; [by eapply input_valid_transition_in_futures |].
      replace (state_update_23 s i 0) with (state_update_23 s' i 0)
        by apply state_update_23_twice.
      apply (Hind (si - 2)); [by lia |..].
      - by eapply input_valid_transition_destination.
      - by symmetry; apply state_update_23_eq.
    }
    repeat split; [done |..].
    + by apply initial_message_is_valid, composition_23_2_initial.
    + by destruct i; cbn in Heqsi |- *; lia.
    + destruct i; cbn; f_equal; subst si s'; cbn; symmetry.
      * by apply state_update_23_two.
      * by apply state_update_23_three.
  - apply input_valid_transition_in_futures
      with (l := label_23 i) (im := Some 3) (om := Some (3 * multiplier_23 i)).
    repeat split; [done |..].
    + by apply initial_message_is_valid, composition_23_3_initial.
    + by destruct i; cbn in Heqsi |- *; lia.
    + destruct i; cbn; f_equal; subst si; cbn in *; symmetry.
      * by rewrite state_update_23_two; f_equal; lia.
      * by rewrite state_update_23_three; f_equal; lia.
  - apply input_valid_transition_in_futures
      with (l := label_23 i) (im := Some 2) (om := Some (2 * multiplier_23 i)).
    repeat split; [done |..].
    + by apply initial_message_is_valid, composition_23_2_initial.
    + by destruct i; cbn in Heqsi |- *; lia.
    + destruct i; cbn; f_equal; subst si; cbn in *; symmetry.
      * by rewrite state_update_23_two; f_equal; lia.
      * by rewrite state_update_23_three; f_equal; lia.
Qed.

(**
  From any composite state whose components are larger than 1
  there is a valid trace reaching [state00].
*)
Theorem free_composite_23_reachable_00 :
  forall (s2 s3 : Z),
    2 <= s2 -> 2 <= s3 ->
    in_futures free_composition_23 (state_23 s2 s3) state00.
Proof.
  intros.
  cut (in_futures free_composition_23 (state_23 s2 s3) (state_23 0 s3)).
  {
    etransitivity; [done |].
    replace state00 with (state_update_23 (state_23 0 s3) three 0).
    - apply free_composition_23_reachable_0; [| by cbn; lia].
      by eapply in_futures_valid_snd.
    - extensionality i; destruct i; cbn.
      + by rewrite state_update_23_neq.
      + by rewrite state_update_23_three; state_update_simpl.
  }
  replace (state_23 0 s3) with (state_update_23 (state_23 s2 s3) two 0).
  - apply free_composition_23_reachable_0; [| by cbn; lia].
    by apply initial_state_is_valid; intros []; cbn; red; lia.
  - extensionality i; destruct i; cbn.
    + by rewrite state_update_23_two; state_update_simpl.
    + by rewrite state_update_23_neq.
Qed.

Definition composite_state_23_sum (s : composite_state components_23) : Z :=
  s two + s three.

Definition parity_constraint_23
  (l : composite_label components_23)
  (sm : composite_state components_23 * option multiplying_message) : Prop :=
    let sm' := composite_transition components_23 l sm in
      Z.Even (composite_state_23_sum sm.1 + composite_state_23_sum sm'.1).

Definition parity_composition_23 : VLSM multiplying_message :=
  composite_vlsm components_23 parity_constraint_23.

Lemma parity_constraint_23_even
  (l : composite_label components_23) (s : composite_state components_23)
  (m : multiplying_message) :
  parity_constraint_23 l (s, Some m) <-> Z.Even m.
Proof.
  unfold parity_constraint_23, composite_state_23_sum.
  by split; intros [n Hn]; destruct l as [[] li]; cbn in *; state_update_simpl;
    exists (s two + s three - n); lia.
Qed.

Lemma parity_composition_23_valid_messages_powers_of_23_right :
  forall (m : multiplying_message),
    valid_message_prop parity_composition_23 m ->
      m = 3 \/
      exists p2 p3 : Z, p2 >= 1 /\ p3 >= 0 /\
        m = 2 ^ p2 * 3 ^ p3.
Proof.
  intros m [s Hvsm].
  assert (Hom : is_Some (Some m)) by (eexists; done).
  replace m with (is_Some_proj Hom) by done.
  revert Hvsm Hom; generalize (Some m) as om; intros.
  clear m; induction Hvsm using valid_state_message_prop_ind.
  - destruct Hom as [m ->]; cbn in *; subst.
    destruct Hom0 as ([] & [] & <-); cbn in *; [| by left].
    by right; exists 1, 0; split; lia.
  - right; destruct Hv as [Hv Hc]; unfold parity_constraint_23 in Hc.
    assert (H_om : is_Some om) by (destruct l as [[] []], om; done).
    destruct om as [m |]; [| by apply is_Some_None in H_om].
    specialize (IHHvsm2 H_om); cbn in *.
    destruct l as [[] []], IHHvsm2 as [| (p2 & p3 & Hgt1 & Heq)];
      cbn in *; inversion Ht; subst; cbn in *.
    + by exists 1, 1; lia.
    + exists (Z.succ p2), p3; split; [lia |].
      by rewrite Z.pow_succ_r; lia.
    + exfalso; clear -Hc.
      destruct Hc as [n Hn]; unfold composite_state_23_sum in Hn.
      by state_update_simpl; lia.
    + exists p2, (Z.succ p3).
      split; [by lia |].
      by rewrite Z.pow_succ_r; lia.
Qed.

Lemma parity_composition_23_valid_messages_powers_of_23_left :
  forall (p2 p3 : Z), 1 <= p2 -> 0 <= p3 ->
    valid_message_prop parity_composition_23 (2 ^ p2 * 3 ^ p3).
Proof.
  intros p2 p3 Hp2; revert p3.
  pose (P (p2 : Z) := forall (p3 : Z), 0 <= p3 ->
    valid_message_prop parity_composition_23 (2 ^ p2 * 3 ^ p3)).
  cut (P p2); [done |].
  revert p2 Hp2; apply Zlt_lower_bound_ind; subst P; cbn.
  intros p2 Hind Hp2.
  destruct (decide (p2 = 1)) as [-> |].
  - clear Hind; apply natlike_ind;
      [by apply initial_message_is_valid, composition_23_2_initial |].
    intros p3 Hp3 Hind.
    apply emitted_messages_are_valid.
    exists (state_23 1 ((2 * 3 ^ p3)), Some (2 ^ 1 * 3 ^ p3)),
      (existT three multiply_label), state10.
    repeat split.
    + by apply initial_state_is_valid; intros []; cbn; red; lia.
    + done.
    + by lia.
    + by cbn; lia.
    + by apply parity_constraint_23_even; exists (3 ^ p3); lia.
    + cbn; f_equal.
      * by extensionality i; destruct i; state_update_simpl; cbn; lia.
      * by f_equal; rewrite Z.pow_succ_r; lia.
  - intros p3 Hp3.
    apply emitted_messages_are_valid.
    exists (state_23 (2 ^ (p2 - 1) * 3 ^ p3) 1, Some (2 ^ (p2 - 1) * 3 ^ p3)),
      (existT two multiply_label), state01.
    repeat split.
    + by apply initial_state_is_valid; intros []; cbn; red; lia.
    + by apply Hind; lia.
    + replace (p2 - 1) with (Z.succ (p2 - 2)) by lia.
      by rewrite Z.pow_succ_r; lia.
    + by cbn; lia.
    + apply parity_constraint_23_even; exists (2 ^ (p2 - 2) * 3 ^ p3).
      replace (p2 - 1) with (Z.succ (p2 - 2)) by lia.
      by rewrite Z.pow_succ_r; lia.
    + cbn; f_equal.
      * by extensionality i; destruct i; state_update_simpl; cbn; lia.
      * replace p2 with (Z.succ (p2 - 1)) at 2 by lia.
        by f_equal; rewrite !Z.pow_succ_r; lia.
Qed.

(**
  The valid messages of the [parity_composition_23] VLSM consist of the initial
  message 3 together with all even integers larger than 1 which can be
  decomposed as a product of powers of 2 and 3.
*)
Theorem parity_composition_23_valid_messages_powers_of_23 :
  forall (m : multiplying_message),
    valid_message_prop parity_composition_23 m <->
      m = 3 \/
      exists p2 p3 : Z, p2 >= 1 /\ p3 >= 0 /\
        m = 2 ^ p2 * 3 ^ p3.
Proof.
  split.
  - by apply parity_composition_23_valid_messages_powers_of_23_right.
  - intros [-> | (? & ? & ? & ? & ->)].
    + by apply initial_message_is_valid, composition_23_3_initial.
    + by apply parity_composition_23_valid_messages_powers_of_23_left; lia.
Qed.

(**
  Final states are valid states from which no further valid transition
  can be taken.
*)
Definition parity_23_final_state (s : composite_state components_23) : Prop :=
  valid_state_prop parity_composition_23 s /\
  ~ exists
      (l : composite_label components_23)
      (om : option multiplying_message)
      (som' : composite_state components_23 * option multiplying_message),
        input_valid_transition parity_composition_23 l (s, om) som'.

Example valid_state_23_geq1 (n m : Z) (Hn : n >= 1) (Hm : m >= 1) :
  valid_state_prop parity_composition_23 (state_23 n m).
Proof.
  by apply initial_state_is_valid; intros []; cbn; red.
Qed.

Example valid_state11 : valid_state_prop parity_composition_23 state11.
Proof. by apply (valid_state_23_geq1 1 1); lia. Qed.

Example valid_state22 : valid_state_prop parity_composition_23 state22.
Proof. by apply valid_state_23_geq1. Qed.

Example valid_state0n (n : Z) (Hn : n >= 1) :
  valid_state_prop parity_composition_23 (state_23 0 n).
Proof.
  apply input_valid_transition_destination
    with (l := existT two multiply_label) (s := state_23 2 n)
      (om := Some 2) (om' := Some 4).
  repeat split.
  - by apply valid_state_23_geq1.
  - by apply initial_message_is_valid, composition_23_2_initial.
  - by lia.
  - by cbn; lia.
  - by apply parity_constraint_23_even; exists 1; lia.
  - by cbn; f_equal; extensionality i; destruct i; cbn; state_update_simpl; cbn.
Qed.

Example valid_staten0 (n : Z) (Hn : n >= 1) :
  valid_state_prop parity_composition_23 (state_23 n 0).
Proof.
  apply input_valid_transition_destination
    with (l := existT three multiply_label) (s := state_23 n 2)
      (om := Some 2) (om' := Some 6).
  repeat split.
  - by apply valid_state_23_geq1.
  - by apply initial_message_is_valid, composition_23_2_initial.
  - by lia.
  - by cbn; lia.
  - by apply parity_constraint_23_even; exists 1; lia.
  - cbn; f_equal; extensionality i; destruct i; cbn; state_update_simpl; cbn; lia.
Qed.

Example valid_state00 : valid_state_prop parity_composition_23 state00.
Proof.
  apply input_valid_transition_destination
    with (l := existT three multiply_label) (s := state02) (om := Some 2) (om' := Some 6).
  repeat split.
  - by apply valid_state0n.
  - by apply initial_message_is_valid, composition_23_2_initial.
  - by lia.
  - by unfold state02; cbn; lia.
  - by red; cbn; unfold composite_state_23_sum; state_update_simpl; cbn; exists 1.
  - by cbn; f_equal; extensionality i; destruct i; cbn; state_update_simpl; cbn.
Qed.

Example valid_state01 : valid_state_prop parity_composition_23 state01.
Proof. by apply valid_state0n. Qed.

Example valid_state10 : valid_state_prop parity_composition_23 state10.
Proof. by apply valid_staten0. Qed.

Lemma parity_23_final_state_prop23_left (s : composite_state components_23) :
  (s = state00 \/ s = state01 \/ s = state10 \/ s = state11) -> parity_23_final_state s.
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
    by destruct i; (destruct om ; [| done]);
      unfold composite_state_23_sum in Hc; cbn in *; state_update_simpl;
      destruct Hcases as [| [| []]]; subst; cbn in *; lia.
Qed.

Lemma valid_state_23_pos :
  forall (s : composite_state components_23),
    valid_state_prop parity_composition_23 s ->
  forall (i : index23), zproj s i >= 0.
Proof.
  intros s Hs; induction Hs using valid_state_prop_ind;
    [by intros i; specialize (Hs i); destruct i; cbn in *; red in Hs; lia |].
  destruct l as [j lj], Ht as [(_ & _ & Hv & Hc) Ht].
  intro i; specialize (IHHs i).
  by destruct j; (destruct om ; [| done]);
    inversion Ht; subst; clear Ht; cbn in *;
    destruct i; cbn in *; state_update_simpl; lia.
Qed.

Lemma parity_23_final_state_prop23_right (s : composite_state components_23) :
  parity_23_final_state s ->
  s = state00 \/ s = state01 \/ s = state10 \/ s = state11.
Proof.
  intros [Hs Hfinal].
  cut ((s two = 0 /\ s three = 0) \/ (s two = 0 /\ s three = 1) \/
    (s two = 1 /\ s three = 0) \/ (s two = 1 /\ s three = 1)).
  {
    intros  [[] | [[] | [[] | []]]].
    - by left; extensionality x; destruct x.
    - by right; left; extensionality x; destruct x.
    - by right; right; left; extensionality x; destruct x.
    - by right; right; right; extensionality x; destruct x.
  }
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
    + by apply initial_message_is_valid, composition_23_2_initial.
    + by lia.
    + by lia.
    + by apply parity_constraint_23_even; exists 1; lia.
  - exists (existT three ()), (Some 2),
      (state_update components_23 s three (s three - 2), Some 6).
    repeat split; [done | ..].
    + by apply initial_message_is_valid, composition_23_2_initial.
    + by lia.
    + by lia.
    + by apply parity_constraint_23_even; exists 1; lia.
Qed.

(**
  The final states of the [parity_composition_23] VLSM consist of
  [state00], [state01], [state10], and [state11].
*)
Theorem parity_23_final_state_prop23_equiv (s : composite_state components_23) :
  parity_23_final_state s
    <->
  s = state00 \/ s = state01 \/ s = state10 \/ s = state11.
Proof.
  split.
  - by apply parity_23_final_state_prop23_right.
  - by apply parity_23_final_state_prop23_left.
Qed.

Lemma parity_composition_23_reachable_0 :
  forall (s : composite_state components_23),
    valid_state_prop parity_composition_23 s ->
  forall (i : index23) (n : Z), 0 <= n -> zproj s i = 2 * n ->
    in_futures parity_composition_23 s (state_update_23 s i 0).
Proof.
  intros s Hs i n Hn. revert s Hs.
  pose (P (n : Z) := forall (s : composite_state components_23),
    valid_state_prop parity_composition_23 s ->
    zproj s i = 2 * n ->
    in_futures parity_composition_23 s (state_update_23 s i 0)).
  cut (P n); [done |].
  revert n Hn.
  apply natlike_ind; subst P; cbn.
  - intros s Hs Hsi.
    cut (state_update_23 s i 0 = s); [by intros ->; apply in_futures_refl |].
    destruct i.
    + by rewrite state_update_23_two, state_update_id.
    + by rewrite state_update_23_three, state_update_id.
  - intros n Hn IHn s Hs Hsi.
    pose (s' := state_update_23 s i (zproj s i - 2)).
    cut (input_valid_transition parity_composition_23 (label_23 i)
      (s, Some 2) (s', Some (2 * multiplier_23 i))).
    {
      transitivity s'; [by eapply input_valid_transition_in_futures |].
      replace (state_update_23 s i 0) with (state_update_23 s' i 0)
        by apply state_update_23_twice.
      apply IHn.
      - by eapply input_valid_transition_destination.
      - by subst s'; rewrite state_update_23_eq, Hsi; lia.
    }
    repeat split; [done |..].
    + by apply initial_message_is_valid, composition_23_2_initial.
    + by destruct i; cbn in Hsi |- *; lia.
    + by apply parity_constraint_23_even; exists 1; lia.
    + destruct i; cbn; f_equal; symmetry.
      * by apply state_update_23_two.
      * by apply state_update_23_three.
Qed.

(**
  From any composite state whose components are even non-negative integers
  there is a valid trace reaching [state00].
*)
Theorem parity_composite_23_reachable_00 :
  forall (s2 s3 : Z), 0 <= s2 -> 0 <= s3 ->
    in_futures parity_composition_23
      (state_23 (2 * s2) (2 * s3)) state00.
Proof.
  intros.
  cut (in_futures parity_composition_23
    (state_23 (2 * s2) (2 * s3)) (state_23 0 (2 * s3))).
  {
    etransitivity; [done |].
    replace state00 with (state_update_23 (state_23 0 (2 * s3)) three 0).
    - eapply parity_composition_23_reachable_0; cycle 2; [done | | lia].
      by eapply in_futures_valid_snd.
    - extensionality i; destruct i; cbn.
      + by rewrite state_update_23_neq.
      + by rewrite state_update_23_three; state_update_simpl.
  }
  replace (state_23 0 (2 * s3))
    with (state_update_23 (state_23 (2 * s2) (2 * s3)) two 0).
  - eapply parity_composition_23_reachable_0; cycle 2; [done | | lia].
    destruct (decide (s2 = 0)) as [-> |], (decide (s3 = 0)) as [-> |].
    + by apply valid_state00.
    + by apply valid_state0n; lia.
    + by apply valid_staten0; lia.
    + by apply valid_state_23_geq1; lia.
  - extensionality i; destruct i; cbn.
    + by rewrite state_update_23_two; state_update_simpl.
    + by rewrite state_update_23_neq.
Qed.

End sec_23_composition.
