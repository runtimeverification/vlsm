From stdpp Require Import prelude finite.
From VLSM.Core Require Import VLSM PreloadedVLSM VLSMProjections.

#[local] Open Scope Z_scope.

(** * Parity VLSM 

  This module demonstrates some basic notions of the VLSM framework. The idea
  of the parity VLSM is to store a tuple and continually decrement one of the
  tuple's elements while a constraint is checked at each step. The name originates
  from the property of this VLSM to preserve the evenness of the tuple elements 
  difference ([valid_states_same_parity]). The definitions and lemmas tap into
  concepts such as valid and constrained traces, transitions, states, and messages.
  Included is also an equivalence proof for two encodings of a definition of
  valid states and messages for the VLSM.
*)

(** ** General arithmetic results

  These lemmas will be helpful in subsequent proofs.
*)

Lemma Zeven_unary_minus :
  forall n : Z, Z.Even n <-> Z.Even (-n).
Proof. by intros n; split; intros [p Hp]; exists (-p); lia. Qed.

Lemma Zeven_preserve_parity :
  forall (n m : Z), Z.Even n -> Z.Even (m - n) -> Z.Even m.
Proof. by intros m n [m'] [n']; exists (m' + n'); lia. Qed.

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
  - apply Zeven_preserve_parity with m; [done |].
    by replace (m + n - m) with n by lia.
  - apply Zeven_preserve_parity with (m + n); [done |].
    replace (m - (m + n)) with (-n) by lia.
    by rewrite <- Zeven_unary_minus.
Qed.

(** ** Custom automation

  Custom tactic used to simplify proofs on valid transitions.
*)

Ltac app_valid_tran :=
  repeat split; cbn; try done;
  [ try by apply initial_state_is_valid
  | try by apply initial_message_is_valid ];
  match goal with
  | |- option_valid_message_prop _ _ => eapply emitted_messages_are_valid
  | |- valid_state_prop _ _ => eapply input_valid_transition_destination
  end.

(** ** Definition of Parity VLSM

  The Parity VLSM will only have one label, the 'd' (decrease) label.
  For this reason, the [unit] type can be used.
*)

Definition Label : Set := unit.

(** The State will hold two integers. *)

Definition State : Type := Z * Z.

(** The VLSM handles integer messages. *)

Definition Message : Type := Z.

(** A VLSM Type is defined using State and Label. *)

Definition ParityType : VLSMType Message :=
{|
  state := State;
  label := Label;
|}.

(**
  The specifications for the initial state, transition
  and validity constraint are as follows:
*)

Definition ParityComponent_initial_state_prop (st : State) : Prop :=
  st.1 >= 0 /\ st.1 = st.2.

Definition ParityComponent_transition
  (l : Label) (s : State) (om : option Message)
  : State * option Message :=
  match om with
  | Some j  => ((s.1, s.2 - j), Some (2 * j))
  | None    => (s, None)
  end.

Definition ParityComponentValid (l : Label) (st : State) (om : option Message) : Prop :=
  match om with
  | Some msg => msg <= st.2 /\ 1 <= msg
  | None     => False
  end.

(**
  One must also provide a proof that the intial state type
  is inhabited as the set of initial states is non-empty.
*)

Definition ParityComponent_initial_state_type : Type :=
  {st : State | ParityComponent_initial_state_prop st}.

Program Definition ParityComponent_initial_state :
  ParityComponent_initial_state_type := exist _ (0, 0) _.
Next Obligation.
Proof. done. Defined.

#[export] Instance Inhabited_ParityComponent_initial_state_type :
  Inhabited (ParityComponent_initial_state_type) :=
    populate (ParityComponent_initial_state).

(**
  An intermediate representation for VLSM is required.
  It uses the previously defined specifications.
*)

Definition ParityMachine : VLSMMachine ParityType :=
{|
  initial_state_prop := ParityComponent_initial_state_prop;
  initial_message_prop := fun (ms : Message) => ms = 2;
  s0 := Inhabited_ParityComponent_initial_state_type;
  transition := fun l '(st, om) => ParityComponent_transition l st om;
  valid := fun l '(st, om) => ParityComponentValid l st om;
|}.

(** The definition of the Parity VLSM: *)

Definition ParityVLSM : VLSM Message :=
{|
  vtype := ParityType;
  vmachine := ParityMachine;
|}.

Definition ulabel : label ParityVLSM := ().

(** ** General VLSM results *)

(** *** Last transition of valid trace is valid *)

Lemma input_valid_transition_last `(X : VLSM message) :
  forall (s f : state X) (tr tr' : list (transition_item X)) (li : transition_item X),
    finite_valid_trace_from_to X s f tr' -> tr' = tr ++ [li] ->
      input_valid_transition_item X (finite_trace_last s tr) li.
Proof.
  by intros * Htr; eapply input_valid_transition_to, valid_trace_forget_last.
Qed.

(** ** Parity VLSM Examples *)

(** *** Example of an arbitrary transition *)

Lemma example_transition_1 `(X : VLSM message) :
  transition ParityVLSM () ((5, 4), Some 10) = ((5, -6), Some 20).
Proof. done. Qed.

(** *** Example of a valid trace *)

Definition trace1_init : list (transition_item ParityVLSM) :=
  [ Build_transition_item ulabel (Some 4) (8, 4) (Some 8)
  ; Build_transition_item ulabel (Some 2) (8, 2) (Some 4) ].

Definition trace1_last_item : transition_item ParityVLSM :=
  Build_transition_item ulabel (Some 2) (8, 0) (Some 4).

Definition trace1 : list (transition_item ParityVLSM) :=
  trace1_init ++ [trace1_last_item].

Definition trace1_first_state : State := (8, 8).

Definition trace1_last_state : State := destination trace1_last_item.

(** Defined trace is valid: *)

Example parity_valid_message_prop_2 : valid_message_prop ParityVLSM 2.
Proof. by apply initial_message_is_valid. Qed.

Example parity_can_emit_4 :
  can_emit ParityVLSM 4.
Proof.
  unfold can_emit.
  exists ((2, 2), Some 2), (), (2, 0).
  repeat split; [| | done | done].
  - by apply initial_state_is_valid.
  - by apply parity_valid_message_prop_2.
Qed.

Example parity_valid_message_prop_4 :
  valid_message_prop ParityVLSM 4.
Proof. by apply (emitted_messages_are_valid ParityVLSM 4 parity_can_emit_4). Qed.

Proposition parity_valid_transition_1 :
  input_valid_transition ParityVLSM ()
    (trace1_first_state, Some 4) ((8, 4), Some 8).
Proof. app_valid_tran. apply parity_can_emit_4. Qed.

Proposition parity_valid_transition_2 :
  input_valid_transition ParityVLSM ()
    ((8, 4), Some 2) ((8, 2), Some 4).
Proof. by app_valid_tran; apply parity_valid_transition_1. Qed.

Proposition parity_valid_transition_3 : 
  input_valid_transition ParityVLSM ()
    ((8, 2), Some 2) ((8, 0), Some 4).
Proof. by app_valid_tran; apply parity_valid_transition_2. Qed.

Example parity_valid_trace1 :
  finite_valid_trace_init_to ParityVLSM trace1_first_state trace1_last_state trace1.
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
  finite_valid_trace_init_to_alt ParityVLSM trace1_first_state trace1_last_state trace1.
Proof.
  constructor; [| done].
  by repeat apply mvt_extend; [.. | apply mvt_empty]; try done;
    [apply parity_valid_message_prop_4 | apply parity_valid_message_prop_2 ..].
Qed.

(** *** Example of a constrained trace *)

Lemma parity_constrained_trace1 : finite_constrained_trace_init_to
  ParityVLSM trace1_first_state trace1_last_state trace1.
Proof.
  constructor; [| done].
  by repeat apply ct_extend; [..| apply ct_empty].
Qed.

Definition trace2_init : list (transition_item ParityVLSM) :=
  [ Build_transition_item ulabel (Some 2) (5, 3) (Some 4)
  ; Build_transition_item ulabel (Some 2) (5, 1) (Some 4) ].

Definition trace2_last_item : transition_item ParityVLSM :=
  Build_transition_item ulabel (Some 1) (5, 0) (Some 2).

Definition trace2 : list (transition_item ParityVLSM) :=
  trace2_init ++ [trace2_last_item].

Definition trace2_init_first_state : State := (5, 5).

Definition trace2_init_last_state : State := (5, 1).

Definition trace2_last_state : State := destination trace2_last_item.

(** The given trace is valid without the last transition *)

Proposition parity_valid_transition_1' :
  input_valid_transition ParityVLSM ()
    (trace2_init_first_state, Some 2) ((5, 3), Some 4).
Proof. by app_valid_tran. Qed.

Proposition parity_valid_transition_2' :
  input_valid_transition ParityVLSM ()
    ((5, 3), Some 2) ((5, 1), Some 4).
Proof. by app_valid_tran; apply parity_valid_transition_1'. Qed.

Example parity_valid_trace2_init : finite_valid_trace_init_to ParityVLSM
  trace2_init_first_state trace2_init_last_state trace2_init.
Proof.
  constructor; [| done].
  repeat apply finite_valid_trace_from_to_extend.
  - by eapply finite_valid_trace_from_to_empty,
      input_valid_transition_destination, parity_valid_transition_2'.
  - by apply parity_valid_transition_2'.
  - by apply parity_valid_transition_1'.
Qed.

Example parity_valid_trace2_init_alt : finite_valid_trace_init_to_alt ParityVLSM
  trace2_init_first_state trace2_init_last_state trace2_init.
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
  finite_constrained_trace_init_to_alt ParityVLSM
    trace2_init_first_state trace2_init_last_state trace2_init.
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
    trace2_init_first_state trace2_last_state trace2.
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

Lemma example_valid_transition :
  input_valid_transition ParityVLSM () ((8, 2), Some 2) ((8, 0), Some 4).
Proof.
  apply (input_valid_transition_last ParityVLSM
  trace1_first_state trace1_last_state trace1_init trace1 trace1_last_item); [| done].
  by apply parity_valid_trace1.
Qed.

(** *** Example of a constrained transition

  The last transition of a constrained trace is constrained.
*)

Example example_constrained_transition :
  input_valid_transition (pre_loaded_with_all_messages_vlsm ParityVLSM) ()
    ((5, 1), Some 1) ((5, 0), Some 2).
Proof.
  apply (input_valid_transition_last (pre_loaded_with_all_messages_vlsm ParityVLSM)
    trace2_init_first_state trace2_last_state trace2_init trace2 trace2_last_item); [| done].
  by apply parity_constrained_trace2.
Qed.

(** ** Parity VLSM Properties *)

(** *** Inclusion into preloaded with all messages *)

Lemma parity_valid_is_constrained :
  VLSM_incl ParityVLSM (pre_loaded_with_all_messages_vlsm ParityVLSM).
Proof.
  by apply vlsm_incl_pre_loaded_with_all_messages_vlsm.
Qed.

(** *** Constrained messages are even integers *)

Lemma constrained_messages_left_impl :
  forall (m : Message), constrained_message_prop_alt ParityVLSM m -> Z.Even m /\ m > 0.
Proof.
  intros m ([s []] & [] & s' & [(_ & _ & []) Ht]).
  inversion Ht; subst.
  by split; [eexists | lia].
Qed.

Lemma constrained_messages_right_impl :
  forall (m : Message), Z.Even m /\ m > 0 -> constrained_message_prop_alt ParityVLSM m.
Proof.
  intros m [[n ->] Hmgt0].
  pose (s := (n, n)). 
  unfold constrained_message_prop, can_emit; cbn.
  exists (s, Some n), (), (n, 0).
  repeat split.
  - by apply initial_state_is_valid; constructor; cbn; lia.
  - by apply any_message_is_valid_in_preloaded.
  - by cbn; lia.
  - by lia.
  - by cbn; do 2 f_equal; lia.
Qed.

Lemma constrained_messages : 
  forall (m : Message), constrained_message_prop_alt ParityVLSM m <-> Z.Even m /\ m > 0.
Proof.
  split.
  - by apply constrained_messages_left_impl.
  - by apply constrained_messages_right_impl.
Qed.

(** *** Constrained states property **)

Lemma constrained_states_right_impl : forall (st : State),
  constrained_state_prop_alt ParityVLSM st ->
    st.1 >= st.2 /\ st.2 >= 0.
Proof.
  induction 1 using valid_state_prop_ind.
  - by destruct Hs; lia.
  - destruct l, om, Ht as [(Hs & _ & []) Ht].
    by inversion Ht; subst; cbn in *; lia.
Qed.

Lemma constrained_states_left_impl : forall (st : State), st.1 >= st.2 /\ st.2 >= 0 ->
  constrained_state_prop_alt ParityVLSM st.
Proof.
  intros st [Hn Hi].
  (* make two cases *)
  destruct (decide (st.1 = st.2)).
  - by apply initial_state_is_valid; split; lia.
  - pose (s := (st.1, st.1)). 
    unfold constrained_state_prop.
    apply input_valid_transition_destination with (l := ()) (s := s)
      (om := Some (st.1 - st.2)) (om' := Some (2 * (st.1 - st.2))).
    repeat split.
    + by apply initial_state_is_valid; constructor; cbn; lia.
    + by apply any_message_is_valid_in_preloaded.
    + by unfold s; cbn; lia.
    + by lia.
    + by destruct st; cbn; do 2 f_equal; lia.
Qed.

Lemma constrained_states :
  forall (st : State),
    constrained_state_prop_alt ParityVLSM st <-> st.1 >= st.2 /\ st.2 >= 0.
Proof.
  split.
  - by apply constrained_states_right_impl.
  - by apply constrained_states_left_impl.
Qed.

(** *** Powers of 2 are valid messages *)

Lemma valid_messages_powers_of_2_right_impl :
  forall (m : option Message),
    option_valid_message_prop ParityVLSM m -> m <> None ->
      exists p : Z, p >= 1 /\ m = Some (2 ^ p).
Proof.
  intros m [s Hvsm] Hmnn.
  induction Hvsm using valid_state_message_prop_ind.
  - unfold option_initial_message_prop, from_option in Hom.
    destruct om; [| done].
    unfold initial_message_prop in Hom; cbn in Hom.
    by exists 1; subst.
  - destruct om, IHHvsm2; inversion Ht; cycle 1; [| done ..].
    inversion H as [Hxgt1 Hs2x].
    apply Some_inj in Hs2x; subst.
    exists (x + 1).
    rewrite <- Z.pow_succ_r; [f_equal |].
    destruct Hv.
    + by split; [lia | done].
    + by lia.
Qed.

Lemma valid_messages_powers_of_2_left_impl :
  forall (p : Z),
    p >= 1 -> option_valid_message_prop ParityVLSM (Some (2 ^ p)).
Proof.
  intros p Hp.
  assert (0 <= p - 1) by lia.
  replace p with (p - 1 + 1) by lia.
  remember (p - 1) as x.
  clear p Hp Heqx.
  revert x H.
  apply natlike_ind.
  - by apply initial_message_is_valid.
  - intros x Hxgt0 Hindh.
    pose (msgin := 2 ^ (x + 1)).
    pose (x' := (msgin, msgin)).
    apply emitted_messages_are_valid.
    exists (x', Some (2 ^ (x + 1))), (), (x'.1, msgin - msgin); subst x' msgin; cbn.
    repeat split; [| by apply Hindh | by cbn | by lia |].
    + by apply initial_state_is_valid; constructor; cbn; lia.
    + by unfold transition; cbn; rewrite <- Z.pow_succ_r, Z.add_succ_l; [| lia].
Qed.

Lemma valid_messages_powers_of_2 : forall (om : option Message),
  om <> None -> ((option_valid_message_prop ParityVLSM om) <->
    (exists p : Z, p >= 1 /\ om = Some (2 ^ p))).
Proof.
  split.
  - by intros; apply valid_messages_powers_of_2_right_impl.
  - by intros (p & Hpgt0 & [= ->]); apply valid_messages_powers_of_2_left_impl.
Qed.

(** *** Valid states hold non-negative integers of the same parity *)

Lemma valid_states_right_impl :
  forall (s : State),
  valid_state_prop ParityVLSM s -> (Z.Even s.2 <-> Z.Even s.1) /\ s.1 >= s.2 /\ s.2 >= 0.
Proof.
  induction 1 using valid_state_prop_ind.
  - destruct Hs as [Hs <-].
    split; [done | ].
    by split; lia.
  - destruct om, l, Ht as [(Hs & Hm & Hv) Ht]; [| done].
    inversion Ht.
    destruct Hv as [Hv1 Hv2], IHvalid_state_prop as (Heven & Hgt1 & Hgt2); cbn.
    apply valid_messages_powers_of_2_right_impl in Hm as [p (Hpgt0 & [= ->])]; [| auto] .
    split_and!; [| by lia ..].
    transitivity (Z.Even s.2); [| done].
    split.
    + apply Zeven_preserve_parity.
      destruct p; [lia | | lia].
      exists (2 ^ (Z.pos p - 1)); cbn; rewrite <- Z.pow_succ_r; [| lia].
      by f_equal; lia.
    + intro Heis.
      apply Zeven_preserve_parity with (n := s.2); [done |].
      exists (- 2 ^ (p - 1)).
      by rewrite Z.mul_opp_r, <- Z.pow_succ_r, Z.sub_1_r, Z.succ_pred; lia.
Qed.

Lemma valid_states_left_impl (s : State) :
  (Z.Even s.2 <-> Z.Even s.1) -> s.1 >= s.2 -> s.2 >= 0 ->
    valid_state_prop ParityVLSM s.
Proof.
  intros Hsameparity Hgt1 Hgt2.
  apply Zeven_equiv_minus in Hsameparity as [d Hd].
  assert (d >= 0) by lia.
  revert s Hgt2 Hgt1 Hd.
  eapply Zlt_0_ind with (P := fun d => forall s : State, s.2 >= 0 ->
    s.1 >= s.2 -> s.1 - s.2 = 2 * d -> valid_state_prop ParityVLSM s); [| by lia].
  intros x Hind _ s Higt0 Hngti Hevendiff.
  destruct x; [.. | by lia].
  - by apply initial_state_is_valid; constructor; lia.
  - apply input_valid_transition_destination
      with (l := ()) (s := (s.1, s.2 + 2)) (om := Some 2) (om' := Some 4).
    repeat split; cbn; [| | by lia | by lia |].
    + by eapply Hind with (y := Z.pos p - 1); cbn; lia.
    + by apply initial_message_is_valid.
    + by destruct s; cbn; do 2 f_equal; by lia.
Qed.

Theorem valid_states_same_parity :
  forall (s : State),
  valid_state_prop ParityVLSM s <-> ((Z.Even s.2 <-> Z.Even s.1) /\ s.1 >= s.2 /\ s.2 >= 0).
Proof.
  split.
  - by apply valid_states_right_impl.
  - by intros []; apply valid_states_left_impl; [done | lia ..].
Qed.
