From VLSM.Lib Require Import Itauto.
From stdpp Require Import prelude finite.
From Coq Require Import Streams FunctionalExtensionality Eqdep_dec.
From VLSM.Lib Require Import Preamble ListExtras.
From VLSM.Core Require Import VLSM Plans VLSMProjections.
From VLSM.Core Require Import PreloadedVLSM ConstrainedVLSM.

(** * VLSM Composition

  This module provides Coq definitions for composite VLSMs and their projections
  to components.
*)

Section sec_VLSM_composition.

(**
  Let us fix a type for <<message>>s, and an <<index>> type for the VLSM components
  such that equality on <<index>> is decidable and let IM be a family of VLSMs
  indexed by <<index>>. Note that all [VLSM]s share the same type of <<message>>s.
*)

Context
  {message : Type}
  `{EqDecision index}
  (IM : index -> VLSM message)
  .

(** ** Free VLSM composition *)

(*
  A [composite_state] is an indexed family of [state]s, yielding for each
  index <<n>> a [state] of [type] <<IT n>>, the [VLSMType] corresponding to
  machine <<n>>.

  Note that the [composite_state] type is the dependent product type of the
  family of [state] types corresponding to each index.
*)
Definition composite_state : Type :=
  forall n : index, state (IM n).

(**
  A [composite_label] is a pair between an index <<N>> and a [label] of <<IT n>>.

  Note that the [composite_label] type is the dependent sum of the family of
  types <<[label (IT n) | n <- index]>>.
*)
Definition composite_label : Type :=
  {n : index & label (IM n)}.

(*
  Declaring this a "canonical structure" will make type checking
  guess that a VLSMType should be composite_type instead of just
  failing, if it has to compare composite_state with state or
  state of an unsolved VLSMType or VLSM.
*)
Canonical Structure composite_type : VLSMType message :=
{|
  state := composite_state;
  label := composite_label;
|}.

(**
  A [composite_state] has the [initial_state_prop]erty if all of its component
  states have the [initial_state_prop]erty in the corresponding component signature.
*)
Definition composite_initial_state_prop (s : composite_state) : Prop :=
  forall n : index, initial_state_prop (IM n) (s n).

Definition composite_initial_state : Type :=
  {s : composite_state | composite_initial_state_prop s}.

Program Definition composite_s0 : composite_initial_state :=
  exist _ (fun (n : index) => `(vs0 (IM n))) _.
Next Obligation.
Proof. by intros i; destruct (vs0 (IM i)). Defined.

#[export] Instance composite_initial_state_inh : Inhabited composite_initial_state :=
  populate composite_s0.

(**
  A message has the [initial_message_prop]erty in the composite
  iff it has the [initial_message_prop]erty in any of the components.
*)
Definition composite_initial_message_prop (m : message) : Prop :=
  exists (n : index) (mi : initial_message (IM n)), proj1_sig mi = m.

(**
  A very useful operation on [composite_state]s is updating the state corresponding
  to a component.
*)
Definition state_update
  (s : composite_state) (i : index) (si : state (IM i)) (j : index) : state (IM j) :=
  match decide (j = i) with
  | left e => eq_rect_r (fun i => state (IM i)) si e
  | _ => s j
  end.

(**
  The [transition] function for the [composite_vlsm] takes a transition in
  the component selected by the index in the given [composite_label]
  with the contained label, and returns the produced message together with
  the state updated on that component.
*)
Definition composite_transition
  (l : composite_label) (som : composite_state * option message)
  : composite_state * option message :=
  let (s, om) := som in
  let (i, li) := l in
  let (si', om') := transition (IM i) li (s i, om) in
    (state_update s i si',  om').

(**
  Given a [composite_label] <<(i, li)>> and a [composite_state]-message
  pair <<(s, om)>>, [composite_valid]ity is defined as [valid]ity in
  the <<i>>th component <<IM i>>.
*)
Definition composite_valid
  (l : composite_label) (som : composite_state * option message) : Prop :=
  let (s, om) := som in
  let (i, li) := l in
    valid (IM i) li (s i, om).

Definition free_composite_vlsm_machine : VLSMMachine composite_type :=
{|
  initial_state_prop := composite_initial_state_prop;
  initial_message_prop := composite_initial_message_prop;
  transition := composite_transition;
  valid := composite_valid;
|}.

Definition free_composite_vlsm : VLSM message :=
  mk_vlsm free_composite_vlsm_machine.

(**
  Composite versions for [transition_item], [option_initial_message_prop] and
  things related to plans and plan items.
*)

Definition composite_transition_item : Type := transition_item composite_type.

Definition option_composite_initial_message_prop : option message -> Prop :=
  from_option composite_initial_message_prop True.

Definition composite_plan_item : Type := plan_item composite_type.

Definition composite_plan : Type := list composite_plan_item.

Definition composite_apply_plan := (@_apply_plan _ composite_type composite_transition).

Definition composite_apply_plan_app
  (start : composite_state)
  (a a' : list plan_item)
  : composite_apply_plan start (a ++ a') =
    let (aitems, afinal) := composite_apply_plan start a in
    let (a'items, a'final) := composite_apply_plan afinal a' in
     (aitems ++ a'items, a'final)
  := (@_apply_plan_app _ composite_type composite_transition start a a').

Definition composite_apply_plan_last
  (start : composite_state)
  (a : list plan_item)
  (after_a := composite_apply_plan start a)
  : finite_trace_last start (fst after_a) = snd after_a
  := (@_apply_plan_last _ composite_type composite_transition start a).

Definition composite_trace_to_plan := (@_trace_to_plan _ composite_type).

(** ** Constrained VLSM composition

  A constrained VLSM composition is a free composition which is further
  constrained with an additional validity constraint.
*)

Definition composite_vlsm
  (constraint : composite_label -> composite_state * option message -> Prop) : VLSM message :=
    constrained_vlsm free_composite_vlsm constraint.

(** [free_constraint] is the constraint that is always true. *)
Definition free_constraint : composite_label -> composite_state * option message -> Prop :=
  fun _ _ => True.

(**
  [free_composite_vlsm] is equivalent to a [composite_vlsm] with a free
  constraint.
*)
Lemma free_composite_vlsm_spec :
  VLSM_eq free_composite_vlsm (composite_vlsm free_constraint).
Proof.
  split.
  - apply (VLSM_incl_embedding_iff); cbn.
    by apply basic_VLSM_strong_embedding; red; cbn.
  - apply (VLSM_incl_embedding_iff); cbn.
    apply basic_VLSM_strong_embedding; red; cbn; [| done..].
    by itauto.
Qed.

(**
  [free_composite_vlsm] is equivalent to [composite_vlsm] with free constraint
  also when preloaded with messages.
*)
Lemma preloaded_free_composite_vlsm_spec :
  forall (initial : message -> Prop),
    VLSM_eq
      (pre_loaded_vlsm free_composite_vlsm initial)
      (pre_loaded_vlsm (composite_vlsm free_constraint) initial).
Proof.
  split.
  - apply (VLSM_incl_embedding_iff); cbn.
    by apply basic_VLSM_strong_embedding; red; cbn.
  - apply (VLSM_incl_embedding_iff); cbn.
    apply basic_VLSM_strong_embedding; red; cbn; [| done..].
    by itauto.
Qed.

Lemma preloaded_with_all_messages_free_composite_vlsm_spec :
  VLSM_eq
    (pre_loaded_with_all_messages_vlsm free_composite_vlsm)
    (pre_loaded_with_all_messages_vlsm (composite_vlsm free_constraint)).
Proof.
  split.
  - apply (VLSM_incl_embedding_iff); cbn.
    by apply basic_VLSM_strong_embedding; red; cbn.
  - apply (VLSM_incl_embedding_iff); cbn.
    apply basic_VLSM_strong_embedding; red; cbn; [| done..].
    by itauto.
Qed.

(** ** Lemmas about state_update

  The next few results describe several properties of the [state_update] operation.
*)

Lemma state_update_neq :
  forall (s : composite_state) (i : index) (si : state (IM i)) (j : index) (Hneq : j <> i),
    state_update s i si j = s j.
Proof.
  by intros; unfold state_update; case_decide.
Qed.

Lemma state_update_eq :
  forall (s : composite_state) (i : index) (si : state (IM i)),
    state_update s i si i = si.
Proof.
  unfold state_update.
  intros.
  case_decide; [| done].
  by replace H with (eq_refl i) by (apply K_dec_type; done).
Qed.

Lemma state_update_id :
  forall (s : composite_state) (i : index) (si : state (IM i)) (Heq : s i = si),
    state_update s i si = s.
Proof.
  intros.
  apply functional_extensionality_dep_good.
  intro j.
  destruct (decide (j = i)); subst.
  - by apply state_update_eq.
  - by apply state_update_neq.
Qed.

Lemma state_update_twice :
  forall (s : composite_state) (i : index) (si si' : state (IM i)),
    state_update (state_update s i si) i si' = state_update s i si'.
Proof.
  intros.
  apply functional_extensionality_dep_good.
  intro j.
  destruct (decide (j = i)).
  - by subst; rewrite state_update_eq; symmetry; apply state_update_eq.
  - by rewrite !state_update_neq.
Qed.

Lemma state_update_twice_neq :
  forall (s : composite_state) (i j : index) (si : state (IM i)) (sj : state (IM j)) (Hij : j <> i),
    state_update (state_update s i si) j sj = state_update (state_update s j sj) i si.
Proof.
  intros.
  apply functional_extensionality_dep_good.
  intro k.
  destruct (decide (k = j)); destruct (decide (k = i)); subst
  ; repeat (rewrite state_update_eq ; try (rewrite state_update_neq; try done))
  ; try done.
  by rewrite !state_update_neq.
Qed.

Lemma composite_transition_state_neq
  (l : composite_label)
  (s s' : composite_state)
  (om om' : option message)
  (Ht : composite_transition l (s, om) = (s', om'))
  (i : index)
  (Hi : i <> projT1 l)
  : s' i = s i.
Proof.
  destruct l; cbn in Ht; destruct (transition _ _ _).
  by inversion Ht; apply state_update_neq.
Qed.

Lemma composite_transition_state_eq
  (i : index)
  (li : label (IM i))
  (s s' : composite_state)
  (om om' : option message)
  (Ht : composite_transition (existT i li) (s, om) = (s', om'))
  : s' i = fst (transition (IM i) li (s i, om)).
Proof.
  by cbn in Ht; destruct (transition _ _ _); inversion Ht; apply state_update_eq.
Qed.

(**
  Updating a composite initial state with a component initial state
  yields a composite initial state.
*)
Lemma composite_update_initial_state_with_initial
  (s : composite_state)
  (Hs : composite_initial_state_prop s)
  (i : index)
  (si : state (IM i))
  (Hsi : initial_state_prop (IM i) si)
  : composite_initial_state_prop (state_update s i si).
Proof.
  intro j. destruct (decide (j = i)); subst.
  - by rewrite state_update_eq.
  - by rewrite state_update_neq.
Qed.

(** ** Lifting functions

  This section contains definitions of functions which lift labels, states,
  etc. from a single component to the composition, and lemmas about these
  functions.
*)

(**
  We can always "lift" state <<sj>> from component <<j>> to a composite state by
  updating an given composite state to <<sj>> on component <<j>>.
*)
Definition lift_to_composite_state
  (s : composite_state) (j : index) (sj : state (IM j)) : composite_state :=
    state_update s j sj.

Definition lift_to_composite_label (j : index) (lj : label (IM j)) : composite_label :=
  existT j lj.

Definition lift_to_composite_transition_item
  (s : composite_state) (j : index) : transition_item (IM j) -> composite_transition_item :=
    pre_VLSM_embedding_transition_item_project (IM j) composite_type
      (lift_to_composite_label j) (lift_to_composite_state s j).

(**
  A specialized version of [lift_to_composite_state] using the initial composite
  state as the base for lifting.
*)
Definition lift_to_composite_state' : forall j : index, state (IM j) -> composite_state :=
  lift_to_composite_state (proj1_sig composite_s0).

Definition lift_to_composite_transition_item' :
  forall j : index, transition_item -> composite_transition_item :=
    lift_to_composite_transition_item (proj1_sig composite_s0).

Definition lift_to_composite_plan_item
  (i : index) (a : vplan_item (IM i)) : composite_plan_item.
Proof.
  destruct a.
  split.
  - exact (existT i label_a).
  - exact input_a.
Defined.

Lemma composite_initial_state_prop_lift :
  forall (j : index) (sj : state (IM j)) (Hinitj : initial_state_prop (IM j) sj),
    composite_initial_state_prop (lift_to_composite_state' j sj).
Proof.
  intros j sj Hinitj i.
  unfold lift_to_composite_state'.
  destruct (decide (i = j)); subst.
  - by rewrite state_update_eq.
  - rewrite state_update_neq; cbn; [| done].
    by destruct (vs0 _) as [s Hs].
Qed.

Lemma lift_to_composite_VLSM_embedding j :
  VLSM_embedding (IM j) free_composite_vlsm
    (lift_to_composite_label j) (lift_to_composite_state' j).
Proof.
  apply basic_VLSM_strong_embedding; intro; intros.
  - cbn; unfold lift_to_composite_state'.
    by rewrite state_update_eq.
  - cbn; unfold lift_to_composite_state' at 1.
    rewrite state_update_eq.
    replace (transition _ _ _) with (s', om').
    unfold lift_to_composite_state'.
    by rewrite state_update_twice.
  - by cbn; apply composite_initial_state_prop_lift.
  - by exists j, (exist _ _ H).
Qed.

Definition lift_to_composite_finite_trace
  (j : index) : list (transition_item (IM j)) -> list composite_transition_item :=
    VLSM_embedding_finite_trace_project (lift_to_composite_VLSM_embedding j).

Definition lift_to_composite_finite_trace_last (j : index) :=
  VLSM_embedding_finite_trace_last (lift_to_composite_VLSM_embedding j).

Lemma lift_to_composite_generalized_preloaded_VLSM_embedding
  (P Q : message -> Prop)
  (PimpliesQ : forall m, P m -> Q m)
  (j : index)
  : VLSM_embedding
      (pre_loaded_vlsm (IM j) P) (pre_loaded_vlsm free_composite_vlsm Q)
      (lift_to_composite_label j) (lift_to_composite_state' j).
Proof.
  apply basic_VLSM_embedding_preloaded_with; intro; intros.
  - by apply PimpliesQ.
  - by cbn; unfold lift_to_composite_state'; rewrite state_update_eq.
  - cbn; unfold lift_to_composite_state' at 1.
    rewrite state_update_eq.
    replace (transition (IM j) l _) with (s', om').
    unfold lift_to_composite_state'.
    by rewrite state_update_twice.
  - by cbn; apply composite_initial_state_prop_lift.
  - by exists j, (exist _ _ H).
Qed.

Lemma lift_to_composite_preloaded_VLSM_embedding (j : index) :
  VLSM_embedding
    (pre_loaded_with_all_messages_vlsm (IM j))
    (pre_loaded_with_all_messages_vlsm free_composite_vlsm)
    (lift_to_composite_label j)
    (lift_to_composite_state' j).
Proof.
  apply basic_VLSM_embedding_preloaded.
  - intro; intros.
    cbn; unfold lift_to_composite_state'; cbn.
    by rewrite state_update_eq.
  - intro; intros; cbn.
    cbn; unfold lift_to_composite_state' at 1.
    rewrite state_update_eq.
    replace (transition l _) with (s', om').
    unfold lift_to_composite_state'.
    by rewrite state_update_twice.
  - by  intros s H; cbn; apply composite_initial_state_prop_lift.
Qed.

(**
  If all messages described by a predicate <<P>> are valid for the free
  composition pre-loaded with messages described by a predicate <<Q>>, then
  any message which can be emitted by a component pre-loaded with <<P>> can
  also be emitted by the free composition pre-loaded with <<Q>>.
*)
Lemma valid_preloaded_lifts_can_be_emitted
  (P Q : message -> Prop)
  (HPvalid : forall dm, P dm -> valid_message_prop (pre_loaded_vlsm free_composite_vlsm Q) dm)
  : forall j m, can_emit (pre_loaded_vlsm (IM j) P) m ->
    can_emit (pre_loaded_vlsm free_composite_vlsm Q) m.
Proof.
  intros j m Hm.
  eapply VLSM_incl_can_emit.
  - apply (pre_loaded_vlsm_incl_relaxed _ (fun m => Q m \/ P m)).
    by itauto.
  - eapply VLSM_embedding_can_emit; [| done].
    apply lift_to_composite_generalized_preloaded_VLSM_embedding.
    by itauto.
Qed.

(**
  As a specialization of [valid_preloaded_lifts_can_be_emitted], if all
  messages described by a predicate <<P>> are valid for the free composition,
  then any message which can be emitted by a component pre-loaded with <<P>>
  can also be emitted by the free composition.
*)
Lemma free_valid_preloaded_lifts_can_be_emitted
  (P : message -> Prop)
  (Hdeps : forall dm, P dm -> valid_message_prop free_composite_vlsm dm)
  : forall i m, can_emit (pre_loaded_vlsm (IM i) P) m ->
    can_emit free_composite_vlsm m.
Proof.
  intros.
  eapply VLSM_incl_can_emit.
  - by eapply (vlsm_is_pre_loaded_with_False free_composite_vlsm).
  - eapply valid_preloaded_lifts_can_be_emitted; [| done].
    intros dm Hdm.
    eapply VLSM_incl_valid_message.
    + by apply (vlsm_is_pre_loaded_with_False free_composite_vlsm).
    + by cbv; itauto.
    + by apply Hdeps.
Qed.

Lemma valid_state_preloaded_composite_free_lift
  (j : index)
  (sj : state (IM j))
  (Hp : valid_state_prop (pre_loaded_with_all_messages_vlsm (IM j)) sj)
  : valid_state_prop
      (pre_loaded_with_all_messages_vlsm free_composite_vlsm)
      (lift_to_composite_state' j sj).
Proof.
  by apply (VLSM_embedding_valid_state (lift_to_composite_preloaded_VLSM_embedding j)).
Qed.

Lemma can_emit_composite_free_lift
  (P Q : message -> Prop)
  (PimpliesQ : forall m, P m -> Q m)
  (j : index)
  (m : message)
  (Htrj : can_emit (pre_loaded_vlsm (IM j) P) m)
  : can_emit (pre_loaded_vlsm free_composite_vlsm Q) m.
Proof.
  eapply VLSM_embedding_can_emit; [| done].
  by apply lift_to_composite_generalized_preloaded_VLSM_embedding.
Qed.

(**
  Updating a composite [valid_state] for the free composition with
  a component initial state yields a composite [valid_state].
*)
Lemma pre_composite_free_update_state_with_initial
  (P : message -> Prop)
  (s : composite_state)
  (Hs : valid_state_prop (pre_loaded_vlsm free_composite_vlsm P) s)
  (i : index)
  (si : state (IM i))
  (Hsi : initial_state_prop (IM i) si)
  : valid_state_prop (pre_loaded_vlsm free_composite_vlsm P) (state_update s i si).
Proof.
  induction Hs using valid_state_prop_ind.
  - apply initial_state_is_valid; cbn.
    by apply composite_update_initial_state_with_initial.
  - destruct Ht as [[Hps [Hom Hv]] Ht]; cbn in Ht, Hv.
    destruct l as [j lj].
    destruct (transition _ _ _) as [sj' omj'] eqn: Htj.
    inversion_clear Ht.
    destruct (decide (i = j)).
    + by subst; rewrite state_update_twice.
    + rewrite state_update_twice_neq by done.
      apply input_valid_transition_destination with (existT j lj) (state_update s i si) om omj'.
      by repeat split; [done | done | ..]; cbn; rewrite state_update_neq;
        [.. | rewrite Htj |].
Qed.

Lemma lift_to_composite_valid_preservation :
  forall (i : index) (cs : composite_state),
  forall l s om, valid (IM i) l (s, om) ->
    composite_valid (lift_to_composite_label i l)
      (lift_to_composite_state cs i s, om).
Proof. by intros; cbn; rewrite state_update_eq. Qed.

Lemma lift_to_composite_transition_preservation :
  forall (i : index) (cs : composite_state),
  forall l s om s' om', transition (IM i) l (s, om) = (s', om') ->
    composite_transition (lift_to_composite_label i l)
      (lift_to_composite_state cs i s, om)
        =
      (lift_to_composite_state cs i s', om').
Proof.
  intros; cbn.
  unfold lift_to_composite_state; rewrite state_update_eq.
  by replace (transition _ _ _) with (s', om'); rewrite state_update_twice.
Qed.

Lemma lift_to_composite_initial_message_preservation :
  forall (i : index),
      forall m, initial_message_prop (IM i) m ->
      composite_initial_message_prop m.
Proof. by intros i m Hm; exists i, (exist _ _ Hm). Qed.

Lemma pre_lift_to_free_weak_embedding :
  forall (i : index) (cs : composite_state) (P : message -> Prop),
    valid_state_prop (pre_loaded_vlsm free_composite_vlsm P) cs ->
    VLSM_weak_embedding
      (pre_loaded_vlsm (IM i) P) (pre_loaded_vlsm free_composite_vlsm P)
      (lift_to_composite_label i) (lift_to_composite_state cs i).
Proof.
  intros i cs P Hvsp.
  apply basic_VLSM_weak_embedding.
  - intros l s om (_ & _ & Hv) _ _.
    by cbn; apply lift_to_composite_valid_preservation.
  - by inversion 1; cbn; apply lift_to_composite_transition_preservation.
  - by intros s Hs; apply pre_composite_free_update_state_with_initial.
  - intros _ _ m _ _ [Hm | Hp]; apply initial_message_is_valid; [left | by right].
    by cbn; eapply lift_to_composite_initial_message_preservation.
Qed.

Lemma lift_to_free_weak_embedding :
  forall (i : index) (cs : composite_state),
      valid_state_prop free_composite_vlsm cs ->
      VLSM_weak_embedding (IM i) free_composite_vlsm
        (lift_to_composite_label i) (lift_to_composite_state cs i).
Proof.
  constructor; intros.
  apply (VLSM_eq_finite_valid_trace_from (vlsm_is_pre_loaded_with_False free_composite_vlsm)),
    pre_lift_to_free_weak_embedding.
  - by apply (VLSM_eq_valid_state (vlsm_is_pre_loaded_with_False free_composite_vlsm)).
  - apply (VLSM_eq_finite_valid_trace_from (vlsm_is_pre_loaded_with_False (IM i))).
    by destruct (IM i).
Qed.

Lemma lift_to_preloaded_free_weak_embedding :
  forall (i : index) (cs : composite_state),
    valid_state_prop (pre_loaded_with_all_messages_vlsm free_composite_vlsm) cs ->
    VLSM_weak_embedding
      (pre_loaded_with_all_messages_vlsm (IM i))
      (pre_loaded_with_all_messages_vlsm free_composite_vlsm)
      (lift_to_composite_label i)
      (lift_to_composite_state cs i).
Proof.
  constructor; intros.
  apply pre_lift_to_free_weak_embedding; [done |].
  by destruct (IM i).
Qed.

End sec_VLSM_composition.

(** ** A tactic for working with the state_update function

  Hint database and tactic for dealing with updates and lifting via [state_update].
*)

Create HintDb state_update.

#[export] Hint Rewrite @state_update_neq using done : state_update.
#[export] Hint Rewrite @state_update_id using done : state_update.
#[export] Hint Rewrite @state_update_eq : state_update.

#[export] Hint Unfold lift_to_composite_state : state_update.
#[export] Hint Unfold lift_to_composite_state' : state_update.

Ltac state_update_simpl :=
  autounfold with state_update in *; autorewrite with state_update in *.

(** ** Basic projection lemmas

  These basic projection lemmas relate
  the [valid_state_prop] and [input_valid_transition] of
  a composite VLSM back to those conditions holding
  over projections to individual components of the state.

  Because the composition may have validly produced
  messages that are not valid for an individual
  component (by interaction between components),
  We cannot just use properties [valid_state_message_prop (IM i)]
  or [input_valid_transition (IM i)].
  For simplicity these lemmas use
  [pre_loaded_with_all_messages_vlsm (IM i)].

  This does not precisely reflect the set of
  messages and transitions that can actually be
  seen in projections of transitions of the composite VLSM,
  but seems to be the best we can do with a result
  type that doesn't mention the other components or
  the composition constraint of the composite.

  Later in this file a
  [composite_constrained_projection_vlsm] is defined
  that shares the states of [IM i] which is more
  precise.
*)

Lemma valid_state_project_preloaded_to_preloaded_free
  message `{EqDecision index} (IM : index -> VLSM message)
  (X := free_composite_vlsm IM)
  (s : state (pre_loaded_with_all_messages_vlsm X)) i :
  valid_state_prop (pre_loaded_with_all_messages_vlsm X) s ->
  valid_state_prop (pre_loaded_with_all_messages_vlsm (IM i)) (s i).
Proof.
  intros [om Hproto].
  apply preloaded_valid_state_prop_iff.
  induction Hproto; [by apply preloaded_valid_initial_state, (Hs i) |].
  destruct l as [j lj]; cbn in Ht.
  destruct (transition lj _) as (si', _om') eqn: Hti.
  inversion_clear Ht.
  destruct (decide (i = j)); subst; state_update_simpl; [| done].
  by apply preloaded_protocol_generated with lj (s j) om _om'; [| apply Hv |].
Qed.

Lemma valid_state_project_preloaded_to_preloaded
  message `{EqDecision index} (IM : index -> VLSM message) constraint
  (X := composite_vlsm IM constraint)
  (s : state (pre_loaded_with_all_messages_vlsm X)) i :
  valid_state_prop (pre_loaded_with_all_messages_vlsm X) s ->
  valid_state_prop (pre_loaded_with_all_messages_vlsm (IM i)) (s i).
Proof.
  intros.
  eapply valid_state_project_preloaded_to_preloaded_free.
  apply VLSM_incl_valid_state; [| done].
  by apply constrained_pre_loaded_vlsm_incl_pre_loaded_with_all_messages.
Qed.

Lemma valid_state_project_preloaded
      message `{EqDecision index} (IM : index -> VLSM message) constraint
      (X := composite_vlsm IM constraint)
      (s : state X) i :
  valid_state_prop X s ->
  valid_state_prop (pre_loaded_with_all_messages_vlsm (IM i)) (s i).
Proof.
  by intros; apply valid_state_project_preloaded_to_preloaded,
    pre_loaded_with_all_messages_valid_state_prop.
Qed.

Lemma composite_transition_project_active
  message `{EqDecision index} (IM : index -> VLSM message) :
  forall (l : composite_label IM) (s : composite_state IM) (im : option message)
    (s' : composite_state IM) (om : option message),
      composite_transition IM l (s, im) = (s', om) ->
      transition (IM (projT1 l)) (projT2 l) (s (projT1 l), im) = (s' (projT1 l), om).
Proof.
  intros [x l]; cbn; intros.
  destruct (transition (IM x) l (s x, im)).
  inversion H.
  f_equal.
  by state_update_simpl.
Qed.

Lemma input_valid_transition_preloaded_project_active_free
  {message} `{EqDecision V} {IM : V -> VLSM message}
  (X := free_composite_vlsm IM)
  l s im s' om :
  input_valid_transition (pre_loaded_with_all_messages_vlsm X) l (s, im) (s', om) ->
  input_valid_transition (pre_loaded_with_all_messages_vlsm (IM (projT1 l))) (projT2 l)
    (s (projT1 l), im) (s' (projT1 l), om).
Proof.
  intro Hptrans.
  destruct Hptrans as [[Hproto_s [_ Hcvalid]] Htrans].
  split; [| by eapply composite_transition_project_active].
  split; [| split].
  - by eapply valid_state_project_preloaded_to_preloaded_free.
  - by apply any_message_is_valid_in_preloaded.
  - by destruct l; apply Hcvalid.
Qed.

Lemma input_valid_transition_preloaded_project_active
  {message} `{EqDecision V} {IM : V -> VLSM message} {constraint}
  (X := composite_vlsm IM constraint)
  l s im s' om :
  input_valid_transition (pre_loaded_with_all_messages_vlsm X) l (s, im) (s', om) ->
  input_valid_transition (pre_loaded_with_all_messages_vlsm (IM (projT1 l))) (projT2 l)
    (s (projT1 l), im) (s' (projT1 l), om).
Proof.
  intros.
  apply input_valid_transition_preloaded_project_active_free.
  apply (@VLSM_incl_input_valid_transition _ _ (pre_loaded_with_all_messages_vlsm X)); [| done].
  by apply constrained_pre_loaded_vlsm_incl_pre_loaded_with_all_messages.
Qed.

Lemma input_valid_transition_project_active
  {message} `{EqDecision V} {IM : V -> VLSM message} {constraint}
  (X := composite_vlsm IM constraint)
  l s im s' om :
  input_valid_transition X l (s, im) (s', om) ->
  input_valid_transition (pre_loaded_with_all_messages_vlsm (IM (projT1 l))) (projT2 l)
    (s (projT1 l), im) (s' (projT1 l), om).
Proof.
  intro Hptrans.
  apply preloaded_weaken_input_valid_transition in Hptrans.
  by revert Hptrans; apply input_valid_transition_preloaded_project_active.
Qed.

Lemma input_valid_transition_preloaded_project_any_free
  {V : Type} (i : V)
  {message : Type} `{EqDecision V} {IM : V -> VLSM message}
  (X := free_composite_vlsm IM)
  (l : label X) s im s' om :
  input_valid_transition (pre_loaded_with_all_messages_vlsm X) l (s, im) (s', om) ->
    s i = s' i \/
    exists li : label (IM i),
      l = existT i li /\
     input_valid_transition (pre_loaded_with_all_messages_vlsm (IM i)) li (s i, im) (s' i, om).
Proof.
  intro Hptrans.
  destruct l as [j lj].
  destruct (decide (i = j)); subst.
  - right.
    exists lj.
    split; [done |].
    by revert Hptrans; apply input_valid_transition_preloaded_project_active_free.
  - left.
    destruct Hptrans as [Hpvalid Htrans]; cbn in Htrans.
    destruct (transition (IM j) lj (s j, im)); inversion_clear Htrans.
    by state_update_simpl.
Qed.

Lemma input_valid_transition_preloaded_project_any
  {V : Type} (i : V)
  {message : Type} `{EqDecision V} {IM : V -> VLSM message} {constraint}
  (X := composite_vlsm IM constraint)
  (l : label X) s im s' om :
  input_valid_transition (pre_loaded_with_all_messages_vlsm X) l (s, im) (s', om) ->
    s i = s' i \/
    exists li : label (IM i),
      l = existT i li /\
      input_valid_transition (pre_loaded_with_all_messages_vlsm (IM i)) li (s i, im) (s' i, om).
Proof.
  intros.
  apply input_valid_transition_preloaded_project_any_free.
  apply (@VLSM_incl_input_valid_transition _ _ (pre_loaded_with_all_messages_vlsm X)); [| done].
  by apply constrained_pre_loaded_vlsm_incl_pre_loaded_with_all_messages.
Qed.

Lemma input_valid_transition_project_any
  {V : Type} (i : V)
  {message : Type} `{EqDecision V} {IM : V -> VLSM message} {constraint}
  (X := composite_vlsm IM constraint)
  (l : label X) s im s' om :
  input_valid_transition X l (s, im) (s', om) ->
    s i = s' i \/
    exists li : label (IM i),
      l = existT i li /\
      input_valid_transition (pre_loaded_with_all_messages_vlsm (IM i)) li (s i, im) (s' i, om).
Proof.
  intro Hproto.
  apply preloaded_weaken_input_valid_transition in Hproto.
  by revert Hproto; apply input_valid_transition_preloaded_project_any.
Qed.

(**
  If a message can be emitted by a composition, then it can be emitted by one of the
  components.
*)

Lemma can_emit_free_composite_project
  {message : Type} `{EqDecision V} {IM : V -> VLSM message}
  (X := free_composite_vlsm IM)
  (m : message)
  (Hemit : can_emit (pre_loaded_with_all_messages_vlsm X) m) :
    exists (j : V), can_emit (pre_loaded_with_all_messages_vlsm (IM j)) m.
Proof.
  apply can_emit_iff in Hemit as (s2 & [s1 oim] & l & Ht).
  exists (projT1 l).
  apply can_emit_iff.
  exists (s2 (projT1 l)), (s1 (projT1 l), oim), (projT2 l).
  by eapply input_valid_transition_preloaded_project_active_free.
Qed.

Lemma can_emit_composite_project
  {message : Type} `{EqDecision V} {IM : V -> VLSM message} {constraint}
  (X := composite_vlsm IM constraint)
  (m : message)
  (Hemit : can_emit (pre_loaded_with_all_messages_vlsm X) m) :
    exists (j : V), can_emit (pre_loaded_with_all_messages_vlsm (IM j)) m.
Proof.
  apply can_emit_free_composite_project.
  eapply VLSM_incl_can_emit; [| done].
  by apply constrained_pre_loaded_vlsm_incl_pre_loaded_with_all_messages.
Qed.

(** ** Binary free composition

  This serves an example of how composition can be built, but is also being
  used in defining the [byzantine_trace_prop]erties.

  This instantiates the regular composition using the [bool] type as an <<index>>.
*)

Section sec_binary_free_composition.

Context
  {message : Type}
  (M1 M2 : VLSM message)
  .

Definition binary_index : Set := bool.

Definition first : binary_index := true.
Definition second : binary_index := false.

#[export] Instance binary_index_dec :  EqDecision binary_index := _.
#[export] Instance binary_index_inhabited : Inhabited binary_index := populate first.

Definition binary_IM
  (i : binary_index)
  : VLSM message
  :=
  match i with
  | true => M1
  | false => M2
  end.

Definition binary_free_composition : VLSM message :=
  composite_vlsm binary_IM (free_constraint binary_IM).

End sec_binary_free_composition.

(** ** Composite decidable initial message

  Here we show that if the [initial_message_prop]erty is decidable for every
  component, then it is decidable for a finite composition as well.
*)

Section sec_composite_decidable_initial_message.

Context
  {message : Type}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  (constraint : composite_label IM -> composite_state IM * option message -> Prop)
  .

Lemma composite_decidable_initial_message
  (Hdec_init : forall i, decidable_initial_messages_prop (IM i))
  : decidable_initial_messages_prop (composite_vlsm IM constraint).
Proof.
  intro m. simpl. unfold composite_initial_message_prop.
  apply
    (Decision_iff
      (P := List.Exists (fun i => initial_message_prop (IM i) m) (enum index))).
  - rewrite <- exists_finite.
    split; intros [i Hm]; exists i.
    + by exists (exist _ _ Hm).
    + by destruct Hm as [[im Hinit] [= ->]].
  - by apply @Exists_dec; intro i; apply Hdec_init.
Qed.

End sec_composite_decidable_initial_message.

(** ** Composite plan properties

  The following results concern facts about applying a [plan Free] <<P>>
  to a [state Free] <<s'>>, knowing its effects on a different [state Free] <<s>>
  which shares some relevant features with <<s'>>.
*)

Section sec_composite_plan_properties.

Context
  {message : Type}
  {index : Type}
  `{EqDecision index}
  (IM : index -> VLSM message)
  (Free := free_composite_vlsm IM)
  .

(* A transition on component <<i>> is [input_valid] from <<s'>> if it is
   [input_valid] from <<s>> and their <<i>>'th components are equal. *)

Lemma relevant_component_transition_free
  (s s' : state Free)
  (l : label Free)
  (input : option message)
  (i := projT1 l)
  (Heq : (s i) = (s' i))
  (Hprs : valid_state_prop Free s')
  (Hiv : input_valid Free l (s, input)) :
  input_valid Free l (s', input).
Proof.
  split_and!; [done | by apply Hiv |].
  cbn in Hiv |- *.
  destruct l.
  simpl in i.
  unfold i in Heq.
  rewrite <- Heq.
  by itauto.
Qed.

(* The effect of the transition is also the same. *)

Lemma relevant_component_transition2_free
  (s s' : state Free)
  (l : label Free)
  (input : option message)
  (i := projT1 l)
  (Heq : (s i) = (s' i))
  (Hprs : valid_state_prop Free s') :
  let (dest, output) := transition Free l (s, input) in
  let (dest', output') := transition Free l (s', input) in
  output = output' /\ (dest i) = (dest' i).
Proof.
  destruct l as [x l]; simpl in i |- *.
  unfold i in Heq; rewrite Heq.
  destruct (transition (IM x) l (s' x, input)).
  by state_update_simpl.
Qed.

Lemma relevant_components_one_free
  (s s' : state Free)
  (Hprs' : valid_state_prop Free s')
  (ai : vplan_item Free)
  (i := projT1 (label_a ai))
  (Heq : (s i) = (s' i))
  (Hpr : finite_valid_plan_from Free s [ai]) :
  let res' := snd (apply_plan Free s' [ai]) in
  let res := snd (apply_plan Free s [ai]) in
  finite_valid_plan_from Free s' [ai] /\
  (res' i) = res i.
Proof.
  simpl.
  unfold finite_valid_plan_from, apply_plan, _apply_plan in *.
  destruct ai; simpl in *.
  match goal with
  |- context [let (_, _) := let (_, _) := ?t in _ in _] =>
    destruct t eqn: eq_trans'
  end.
  match goal with
  |- context [let (_, _) := let (_, _) := ?t in _ in _] =>
    destruct t eqn: eq_trans
  end.
  inversion Hpr; subst.
  split.
  - assert (Ht' : input_valid_transition Free label_a (s', input_a) (c, o)).
    {
      unfold input_valid_transition in *.
      destruct Ht as [Hpr_valid Htrans].
      by apply relevant_component_transition_free with (s' := s') in Hpr_valid; itauto.
    }
    apply finite_valid_trace_from_extend; [| done].
    apply finite_valid_trace_from_empty.
    by apply input_valid_transition_destination in Ht'.
  - specialize (relevant_component_transition2_free s s' label_a input_a Heq Hprs') as Hrel.
    cbn in *.
    repeat case_match.
    unfold i; cbn in *.
    by itauto congruence.
Qed.

(**
  Transitioning on some index different from <<i>> does not affect
  component <<i>>.
*)
Lemma irrelevant_components_one
  (s : state (composite_type IM))
  (ai : composite_plan_item IM)
  (i : index)
  (Hdif : i <> projT1 (label_a ai)) :
  let res := snd (composite_apply_plan IM s [ai]) in
  (res i) = (s i).
Proof.
  unfold composite_apply_plan, apply_plan, _apply_plan; cbn.
  repeat case_match; cbn.
  inversion H; inversion H1; subst.
  by state_update_simpl.
Qed.

(**
  Same as [irrelevant_components_one], but for
  multiple transitions.
*)
Lemma irrelevant_components
  (s : state (composite_type IM))
  (a : composite_plan IM)
  (a_indices := List.map (@projT1 _ _) (List.map (@label_a _ _) a))
  (i : index)
  (Hdif : i ∉ a_indices) :
  let res := snd (composite_apply_plan IM s a) in
  (res i) = (s i).
Proof.
  induction a using rev_ind.
  - by simpl; itauto.
  - simpl in *.
    rewrite (composite_apply_plan_app IM).
    destruct (composite_apply_plan IM s a) as (tra, sa) eqn: eq_a; simpl in *.
    destruct (composite_apply_plan IM sa [x]) as (trx, sx) eqn: eq_x; simpl in *.

    unfold a_indices in Hdif.
    rewrite map_app in Hdif.
    rewrite map_app in Hdif.

    spec IHa. {
      intro Hin.
      contradict Hdif.
      apply elem_of_app.
      by left.
    }

    rewrite <- IHa.
    replace sx with (snd (composite_apply_plan IM sa [x])) by (rewrite eq_x; done).
    apply irrelevant_components_one.
    intros contra.
    rewrite contra in Hdif.

    rewrite elem_of_app in Hdif; simpl in Hdif.
    contradict Hdif.
    subst.
    by right; left.
Qed.

(* Same as relevant_components_one but for multiple transitions. *)

Lemma relevant_components_free
  (s s' : state Free)
  (Hprs' : valid_state_prop Free s')
  (a : plan Free)
  (a_indices := List.map (@projT1 _ _) (List.map (@label_a _ _) a))
  (li : list index)
  (Heq : forall (i : index), i ∈ li -> (s' i) = (s i))
  (Hincl : a_indices ⊆ li)
  (Hpr : finite_valid_plan_from Free s a) :
  let res' := snd (apply_plan Free s' a) in
  let res := snd (apply_plan Free s a) in
  finite_valid_plan_from Free s' a /\
  (forall (i : index), i ∈ li -> (res' i) = res i).
Proof.
  induction a using rev_ind; cbn in *; [by auto using finite_valid_plan_empty |].
  apply finite_valid_plan_from_app_iff in Hpr as [Hrem Hsingle].
  spec IHa.
  {
    remember (List.map (@projT1 _ (fun n : index => label (IM n))) (List.map label_a a)) as small.
    transitivity a_indices; [| done].
    unfold a_indices.
    intros e H; simpl.
    rewrite 2 map_app, elem_of_app.
    by itauto.
  }
  spec IHa; [done |].
  destruct IHa as [IHapr IHaind].
  specialize (relevant_components_one_free (snd (apply_plan Free s a))
    (snd (apply_plan Free s' a))) as Hrel.
  spec Hrel; [by apply apply_plan_last_valid; itauto |].
  specialize (Hrel x); simpl in *.
  spec Hrel.
  {
    specialize (IHaind (projT1 (label_a x))).
    symmetry.
    apply IHaind.
    specialize (Hincl (projT1 (label_a x))).
    apply Hincl.
    unfold a_indices.
    by rewrite 2 map_app, elem_of_app; right; left.
  }
  specialize (Hrel Hsingle).
  destruct Hrel as [Hrelpr Hrelind].
  split; [by apply finite_valid_plan_from_app_iff; split |].
  intros i Hi.
  rewrite !apply_plan_app.
  destruct (apply_plan Free s' a) as [tra' sa'] eqn: eq_as'.
  destruct (apply_plan Free s a) as [tra sa] eqn: eq_as.
  simpl in *.
  destruct (apply_plan Free sa [x]) as [trx sx] eqn: eq_xsa.
  destruct (apply_plan Free sa' [x]) as [trx' sx'] eqn: eq_xsa'.
  simpl in *.
  destruct (decide (i = (projT1 (label_a x)))); [by rewrite e |].
  apply (f_equal snd) in eq_xsa, eq_xsa'.
  replace sx' with (snd (composite_apply_plan IM sa' [x])).
  replace sx with (snd (composite_apply_plan IM sa [x])).
  specialize (irrelevant_components_one sa x i n) as Hdiff.
  specialize (irrelevant_components_one sa' x i n) as Hdiff0.
  setoid_rewrite Hdiff.
  setoid_rewrite Hdiff0.
  by apply IHaind.
Qed.

End sec_composite_plan_properties.

(** ** Properties of the empty composition *)

Section sec_empty_composition_properties.

Context {message : Type}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  (constraint : composite_label IM -> composite_state IM * option message -> Prop)
  (X := composite_vlsm IM constraint)
  (Hempty_index : enum index = [])
  .

Lemma empty_composition_no_index
  (i : index)
  : False.
Proof.
  by specialize (elem_of_enum i); rewrite Hempty_index; apply not_elem_of_nil.
Qed.

Lemma empty_composition_single_state
  (s : composite_state IM)
  : s = (proj1_sig (composite_s0 IM)).
Proof.
  by extensionality i; elim (empty_composition_no_index i).
Qed.

Lemma empty_composition_no_label
  (l : composite_label IM)
  : False.
Proof.
  by destruct l as [i _]; elim (empty_composition_no_index i).
Qed.

Lemma empty_composition_no_initial_message
  : forall m, ~ composite_initial_message_prop IM m.
Proof.
  by intros m [i _]; elim (empty_composition_no_index i).
Qed.

Lemma empty_composition_no_emit
  : forall m, ~ can_emit X m.
Proof.
  by intros m [s' [l _]]; elim (empty_composition_no_label l).
Qed.

Lemma empty_composition_no_valid_message
  : forall m, ~ valid_message_prop X m.
Proof.
  intros m Hm.
  apply emitted_messages_are_valid_iff in Hm as [Hinit | Hemit].
  - by elim (empty_composition_no_initial_message _ Hinit).
  - by elim (empty_composition_no_emit _ Hemit).
Qed.

Lemma pre_loaded_empty_composition_no_emit
  (seed : message -> Prop)
  (PreX := pre_loaded_vlsm X seed)
  : forall m, ~ can_emit PreX m.
Proof.
  by intros m [s' [l _]]; elim (empty_composition_no_label l).
Qed.

Lemma pre_loaded_empty_free_composition_no_emit
  (seed : message -> Prop)
  (PreX := pre_loaded_vlsm (free_composite_vlsm IM) seed)
  : forall m, ~ can_emit PreX m.
Proof.
  by intros m [s' [l _]]; elim (empty_composition_no_label l).
Qed.

Lemma pre_loaded_with_all_empty_composition_no_emit
  : forall m, ~ can_emit (pre_loaded_with_all_messages_vlsm X) m.
Proof.
  by intros m [s' [l _]]; elim (empty_composition_no_label l).
Qed.

End sec_empty_composition_properties.

(** ** Properties of extensionally-equal indexed compositions

  If two indexed sets of VLSMs are extensionally-equal, then we can establish a
  [VLSM_embedding] between their compositions with subsumable constraints
  (and pre-loaded with the same set of messages).
*)

Section sec_same_IM_embedding.

Context
  {message : Type}
  `{EqDecision index}
  (IM1 IM2 : index -> VLSM message)
  (Heq : forall i, IM1 i = IM2 i)
  .

Definition same_IM_label_rew
  (l1 : composite_label IM1)
  : composite_label IM2 :=
  existT (projT1 l1) (same_VLSM_label_rew (Heq (projT1 l1)) (projT2 l1)).

Definition same_IM_state_rew
  (s1 : composite_state IM1)
  : composite_state IM2 :=
  fun i => same_VLSM_state_rew (Heq i) (s1 i).

Section sec_pre_loaded_constrained.

Context
  (constraint1 : composite_label IM1 -> composite_state IM1 * option message -> Prop)
  (constraint2 : composite_label IM2 -> composite_state IM2 * option message -> Prop)
  (constraint_projection
    : forall s1, valid_state_prop (pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM1)) s1 ->
      forall l1 om, constraint1 l1 (s1, om) ->
    constraint2 (same_IM_label_rew l1) (same_IM_state_rew s1, om))
  (seed : message -> Prop)
  .

Lemma same_IM_embedding
  : VLSM_embedding
    (pre_loaded_vlsm (composite_vlsm IM1 constraint1) seed)
    (pre_loaded_vlsm (composite_vlsm IM2 constraint2) seed)
    same_IM_label_rew
    same_IM_state_rew.
Proof.
  apply basic_VLSM_embedding; intros l **.
  - destruct Hv as [Hs [Hom [Hv Hc]]].
    apply constraint_projection in Hc; cycle 1.
    + apply VLSM_incl_valid_state; [| done].
      by apply constrained_pre_loaded_vlsm_incl_pre_loaded_with_all_messages.
    + split; [| done].
      clear Hc. revert Hv. destruct l as (i, li). cbn.
      by apply same_VLSM_valid_preservation.
  - apply proj2 in H. revert H. destruct l as (i, li). cbn.
    destruct (transition (IM1 i) _ _) as (si'1, _om') eqn: Ht1.
    unfold same_IM_state_rew at 1.
    erewrite same_VLSM_transition_preservation; [| done].
    inversion 1; subst; clear H.
    f_equal. extensionality j.
    unfold same_IM_state_rew at 2.
    by destruct (decide (i = j)); subst; state_update_simpl.
  - by intros i; apply same_VLSM_initial_state_preservation, H.
  - apply initial_message_is_valid.
    destruct HmX as [[i [[im Him] Hi]] | Hseed]; [| by right].
    simpl in Hi. subst im.
    cbn. unfold composite_initial_message_prop.
    left; exists i.
    unshelve esplit.
    + by exists m; eapply same_VLSM_initial_message_preservation; eauto.
    + done.
Qed.

End sec_pre_loaded_constrained.

Lemma same_IM_preloaded_free_embedding :
  VLSM_embedding
    (pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM1))
    (pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM2))
    same_IM_label_rew
    same_IM_state_rew.
Proof.
  constructor.
  intros s1 tr1 Htr1.
  eapply VLSM_incl_finite_valid_trace in Htr1; [| by apply preloaded_free_composite_vlsm_spec].
  pose proof (Hproj := same_IM_embedding (free_constraint IM1) (free_constraint IM2)
    ltac:(done) (fun _ => True)).
  apply (VLSM_embedding_finite_valid_trace Hproj) in Htr1.
  eapply VLSM_incl_finite_valid_trace in Htr1; [done |].
  by apply preloaded_free_composite_vlsm_spec.
Qed.

End sec_same_IM_embedding.

Arguments same_IM_label_rew {_ _ _ _} _ _ : assert.
Arguments same_IM_state_rew {_ _ _ _} _ _ _ : assert.

(** ** Valid transitions in a composition *)

Section sec_composite_valid_transition.

Context
  {message : Type}
  `{EqDecision index}
  (IM : index -> VLSM message)
  (Free := free_composite_vlsm IM)
  (RFree := pre_loaded_with_all_messages_vlsm Free)
  .

Record CompositeValidTransition l s1 iom s2 oom : Prop :=
{
  cvt_valid : composite_valid IM l (s1, iom);
  cvt_transition : composite_transition IM l (s1, iom) = (s2, oom);
}.

Definition composite_valid_transition_item
  (s : composite_state IM) (item : composite_transition_item IM) : Prop :=
  CompositeValidTransition (l item) s (input item) (destination item) (output item).

Lemma composite_valid_transition_reachable_iff l s1 iom s2 oom :
  CompositeValidTransition l s1 iom s2 oom <-> ValidTransition RFree l s1 iom s2 oom.
Proof.
  split; [by intros []; constructor |].
  intros []; constructor.
  - by apply vt_valid.
  - by apply vt_transition.
Qed.

Inductive CompositeValidTransitionNext (s1 s2 : composite_state IM) : Prop :=
| composite_transition_next : forall l iom oom,
    CompositeValidTransition l s1 iom s2 oom ->
    CompositeValidTransitionNext s1 s2.

Lemma composite_valid_transition_next :
  forall l s1 iom s2 oom,
    CompositeValidTransition l s1 iom s2 oom -> CompositeValidTransitionNext s1 s2.
Proof. by intros * [Hv Ht]; econstructor. Qed.

Definition composite_valid_transition_future : relation (composite_state IM) :=
  tc CompositeValidTransitionNext.

Lemma CompositeValidTransitionNext_reachable_iff s1 s2 :
  CompositeValidTransitionNext s1 s2 <-> ValidTransitionNext RFree s1 s2.
Proof.
  by split; intros []; econstructor; apply composite_valid_transition_reachable_iff.
Qed.

Lemma composite_valid_transition_projection :
  forall l s1 iom s2 oom,
    CompositeValidTransition l s1 iom s2 oom ->
    ValidTransition (IM (projT1 l)) (projT2 l) (s1 (projT1 l)) iom (s2 (projT1 l)) oom /\
    s2 = state_update IM s1 (projT1 l) (s2 (projT1 l)).
Proof.
  intros [i li] * [Hv Ht]; cbn in Ht; destruct (transition _ _ _) eqn: Hti.
  by inversion Ht; subst; cbn; state_update_simpl.
Qed.

Lemma composite_valid_transition_projection_inv :
  forall i li si1 iom si2 oom,
    ValidTransition (IM i) li si1 iom si2 oom ->
    forall s1, s1 i = si1 -> forall s2, s2 = state_update IM s1 i si2 ->
    CompositeValidTransition (existT i li) s1 iom s2 oom.
Proof.
  intros * [Hv Ht] s1 <- s2 ->; split; [done |].
  by cbn; replace (transition _ _ _) with (si2, oom).
Qed.

Inductive CompositeValidTransitionsFromTo
  : composite_state IM -> composite_state IM -> list (composite_transition_item IM) -> Prop :=
| cvtft_empty : forall s, CompositeValidTransitionsFromTo s s []
| cvtft_cons : forall s s' tr item,
    CompositeValidTransitionsFromTo s s' tr ->
    composite_valid_transition_item s' item ->
    CompositeValidTransitionsFromTo s (destination item) (tr ++ [item]).

Lemma CompositeValidTransitionsFromTo_trace : forall s s' tr,
  finite_valid_trace_from_to RFree s s' tr ->
  CompositeValidTransitionsFromTo s s' tr.
Proof.
  induction 1 using finite_valid_trace_from_to_rev_ind; [by constructor |].
  remember {| destination := sf |} as item.
  replace sf with (destination item) by (subst; done).
  econstructor; [done |]; subst.
  by apply composite_valid_transition_reachable_iff, input_valid_transition_forget_input.
Qed.

End sec_composite_valid_transition.
