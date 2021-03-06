From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude finite.
From Coq Require Import Streams FunctionalExtensionality FinFun.
From VLSM Require Import Lib.Preamble Lib.ListExtras Lib.StdppListSet Lib.StreamExtras.
From VLSM Require Import Core.VLSM Core.Plans Core.VLSMProjections.

(** * VLSM Composition *)

(**
This module provides Coq definitions for composite VLSMs and their projections
to components.
*)

Section VLSM_composition.

(**
Let us fix a type for <<message>>s, and an <<index>> type for the VLSM components
such that equality on <<index>> is decidable.
*)

  Context {message : Type}
          `{EqDecision index}
          (IM : index -> VLSM message)
          .

  Section composite_type.

(** ** The type of a composite VLSM

Let IM be a family of VLSMs indexed by <<index>>. Note that all
[VLSM]s share the same type of <<message>>s.

*)

(**
A [composite_state] is an indexed family of [state]s, yielding for each
index <<n>> a [state] of [type] <<IT n>>, the [VLSMType] corresponding to
machine <<n>>.

Note that the [composite_state] type is the dependent product type of the
family of [state] types corresponding to each index.
*)
    Definition composite_state : Type :=
      forall n : index, vstate (IM n).

(**
A [composite_label] is a pair between an index <<N>> and a [label] of <<IT n>>.

Note that the [composite_label] type is the dependent sum of the family of
types <<[@label _ (IT n) | n <- index]>>.
*)
    Definition composite_label
      : Type
      := sigT (fun n => vlabel (IM n)).

    (* Declaring this a "canonical structure" will make type checking
       guess that a VLSMType should be composite_type instead of just
       failing, if it has to compare composite_state with state or
       vstate of an unsolved VLSMType or VLSM.
     *)
    Canonical Structure composite_type : VLSMType message :=
      {| state := composite_state
       ; label := composite_label
      |}.

    Definition composite_transition_item : Type := @transition_item message composite_type.

(**
A very useful operation on [composite_state]s is updating the state corresponding
to a component:
*)
    Definition state_update
               (s : composite_state)
               (i : index)
               (si : vstate (IM i))
               (j : index)
      : vstate (IM j)
      :=
      match decide (j = i) with
      | left e => eq_rect_r (fun i => vstate (IM i)) si e
      | _ => s j
      end.

(**
The next few results describe several properties of the [state_update] operation.
*)
    Lemma state_update_neq
               (s : composite_state)
               (i : index)
               (si : vstate (IM i))
               (j : index)
               (Hneq : j <> i)
      : state_update s i si j = s j.
    Proof.
      by unfold state_update; case_decide.
    Qed.

    Lemma state_update_eq
               (s : composite_state)
               (i : index)
               (si : vstate (IM i))
      : state_update s i si i = si.
    Proof.
      by unfold state_update, decide, decide_rel; rewrite eq_dec_refl.
    Qed.

    Lemma state_update_id
               (s : composite_state)
               (i : index)
               (si : vstate (IM i))
               (Heq : s i = si)
      : state_update s i si = s.
    Proof.
      apply functional_extensionality_dep_good.
      intro j.
      destruct (decide (j = i)).
      - subst. apply state_update_eq.
      - by apply state_update_neq.
    Qed.

    Lemma state_update_twice
               (s : composite_state)
               (i : index)
               (si si': vstate (IM i))
      : state_update (state_update s i si) i si' = state_update s i si'.
    Proof.
      apply functional_extensionality_dep_good.
      intro j.
      destruct (decide (j = i)).
      - subst. rewrite state_update_eq. symmetry. apply state_update_eq.
      - by rewrite !state_update_neq.
    Qed.

    Lemma state_update_twice_neq
               (s : composite_state)
               (i j : index)
               (si : vstate (IM i))
               (sj : vstate (IM j))
               (Hij : j <> i)
      : state_update (state_update s i si) j sj
      = state_update (state_update s j sj) i si.
    Proof.
      apply functional_extensionality_dep_good.
      intro k.
      destruct (decide (k = j)); destruct (decide (k = i)); subst
      ; repeat (rewrite state_update_eq ; try (rewrite state_update_neq; try done))
      ; try done.
      by rewrite !state_update_neq.
    Qed.
  End composite_type.

  Section sec_composite_vlsm.
(** ** Constrained VLSM composition

Assume an non-empty <<index>> type and let <<IT>> be
an <<index>>ed family of [VLSMType]s, and for each index <<i>>, let <<IM i>> be
a [VLSMMachine] of type <<IT i>>.
*)

(**
A [composite_state] has the [initial_state_prop]erty if all of its component
states have the [initial_state_prop]erty in the corresponding component signature.
*)
    Definition composite_initial_state_prop
               (s : composite_state)
      : Prop
      :=
        forall n : index, vinitial_state_prop (IM n) (s n).

    Definition composite_initial_state
      := sig composite_initial_state_prop.

    Definition composite_s0 : composite_initial_state.
    Proof.
      exists (fun (n : index) => proj1_sig (vs0 (IM n))).
      by intro i; destruct (vs0 (IM i)) as [s Hs].
    Defined.

    #[global] Instance composite_initial_state_inh : Inhabited composite_initial_state :=
      {| inhabitant := composite_s0 |}.

(**
A message has the [initial_message_prop]erty in the composite
iff it has the [initial_message_prop]erty in any of the components.
*)
    Definition composite_initial_message_prop (m : message) : Prop
      :=
        exists (n : index) (mi : vinitial_message (IM n)), proj1_sig mi = m.

    Definition option_composite_initial_message_prop : option message -> Prop
      := from_option composite_initial_message_prop True.

    Definition lift_to_composite_label
      (j : index)
      (lj : vlabel (IM j))
      : composite_label
      := existT j lj.

(**
We can always "lift" state <<sj>> from component <<j>> to a composite state by
updating an given composite state to <<sj>> on component <<j>>.
*)
    Definition lift_to_composite_state
      (s : composite_state)
      (j : index)
      (sj : vstate (IM j))
      : composite_state
      := state_update s j sj.

    Definition lift_to_composite_transition_item
      (s : composite_state)
      (j : index)
      : vtransition_item (IM j) -> composite_transition_item :=
      pre_VLSM_full_projection_transition_item_project (type (IM j)) composite_type
        (lift_to_composite_label j) (lift_to_composite_state s j).

(**
A specialized version of [lift_to_composite_state] using the initial composite
state as the base for lifting.
*)
    Definition lift_to_composite_state'
      := lift_to_composite_state (proj1_sig composite_s0).

    Definition lift_to_composite_transition_item'
      := lift_to_composite_transition_item (proj1_sig composite_s0).

    (**
    Composite versions for [plan_item] and [plan].
    *)
    Definition composite_plan_item := @plan_item _ composite_type.
    Definition composite_plan := list composite_plan_item.

    Definition lift_to_composite_plan_item
      (i : index)
      (a : vplan_item (IM i)) :
      composite_plan_item.
    Proof.
      destruct a.
      split.
      - exact (existT i label_a).
      - exact input_a.
    Defined.

(**
The [transition] function for the [composite_vlsm] takes a transition in
the component selected by the index in the given [composite_label]
with the contained label,
and returns the produced message together with the state updated on that
component:
*)
    Definition composite_transition
      (l : composite_label)
      (som : composite_state * option message)
      : composite_state * option message
      :=
      let (s, om) := som in
      let (i, li) := l in
      let (si', om') := vtransition (IM i) li (s i, om) in
      (state_update s i si',  om').

    Lemma composite_transition_state_neq
      (l : composite_label)
      (s s' : composite_state)
      (om om' : option message)
      (Ht : composite_transition l (s, om) = (s', om'))
      (i : index)
      (Hi : i <> projT1 l)
      : s' i = s i.
    Proof.
      destruct l; cbn in Ht; destruct (vtransition _ _ _).
      by inversion Ht; apply state_update_neq.
    Qed.

    Lemma composite_transition_state_eq
      (i : index)
      (li : vlabel (IM i))
      (s s' : composite_state)
      (om om' : option message)
      (Ht : composite_transition (existT i li) (s, om) = (s', om'))
      : s' i = fst (vtransition (IM i) li (s i, om)).
    Proof.
      cbn in Ht; destruct (vtransition _ _ _); inversion Ht; apply state_update_eq.
    Qed.

(**
Given a [composite_label] <<(i, li)>> and a [composite_state]-message
pair <<(s, om)>>, [composite_valid]ity is defined as [valid]ity in
the <<i>>th component <<IM i>>.
*)
    Definition composite_valid
      (l : composite_label)
      (som : composite_state * option message)
      : Prop
      :=
      let (s, om) := som in
      let (i, li) := l in
      vvalid (IM i) li (s i, om).

(**
A <<constraint>> for a composite VLSM is a [valid]ity condition defined
directly on [composite_label]s and [composite_state]s, thus being able to
impose a global condition.

[constrained_composite_valid]ity interposes such a <<constraint>> on top of
the [composite_valid]ity.
*)

    Definition constrained_composite_valid
      (constraint : composite_label -> composite_state * option message -> Prop)
      (l : composite_label)
      (som : composite_state * option message)
      :=
      composite_valid l som /\ constraint l som.

    Definition composite_vlsm_machine
      (constraint : composite_label -> composite_state * option message -> Prop)
      : VLSMMachine composite_type
      :=
      {| initial_state_prop := composite_initial_state_prop
       ; initial_message_prop := composite_initial_message_prop
       ; transition := composite_transition
       ; valid := constrained_composite_valid constraint
      |}.

    Definition composite_vlsm
      (constraint : composite_label -> composite_state * option message -> Prop)
      : VLSM message
      := mk_vlsm (composite_vlsm_machine constraint).

    (** Composite versions for the generic [_apply_plan]-related definitions and
    results.
    *)
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

  Lemma composite_initial_state_prop_lift
    (j : index)
    (sj : vstate (IM j))
    (Hinitj : vinitial_state_prop (IM j) sj)
    : composite_initial_state_prop (lift_to_composite_state' j sj).
  Proof.
    intro i.
    unfold lift_to_composite_state'.
    destruct (decide (i = j)); subst.
    - by rewrite state_update_eq.
    - rewrite state_update_neq; cbn; [| done].
      by destruct (vs0 _) as [s Hs].
  Qed.

(** ** Free VLSM composition

The [free_constraint] is defined to be [True] for all inputs.
Thus, the [free_composite_vlsm] is the [composite_vlsm] using the
[free_constraint].
*)

    Definition free_constraint
      (l : composite_label)
      (som : composite_state * option message)
      : Prop
      := True.

    Definition free_composite_vlsm : VLSM message
      := composite_vlsm free_constraint.

    Lemma lift_to_composite_vlsm_full_projection j
      : VLSM_full_projection (IM j) free_composite_vlsm (lift_to_composite_label j) (lift_to_composite_state' j).
    Proof.
      apply basic_VLSM_strong_full_projection; intro; intros.
      - split; [| done]. simpl.
        unfold lift_to_composite_state'. rewrite state_update_eq. apply H.
      - unfold vtransition. simpl. unfold lift_to_composite_state' at 1.
        rewrite state_update_eq. replace (vtransition _ _ _) with (s', om').
        f_equal. unfold lift_to_composite_state'. apply state_update_twice.
      - by apply composite_initial_state_prop_lift.
      - by exists j, (exist _ _ H).
    Qed.

    Definition lift_to_composite_finite_trace j
      : list (vtransition_item (IM j)) -> list composite_transition_item
      := VLSM_full_projection_finite_trace_project (lift_to_composite_vlsm_full_projection j).

    Definition lift_to_composite_finite_trace_last j
      := VLSM_full_projection_finite_trace_last (lift_to_composite_vlsm_full_projection j).

    Lemma constraint_free_incl
      (constraint : composite_label -> composite_state  * option message -> Prop)
      : VLSM_incl (composite_vlsm constraint) free_composite_vlsm.
    Proof.
      apply basic_VLSM_strong_incl; firstorder.
    Qed.

    Lemma composite_pre_loaded_vlsm_incl_pre_loaded_with_all_messages
      (constraint : composite_label -> composite_state  * option message -> Prop)
      (P : message -> Prop)
      : VLSM_incl (pre_loaded_vlsm (composite_vlsm constraint) P) (pre_loaded_with_all_messages_vlsm free_composite_vlsm).
    Proof.
      by apply basic_VLSM_strong_incl; cbv; [..|itauto|].
    Qed.

    Lemma constraint_free_valid_state_message_preservation
      (constraint : composite_label -> composite_state * option message -> Prop)
      s om
      (Hsom : valid_state_message_prop (composite_vlsm constraint) s om)
      : valid_state_message_prop free_composite_vlsm s om.
    Proof.
      revert Hsom.
      by apply (VLSM_incl_valid_state_message (constraint_free_incl constraint)); intro.
    Qed.

    Section sec_constraint_subsumption.
(** ** Constraint subsumption *)

(**
A <<constraint1>> is subsumed by <<constraint2>> if <<constraint1>> is stronger
than <<constraint2>> for any input.
*)
    Definition strong_constraint_subsumption
        (constraint1 constraint2 : composite_label -> composite_state * option message -> Prop)
        :=
        forall (l : composite_label) (som : composite_state * option message),
          constraint1 l som -> constraint2 l som.

(**
A weaker version of [strong_constraint_subsumption] requiring [input_valid]ity
w.r.t. [pre_loaded_with_all_messages_vlsm] as a precondition for the subsumption
property.

This definition is useful in proving [VLSM_incl]usions between [VLSM]s
pre-loaded with all messages (Lemma [preloaded_constraint_subsumption_incl]).

Although there are currently no explicit cases for its usage, it might be more
useful than the [strong_constraint_subsumption] property in cases where proving
constraint subsumption relies on the state being valid and/or the message
being valid.
*)
    Definition preloaded_constraint_subsumption
        (constraint1 constraint2 : composite_label -> composite_state * option message -> Prop)
        :=
        forall (l : composite_label) (som : state * option message),
            input_valid (pre_loaded_with_all_messages_vlsm (composite_vlsm constraint1)) l som ->
            constraint2 l som.

(**
A weaker version of [preloaded_constraint_subsumption] requiring [input_valid]ity
as a precondition for the subsumption property.

This definition is usually useful in proving [VLSM_incl]usions between regular
[VLSM]s (Lemma [constraint_subsumption_incl]).

It is more useful than the [strong_constraint_subsumption] property in cases
where proving constraint subsumption relies on the state/message being valid
and/or the message being valid (e.g., Lemma [Fixed_incl_StrongFixed]).
*)
    Definition input_valid_constraint_subsumption
        (constraint1 constraint2 : composite_label -> composite_state * option message -> Prop)
        :=
        forall (l : composite_label) (som : composite_state * option message),
          input_valid (composite_vlsm constraint1) l som -> constraint2 l som.

(**
The weakest form [constraint_subsumption] also requires that the input
state and message are valid for the composition under the second constraint.
*)
    Definition weak_input_valid_constraint_subsumption
        (constraint1 constraint2 : composite_label -> composite_state * option message -> Prop)
        :=
        forall (l : composite_label) (som : composite_state * option message),
          input_valid (composite_vlsm constraint1) l som ->
          valid_state_prop (composite_vlsm constraint2) som.1 ->
          option_valid_message_prop (composite_vlsm constraint2) som.2 ->
          constraint2 l som.

    Context
      (constraint1 constraint2 : composite_label -> composite_state * option message -> Prop)
      (X1 := composite_vlsm constraint1)
      (X2 := composite_vlsm constraint2)
      .

(**
Let <<X1>>, <<X2>> be two compositions of the same family of VLSMs but with
constraints <<constraint1>> and <<constraint2>>, respectively. Further assume
that <<constraint1>> is subsumed by <<constraint2>>.

We will show that <<X1>> is trace-included into <<X2>> by applying
Lemma [basic_VLSM_incl]
*)

(* begin hide *)
    Lemma weak_constraint_subsumption_incl
      (Hsubsumption : weak_input_valid_constraint_subsumption constraint1 constraint2)
      : VLSM_incl X1 X2.
    Proof.
      apply basic_VLSM_incl.
      - by intros s Hs.
      - by intros _ _ m _ _ Hm; apply initial_message_is_valid.
      - split; [apply Hv | auto].
      - by intros l s om s' om' Ht; apply Ht.
    Qed.

    Lemma constraint_subsumption_input_valid
      (Hsubsumption : input_valid_constraint_subsumption constraint1 constraint2)
      (l : label)
      (s : state)
      (om : option message)
      (Hv : input_valid X1 l (s, om))
      : vvalid X2 l (s, om).
    Proof.
      by split; [apply Hv | apply Hsubsumption].
    Qed.

    Lemma constraint_subsumption_valid_state_message_preservation
      (Hsubsumption : input_valid_constraint_subsumption constraint1 constraint2)
      (s : state)
      (om : option message)
      (Hps : valid_state_message_prop X1 s om)
      : valid_state_message_prop X2 s om.
    Proof.
      induction Hps.
      - by apply valid_initial_state_message.
      - apply (valid_generated_state_message X2) with s _om _s om l. 1-2, 4: done.
        apply constraint_subsumption_input_valid; [done |].
        by split_and!; [exists _om | exists _s|].
    Qed.

    Lemma constraint_subsumption_incl
      (Hsubsumption : input_valid_constraint_subsumption constraint1 constraint2)
      : VLSM_incl X1 X2.
    Proof.
      apply basic_VLSM_incl; intro; intros.
      - done.
      - by apply initial_message_is_valid.
      - by apply constraint_subsumption_input_valid.
      - by apply H.
    Qed.

    Lemma preloaded_constraint_subsumption_input_valid
      (Hpre_subsumption : preloaded_constraint_subsumption constraint1 constraint2)
      (l : label)
      (s : state)
      (om : option message)
      (Hv : input_valid (pre_loaded_with_all_messages_vlsm X1) l (s, om))
      : vvalid X2 l (s, om).
    Proof.
      by split; [apply Hv | apply Hpre_subsumption].
    Qed.

    Lemma preloaded_constraint_subsumption_incl
      (Hpre_subsumption : preloaded_constraint_subsumption constraint1 constraint2)
      : VLSM_incl (pre_loaded_with_all_messages_vlsm X1) (pre_loaded_with_all_messages_vlsm X2).
    Proof.
      apply basic_VLSM_incl; intro; intros; [done | | | apply H].
      - by apply initial_message_is_valid.
      - by apply preloaded_constraint_subsumption_input_valid.
    Qed.

    Lemma weak_constraint_subsumption_weakest
      (Hsubsumption : input_valid_constraint_subsumption constraint1 constraint2)
      : weak_input_valid_constraint_subsumption constraint1 constraint2.
    Proof.
      intros l som Hv _ _. auto.
    Qed.

    Lemma preloaded_constraint_subsumption_stronger
      (Hpre_subsumption : preloaded_constraint_subsumption constraint1 constraint2)
      : input_valid_constraint_subsumption constraint1 constraint2.
    Proof.
      intros l som Hv. apply (Hpre_subsumption l som).
      destruct som.
      revert Hv.
      apply (VLSM_incl_input_valid (vlsm_incl_pre_loaded_with_all_messages_vlsm (composite_vlsm constraint1))).
    Qed.

    Lemma strong_constraint_subsumption_strongest
      (Hstrong_subsumption : strong_constraint_subsumption constraint1 constraint2)
      : preloaded_constraint_subsumption constraint1 constraint2.
    Proof.
      intros l (s, om) [_ [_ [_ Hc]]]. revert Hc. apply Hstrong_subsumption.
    Qed.

    Lemma constraint_subsumption_byzantine_message_prop
      (Hpre_subsumption : preloaded_constraint_subsumption constraint1 constraint2)
      (m : message)
      (Hm : byzantine_message_prop X1 m)
      : byzantine_message_prop X2 m.
    Proof.
      revert Hm.
      apply (VLSM_incl_can_emit (preloaded_constraint_subsumption_incl Hpre_subsumption)).
    Qed.

(* end hide *)
    End sec_constraint_subsumption.

    Lemma preloaded_constraint_free_incl
      (constraint : composite_label -> composite_state  * option message -> Prop)
      : VLSM_incl (pre_loaded_with_all_messages_vlsm (composite_vlsm constraint)) (pre_loaded_with_all_messages_vlsm free_composite_vlsm).
    Proof.
      by apply preloaded_constraint_subsumption_incl.
    Qed.

    (* TODO(traiansf): There are many places where, because the lemma below
      was missing, it was either reproved locally, or multiple VLSM_incl_
      lemmas were used to achieve a similar result. It would be nice to
      find those usages and use this lemma instad.
    *)
    Lemma constraint_preloaded_free_incl
      (constraint : composite_label -> composite_state  * option message -> Prop)
      : VLSM_incl (composite_vlsm constraint) (pre_loaded_with_all_messages_vlsm free_composite_vlsm).
    Proof.
      eapply VLSM_incl_trans.
      - apply vlsm_incl_pre_loaded_with_all_messages_vlsm.
      - apply preloaded_constraint_free_incl.
    Qed.

    Lemma lift_to_composite_generalized_preloaded_vlsm_full_projection
      (P Q : message -> Prop)
      (PimpliesQ : forall m, P m -> Q m)
      (j : index)
      : VLSM_full_projection (pre_loaded_vlsm (IM j) P) (pre_loaded_vlsm free_composite_vlsm Q) (lift_to_composite_label j) (lift_to_composite_state' j).
    Proof.
      apply basic_VLSM_full_projection_preloaded_with; intro; intros.
      - by apply PimpliesQ.
      - split; cbn; [| done].
        unfold lift_to_composite_state'. rewrite state_update_eq. apply H.
      - unfold vtransition. simpl. unfold lift_to_composite_state' at 1.
        rewrite state_update_eq. replace (vtransition (IM j) l _) with (s', om').
        f_equal. unfold lift_to_composite_state'. apply state_update_twice.
      - by apply composite_initial_state_prop_lift.
      - by exists j, (exist _ _ H).
    Qed.

    Lemma lift_to_composite_preloaded_vlsm_full_projection
      (j : index)
      : VLSM_full_projection (pre_loaded_with_all_messages_vlsm (IM j)) (pre_loaded_with_all_messages_vlsm free_composite_vlsm) (lift_to_composite_label j) (lift_to_composite_state' j).
    Proof.
      apply basic_VLSM_full_projection_preloaded.
      - intro; intros. split; [| done]. simpl.
        unfold lift_to_composite_state'. rewrite state_update_eq. apply H.
      - intro; intros. unfold vtransition. simpl. unfold vtransition. simpl. unfold lift_to_composite_state' at 1.
        rewrite state_update_eq. replace (transition l _) with (s', om').
        f_equal. unfold lift_to_composite_state'. apply state_update_twice.
      - by intros s H; apply composite_initial_state_prop_lift.
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
        itauto.
      - eapply VLSM_full_projection_can_emit; [| done].
        apply lift_to_composite_generalized_preloaded_vlsm_full_projection.
        itauto.
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
      - eapply VLSM_eq_proj2, (vlsm_is_pre_loaded_with_False free_composite_vlsm).
      - eapply valid_preloaded_lifts_can_be_emitted; [| done].
        intros dm Hdm.
        eapply VLSM_incl_valid_message.
        + apply VLSM_eq_proj1, (vlsm_is_pre_loaded_with_False free_composite_vlsm).
        + cbv; itauto.
        + by apply Hdeps.
    Qed.

    Lemma valid_state_preloaded_composite_free_lift
      (j : index)
      (sj : vstate (IM j))
      (Hp : valid_state_prop (pre_loaded_with_all_messages_vlsm (IM j)) sj)
      : valid_state_prop (pre_loaded_with_all_messages_vlsm free_composite_vlsm) (lift_to_composite_state' j sj).
    Proof.
      by apply (VLSM_full_projection_valid_state (lift_to_composite_preloaded_vlsm_full_projection j)).
    Qed.

    Lemma can_emit_composite_free_lift
      (P Q : message -> Prop)
      (PimpliesQ : forall m, P m -> Q m)
      (j : index)
      (m : message)
      (Htrj : can_emit (pre_loaded_vlsm (IM j) P) m)
      : can_emit (pre_loaded_vlsm free_composite_vlsm Q) m.
    Proof.
      eapply VLSM_full_projection_can_emit.
      - by apply lift_to_composite_generalized_preloaded_vlsm_full_projection.
      - done.
    Qed.

    (** Updating a composite initial state with a component initial state
    yields a composite initial state *)
    Lemma composite_update_initial_state_with_initial
      (s : composite_state)
      (Hs : composite_initial_state_prop s)
      (i : index)
      (si : vstate (IM i))
      (Hsi : vinitial_state_prop (IM i) si)
      : composite_initial_state_prop (state_update s i si).
    Proof.
      intro j. destruct (decide (j = i)); subst.
      - by rewrite state_update_eq.
      - by rewrite state_update_neq.
    Qed.

    (** Updating a composite [valid_state] for the free composition with
    a component initial state yields a composite [valid_state] *)
    Lemma pre_composite_free_update_state_with_initial
      (P : message -> Prop)
      (s : composite_state)
      (Hs : valid_state_prop (pre_loaded_vlsm free_composite_vlsm P) s)
      (i : index)
      (si : vstate (IM i))
      (Hsi : vinitial_state_prop (IM i) si)
      : valid_state_prop (pre_loaded_vlsm free_composite_vlsm P) (state_update s i si).
    Proof.
      induction Hs using valid_state_prop_ind.
      - by apply initial_state_is_valid, composite_update_initial_state_with_initial.
      - destruct Ht as [[Hps [Hom [Hv _]]] Ht]; cbn in Ht, Hv.
        destruct l as [j lj].
        destruct (vtransition _ _ _) as [sj' omj'] eqn: Htj.
        inversion_clear Ht.
        destruct (decide (i = j)).
        + by subst; rewrite state_update_twice.
        + rewrite state_update_twice_neq by done.
          apply input_valid_transition_destination with (existT j lj) (state_update s i si) om omj'.
          by repeat split; [done | done |..]; cbn; rewrite state_update_neq;
            [..| rewrite Htj |].
    Qed.

    Lemma lift_to_composite_valid_preservation :
      forall (i : index) (cs : composite_state),
      forall l s om, vvalid (IM i) l (s, om) ->
        composite_valid (lift_to_composite_label i l)
          (lift_to_composite_state cs i s, om).
    Proof. by intros; cbn; rewrite state_update_eq. Qed.

    Lemma lift_to_composite_transition_preservation :
      forall (i : index) (cs : composite_state),
      forall l s om s' om', vtransition (IM i) l (s, om) = (s', om') ->
        composite_transition (lift_to_composite_label i l)
          (lift_to_composite_state cs i s, om)
            =
          (lift_to_composite_state cs i s', om').
    Proof.
      intros; cbn.
      unfold lift_to_composite_state; rewrite state_update_eq.
      by replace (vtransition _ _ _) with (s', om'); rewrite state_update_twice.
    Qed.

    Lemma lift_to_composite_initial_message_preservation :
      forall (i : index),
          forall m, vinitial_message_prop (IM i) m ->
          composite_initial_message_prop m.
    Proof. by intros i m Hm; exists i, (exist _ _ Hm). Qed.
 
    Lemma pre_lift_to_free_weak_full_projection :
      forall (i : index) (cs : composite_state) (P : message -> Prop),
          valid_state_prop (pre_loaded_vlsm free_composite_vlsm P) cs ->
          VLSM_weak_full_projection
            (pre_loaded_vlsm (IM i) P) (pre_loaded_vlsm free_composite_vlsm P)
            (lift_to_composite_label i) (lift_to_composite_state cs i).
    Proof.
      intros i cs P Hvsp.
      apply basic_VLSM_weak_full_projection.
      - intros l s om (_ & _ & Hv) _ _.
        by split; [apply lift_to_composite_valid_preservation |].
      - by inversion 1; apply lift_to_composite_transition_preservation.
      - by intros s Hs; apply pre_composite_free_update_state_with_initial.
      - intros _ _ m _ _ [Hm | Hp]; apply initial_message_is_valid; [left | by right].
        by eapply lift_to_composite_initial_message_preservation.
    Qed.

    Lemma lift_to_free_weak_full_projection :
      forall (i : index) (cs : composite_state),
          valid_state_prop free_composite_vlsm cs ->
          VLSM_weak_full_projection (IM i) free_composite_vlsm
            (lift_to_composite_label i) (lift_to_composite_state cs i).
    Proof.
      constructor; intros.
      apply (VLSM_eq_finite_valid_trace_from (vlsm_is_pre_loaded_with_False free_composite_vlsm)),
            pre_lift_to_free_weak_full_projection.
      - by apply (VLSM_eq_valid_state (vlsm_is_pre_loaded_with_False free_composite_vlsm)).
      - apply (VLSM_eq_finite_valid_trace_from (vlsm_is_pre_loaded_with_False (IM i))).
        by destruct (IM i).
    Qed.

    Lemma lift_to_preloaded_free_weak_full_projection :
      forall (i : index) (cs : composite_state),
          valid_state_prop (pre_loaded_with_all_messages_vlsm free_composite_vlsm) cs ->
          VLSM_weak_full_projection
            (pre_loaded_with_all_messages_vlsm (IM i)) (pre_loaded_with_all_messages_vlsm free_composite_vlsm)
            (lift_to_composite_label i) (lift_to_composite_state cs i).
    Proof.
      constructor; intros.
      apply (VLSM_eq_finite_valid_trace_from (pre_loaded_with_all_messages_vlsm_is_pre_loaded_with_True free_composite_vlsm)),
            pre_lift_to_free_weak_full_projection.
      - by apply (VLSM_eq_valid_state (pre_loaded_with_all_messages_vlsm_is_pre_loaded_with_True free_composite_vlsm)).
      - apply (VLSM_eq_finite_valid_trace_from (pre_loaded_with_all_messages_vlsm_is_pre_loaded_with_True (IM i))).
        by destruct (IM i).
    Qed.

  End sec_composite_vlsm.

End VLSM_composition.

(**
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

Lemma valid_state_project_preloaded_to_preloaded
      message `{EqDecision index} (IM : index -> VLSM message) constraint
      (X:=composite_vlsm IM constraint)
      (s: vstate (pre_loaded_with_all_messages_vlsm X)) i:
  valid_state_prop (pre_loaded_with_all_messages_vlsm X) s ->
  valid_state_prop (pre_loaded_with_all_messages_vlsm (IM i)) (s i).
Proof.
  intros [om Hproto].
  apply preloaded_valid_state_prop_iff.
  induction Hproto.
  - apply preloaded_valid_initial_state.
    apply (Hs i).
  - destruct l as [j lj].
    simpl in Ht. unfold vtransition in Ht. simpl in Ht.
    destruct (vtransition (IM j) _ _) as (si', _om') eqn:Hti.
    inversion_clear Ht.
    destruct (decide (i = j)).
    + subst j.
      rewrite state_update_eq.
      apply preloaded_protocol_generated with lj (s i) om _om'; [done | | done].
      apply Hv.
    + by rewrite state_update_neq.
Qed.

Lemma valid_state_project_preloaded
      message `{EqDecision index} (IM : index -> VLSM message) constraint
      (X:=composite_vlsm IM constraint)
      (s: vstate X) i:
  valid_state_prop X s ->
  valid_state_prop (pre_loaded_with_all_messages_vlsm (IM i)) (s i).
Proof.
  change (vstate X) with (vstate (pre_loaded_with_all_messages_vlsm X)) in s.
  intros [om Hproto].
  apply valid_state_project_preloaded_to_preloaded.
  exists om.
  by apply preloaded_weaken_valid_state_message_prop.
Qed.

Lemma composite_transition_project_active
      message `{EqDecision index} (IM : index -> VLSM message)
  : forall (l : composite_label IM) (s : composite_state IM) (im : option message) (s' : composite_state IM) (om : option message),
      composite_transition IM l (s, im) = (s', om) ->
      vtransition (IM (projT1 l)) (projT2 l) (s (projT1 l), im) = (s' (projT1 l), om).
Proof.
  intros.
  destruct l;simpl.
  simpl in H.
  destruct (vtransition (IM x) v (s x, im)).
  inversion H.
  f_equal.
  by rewrite state_update_eq.
Qed.

Lemma input_valid_transition_preloaded_project_active
      {message} `{EqDecision V} {IM: V -> VLSM message} {constraint}
      (X := composite_vlsm IM constraint)
      l s im s' om:
  input_valid_transition (pre_loaded_with_all_messages_vlsm X) l (s,im) (s',om) ->
  input_valid_transition (pre_loaded_with_all_messages_vlsm (IM (projT1 l))) (projT2 l)
                         (s (projT1 l), im) (s' (projT1 l), om).
Proof.
  intro Hptrans.
  destruct Hptrans as [Hpvalid Htrans].
  split.
  - destruct Hpvalid as [Hproto_s [_ Hcvalid]].
    split;[|split].
    + revert Hproto_s.
      apply valid_state_project_preloaded_to_preloaded.
    + apply any_message_is_valid_in_preloaded.
    + destruct l. apply Hcvalid.
  - revert Htrans; rapply composite_transition_project_active.
Qed.

Lemma input_valid_transition_project_active
      {message} `{EqDecision V} {IM: V -> VLSM message} {constraint}
      (X := composite_vlsm IM constraint)
      l s im s' om:
  input_valid_transition X l (s,im) (s',om) ->
  input_valid_transition (pre_loaded_with_all_messages_vlsm (IM (projT1 l))) (projT2 l)
                         (s (projT1 l), im) (s' (projT1 l), om).
Proof.
  intro Hptrans.
  apply preloaded_weaken_input_valid_transition in Hptrans.
  revert Hptrans.
  apply input_valid_transition_preloaded_project_active.
Qed.

Lemma input_valid_transition_preloaded_project_any {V} (i:V)
      {message} `{EqDecision V} {IM: V -> VLSM message} {constraint}
      (X := composite_vlsm IM constraint)
      (l:vlabel X) s im s' om:
  input_valid_transition (pre_loaded_with_all_messages_vlsm X) l (s,im) (s',om) ->
  (s i = s' i \/
   exists li, (l = existT i li) /\
   input_valid_transition (pre_loaded_with_all_messages_vlsm (IM i))
                          li
                          (s i,im) (s' i,om)).
Proof.
  intro Hptrans.
  destruct l as [j lj].
  destruct (decide (i = j)).
  - subst j.
    right.
    exists lj.
    split; [done |].
    revert Hptrans.
    apply input_valid_transition_preloaded_project_active.
  - left.
    destruct Hptrans as [Hpvalid Htrans].
    cbn in Htrans.
    destruct (vtransition (IM j) lj (s j, im)).
    inversion_clear Htrans.
    by rewrite state_update_neq.
Qed.

Lemma input_valid_transition_project_any {V} (i:V)
      {message} `{EqDecision V} {IM: V -> VLSM message} {constraint}
      (X := composite_vlsm IM constraint)
      (l:vlabel X) s im s' om:
  input_valid_transition X l (s,im) (s',om) ->
  (s i = s' i \/
   exists li, (l = existT i li) /\
   input_valid_transition (pre_loaded_with_all_messages_vlsm (IM i))
                          li
                          (s i,im) (s' i,om)).
Proof.
  intro Hproto.
  apply preloaded_weaken_input_valid_transition in Hproto.
  revert Hproto.
  apply input_valid_transition_preloaded_project_any.
Qed.

(** If a message can be emitted by a composition, then it can be emitted by one of the
components.
*)
Lemma can_emit_composite_project
  {message} `{EqDecision V} {IM: V -> VLSM message} {constraint}
  (X := composite_vlsm IM constraint)
  (m : message)
  (Hemit: can_emit (pre_loaded_with_all_messages_vlsm X) m)
  : exists (j : V), can_emit (pre_loaded_with_all_messages_vlsm (IM j)) m.
Proof.
  apply can_emit_iff in Hemit.
  destruct Hemit as [s2 [(s1, oim) [l Ht]]].
  exists (projT1 l).
  apply can_emit_iff.
  exists (s2 (projT1 l)).
  exists (s1 (projT1 l), oim), (projT2 l).
  revert Ht. apply input_valid_transition_preloaded_project_active.
Qed.

Section binary_free_composition.

(** ** Free composition of two VLSMs

This serves an example of how composition can be built, but is also being
used in defining the [byzantine_trace_prop]erties.

This instantiates the regular composition using the [bool] type as an <<index>>.

*)
  Context
    {message : Type}
    (M1 M2 : VLSM message)
    .

  Definition binary_index : Set := bool.

  Definition first : binary_index := true.
  Definition second : binary_index := false.

  #[global] Instance binary_index_dec :  EqDecision binary_index := _.
  #[global] Instance binary_index_inhabited : Inhabited binary_index
    :=
    populate first.

  Definition binary_IM
    (i : binary_index)
    : VLSM message
    :=
    match i with
    | true => M1
    | false => M2
    end.

  Definition binary_free_composition
    : VLSM message
    := free_composite_vlsm binary_IM.

End binary_free_composition.

Section composite_decidable_initial_message.

(** ** Composite decidable initial message

Here we show that if the [initial_message_prop]erty is decidable for every
component, then it is decidable for a finite composition as well.

*)

Context
  {message : Type}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  (constraint : composite_label IM -> composite_state IM * option message -> Prop)
  .

Lemma composite_decidable_initial_message
  (Hdec_init : forall i, vdecidable_initial_messages_prop (IM i))
  : decidable_initial_messages_prop (composite_vlsm_machine IM constraint).
Proof.
  intro m. simpl. unfold composite_initial_message_prop.
  apply
    (Decision_iff
      (P := List.Exists (fun i => vinitial_message_prop (IM i) m) (enum index))
    ).
  - rewrite <- exists_finite.
    split; intros [i Hm]; exists i.
    + by exists (exist _ _ Hm).
    + by destruct Hm as [[im Hinit] [= ->]].
  - apply @Exists_dec. intro i. apply Hdec_init.
Qed.

End composite_decidable_initial_message.

Section composite_plan_properties.

  Context {message : Type}
          {index : Type}
          `{EqDecision index}
          (IM :index -> VLSM message)
          (Free := free_composite_vlsm IM)
          .

  (** ** Composite Plan Properties

     The following results concern facts about applying a [plan Free] <<P>>
     to a [vstate Free] <<s'>>, knowing its effects on a different [vstate Free] <<s>>
     which shares some relevant features with <<s'>>. *)

  (* A transition on component <<i>> is [input_valid] from <<s'>> if it is
     [input_valid] from <<s>> and their <<i>>'th components are equal. *)

  Lemma relevant_component_transition
    (s s' : vstate Free)
    (l : vlabel Free)
    (input : option message)
    (i := projT1 l)
    (Heq : (s i) = (s' i))
    (Hprs : valid_state_prop Free s')
    (Hiv : input_valid Free l (s, input)) :
    input_valid Free l (s', input).
  Proof.
    unfold input_valid in *.
    split_and!; try itauto.
    unfold valid in *; simpl in *.
    unfold constrained_composite_valid in *.
    unfold composite_valid in *.
    unfold free_constraint in *; simpl.
    unfold vvalid in *.
    destruct l.
    simpl in i.
    unfold i in Heq.
    rewrite <- Heq.
    itauto.
  Qed.

  (* The effect of the transition is also the same *)

  Lemma relevant_component_transition2
    (s s' : vstate Free)
    (l : vlabel Free)
    (input : option message)
    (i := projT1 l)
    (Heq : (s i) = (s' i))
    (Hprs : valid_state_prop Free s') :
    let (dest, output) := vtransition Free l (s, input) in
    let (dest', output') := vtransition Free l (s', input) in
    output = output' /\ (dest i) = (dest' i).
  Proof.
    unfold vtransition.
    unfold transition.
    destruct l; simpl.
    simpl in i.
    unfold i in Heq.
    rewrite Heq.
    destruct (vtransition (IM x) v (s' x, input)).
    split; [done|].
    unfold i.
    by rewrite !state_update_eq.
  Qed.

  Lemma relevant_components_one
    (s s' : vstate Free)
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
    unfold finite_valid_plan_from in *.
    unfold apply_plan, _apply_plan in *.
    destruct ai; simpl in *.
    match goal with
    |- context [let (_, _) := let (_, _) := ?t in _ in _] =>
      destruct t eqn : eq_trans'
    end.
    match goal with
    |- context [let (_, _) := let (_, _) := ?t in _ in _] =>
      destruct t eqn : eq_trans
    end.
    inversion Hpr; subst.
    split.
    - assert (Ht' : input_valid_transition Free label_a (s', input_a) (s0, o)). {
        unfold input_valid_transition in *.
        destruct Ht as [Hpr_valid Htrans].
        apply relevant_component_transition with (s' := s') in Hpr_valid.
        all : itauto.
      }

      apply finite_valid_trace_from_extend; [| done].
      apply finite_valid_trace_from_empty.
      by apply input_valid_transition_destination in Ht'.
    - simpl.
      specialize (relevant_component_transition2 s s' label_a input_a) as Hrel.
      simpl in Hrel. unfold i in Heq. specialize (Hrel Heq Hprs').
      match type of Hrel with
      | let (_, _) := ?t in _ => replace t with (s1, o0) in Hrel
      end.
      match type of Hrel with
      | let (_, _) := ?t in _ => replace t with (s0, o) in Hrel
      end.
      unfold i.
      itauto.
  Qed.

  (* Transitioning on some index different from <<i>> does not affect
     component i. *)

  Lemma irrelevant_components_one
    (s : state)
    (ai : composite_plan_item IM)
    (i : index)
    (Hdif : i <> projT1 (label_a ai)) :
    let res := snd (composite_apply_plan IM s [ai]) in
    (res i) = (s i).
  Proof.
    unfold composite_apply_plan, apply_plan, _apply_plan.
    simpl.
    destruct ai.
    match goal with
    |- context [let (_, _) := let (_, _) := ?t in _ in _] =>
      destruct t eqn : eq_trans
    end.
    simpl in *.
    unfold vtransition in eq_trans.
    simpl in eq_trans.
    destruct label_a; simpl in *.
    match type of eq_trans with
    | (let (si', om') := ?t in _) = _ => destruct t end.
    inversion eq_trans.
    by rewrite state_update_neq.
  Qed.

  (* Same as the previous result, but for multiple transitions. *)

  Lemma irrelevant_components
    (s : state)
    (a : composite_plan IM)
    (a_indices := List.map (@projT1 _ _) (List.map (@label_a _ _) a))
    (i : index)
    (Hdif : i ??? a_indices) :
    let res := snd (composite_apply_plan IM s a) in
    (res i) = (s i).
  Proof.
    induction a using rev_ind.
    - simpl; itauto.
    - simpl in *.
      rewrite (composite_apply_plan_app IM).
      destruct (composite_apply_plan IM s a) as (tra, sa) eqn : eq_a; simpl in *.
      destruct (composite_apply_plan IM sa [x]) as (trx, sx) eqn : eq_x; simpl in *.

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
      right; left.
  Qed.

  (* Same as relevant_components_one but for multiple transitions *)

  Lemma relevant_components
    (s s' : vstate Free)
    (Hprs' : valid_state_prop Free s')
    (a : plan Free)
    (a_indices := List.map (@projT1 _ _) (List.map (@label_a _ _) a))
    (li : list index)
    (Heq : forall (i : index), i ??? li -> (s' i) = (s i))
    (Hincl : a_indices ??? li)
    (Hpr : finite_valid_plan_from Free s a) :
    let res' := snd (apply_plan Free s' a) in
    let res := snd (apply_plan Free s a) in
    finite_valid_plan_from Free s' a /\
    (forall (i : index), i ??? li -> (res' i) = res i).
  Proof.
    induction a using rev_ind.
    - by split; [apply finite_valid_plan_empty|].
    - simpl in *.
      apply finite_valid_plan_from_app_iff in Hpr.
      destruct Hpr as [Hrem Hsingle].

      spec IHa. {
        remember (List.map (@projT1 _ (fun n : index => vlabel (IM n))) (List.map label_a a)) as small.
        transitivity a_indices; [| done].
        unfold a_indices.
        intros e H; simpl.
        rewrite 2 map_app, elem_of_app.
        itauto.
      }

      spec IHa; [done |].

      destruct IHa as [IHapr IHaind].

      specialize (relevant_components_one (snd (apply_plan Free s a)) (snd (apply_plan Free s' a))) as Hrel.

      spec Hrel. {
        apply apply_plan_last_valid.
        all : itauto.
      }

      specialize (Hrel x); simpl in *.

      spec Hrel. {
        specialize (IHaind (projT1 (label_a x))).
        symmetry.
        apply IHaind.
        specialize (Hincl (projT1 (label_a x))).
        apply Hincl.
        unfold a_indices.
        rewrite 2 map_app, elem_of_app.
        right; left.
      }

      specialize (Hrel Hsingle).
      destruct Hrel as [Hrelpr Hrelind].
      split.
      + apply finite_valid_plan_from_app_iff.
        split; itauto.
      + intros i Hi.
        specialize (IHaind i Hi).
        specialize (Heq i Hi).
        rewrite !apply_plan_app.
        simpl in *.
        destruct (apply_plan Free s' a)
          as (tra', sa') eqn : eq_as'.
        destruct (apply_plan Free s a)
          as (tra, sa) eqn : eq_as.
        simpl in *.
        destruct (apply_plan Free sa [x])
          as (trx, sx) eqn : eq_xsa.
        destruct (apply_plan Free sa' [x])
          as (trx', sx') eqn : eq_xsa'.
        simpl in *.
        destruct (decide (i = (projT1 (label_a x)))).
        * rewrite e; itauto.
        * specialize (irrelevant_components_one sa) as Hdiff.
          specialize (Hdiff x i n).

          specialize (irrelevant_components_one sa') as Hdiff0.
          specialize (Hdiff0 x i n).
          simpl in *.
          apply (f_equal snd) in eq_xsa.
          apply (f_equal snd) in eq_xsa'.

          replace sx' with (snd (composite_apply_plan IM sa' [x])).
          replace sx with (snd (composite_apply_plan IM sa [x])).
          setoid_rewrite Hdiff.
          by setoid_rewrite Hdiff0.
  Qed.

End composite_plan_properties.

Section empty_composition_properties.

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
  specialize (elem_of_enum i); rewrite Hempty_index; apply not_elem_of_nil.
Qed.

Lemma empty_composition_single_state
  (s : composite_state IM)
  : s = (proj1_sig (composite_s0 IM)).
Proof.
  extensionality i; elim (empty_composition_no_index i).
Qed.

Lemma empty_composition_no_label
  (l : composite_label IM)
  : False.
Proof.
  destruct l as (i, _). elim (empty_composition_no_index i).
Qed.

Lemma empty_composition_no_initial_message
  : forall m, ~ composite_initial_message_prop IM m.
Proof.
  intros m [i _]. elim (empty_composition_no_index i).
Qed.

Lemma empty_composition_no_emit
  : forall m, ~ can_emit X m.
Proof.
  intros m [s' [l _]]; elim (empty_composition_no_label l).
Qed.

Lemma empty_composition_no_valid_message
  : forall m, ~ valid_message_prop X m.
Proof.
  intros m Hm.
  apply emitted_messages_are_valid_iff in Hm as [Hinit | Hemit].
  - elim (empty_composition_no_initial_message _ Hinit).
  - elim (empty_composition_no_emit _ Hemit).
Qed.

Lemma pre_loaded_empty_composition_no_emit
  (seed : message -> Prop)
  (PreX := pre_loaded_vlsm X seed)
  : forall m, ~ can_emit PreX m.
Proof.
  intros m [s' [l _]]; elim (empty_composition_no_label l).
Qed.

Lemma pre_loaded_with_all_empty_composition_no_emit
  : forall m, ~ can_emit (pre_loaded_with_all_messages_vlsm X) m.
Proof.
  intros m [s' [l _]]; elim (empty_composition_no_label l).
Qed.

End empty_composition_properties.

(** ** Properties of extensionally-equal indexed compositions

If two indexed sets of VLSMs are extensionally-equal, then we can establish a
[VLSM_full_projection] between their compositions with subsumable constraints
(and pre-loaded with the same set of messages).
*)
Section sec_same_IM_full_projection.

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

Section pre_loaded_constrained.

Context
  (constraint1 : composite_label IM1 -> composite_state IM1 * option message -> Prop)
  (constraint2 : composite_label IM2 -> composite_state IM2 * option message -> Prop)
  (constraint_projection
    : forall s1, valid_state_prop (pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM1)) s1 ->
      forall l1 om, constraint1 l1 (s1,om) ->
    constraint2 (same_IM_label_rew l1) (same_IM_state_rew s1, om))
  (seed : message -> Prop)
  .

Lemma same_IM_full_projection
  : VLSM_full_projection
    (pre_loaded_vlsm (composite_vlsm IM1 constraint1) seed)
    (pre_loaded_vlsm (composite_vlsm IM2 constraint2) seed)
    same_IM_label_rew
    same_IM_state_rew.
Proof.
  apply basic_VLSM_full_projection; intros l **.
  - destruct Hv as [Hs [Hom [Hv Hc]]].
    apply constraint_projection in Hc; cycle 1.
    + apply VLSM_incl_valid_state; [| done].
      apply composite_pre_loaded_vlsm_incl_pre_loaded_with_all_messages.
    + split; [| done].
      clear Hc. revert Hv. destruct l as (i, li). cbn.
      apply same_VLSM_valid_preservation.
  - apply proj2 in H. revert H. destruct l as (i, li). cbn.
    destruct (vtransition (IM1 i) _ _) as (si'1, _om') eqn: Ht1.
    unfold same_IM_state_rew at 1.
    erewrite same_VLSM_transition_preservation; [| done].
    inversion 1; subst; clear H.
    f_equal. extensionality j.
    unfold same_IM_state_rew at 2.
    destruct (decide (i = j)).
    + by subst; rewrite !state_update_eq.
    + by rewrite !state_update_neq.
  - intros i. apply same_VLSM_initial_state_preservation, H.
  - apply initial_message_is_valid.
    destruct HmX as [[i [[im Him] Hi]] | Hseed]; [| by right].
    simpl in Hi. subst im.
    cbn. unfold composite_initial_message_prop.
    left. exists i.
    assert (Hm : vinitial_message_prop (IM2 i) m).
    + eapply same_VLSM_initial_message_preservation; eauto.
    + by exists (exist _ m Hm).
Qed.

End pre_loaded_constrained.

Lemma same_IM_preloaded_free_full_projection
  : VLSM_full_projection
    (pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM1))
    (pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM2))
    same_IM_label_rew
    same_IM_state_rew.
Proof.
  constructor.
  intros s1 tr1 Htr1.
  specialize (pre_loaded_with_all_messages_vlsm_is_pre_loaded_with_True (free_composite_vlsm IM1)) as Heq1.
  apply (VLSM_eq_finite_valid_trace Heq1) in Htr1.
  clear Heq1.
  specialize (same_IM_full_projection (free_constraint IM1) (free_constraint IM2))
    as Hproj.
  spec Hproj; [done |].
  specialize (Hproj (fun _ => True)).
  apply (VLSM_full_projection_finite_valid_trace Hproj) in Htr1.
  specialize (pre_loaded_with_all_messages_vlsm_is_pre_loaded_with_True (free_composite_vlsm IM2)) as Heq2.
  by apply (VLSM_eq_finite_valid_trace Heq2).
Qed.

End sec_same_IM_full_projection.

Arguments same_IM_label_rew {_ _ _ _} _ _ : assert.
Arguments same_IM_state_rew {_ _ _ _} _ _ _ : assert.

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
    cvt_transition : composite_transition IM l (s1, iom) = (s2, oom)
  }.

Definition composite_valid_transition_item
  (s : composite_state IM) (item : composite_transition_item IM) : Prop :=
  CompositeValidTransition (l item) s (input item) (destination item) (output item).

Lemma composite_valid_transition_reachable_iff l s1 iom s2 oom :
  CompositeValidTransition l s1 iom s2 oom <-> ValidTransition RFree l s1 iom s2 oom.
Proof. by firstorder. Qed.

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
  intros [i li] * [Hv Ht]; cbn in Ht; destruct (vtransition _ _ _) eqn:Hti.
  by inversion Ht; subst; cbn; rewrite state_update_eq; repeat split.
Qed.

Lemma composite_valid_transition_projection_inv :
  forall i li si1 iom si2 oom,
    ValidTransition (IM i) li si1 iom si2 oom ->
    forall s1, s1 i = si1 -> forall s2, s2 = state_update IM s1 i si2 ->
    CompositeValidTransition (existT i li) s1 iom s2 oom.
Proof.
  intros * [Hv Ht] s1 <- s2 ->; split; [done |].
  by cbn; replace (vtransition _ _ _) with (si2, oom).
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

Section sec_composite_history_vlsm.

Context
  {message : Type}
  `{EqDecision index}
  (IM : index -> VLSM message)
  `{forall i, HistoryVLSM (IM i)}
  (Free := free_composite_vlsm IM)
  (RFree := pre_loaded_with_all_messages_vlsm Free)
  .

Lemma not_CompositeValidTransitionNext_initial :
  forall s2, composite_initial_state_prop IM s2 ->
  forall s1, ~ CompositeValidTransitionNext IM s1 s2.
Proof.
  intros s2 Hs2 s1 [* Hs1].
  apply composite_valid_transition_projection, proj1, valid_transition_next in Hs1; cbn in Hs1.
  by contradict Hs1; apply not_ValidTransitionNext_initial, Hs2.
Qed.

Lemma composite_quasi_unique_transition_to_state :
  forall [s],
  forall [l1 s1 iom1 oom1], CompositeValidTransition IM l1 s1 iom1 s oom1 ->
  forall [l2 s2 iom2 oom2], CompositeValidTransition IM l2 s2 iom2 s oom2 ->
  projT1 l1 = projT1 l2 ->
  l1 = l2 /\ s1 = s2 /\ iom1 = iom2 /\ oom1 = oom2.
Proof.
  intros ? [i li1] * Ht1 [_i li2] * Ht2 [=]; subst _i.
  apply composite_valid_transition_projection in Ht1, Ht2; cbn in Ht1, Ht2.
  destruct Ht1 as [Ht1 Heq_s], Ht2 as [Ht2 Heqs].
  rewrite Heq_s in Heqs at 1; clear Heq_s.
  specialize (unique_transition_to_state Ht1 Ht2) as Heq;
    destruct_and! Heq; subst; repeat split.
  extensionality j; destruct (decide (i = j)); [by subst |].
  apply f_equal with (f := fun s => s j) in Heqs.
  by rewrite !state_update_neq in Heqs.
Qed.

Lemma CompositeValidTransition_reflects_rechability :
  forall l s1 iom s2 oom,
  CompositeValidTransition IM l s1 iom s2 oom ->
  valid_state_prop RFree s2 ->
  input_valid_transition RFree l (s1, iom) (s2, oom).
Proof.
  intros * Hnext Hs2; revert l s1 iom oom Hnext.
  induction Hs2 using valid_state_prop_ind; intros * Hnext.
  - apply composite_valid_transition_next in Hnext.
    by contradict Hnext; apply not_CompositeValidTransitionNext_initial.
  - destruct l as [i li], l0 as [j lj].
    destruct (decide (i = j)).
    + subst; apply input_valid_transition_forget_input in Ht as Hvt.
      apply composite_valid_transition_reachable_iff in Hvt.
      specialize (composite_quasi_unique_transition_to_state Hnext Hvt eq_refl) as Heq.
      by destruct_and! Heq; simplify_eq.
    + apply input_valid_transition_forget_input in Ht as Hti.
      apply composite_valid_transition_reachable_iff,
        composite_valid_transition_projection in Hti;
        cbn in Hti; destruct Hti as [[Hvi Hti] Heqs'].
      apply composite_valid_transition_projection in Hnext;
        cbn in Hnext; destruct Hnext as [[Hvj Htj] Heq_s'].
      rewrite Heq_s', state_update_neq in Heqs' by done.
      specialize (IHHs2 (existT j lj) (state_update IM s j (s1 j)) iom oom).
      spec IHHs2.
      {
        apply composite_valid_transition_projection_inv with (s1 j) (s' j).
        - by split.
        - by apply state_update_eq.
        - rewrite state_update_twice.
          symmetry; apply state_update_id.
          apply f_equal with (f := fun s => s j) in Heqs'.
          by rewrite state_update_eq, state_update_neq in Heqs'.
      }
      assert (Hss1 : input_valid_transition RFree (existT i li)
                  (state_update IM s j (s1 j), om) (s1, om')).
      {
        repeat split; [apply IHHs2 | apply any_message_is_valid_in_preloaded |..].
        - by cbn; rewrite state_update_neq.
        - cbn; rewrite state_update_neq by done.
          replace (vtransition _ _ _) with (s' i, om').
          f_equal; extensionality k; apply f_equal with (f := fun s => s k) in Heqs'.
          destruct (decide (i = k)); [|destruct (decide (j = k))].
          + by subst; rewrite state_update_eq, Heq_s', state_update_neq.
          + by subst; rewrite state_update_neq, state_update_eq.
          + by rewrite !state_update_neq in Heqs' |- *.
      }
      repeat split; cbn.
      * by eapply input_valid_transition_destination.
      * by apply any_message_is_valid_in_preloaded.
      * done.
      * by replace (vtransition _ _ _) with (s' j, oom); f_equal.
Qed.

Lemma CompositeValidTransitionNext_reflects_rechability :
  forall s1 s2, CompositeValidTransitionNext IM s1 s2 ->
    valid_state_prop RFree s2 -> valid_state_prop RFree s1.
Proof.
  by intros s1 s2 []; eapply CompositeValidTransition_reflects_rechability.
Qed.

Lemma composite_valid_transition_future_reflects_rechability :
  forall s1 s2, composite_valid_transition_future IM s1 s2 ->
    valid_state_prop RFree s2 -> valid_state_prop RFree s1.
Proof. by apply tc_reflect, CompositeValidTransitionNext_reflects_rechability. Qed.

Lemma composite_valid_transitions_from_to_reflects_reachability :
  forall s s' tr,
  CompositeValidTransitionsFromTo IM s s' tr ->
  valid_state_prop RFree s' -> finite_valid_trace_from_to RFree s s' tr.
Proof.
  induction 1; intros; [by constructor |].
  assert (Hitem : input_valid_transition RFree (l item) (s', input item)
                          (destination item, output item))
    by (apply CompositeValidTransition_reflects_rechability; done).
  eapply finite_valid_trace_from_to_app.
  - apply IHCompositeValidTransitionsFromTo.
    by eapply input_valid_transition_origin.
  - by destruct item; apply finite_valid_trace_from_to_singleton.
Qed.

End sec_composite_history_vlsm.
