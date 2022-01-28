From stdpp Require Import prelude.
From Coq Require Import Streams FunctionalExtensionality FinFun Eqdep.
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
          {index : Type}
          {IndEqDec : EqDecision index}
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
    Definition _composite_state : Type :=
      forall n : index, vstate (IM n).

(**
A [composite_label] is a pair between an index <<N>> and a [label] of <<IT n>>.

Note that the [composite_label] type is the dependent sum of the family of
types <<[@label _ (IT n) | n <- index]>>.
*)
    Definition _composite_label
      : Type
      := sigT (fun n => vlabel (IM n)).

    Definition composite_type : VLSMType message :=
      {| state := _composite_state
       ; label := _composite_label
      |}.

    Definition composite_state := @state message composite_type.
    Definition composite_label := @label message composite_type.
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
      unfold state_update. destruct (decide (j = i)); try contradiction. reflexivity.
    Qed.

    Lemma state_update_eq
               (s : composite_state)
               (i : index)
               (si : vstate (IM i))
      : state_update s i si i = si.
    Proof.
      unfold state_update.
      unfold decide, decide_rel.
      rewrite eq_dec_refl. reflexivity.
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
      - apply state_update_neq. assumption.
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
      - repeat rewrite state_update_neq; try assumption.
        reflexivity.
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
      ; repeat (rewrite state_update_eq ; try (rewrite state_update_neq; try assumption))
      ; try reflexivity.
      repeat (rewrite state_update_neq; try assumption).
      reflexivity.
    Qed.
  End composite_type.

  Section composite_sig.
(** ** The signature of a composite VLSM

Assume an non-empty <<index>> type and let <<IT>> be
an <<index>>ed family of [VLSMType]s, and for each index <<i>>, let <<IS i>> be
a [VLSMSign]ature of type <<IT i>>.
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
      intro i. destruct (vs0 (IM i)) as [s Hs]. assumption.
    Defined.

    Global Instance composite_initial_state_inh : Inhabited composite_initial_state :=
      {| inhabitant := composite_s0 |}.

(**
A message has the [initial_message_prop]erty in the [composite_sig]nature
iff it has the [initial_message_prop]erty in any of the component signatures.
*)
    Definition composite_initial_message_prop (m : message) : Prop
      :=
        exists (n : index) (mi : vinitial_message (IM n)), proj1_sig mi = m.

    Definition option_composite_initial_message_prop : option message -> Prop
      := from_option composite_initial_message_prop True.

    Definition composite_sig
      : VLSMSign composite_type
      :=
        {|   initial_state_prop := composite_initial_state_prop
           ; initial_message_prop := composite_initial_message_prop
        |}.

(**
We can always "lift" state <<sj>> from component <<j>> to a composite state by
updating an initial composite state, say [s0], to <<sj>> on component <<j>>.
*)
    Definition lift_to_composite_label
      (j : index)
      (lj : vlabel (IM j))
      : composite_label
      := existT j lj.

    Definition lift_to_composite_state
      (j : index)
      (sj : vstate (IM j))
      (s0X := proj1_sig composite_s0)
      : composite_state
      := state_update s0X j sj.

    Definition lift_to_composite_transition_item
      (j : index)
      (item : vtransition_item (IM j))
      (s0X := proj1_sig composite_s0)
      : @transition_item _ composite_type.
    Proof.
      destruct item.
      split.
      - exact (existT j l).
      - exact input.
      - exact (lift_to_composite_state j destination).
      - exact output.
    Defined.

    Definition lift_to_composite_state'
      (s : composite_state)
      (j : index)
      (sj : vstate (IM j))
      : composite_state
      := state_update s j sj.

    Definition lift_to_composite_transition_item'
      (s : composite_state)
      (j : index)
      (item : vtransition_item (IM j))
      : @transition_item _ composite_type.
    Proof.
      destruct item.
      split.
      - exact (existT j l).
      - exact input.
      - exact (lift_to_composite_state' s j destination).
      - exact output.
    Defined.

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

  End composite_sig.

  Section sec_composite_vlsm.
(** ** Constrained VLSM composition

Assume an non-empty <<index>> type, let
<<IT>> be an <<index>>ed family of [VLSMType]s, and for each index <<i>>, let
<<IS i>> be a [VLSMSign]ature of type <<IT i>> and <<IM i>> be a VLSM of
signature <<IS i>>.
*)

(**
The [transition] function for the [composite_vlsm] is defined as follows
takes a transition in the VLSM corresponding to the given [composite_label]
and returnes the produced message together with the state updated on that
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
      : VLSMClass composite_sig
      :=
      {|  transition := composite_transition
       ;  valid := constrained_composite_valid constraint
      |}.

    Definition composite_vlsm
      (constraint : composite_label -> composite_state * option message -> Prop)
      : VLSM message
      := mk_vlsm (composite_vlsm_machine constraint).

    Lemma composite_transition_state_neq
      {constraint : composite_label -> composite_state * option message -> Prop}
      (l : composite_label)
      (s s' : composite_state)
      (om om' : option message)
      (Ht : input_valid_transition (composite_vlsm constraint) l (s, om) (s', om'))
      (i : index)
      (Hi : i <> projT1 l)
      : s' i = s i.
    Proof.
      destruct Ht as [_ Ht]. simpl in Ht. destruct l as (il, l). simpl in Hi.
      destruct (vtransition (IM il) l (s il, om)) as (si', omi') eqn:Ht'.
      inversion Ht. subst omi'. apply state_update_neq. assumption.
    Qed.

    Lemma composite_transition_state_eq
      {constraint : composite_label -> composite_state * option message -> Prop}
      (l : composite_label)
      (s s' : composite_state)
      (om om' : option message)
      (Ht : input_valid_transition (composite_vlsm constraint) l (s, om) (s', om'))
      (il := projT1 l)
      : s' il = fst (vtransition (IM il) (projT2 l) (s il, om)).
    Proof.
      destruct Ht as [_ Ht]. simpl in Ht.
      unfold il in *. clear il. destruct l as (il, l). simpl.
      destruct (vtransition (IM il) l (s il, om)) as (si', omi') eqn:Ht'.
      inversion Ht. apply state_update_eq.
    Qed.

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

  Lemma lift_to_composite_state_initial
    (j : index)
    (sj : vstate (IM j))
    (Hinitj : vinitial_state_prop (IM j) sj)
    : composite_initial_state_prop (lift_to_composite_state j sj).
  Proof.
    intro i.
    unfold lift_to_composite_state.
    destruct (decide (i = j)).
    - subst. rewrite state_update_eq. assumption.
    - rewrite state_update_neq; try assumption.
      simpl.
      destruct (vs0 _) as [s Hs].
      assumption.
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
      : VLSM_full_projection (IM j) free_composite_vlsm (lift_to_composite_label j) (lift_to_composite_state j).
    Proof.
      apply basic_VLSM_strong_full_projection; intro; intros.
      - split; [|exact I]. simpl.
        unfold lift_to_composite_state. rewrite state_update_eq. apply H.
      - unfold vtransition. simpl. unfold lift_to_composite_state at 1.
        rewrite state_update_eq. replace (vtransition _ _ _) with (s', om').
        f_equal. unfold lift_to_composite_state. apply state_update_twice.
      - apply lift_to_composite_state_initial. assumption.
      - exists j, (exist _ _ H). reflexivity.
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
      apply basic_VLSM_strong_incl; intro; intros; [assumption..| |assumption].
      split; [apply H|exact I].
    Qed.

    Lemma composite_pre_loaded_vlsm_incl_pre_loaded_with_all_messages
      (constraint : composite_label -> composite_state  * option message -> Prop)
      (P : message -> Prop)
      : VLSM_incl (pre_loaded_vlsm (composite_vlsm constraint) P) (pre_loaded_with_all_messages_vlsm free_composite_vlsm).
    Proof.
      apply basic_VLSM_strong_incl; cbv; intuition.
    Qed.

    Lemma constraint_free_valid_state_message_preservation
      (constraint : composite_label -> composite_state * option message -> Prop)
      s om
      (Hsom : valid_state_message_prop (composite_vlsm constraint) s om)
      : valid_state_message_prop free_composite_vlsm s om.
    Proof.
      revert Hsom.
      apply (VLSM_incl_valid_state_message (constraint_free_incl constraint)); intro; intros; assumption.
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
      apply basic_VLSM_incl; intro; intros.
      - assumption.
      - apply initial_message_is_valid. assumption.
      - split; [apply Hv | auto].
      - apply H.
    Qed.

    Lemma constraint_subsumption_input_valid
      (Hsubsumption : input_valid_constraint_subsumption constraint1 constraint2)
      (l : label)
      (s : state)
      (om : option message)
      (Hv : input_valid X1 l (s, om))
      : vvalid X2 l (s, om).
    Proof.
      split; [apply Hv|apply Hsubsumption]. assumption.
    Qed.

    Lemma constraint_subsumption_valid_state_message_preservation
      (Hsubsumption : input_valid_constraint_subsumption constraint1 constraint2)
      (s : state)
      (om : option message)
      (Hps : valid_state_message_prop X1 s om)
      : valid_state_message_prop X2 s om.
    Proof.
      induction Hps.
      - apply (valid_initial_state_message X2);assumption.
      - apply (valid_generated_state_message X2) with s _om _s om l; try assumption.
        apply constraint_subsumption_input_valid; [assumption|].
        split;[|split];[exists _om|exists _s|];assumption.
    Qed.

    Lemma constraint_subsumption_incl
      (Hsubsumption : input_valid_constraint_subsumption constraint1 constraint2)
      : VLSM_incl X1 X2.
    Proof.
      apply basic_VLSM_incl; intro; intros.
      - assumption.
      - apply initial_message_is_valid. assumption.
      - apply constraint_subsumption_input_valid; assumption.
      - apply H.
    Qed.

    Lemma preloaded_constraint_subsumption_input_valid
      (Hpre_subsumption : preloaded_constraint_subsumption constraint1 constraint2)
      (l : label)
      (s : state)
      (om : option message)
      (Hv : input_valid (pre_loaded_with_all_messages_vlsm X1) l (s, om))
      : vvalid X2 l (s, om).
    Proof.
      split; [apply Hv|apply Hpre_subsumption]. assumption.
    Qed.

    Lemma preloaded_constraint_subsumption_incl
      (Hpre_subsumption : preloaded_constraint_subsumption constraint1 constraint2)
      : VLSM_incl (pre_loaded_with_all_messages_vlsm X1) (pre_loaded_with_all_messages_vlsm X2).
    Proof.
      apply basic_VLSM_incl; intro; intros; [assumption| | |apply H].
      - apply initial_message_is_valid. assumption.
      - apply preloaded_constraint_subsumption_input_valid; assumption.
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
      apply preloaded_constraint_subsumption_incl.
      intro; intros; exact I.
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
      : VLSM_full_projection (pre_loaded_vlsm (IM j) P) (pre_loaded_vlsm free_composite_vlsm Q) (lift_to_composite_label j) (lift_to_composite_state j).
    Proof.
      apply basic_VLSM_full_projection_preloaded_with; intro; intros.
      - revert m H. assumption.
      - split; [|exact I]. simpl.
        unfold lift_to_composite_state. rewrite state_update_eq. apply H.
      - unfold vtransition. simpl. unfold lift_to_composite_state at 1.
        rewrite state_update_eq. replace (vtransition (IM j) l _) with (s', om').
        f_equal. unfold lift_to_composite_state. apply state_update_twice.
      - apply lift_to_composite_state_initial. assumption.
      - exists j, (exist _ _ H); reflexivity.
    Qed.

    Lemma lift_to_composite_preloaded_vlsm_full_projection
      (j : index)
      : VLSM_full_projection (pre_loaded_with_all_messages_vlsm (IM j)) (pre_loaded_with_all_messages_vlsm free_composite_vlsm) (lift_to_composite_label j) (lift_to_composite_state j).
    Proof.
      apply basic_VLSM_full_projection_preloaded.
      - intro; intros. split; [|exact I]. simpl.
        unfold lift_to_composite_state. rewrite state_update_eq. apply H.
      - intro; intros. unfold vtransition. simpl. unfold vtransition. simpl. unfold lift_to_composite_state at 1.
        rewrite state_update_eq. replace (transition l _) with (s', om').
        f_equal. unfold lift_to_composite_state. apply state_update_twice.
      - intro; intros. apply lift_to_composite_state_initial. assumption.
    Qed.

    Lemma valid_state_preloaded_composite_free_lift
      (j : index)
      (sj : vstate (IM j))
      (Hp : valid_state_prop (pre_loaded_with_all_messages_vlsm (IM j)) sj)
      : valid_state_prop (pre_loaded_with_all_messages_vlsm free_composite_vlsm) (lift_to_composite_state j sj).
    Proof.
      apply (VLSM_full_projection_valid_state (lift_to_composite_preloaded_vlsm_full_projection j))
      ; assumption.
    Qed.

    Lemma can_emit_composite_free_lift
      (P Q : message -> Prop)
      (PimpliesQ : forall m, P m -> Q m)
      (j : index)
      (m : message)
      (Htrj : can_emit (pre_loaded_vlsm (IM j) P) m)
      : can_emit (pre_loaded_vlsm free_composite_vlsm Q) m.
    Proof.
      apply (VLSM_full_projection_can_emit (lift_to_composite_generalized_preloaded_vlsm_full_projection _ _ PimpliesQ j)).
      assumption.
    Qed.

    (** Updating a composite initial state with a component initial state
    yields a composite initial state *)
    Lemma composite_free_update_initial_state_with_initial
      (s : vstate free_composite_vlsm)
      (Hs : vinitial_state_prop free_composite_vlsm s)
      (i : index)
      (si : vstate (IM i))
      (Hsi : vinitial_state_prop (IM i) si)
      : vinitial_state_prop free_composite_vlsm (state_update s i si).
    Proof.
      intro j. destruct (decide (j = i)).
      - subst. rewrite state_update_eq. assumption.
      - rewrite state_update_neq; try assumption. apply Hs.
    Qed.

    (** Updating a composite [valid_state] for the free composition with
    a component initial state yields a composite [valid_state] *)
    Lemma composite_free_update_state_with_initial
      (s : vstate free_composite_vlsm)
      (Hs : valid_state_prop free_composite_vlsm s)
      (i : index)
      (si : vstate (IM i))
      (Hsi : vinitial_state_prop (IM i) si)
      : valid_state_prop free_composite_vlsm (state_update s i si).
    Proof.
      generalize dependent s. apply valid_state_prop_ind; intros.
      - remember (state_update s i si) as s'.
        assert (Hs' : vinitial_state_prop free_composite_vlsm s')
          by (subst; apply composite_free_update_initial_state_with_initial; assumption).
        apply initial_state_is_valid.
        assumption.
      - destruct Ht as [[Hps [Hom Hv]] Ht].
        unfold transition in Ht. simpl in Ht.
        destruct Hv as [Hv _]. simpl in Hv.
        destruct l as (j, lj).
        destruct (vtransition (IM j) lj (s j, om)) as (sj', omj') eqn:Htj.
        inversion Ht. subst s' om'. clear Ht.
        destruct (decide (i = j)).
        + subst. rewrite state_update_twice. assumption.
        + rewrite state_update_twice_neq; try assumption.
          destruct Hs as [_om Hs].
          destruct Hom as [_s Hom].
          specialize
            (valid_generated_state_message free_composite_vlsm _ _ Hs _ _ Hom  (existT j lj))
            as Hgen.
          assert (n' : j <> i) by (intro contra; subst; elim n; reflexivity).
          spec Hgen.
          { split; try exact I. simpl. rewrite state_update_neq; assumption. }
          simpl in Hgen.
          rewrite state_update_neq in Hgen; try assumption. simpl in *.
          rewrite Htj in Hgen.
          eexists _. apply Hgen. reflexivity.
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
      apply preloaded_protocol_generated with lj (s i) om _om';[assumption| |assumption].
      apply Hv.
    + rewrite state_update_neq by assumption.
      exact IHHproto1.
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
  apply preloaded_weaken_valid_state_message_prop.
  assumption.
Qed.

Lemma composite_transition_project_active
      message `{EqDecision index} (IM : index -> VLSM message)
  : forall (l : label) (s : state) (im : option message) (s' : state) (om : option message),
      composite_transition IM l (s, im) = (s', om) ->
      vtransition (IM (projT1 l)) (projT2 l) (s (projT1 l), im) = (s' (projT1 l), om).
Proof.
  intros.
  destruct l;simpl.
  simpl in H.
  destruct (vtransition (IM x) v (s x, im)).
  inversion H.
  f_equal.
  rewrite state_update_eq.
  reflexivity.
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
  - apply composite_transition_project_active in Htrans;assumption.
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
    split;[reflexivity|].
    revert Hptrans.
    apply input_valid_transition_preloaded_project_active.
  - left.
    destruct Hptrans as [Hpvalid Htrans].
    cbn in Htrans.
    destruct (vtransition (IM j) lj (s j, im)).
    inversion_clear Htrans.
    rewrite state_update_neq by assumption.
    reflexivity.
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

(** If a message can be emitted by a composition, then it can be emited by one of the
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

  Global Instance binary_index_dec :  EqDecision binary_index := _.
  Global Instance binary_index_inhabited : Inhabited binary_index
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
  {index : Type}
  {IndEqDec : EqDecision index}
  (IM : index -> VLSM message)
  {index_listing : list index}
  (finite_index : Listing index_listing).

Lemma composite_decidable_initial_message
  (Hdec_init : forall i, vdecidable_initial_messages_prop (IM i))
  : decidable_initial_messages_prop (composite_sig IM).
Proof.
  intro m. simpl. unfold composite_initial_message_prop.
  apply
    (Decision_iff
      (P := List.Exists (fun i => vinitial_message_prop (IM i) m) index_listing)
    ).
  - rewrite <- exists_finite by (apply finite_index).
    split; intros [i Hm]; exists i.
    + exists (exist _ _ Hm). reflexivity.
    + destruct Hm as [[im Hinit] Him]. subst. assumption.
  - apply @Exists_dec. intro i. apply Hdec_init.
Qed.

End composite_decidable_initial_message.

Section composite_plan_properties.

  Context {message : Type}
          {index : Type}
          {IndEqDec : EqDecision index}
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
    split; [intuition|intuition|..].
    unfold valid in *; simpl in *.
    unfold constrained_composite_valid in *.
    unfold composite_valid in *.
    unfold free_constraint in *; simpl.
    unfold vvalid in *.
    destruct l.
    simpl in i.
    unfold i in Heq.
    rewrite <- Heq.
    assumption.
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
    destruct (vtransition (IM x) v (s' x, input)); [intuition|..].
    unfold i.
    rewrite state_update_eq.
    rewrite state_update_eq.
    reflexivity.
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
        all : intuition.
      }

      apply finite_valid_trace_from_extend.
      apply finite_valid_trace_from_empty.
      apply input_valid_transition_destination in Ht'; assumption.
      assumption.
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
      intuition.
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
    rewrite state_update_neq.
    reflexivity.
    assumption.
  Qed.

  (* Same as the previous result, but for multiple transitions. *)

  Lemma irrelevant_components
    (s : state)
    (a : composite_plan IM)
    (a_indices := List.map (@projT1 _ _) (List.map (@label_a _ _) a))
    (i : index)
    (Hdif : i ∉ a_indices) :
    let res := snd (composite_apply_plan IM s a) in
    (res i) = (s i).
  Proof.
    induction a using rev_ind.
    - simpl; intuition.
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
        left.
        assumption.
      }

      rewrite <- IHa.
      replace sx with (snd (composite_apply_plan IM sa [x])) by (rewrite eq_x; reflexivity).
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
    (Heq : forall (i : index), i ∈ li -> (s' i) = (s i))
    (Hincl : a_indices ⊆ li)
    (Hpr : finite_valid_plan_from Free s a) :
    let res' := snd (apply_plan Free s' a) in
    let res := snd (apply_plan Free s a) in
    finite_valid_plan_from Free s' a /\
    (forall (i : index), i ∈ li -> (res' i) = res i).
  Proof.
    induction a using rev_ind.
    - split.
      apply finite_valid_plan_empty.
      assumption.
      simpl. assumption.
    - simpl in *.
      apply finite_valid_plan_from_app_iff in Hpr.
      destruct Hpr as [Hrem Hsingle].

      spec IHa. {
        remember (List.map (@projT1 _ (fun n : index => vlabel (IM n))) (List.map label_a a)) as small.
        transitivity a_indices.
        unfold a_indices.
        intros e H; simpl.
        rewrite 2 map_app, elem_of_app.
        left; assumption.
        intuition.
      }

      spec IHa. {
        assumption.
      }

      destruct IHa as [IHapr IHaind].

      specialize (relevant_components_one (snd (apply_plan Free s a)) (snd (apply_plan Free s' a))) as Hrel.

      spec Hrel. {
        apply apply_plan_last_valid.
        all : intuition.
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
        split; intuition.
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
        * rewrite e; intuition.
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
          setoid_rewrite Hdiff0.
          assumption.
  Qed.

End composite_plan_properties.

Section empty_composition_properties.

Context {message : Type}
  {index : Type}
  {IndEqDec : EqDecision index}
  (IM : index -> VLSM message)
  (constraint : composite_label IM -> composite_state IM * option message -> Prop)
  (X := composite_vlsm IM constraint)
  (index_listing : list index)
  (finite_index : Listing index_listing)
  (Hempty_index : index_listing = [])
  .

Lemma empty_composition_no_index
  (i : index)
  : False.
Proof.
  specialize (proj2 finite_index i) as Hin.
  subst index_listing. contradiction.
Qed.

Lemma empty_composition_single_state
  (s : composite_state IM)
  : s = (proj1_sig (composite_s0 IM)).
Proof.
  apply functional_extensionality_dep_good.
  intro i. elim (empty_composition_no_index i).
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
  intros m [s' [l _]].
  elim (empty_composition_no_label l).
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
  intros m [s' [l _]].
  elim (empty_composition_no_label l).
Qed.

Lemma pre_loaded_with_all_empty_composition_no_emit
  : forall m, ~ can_emit (pre_loaded_with_all_messages_vlsm X) m.
Proof.
  intros m [s' [l _]].
  elim (empty_composition_no_label l).
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
    + apply (VLSM_incl_valid_state
              (composite_pre_loaded_vlsm_incl_pre_loaded_with_all_messages IM1 constraint1 seed)).
      assumption.
    + split; [|assumption].
      clear Hc. revert Hv. destruct l as (i, li). cbn.
      apply same_VLSM_valid_preservation.
  - apply proj2 in H. revert H. destruct l as (i, li). cbn.
    destruct (vtransition (IM1 i) _ _) as (si'1, _om') eqn: Ht1.
    unfold same_IM_state_rew at 1.
    erewrite same_VLSM_transition_preservation; [|eassumption].
    inversion 1; subst; clear H.
    f_equal. extensionality j.
    unfold same_IM_state_rew at 2.
    destruct (decide (i = j)).
    + subst. rewrite !state_update_eq. reflexivity.
    + rewrite !state_update_neq by congruence. reflexivity.
  - intros i. apply same_VLSM_initial_state_preservation, H.
  - apply initial_message_is_valid.
    destruct HmX as [[i [[im Him] Hi]] | Hseed]; [| right; assumption].
    simpl in Hi. subst im.
    cbn. unfold composite_initial_message_prop.
    left. exists i.
    assert (Hm : vinitial_message_prop (IM2 i) m).
    + eapply same_VLSM_initial_message_preservation; eauto.
    + exists (exist _ m Hm). reflexivity.
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
  spec Hproj. { intros. exact I. }
  specialize (Hproj (fun _ => True)).
  apply (VLSM_full_projection_finite_valid_trace Hproj) in Htr1.
  specialize (pre_loaded_with_all_messages_vlsm_is_pre_loaded_with_True (free_composite_vlsm IM2)) as Heq2.
  apply (VLSM_eq_finite_valid_trace Heq2).
  assumption.
Qed.

End sec_same_IM_full_projection.

Arguments same_IM_label_rew {_ _ _ _} _ _ : assert.
Arguments same_IM_state_rew {_ _ _ _} _ _ _ : assert.
