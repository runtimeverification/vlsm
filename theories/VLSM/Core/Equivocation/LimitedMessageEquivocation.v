From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude finite.
From Coq Require Import FinFun RIneq.
From VLSM.Lib Require Import Preamble Measurable StdppListSet RealsExtras ListSetExtras.
From VLSM.Core Require Import VLSM VLSMProjections MessageDependencies Composition Equivocation Equivocation.FixedSetEquivocation Equivocation.TraceWiseEquivocation.
From VLSM.Core Require Import Equivocation.WitnessedEquivocation.

(** * VLSM Limited Message Equivocation

In this section we define the notion of limited (message-based) equivocation.

This notion is slightly harder to define than that of fixed-set equivocation,
because, while for the latter we fix a set and let only the nodes belonging to
that set to equivocate, in the case of limited equivocation, the set of nodes
equivocating can change dynamically, each node being virtually allowed to
equivocate as long as the weight of all nodes currently equivocating does
not pass a certain threshold.

As we need to be able to measure the amount of equivocation in a given state
to design a composition constraint preventing equivocation weight from passing
the threshold, we need an appropriate measure of equivocation.
We here choose [is_equivocating_tracewise] as this measure.

Moreover, to further limit the amount of equivocation allowed when producing
a message, we assume a full-node-like  condition to be satisfied by all nodes.
This  guarantees that whenever a message not-previously send is received in a
state, the amount of equivocation would only grow with the weight of the
sender of the message (if that wasn't already known as an equivocator).
*)

Section sec_limited_message_equivocation.

Context
  {message : Type}
  `{EqDecision index}
  `{ReachableThreshold validator}
  (IM : index -> VLSM message)
  (equivocating : composite_state IM -> validator -> Prop)
  (Hno_initial_equivocation :
    forall s, composite_initial_state_prop IM s ->
    forall v, ~ equivocating s v)
  .

Inductive LimitedEquivocationProp (s : composite_state IM) : Prop :=
  limited_equivocation :
    forall (vs : set validator)
      (Hnodup_vs : NoDup vs)
      (Heqv_vs : forall v, equivocating s v -> v ∈ vs)
      (Hlimited : (sum_weights vs <= proj1_sig threshold)%R),
      LimitedEquivocationProp s.

Definition limited_equivocation_constraint
  (l : composite_label IM)
  (som : composite_state IM * option message)
  : Prop :=
  LimitedEquivocationProp (composite_transition IM l som).1.

Definition limited_equivocation_composite_vlsm : VLSM message :=
  composite_vlsm IM limited_equivocation_constraint.

Lemma limited_equivocation_valid_state s
  : valid_state_prop limited_equivocation_composite_vlsm s ->
    LimitedEquivocationProp s.
Proof.
  intros Hs; apply valid_state_prop_iff in Hs
    as [[[is His] ->] | (l & [s' om'] & om & [(_ & _ & _ & Hv) Ht])].
  - exists []; [constructor |..].
    + by intros v Hv; contradict Hv; apply Hno_initial_equivocation.
    + by destruct threshold; apply Rge_le.
  - by cbv in Hv, Ht; rewrite Ht in Hv.
Qed.

End sec_limited_message_equivocation.

Section sec_basic_limited_message_equivocation.

Context
  {message : Type}
  `{EqDecision index}
  `{EqDecision validator}
  (IM : index -> VLSM message)
  `{BasicEquivocation (composite_state IM) validator}
  .

Definition basic_limited_equivocation_constraint :=
  limited_equivocation_constraint IM is_equivocating.

Definition basic_limited_equivocation_composite_vlsm : VLSM message :=
  limited_equivocation_composite_vlsm IM is_equivocating.

Lemma LimitedEquivocationProp_impl_not_heavy :
  forall s, LimitedEquivocationProp IM is_equivocating s -> not_heavy s.
Proof.
  intros s [].
  apply Rle_trans with (sum_weights vs); [| done].
  apply sum_weights_subseteq.
  - apply NoDup_elements.
  - apply Hnodup_vs.
  - intros v Hv; apply Heqv_vs; apply elem_of_elements, elem_of_filter in Hv;
    destruct Hv as [Hsv _]; by apply Hsv.
Qed.

Definition basic_equivocation_state_validators_comprehensive_prop : Prop :=
  forall s v, is_equivocating s v -> v ∈ state_validators s.

Lemma not_heavy_impl_LimitedEquivocationProp
  (Hcomprehensive : basic_equivocation_state_validators_comprehensive_prop)
  : forall s, not_heavy s -> LimitedEquivocationProp IM is_equivocating s.
Proof.
  intros s Hs; exists (elements(equivocating_validators s));
    [apply NoDup_elements | | done].
  intros v Hv; apply elem_of_elements, elem_of_filter; split; [done |].
  by apply Hcomprehensive.
Qed.

End sec_basic_limited_message_equivocation.

Section tracewise_limited_message_equivocation.

Context
  {message : Type}
  `{finite.Finite index}
  `{ReachableThreshold index}
  (IM : index -> VLSM message)
  `{forall i, HasBeenSentCapability (IM i)}
  `{forall i, HasBeenReceivedCapability (IM i)}
  (Free := free_composite_vlsm IM)
  (sender : message -> option index)
  `{RelDecision _ _ (is_equivocating_tracewise_no_has_been_sent IM id sender)}
  `{FinSet index Ci}
  (Htracewise_BasicEquivocation : BasicEquivocation (composite_state IM) index Ci
    := equivocation_dec_tracewise IM id sender)
  .

Existing Instance Htracewise_BasicEquivocation.

Lemma tracewise_basic_equivocation_state_validators_comprehensive_prop :
  basic_equivocation_state_validators_comprehensive_prop IM.
Proof. intros s v _; cbn; apply elem_of_list_to_set, elem_of_enum. 
Qed.

Definition tracewise_limited_equivocation_constraint :=
  basic_limited_equivocation_constraint IM.

Definition tracewise_limited_equivocation_vlsm_composition : VLSM message :=
  basic_limited_equivocation_composite_vlsm IM.

Lemma full_node_limited_equivocation_valid_state_weight s
  : valid_state_prop tracewise_limited_equivocation_vlsm_composition s ->
    LimitedEquivocationProp IM is_equivocating s.
Proof.
  apply limited_equivocation_valid_state.
  by intros; apply initial_state_not_is_equivocating_tracewise.
Qed.

Lemma tracewise_not_heavy_LimitedEquivocationProp_iff :
  forall s, not_heavy s <-> LimitedEquivocationProp IM is_equivocating s.
Proof.
  intros; split.
  - apply not_heavy_impl_LimitedEquivocationProp,
      tracewise_basic_equivocation_state_validators_comprehensive_prop.
  - apply LimitedEquivocationProp_impl_not_heavy.
Qed.

End tracewise_limited_message_equivocation.

Section fixed_limited_message_equivocation.

(** ** Fixed Message Equivocation implies Limited Message Equivocation

In this section we show that if the set of allowed equivocators for a fixed
equivocation constraint is of weight smaller than the threshold accepted for
limited message equivocation, then any valid trace for the fixed equivocation
constraint is also a trace under the limited equivocation constraint.
*)

Context
  `{FinSet index Ci}
  {message : Type}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  `{forall i, HasBeenSentCapability (IM i)}
  `{forall i, HasBeenReceivedCapability (IM i)}
  (equivocators : list index)
  (Free := free_composite_vlsm IM)
  (Fixed := fixed_equivocation_vlsm_composition IM equivocators)
  (StrongFixed := strong_fixed_equivocation_vlsm_composition IM equivocators)
  (PreFree := pre_loaded_with_all_messages_vlsm Free)
  `{ReachableThreshold index}
  (Hlimited : (sum_weights (remove_dups equivocators) <= proj1_sig threshold)%R )
  (sender : message -> option index)
  (Hsender_safety : sender_safety_alt_prop IM (fun i => i) sender)
  `{RelDecision _ _ (is_equivocating_tracewise_no_has_been_sent IM (fun i => i) sender)}
  (Limited : VLSM message := tracewise_limited_equivocation_vlsm_composition IM sender)
  (Htracewise_BasicEquivocation : BasicEquivocation (composite_state IM) index Ci
    := equivocation_dec_tracewise IM (fun i => i) sender)
  (tracewise_not_heavy := @not_heavy _ _ _ _ _ _ _ _ _ _ _ _ _ _ Htracewise_BasicEquivocation)
  (tracewise_equivocating_validators := @equivocating_validators _ _ _ _ _ _ _ _ _ _ _ _ _ _ Htracewise_BasicEquivocation)
  .

Lemma StrongFixed_valid_state_not_heavy s
  (Hs : valid_state_prop StrongFixed s)
  : tracewise_not_heavy s.
Proof.
  cut (elements(tracewise_equivocating_validators s) ⊆ equivocators).
  { intro Hincl.
    unfold tracewise_not_heavy, not_heavy.
    transitivity (sum_weights (remove_dups equivocators)). 
    - apply sum_weights_subseteq.
      + apply NoDup_elements.
      + apply NoDup_remove_dups.
      + intros i Hi; apply elem_of_remove_dups, Hincl; unfold tracewise_equivocating_validators; apply Hi. 
    - apply Hlimited.
  }
  assert (StrongFixedinclPreFree : VLSM_incl StrongFixed PreFree).
  { apply VLSM_incl_trans with (machine Free).
    - apply (constraint_free_incl IM (strong_fixed_equivocation_constraint IM equivocators)).
    - apply vlsm_incl_pre_loaded_with_all_messages_vlsm.
  }
  apply valid_state_has_trace in Hs as [is [tr Htr]].
  apply (VLSM_incl_finite_valid_trace_init_to StrongFixedinclPreFree) in Htr as Hpre_tr.
  intros v Hv. apply elem_of_elements, equivocating_validators_is_equivocating_tracewise_iff in Hv as Hvs'.
  specialize (Hvs' _ _ Hpre_tr).
  destruct Hvs' as [m0 [Hsender0 [pre [item [suf [Heqtr [Hm0 Heqv]]]]]]].
  rewrite Heqtr in Htr.
  destruct Htr as [Htr Hinit].
  change (pre ++ item::suf) with (pre ++ [item] ++ suf) in Htr.
  apply (finite_valid_trace_from_to_app_split StrongFixed) in Htr.
  destruct Htr as [Hpre Hitem].
  apply (VLSM_incl_finite_valid_trace_from_to StrongFixedinclPreFree) in Hpre as Hpre_pre.
  apply valid_trace_last_pstate in Hpre_pre as Hs_pre.
  apply (finite_valid_trace_from_to_app_split StrongFixed), proj1 in Hitem.
  inversion Hitem; subst; clear Htl Hitem. simpl in Hm0. subst.
  destruct Ht as [(_ & _ & _ & Hc) _].
  destruct Hc as [(i & Hi & Hsenti) | Hemit].
  + assert (Hsent : composite_has_been_sent IM (finite_trace_last is pre) m0)
      by (exists i; done).
    apply (composite_proper_sent IM) in Hsent; [| done].
    by specialize (Hsent _ _ (conj Hpre_pre Hinit)).
  +  by apply (SubProjectionTraces.sub_can_emit_sender IM equivocators (fun i => i) sender Hsender_safety _ _ v)
           in Hemit.
Qed.

Lemma StrongFixed_incl_Limited : VLSM_incl StrongFixed Limited.
Proof.
  apply constraint_subsumption_incl.
  intros [i li] [s om] Hpv.
  unfold limited_equivocation_constraint.
  destruct (composite_transition _ _ _) as [s' om'] eqn: Ht.
  apply tracewise_not_heavy_LimitedEquivocationProp_iff. unfold not_heavy. 
  apply StrongFixed_valid_state_not_heavy
    ,(input_valid_transition_destination StrongFixed).
Qed.

Lemma Fixed_incl_Limited : VLSM_incl Fixed Limited.
Proof.
  specialize (Fixed_eq_StrongFixed IM equivocators)
    as Heq.
  apply VLSM_eq_proj1 in Heq.
  apply VLSM_incl_trans with (machine StrongFixed).
  - apply Heq.
  - apply StrongFixed_incl_Limited.
Qed.

End fixed_limited_message_equivocation.

Section has_limited_equivocation.

(** ** Limited Equivocation derived from Fixed Equivocation

We say that a trace has the [fixed_limited_equivocation_prop]erty if it is
valid for the composition using a [generalized_fixed_equivocation_constraint]
induced by a subset of indices whose weight is less than the allowed
[ReachableThreshold].
*)

Context
  {message : Type}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  `{forall i, HasBeenSentCapability (IM i)}
  `{forall i, HasBeenReceivedCapability (IM i)}
  `{ReachableThreshold index}
  .

Definition fixed_limited_equivocation_prop
  (s : composite_state IM)
  (tr : list (composite_transition_item IM))
  : Prop
  := exists (equivocators : list index) (Fixed := fixed_equivocation_vlsm_composition IM equivocators),
    (sum_weights (remove_dups equivocators) <= `threshold)%R /\
    finite_valid_trace Fixed s tr.

Context
  (sender : message -> option index)
  (message_dependencies : message -> set message)
  `{RelDecision _ _ (is_equivocating_tracewise_no_has_been_sent IM (fun i => i) sender)}
  (Limited : VLSM message := tracewise_limited_equivocation_vlsm_composition IM sender)
  .

(** Traces with the [fixed_limited_equivocation_prop]erty are valid for the
composition using a [limited_equivocation_constraint].
*)
Lemma traces_exhibiting_limited_equivocation_are_valid
  (Hsender_safety : sender_safety_alt_prop IM (fun i => i) sender)
  : forall s tr, fixed_limited_equivocation_prop s tr -> finite_valid_trace Limited s tr.
Proof.
  intros s tr [equivocators [Hlimited Htr]].
  eapply VLSM_incl_finite_valid_trace; [| done]. apply Fixed_incl_Limited.
  - apply Hlimited.
  - apply Hsender_safety.
Qed.

(** Traces having the [strong_trace_witnessing_equivocation_prop]erty, which
are valid for the free composition and whose final state is [not_heavy] have
the [fixed_limited_equivocation_prop]erty.
*)
(*Lemma traces_exhibiting_limited_equivocation_are_valid_rev
  `{FinSet index Ci}
  (Hke : WitnessedEquivocationCapability IM id sender)
  `{!Irreflexive (msg_dep_happens_before message_dependencies)}
  `{forall i, MessageDependencies (IM i) message_dependencies}
  (Hfull : forall i, message_dependencies_full_node_condition_prop (IM i) message_dependencies)
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  (can_emit_signed : channel_authentication_prop IM id sender)
  (Htracewise_basic_equivocation : BasicEquivocation (composite_state IM) index Ci
    := equivocation_dec_tracewise IM (fun i => i) sender)
    (tracewise_not_heavy := @not_heavy _ _ _ _ _ _ _ _ _ _ _ _ _ _ Htracewise_basic_equivocation)
  : forall is s tr, strong_trace_witnessing_equivocation_prop IM id sender is tr ->
    finite_valid_trace_init_to (free_composite_vlsm IM) is s tr ->
    tracewise_not_heavy s ->
    fixed_limited_equivocation_prop is tr.
Proof.
  intros is s tr Hstrong Htr Hnot_heavy.
  exists (elements(equivocating_validators s)).
  split; cycle 1.
  - by eapply valid_trace_forget_last, strong_witness_has_fixed_equivocation.
  - replace (sum_weights _) with (equivocation_fault s); [done |].
    apply set_eq_nodup_sum_weight_eq.
    + apply equivocating_validators_nodup.
    + apply NoDup_remove_dups.
    + apply ListSetExtras.set_eq_extract_forall.
      intro i. rewrite elem_of_remove_dups. itauto.
Qed.*)

(** Traces with the [strong_trace_witnessing_equivocation_prop]erty, which are
valid for the composition using a [limited_equivocation_constraint]
have the [fixed_limited_equivocation_prop]erty.
*)
(*Lemma limited_traces_exhibiting_limited_equivocation_are_valid_rev
  (Hke : WitnessedEquivocationCapability IM id sender)
  `{!Irreflexive (msg_dep_happens_before message_dependencies)}
  `{forall i, MessageDependencies (IM i) message_dependencies}
  (Hfull : forall i, message_dependencies_full_node_condition_prop (IM i) message_dependencies)
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  (can_emit_signed : channel_authentication_prop IM id sender)
  : forall s tr, strong_trace_witnessing_equivocation_prop IM id sender s tr ->
    finite_valid_trace Limited s tr -> fixed_limited_equivocation_prop s tr.
Proof.
  intros s tr Hstrong Htr.
  eapply traces_exhibiting_limited_equivocation_are_valid_rev; [done.. | |].
  - apply valid_trace_add_default_last.
    eapply VLSM_incl_finite_valid_trace; [| done].
    apply constraint_free_incl.
  - apply tracewise_not_heavy_LimitedEquivocationProp_iff,
      full_node_limited_equivocation_valid_state_weight,
      finite_valid_trace_last_pstate with (X := Limited), Htr.
Qed.*)

(** Any state which is valid for limited equivocation can be produced by
a trace having the [fixed_limited_equivocation_prop]erty.
*)
Lemma limited_valid_state_has_trace_exhibiting_limited_equivocation
  (Hke : WitnessedEquivocationCapability IM id sender)
  `{!Irreflexive (msg_dep_happens_before message_dependencies)}
  `{forall i, MessageDependencies (IM i) message_dependencies}
  (Hfull : forall i, message_dependencies_full_node_condition_prop (IM i) message_dependencies)
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  (can_emit_signed : channel_authentication_prop IM id sender)
  : forall s, valid_state_prop Limited s ->
    exists is tr, finite_trace_last is tr = s /\ fixed_limited_equivocation_prop is tr.
Proof.
  intros s Hs.
  assert (Hfree_s : valid_state_prop (free_composite_vlsm IM) s)
    by (revert Hs; apply VLSM_incl_valid_state, constraint_free_incl). 
  destruct
    (free_has_strong_trace_witnessing_equivocation_prop IM id sender _ s Hfree_s)
    as (is & tr & Htr & Heqv).
  exists is, tr.
  apply valid_trace_get_last in Htr as Hlst.
  split; [done |].
  eapply traces_exhibiting_limited_equivocation_are_valid_rev; [done.. |].
  by apply tracewise_not_heavy_LimitedEquivocationProp_iff,
    full_node_limited_equivocation_valid_state_weight.
Qed.

End has_limited_equivocation.
