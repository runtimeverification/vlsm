From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude finite.
From Coq Require Import FinFun RIneq.
From VLSM.Lib Require Import Preamble Measurable StdppListSet RealsExtras ListSetExtras.
From VLSM.Core Require Import VLSM VLSMProjections MessageDependencies Composition Equivocation.
From VLSM.Core Require Import FixedSetEquivocation LimitedEquivocation.
From VLSM.Core Require Import TraceWiseEquivocation.
From VLSM.Core Require Import WitnessedEquivocation.

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

Section sec_basic_limited_message_equivocation.

Context
  {message : Type}
  `{EqDecision index}
  `{EqDecision validator}
  (IM : index -> VLSM message)
  `{BasicEquivocation (composite_state IM) validator}
  .

Definition basic_limited_equivocation_constraint :=
  limited_equivocation_constraint IM threshold is_equivocating (Cv := Cv).

Definition basic_limited_equivocation_composite_vlsm : VLSM message :=
  limited_equivocation_composite_vlsm IM threshold is_equivocating (Cv := Cv).

Lemma LimitedEquivocationProp_impl_not_heavy :
  forall s, LimitedEquivocationProp (Cv := Cv) IM threshold is_equivocating s -> not_heavy s.
Proof.
  intros s [].
  apply Rle_trans with (sum_weights vs); [| done].
  apply sum_weights_subseteq; intros v Hv.
  apply elem_of_filter in Hv as [Hvsl Hvsr].
  by apply Heqv_vs, Hvsl.
Qed.

Definition basic_equivocation_state_validators_comprehensive_prop : Prop :=
  forall s v, is_equivocating s v -> v ∈ state_validators s.

Lemma not_heavy_impl_LimitedEquivocationProp
  (Hcomprehensive : basic_equivocation_state_validators_comprehensive_prop)
  : forall s, not_heavy s -> LimitedEquivocationProp (Cv := Cv) IM threshold is_equivocating s.
Proof.
  intros s Hs.
  exists (equivocating_validators s); [| done].
  intros v Hv; apply elem_of_filter.
  split; [done |].
  by apply Hcomprehensive.
Qed.

End sec_basic_limited_message_equivocation.

Section sec_tracewise_limited_message_equivocation.

Context
  {message index : Type}
  (IM : index -> VLSM message)
  (threshold : R)
  `{EqDecision index}
  `{forall i, HasBeenSentCapability (IM i)}
  `{forall i, HasBeenReceivedCapability (IM i)}
  (Free := free_composite_vlsm IM)
  `{finite.Finite validator}
  `{ReachableThreshold validator Cv threshold}
  (A : validator -> index)
  (sender : message -> option validator)
  (equivocating := is_equivocating_tracewise_no_has_been_sent IM A sender)
  .

Definition tracewise_limited_equivocation_constraint :=
  limited_equivocation_constraint IM threshold equivocating (Cv := Cv).

Definition tracewise_limited_equivocation_vlsm_composition : VLSM message :=
  limited_equivocation_composite_vlsm IM threshold equivocating (Cv := Cv).

Lemma full_node_limited_equivocation_valid_state_weight s
  : valid_state_prop tracewise_limited_equivocation_vlsm_composition s ->
    LimitedEquivocationProp (Cv := Cv) IM threshold equivocating s.
Proof.
  eapply limited_equivocation_valid_state; [done |].
  by intros; apply initial_state_not_is_equivocating_tracewise.
Qed.

End sec_tracewise_limited_message_equivocation.

Section sec_fixed_limited_message_equivocation.

(** ** Fixed Message Equivocation implies Limited Message Equivocation

  In this section we show that if the set of allowed equivocators for a fixed
  equivocation constraint is of weight smaller than the threshold accepted for
  limited message equivocation, then any valid trace for the fixed equivocation
  constraint is also a trace under the limited equivocation constraint.
*)

Context
  {message index : Type}
  (IM : index -> VLSM message)
  (threshold : R)
  `{FinSet index Ci}
  `{!finite.Finite index}
  `{forall i, HasBeenSentCapability (IM i)}
  `{forall i, HasBeenReceivedCapability (IM i)}
  (Free := free_composite_vlsm IM)
  `{finite.Finite validator}
  `{ReachableThreshold validator Cv threshold}
  (A : validator -> index)
  `{! Inj (=) (=) A}
  (sender : message -> option validator)
  (eqv_validators : Cv)
  (equivocators := fin_sets.set_map A eqv_validators : Ci)
  (Hlimited : (sum_weights eqv_validators <= threshold)%R )
  (Hsender_safety : sender_safety_alt_prop IM A sender)
  (equivocating := is_equivocating_tracewise_no_has_been_sent IM A sender)
  (Fixed := fixed_equivocation_vlsm_composition IM equivocators)
  (StrongFixed := strong_fixed_equivocation_vlsm_composition IM equivocators)
  (PreFree := pre_loaded_with_all_messages_vlsm Free)
  (Limited : VLSM message := tracewise_limited_equivocation_vlsm_composition (Cv := Cv) IM threshold A sender)
  .

Lemma StrongFixed_valid_state_not_heavy s
  (Hs : valid_state_prop StrongFixed s)
  : LimitedEquivocationProp IM threshold equivocating s (Cv := Cv).
Proof.
  exists eqv_validators; [| done].
  assert (StrongFixedinclPreFree : VLSM_incl StrongFixed PreFree).
  {
    apply VLSM_incl_trans with (machine Free).
    - by apply (constraint_free_incl IM (strong_fixed_equivocation_constraint IM equivocators)).
    - by apply vlsm_incl_pre_loaded_with_all_messages_vlsm.
  }
  apply valid_state_has_trace in Hs as [is [tr Htr]].
  apply (VLSM_incl_finite_valid_trace_init_to StrongFixedinclPreFree) in Htr as Hpre_tr.
  intros v Hv.
  specialize (Hv _ _ Hpre_tr).
  destruct Hv as [m0 [Hsender0 [pre [item [suf [Heqtr [Hm0 Heqv]]]]]]].
  rewrite Heqtr in Htr.
  destruct Htr as [Htr Hinit].
  change (pre ++ item :: suf) with (pre ++ [item] ++ suf) in Htr.
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
  + apply (SubProjectionTraces.sub_can_emit_sender IM (elements equivocators)
      A sender Hsender_safety _ _ v), elem_of_elements in Hemit; [| done].
    apply elem_of_map in Hemit as (_v & HeqAv & H_v).
    eapply inj in HeqAv; [| done].
    by subst.
Qed.

Lemma StrongFixed_incl_Limited : VLSM_incl StrongFixed Limited.
Proof.
  apply constraint_subsumption_incl.
  intros [i li] [s om] Hpv.
  unfold limited_equivocation_constraint.
  destruct (composite_transition _ _ _) as [s' om'] eqn: Ht.
  by eapply StrongFixed_valid_state_not_heavy, input_valid_transition_destination.
Qed.

Lemma Fixed_incl_Limited : VLSM_incl Fixed Limited.
Proof.
  specialize (Fixed_eq_StrongFixed IM equivocators)
    as Heq.
  apply VLSM_eq_proj1 in Heq.
  apply VLSM_incl_trans with (machine StrongFixed).
  - by apply Heq.
  - by apply StrongFixed_incl_Limited.
Qed.

End sec_fixed_limited_message_equivocation.

Section sec_has_limited_equivocation.

(** ** Limited Equivocation derived from Fixed Equivocation

  We say that a trace has the [fixed_limited_equivocation_prop]erty if it is
  valid for the composition using a [generalized_fixed_equivocation_constraint]
  induced by a subset of indices whose weight is less than the allowed
  [ReachableThreshold].
*)

Context
  {message}
  `{FinSet index Ci}
  `{!finite.Finite index}
  (IM : index -> VLSM message)
  (threshold : R)
  `{finite.Finite validator}
  `{ReachableThreshold validator Cv threshold}
  (A : validator -> index)
  `{!Inj (=) (=) A}
  (sender : message -> option validator)
  `{forall i, HasBeenSentCapability (IM i)}
  `{forall i, HasBeenReceivedCapability (IM i)}
  (equivocating := is_equivocating_tracewise_no_has_been_sent IM A sender)
  .

Definition fixed_limited_equivocation_prop
  (s : composite_state IM)
  (tr : list (composite_transition_item IM))
  : Prop
  :=
    exists equivocators : Cv,
      (sum_weights equivocators <= threshold)%R /\
      finite_valid_trace (fixed_equivocation_vlsm_composition (Ci := Ci) IM (fin_sets.set_map A equivocators)) s tr.

Context
  `{FinSet message Cm}
  (message_dependencies : message -> Cm)
  (Limited : VLSM message := tracewise_limited_equivocation_vlsm_composition (Cv := Cv) IM threshold A sender)
  .

(**
  Traces with the [fixed_limited_equivocation_prop]erty are valid for the
  composition using a [limited_equivocation_constraint].
*)
Lemma traces_exhibiting_limited_equivocation_are_valid
  (Hsender_safety : sender_safety_alt_prop IM A sender)
  : forall s tr, fixed_limited_equivocation_prop s tr -> finite_valid_trace Limited s tr.
Proof.
  intros s tr [equivocators [Hlimited Htr]].
  eapply VLSM_incl_finite_valid_trace; [| done].
  by eapply Fixed_incl_Limited.
Qed.

(**
  Traces having the [strong_trace_witnessing_equivocation_prop]erty, which
  are valid for the free composition and whose final state is [not_heavy] have
  the [fixed_limited_equivocation_prop]erty.
*)
Lemma traces_exhibiting_limited_equivocation_are_valid_rev
  (Hke : WitnessedEquivocationCapability IM threshold A sender (Cv := Cv))
  `{!Irreflexive (msg_dep_happens_before message_dependencies)}
  `{forall i, MessageDependencies (IM i) message_dependencies}
  (Hfull : forall i, message_dependencies_full_node_condition_prop (IM i) message_dependencies)
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  (can_emit_signed : channel_authentication_prop IM A sender)
  : forall is s tr, strong_trace_witnessing_equivocation_prop IM threshold A sender is tr (Cv := Cv) ->
    finite_valid_trace_init_to (free_composite_vlsm IM) is s tr ->
    LimitedEquivocationProp (Cv := Cv) IM threshold equivocating s ->
    fixed_limited_equivocation_prop is tr.
Proof.
  intros is s tr Hstrong Htr Hnot_heavy.
  exists (equivocating_validators s).
  split; cycle 1.
  - by eapply valid_trace_forget_last, strong_witness_has_fixed_equivocation.
  - by replace (sum_weights _) with (equivocation_fault s).
Qed.

(**
  Traces with the [strong_trace_witnessing_equivocation_prop]erty, which are
  valid for the composition using a [limited_equivocation_constraint]
  have the [fixed_limited_equivocation_prop]erty.
*)
Lemma limited_traces_exhibiting_limited_equivocation_are_valid_rev
  (Hke : WitnessedEquivocationCapability IM threshold A sender (Cv := Cv))
  `{!Irreflexive (msg_dep_happens_before message_dependencies)}
  `{forall i, MessageDependencies (IM i) message_dependencies}
  (Hfull : forall i, message_dependencies_full_node_condition_prop (IM i) message_dependencies)
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  (can_emit_signed : channel_authentication_prop IM A sender)
  : forall s tr, strong_trace_witnessing_equivocation_prop IM threshold A sender s tr (Cv := Cv) ->
    finite_valid_trace Limited s tr -> fixed_limited_equivocation_prop s tr.
Proof.
  intros s tr Hstrong Htr.
  eapply traces_exhibiting_limited_equivocation_are_valid_rev; [done.. | |].
  - apply valid_trace_add_default_last.
    eapply VLSM_incl_finite_valid_trace; [| done].
    by apply constraint_free_incl.
  - by apply tracewise_not_heavy_LimitedEquivocationProp_iff,
      full_node_limited_equivocation_valid_state_weight,
      finite_valid_trace_last_pstate with (X := Limited), Htr.
Qed.

(**
  Any state which is valid for limited equivocation can be produced by
  a trace having the [fixed_limited_equivocation_prop]erty.
*)

Lemma limited_valid_state_has_trace_exhibiting_limited_equivocation
  (Hke : WitnessedEquivocationCapability IM threshold A sender (Cv := Cv))
  `{!Irreflexive (msg_dep_happens_before message_dependencies)}
  `{forall i, MessageDependencies (IM i) message_dependencies}
  (Hfull : forall i, message_dependencies_full_node_condition_prop (IM i) message_dependencies)
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  (can_emit_signed : channel_authentication_prop IM A sender)
  : forall s, valid_state_prop Limited s ->
    exists is tr, finite_trace_last is tr = s /\ fixed_limited_equivocation_prop is tr.
Proof.
  intros s Hs.
  assert (Hfree_s : valid_state_prop (free_composite_vlsm IM) s)
    by (revert Hs; apply VLSM_incl_valid_state, constraint_free_incl).
  destruct
    (free_has_strong_trace_witnessing_equivocation_prop IM threshold A sender _ s Hfree_s)
    as (is & tr & Htr & Heqv).
  exists is, tr.
  apply valid_trace_get_last in Htr as Hlst.
  split; [done |].
  eapply traces_exhibiting_limited_equivocation_are_valid_rev; [done.. |].
  by apply tracewise_not_heavy_LimitedEquivocationProp_iff,
    full_node_limited_equivocation_valid_state_weight.
Qed.

End sec_has_limited_equivocation.
