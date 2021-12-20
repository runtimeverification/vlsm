From stdpp Require Import prelude finite.
From Coq Require Import FunctionalExtensionality Reals.
From VLSM.Lib Require Import Preamble StdppListSet Measurable FinFunExtras StdppExtras.
From VLSM Require Import Core.VLSM Core.MessageDependencies Core.VLSMProjections Core.Composition Core.SubProjectionTraces.
From VLSM Require Import Core.ByzantineTraces Core.ByzantineTraces.FixedSetByzantineTraces.
From VLSM Require Import Core.Validating Core.Equivocation Core.Equivocation.FixedSetEquivocation Core.Equivocation.LimitedEquivocation Core.Equivocation.LimitedEquivocation Core.Equivocation.TraceWiseEquivocation.

(** * VLSM Compositions with byzantine nodes of limited weight

In this module we define and study protocol traces allowing a (weight-)limited
amount of byzantine faults.

We will show that, if the non-byzantine nodes are validating for a
composition constraint allowing only a limited amount of equivocation, then
they do not distinguish between byzantine nodes and equivocating ones, that is,
projections of traces with byzantine faults to the non-byzantine nodes are
projections of traces of the composition of the regular nodes under a
composition constraint allowing only a limited amount of equivocation.
*)

Section limited_byzantine_traces.

Context
  {message : Type}
  `{EqDecision index}
  (IM : index -> VLSM message)
  (Hbs : forall i : index, HasBeenSentCapability (IM i))
  (Hbr : forall i : index, HasBeenReceivedCapability (IM i))
  (sender : message -> option index)
  {finite_index : finite.Finite index}
  `{ReachableThreshold index}
  .

(**
We define the [limited_byzantine_trace_prop]erty in two steps. First, we
leverage the [fixed_byzantine_trace_alt_prop]erty by assuming a fixed selection
of <<byzantine>> nodes whose added weight is below the [ReachableThreshold].
*)
Definition fixed_limited_byzantine_trace_prop
  (s : composite_state IM)
  (tr : list (composite_transition_item IM))
  (byzantine : set index)
  : Prop
  := (sum_weights (remove_dups byzantine) <= `threshold)%R /\
     fixed_byzantine_trace_alt_prop IM Hbs byzantine (fun i => i) sender s tr.

(** The union of traces with the [fixed_limited_byzantine_trace_prop]erty over
all possible selections of (limited) byzantine nodes.
*)
Definition limited_byzantine_trace_prop
  (s : composite_state IM)
  (tr : list (composite_transition_item IM))
  : Prop :=
  exists byzantine, fixed_limited_byzantine_trace_prop s tr byzantine.

Context
  {is_equivocating_tracewise_no_has_been_sent_dec : RelDecision (is_equivocating_tracewise_no_has_been_sent IM (fun i => i) sender)}
  (limited_constraint := limited_equivocation_constraint IM (listing_from_finite index) sender)
  (Limited : VLSM message := composite_vlsm IM limited_constraint)
  (Hvalidating: forall i : index, validating_projection_prop IM limited_constraint i)
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  (can_emit_signed : channel_authentication_prop IM Datatypes.id sender)
  (Hbo := fun i => HasBeenObservedCapability_from_sent_received (IM i))
  (message_dependencies : message -> set message)
  (HMsgDep : forall i, MessageDependencies message_dependencies (IM i))
  (Hfull : forall i, message_dependencies_full_node_condition_prop message_dependencies (IM i))
  .

(** ** Assuming the byzantine nodes are known
We will first fix a selection of <<byzantine>> nodes of limited weight and
analyze traces with the [fixed_limited_byzantine_trace_prop]erty w.r.t. that
selection.
*)

Section fixed_limited_selection.

Context
  (byzantine: set index)
  (non_byzantine : set index := set_diff (enum index) byzantine)
  (Hlimit: (sum_weights (remove_dups byzantine) <= `threshold)%R)
  (PreNonByzantine := pre_loaded_fixed_non_byzantine_vlsm IM Hbs byzantine (λ i : index, i) sender)
  (Htracewise_BasicEquivocation : BasicEquivocation (composite_state IM) index
    := equivocation_dec_tracewise IM (fun i => i) sender (listing_from_finite index))
  (tracewise_not_heavy := @not_heavy _ _ _ _ Htracewise_BasicEquivocation)
  (tracewise_equivocating_validators := @equivocating_validators _ _ _ _ Htracewise_BasicEquivocation)
  .

(** When replacing the byzantine components of a composite [protocol_state] with
initial states for those machines we obtain a state which is [not_heavy].
*)
Lemma limited_PreNonByzantine_protocol_state_lift_not_heavy s
  (Hs : protocol_state_prop PreNonByzantine s)
  (sX := lift_sub_state IM non_byzantine s)
  : tracewise_not_heavy sX.
Proof.
  cut (tracewise_equivocating_validators sX ⊆ byzantine).
  { intro Hincl.
    unfold tracewise_not_heavy, not_heavy.
    transitivity (sum_weights (remove_dups byzantine)); [|assumption].
    apply sum_weights_subseteq.
    - apply equivocating_validators_nodup.
    - apply NoDup_remove_dups.
    - intros i Hi. apply elem_of_remove_dups, Hincl, Hi.
  }
  apply protocol_state_has_trace in Hs as [is [tr Htr]].
  specialize (preloaded_non_byzantine_vlsm_lift IM Hbs byzantine (fun i => i) sender)
    as Hproj.
  apply (VLSM_full_projection_finite_protocol_trace_init_to Hproj) in Htr as Hpre_tr.
  intros v Hv.
  apply equivocating_validators_is_equivocating_tracewise_iff in Hv as Hvs'.
  specialize (Hvs' _ _ Hpre_tr).
  destruct Hvs' as [m0 [Hsender0 [preX [itemX [sufX [Htr_pr [Hm0 Heqv]]]]]]].
  apply map_eq_app in Htr_pr as [pre [item_suf [Heqtr [Hpre_pr Hitem_suf_pr]]]].
  apply map_eq_cons in Hitem_suf_pr as [item [suf [Heqitem_suf [Hitem_pr Hsuf_pr]]]].
  subst tr item_suf. clear Hsuf_pr.
  subst itemX. cbn in Hm0.
  change (pre ++ item::suf) with (pre ++ [item] ++ suf) in Htr.
  destruct Htr as [Htr Hinit].
  apply (finite_protocol_trace_from_to_app_split PreNonByzantine) in Htr.
  destruct Htr as [Hpre Hitem].
  apply (VLSM_full_projection_finite_protocol_trace_from_to Hproj) in Hpre as Hpre_pre.
  apply ptrace_last_pstate in Hpre_pre as Hs_pre.
  apply (finite_protocol_trace_from_to_app_split PreNonByzantine), proj1 in Hitem.
  inversion Hitem; subst; clear Htl Hitem. simpl in Hm0. subst.
  destruct Ht as [[_ [_ [_ [Hc _]]]] _].
  destruct Hc as [[sub_i Hsenti] | Hemit].
  + destruct_dec_sig sub_i i Hi Heqsub_i; subst sub_i.
    assert (Hsent : composite_has_been_sent IM Hbs
                      (lift_sub_state IM non_byzantine (finite_trace_last is pre)) m0).
    { exists i.
      unfold lift_sub_state.
      rewrite lift_sub_state_to_eq with (Hi0 := Hi).
      assumption.
    }
    apply (composite_proper_sent IM (listing_from_finite index)) in Hsent; [|assumption].
    apply (VLSM_full_projection_initial_state Hproj) in Hinit.
    specialize (Hsent _ _ (conj Hpre_pre Hinit)).
    contradiction.
  + specialize (proj1 Hemit) as [i [Hi Hsigned]].
    subst.
    destruct (decide (i ∈ byzantine)).
      * unfold channel_authenticated_message in Hsigned.
        rewrite Hsender0 in Hsigned.
        apply Some_inj in Hsigned.
        subst. assumption.
      * elim Hi.
        apply set_diff_intro; [apply finite_index|assumption].
Qed.

(** When replacing the byzantine components of a composite [protocol_state] with
initial states for those machines validity of transitions for the non-byzantine
components is preserved.
*)
Lemma limited_PreNonByzantine_lift_valid
  : weak_full_projection_valid_preservation PreNonByzantine Limited
    (lift_sub_label IM non_byzantine)
    (lift_sub_state IM non_byzantine).
Proof.
  intros l s om Hv HsY HomY.
  repeat split.
  - apply lift_sub_valid, Hv.
  - unfold limited_constraint, limited_equivocation_constraint.
    destruct
      (composite_transition (sub_IM IM non_byzantine) l (s, om))
      as (s', om') eqn: Ht.
    apply (lift_sub_transition IM non_byzantine) in Ht
      as HtX.
    simpl in HtX |- *. rewrite HtX. simpl.
    apply limited_PreNonByzantine_protocol_state_lift_not_heavy.
    eapply protocol_transition_destination; split; eassumption.
Qed.

(** By replacing the byzantine components of a composite [protocol_state] with
initial states for those machines and ignoring transitions for byzantine nodes
we obtain valid protocol traces for the <<Limited>> equivocation composition.
*)
Lemma limited_PreNonByzantine_vlsm_lift
  : VLSM_full_projection PreNonByzantine Limited
      (lift_sub_label IM non_byzantine)
      (lift_sub_state IM non_byzantine).
Proof.
  apply basic_VLSM_full_projection; intro; intros.
  - apply limited_PreNonByzantine_lift_valid; assumption.
  - apply lift_sub_transition. apply H0.
  - apply (lift_sub_state_initial IM); assumption.
  - destruct HmX as [[sub_i [[im Him] Heqm]] | Hseeded].
    + simpl in Heqm. subst.
      destruct_dec_sig sub_i i Hi Heqsub_i.
      subst. unfold sub_IM in Him. simpl in Him.
      clear -Him.
      apply initial_message_is_protocol.
      exists i, (exist _ m Him); intuition.
    + destruct Hseeded as [Hsigned [i [Hi [li [si Hpre_valid]]]]].
      apply set_diff_elim2 in Hi.
      specialize (Hvalidating i _ _ Hpre_valid)
        as [_ [_ [_ [Hmsg _]]]].
      assumption.
Qed.

End fixed_limited_selection.

(**
Given a trace with the [fixed_limited_byzantine_trace_prop]erty for a selection
of <<byzantine>> nodes, there exists protocol valid trace for the <<Limited>>
equivocation composition such that the projection of the two traces to
the <<non-byzantine>> nodes coincide.
*)
Lemma validating_fixed_limited_non_byzantine_traces_are_limited_non_equivocating s tr byzantine
  (not_byzantine : set index := set_diff (enum index) byzantine)
  : fixed_limited_byzantine_trace_prop s tr byzantine ->
    exists bs btr,
      finite_protocol_trace Limited bs btr /\
      composite_state_sub_projection IM not_byzantine s = composite_state_sub_projection IM not_byzantine bs /\
      finite_trace_sub_projection IM not_byzantine tr = finite_trace_sub_projection IM not_byzantine btr.
Proof.
  intros [Hlimit Hfixed].
  eexists _, _; split.
  - apply (VLSM_full_projection_finite_protocol_trace
            (limited_PreNonByzantine_vlsm_lift byzantine Hlimit)).
    exact Hfixed.
  - unfold lift_sub_state.
    rewrite composite_state_sub_projection_lift.
    split; [reflexivity|].
    symmetry. apply composite_trace_sub_projection_lift.
Qed.

(** ** The main result

Given any trace with the [limited_byzantine_trace_prop]erty, there exist
a protocol valid trace for the <<Limited>> equivocation composition and
a selection of nodes of limited weight such that the projection of the
two traces to the nodes not in the selection coincide.
*)
Lemma validating_limited_non_byzantine_traces_are_limited_non_equivocating s tr
  : limited_byzantine_trace_prop s tr ->
    exists bs btr,
      finite_protocol_trace Limited bs btr /\
      exists selection (selection_complement := set_diff (enum index) selection),
      (sum_weights (remove_dups selection) <= `threshold)%R /\
      composite_state_sub_projection IM selection_complement s = composite_state_sub_projection IM selection_complement bs /\
      finite_trace_sub_projection IM selection_complement tr = finite_trace_sub_projection IM selection_complement btr.
Proof.
  intros [byzantine Hlimited].
  apply proj1 in Hlimited as Hlimit.
  apply validating_fixed_limited_non_byzantine_traces_are_limited_non_equivocating
    in Hlimited
    as [bs [btr [Hlimited [Hs_pr Htr_pr]]]].
  exists bs, btr. split; [assumption|].
  exists byzantine.
  repeat split; assumption.
Qed.

End limited_byzantine_traces.
