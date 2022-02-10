From stdpp Require Import prelude finite.
From Coq Require Import FunctionalExtensionality Reals.
From VLSM.Lib Require Import Preamble StdppListSet Measurable FinFunExtras StdppExtras ListSetExtras.
From VLSM.Core Require Import VLSM MessageDependencies VLSMProjections Composition ProjectionTraces SubProjectionTraces AnnotatedVLSM.
From VLSM Require Import Core.ByzantineTraces Core.ByzantineTraces.FixedSetByzantineTraces.
From VLSM Require Import Core.Validator Core.Equivocation Core.Equivocation.FixedSetEquivocation Core.Equivocation.LimitedEquivocation Core.Equivocation.LimitedEquivocation Core.Equivocation.MsgDepLimitedEquivocation Core.Equivocation.TraceWiseEquivocation.

(** * VLSM Compositions with byzantine nodes of limited weight

In this module we define and study protocol executions allowing a
(weight-)limited amount of byzantine faults.

We will show that, if the non-byzantine nodes are validators for a
composition constraint allowing only a limited amount of equivocation, then
they do not distinguish between byzantine nodes and equivocating ones, that is,
projections of traces with byzantine faults to the non-byzantine nodes are
projections of traces of the composition of the regular nodes under a
composition constraint allowing only a limited amount of equivocation.
*)

Section sec_limited_byzantine_traces.

Context
  {message : Type}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  (Hbs : forall i : index, HasBeenSentCapability (IM i))
  (Hbr : forall i : index, HasBeenReceivedCapability (IM i))
  (sender : message -> option index)
  `{ReachableThreshold index}
  .

Definition limited_byzantine_set : Type :=
  { byzantine : set index | (sum_weights (remove_dups byzantine) <= `threshold)%R }.

Definition limited_byzantine_trace : Type :=
  { limited_byzantine : limited_byzantine_set & fixed_byzantine_trace IM Hbs (` limited_byzantine) Datatypes.id sender}.

Context
  (message_dependencies : message -> set message)
  (HMsgDep : forall i, MessageDependencies message_dependencies (IM i))
  (full_message_dependencies : message -> set message)
  (HFullMsgDep : FullMessageDependencies message_dependencies full_message_dependencies)
  (Limited := msg_dep_limited_equivocation_vlsm IM Hbs Hbr full_message_dependencies sender)
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  (Hchannel : channel_authentication_prop IM Datatypes.id sender)
  (Hsender_safety : sender_safety_alt_prop IM Datatypes.id sender :=
    channel_authentication_sender_safety _ _ _ Hchannel)
  .

Program Definition limited_equivocating_traces_are_byzantine is tr
  (Htr : finite_valid_trace Limited is tr)
  (equivocators := state_annotation (finite_trace_last is tr))
  : limited_byzantine_trace :=
  existT (exist _ equivocators _)
    (fixed_equivocating_traces_are_byzantine_traces IM equivocators Datatypes.id sender no_initial_messages_in_IM Hchannel (original_state is) (pre_VLSM_full_projection_finite_trace_project
    (type Limited) (composite_type IM) Datatypes.id original_state
    tr) _).
Next Obligation.
  intros; cbn.
  eapply msg_dep_fixed_limited_equivocation_witnessed; eassumption.
Qed.
Next Obligation.
  intros; cbn.
  eapply msg_dep_fixed_limited_equivocation_witnessed; eassumption.
Qed.


End sec_limited_byzantine_traces.

(*

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

(** When replacing the byzantine components of a composite [valid_state] with
initial states for those machines we obtain a state which is [not_heavy].
*)
Lemma limited_PreNonByzantine_valid_state_lift_not_heavy s
  (Hs : valid_state_prop PreNonByzantine s)
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
  apply valid_state_has_trace in Hs as [is [tr Htr]].
  specialize (preloaded_non_byzantine_vlsm_lift IM Hbs byzantine (fun i => i) sender)
    as Hproj.
  apply (VLSM_full_projection_finite_valid_trace_init_to Hproj) in Htr as Hpre_tr.
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
  apply (finite_valid_trace_from_to_app_split PreNonByzantine) in Htr.
  destruct Htr as [Hpre Hitem].
  apply (VLSM_full_projection_finite_valid_trace_from_to Hproj) in Hpre as Hpre_pre.
  apply valid_trace_last_pstate in Hpre_pre as Hs_pre.
  apply (finite_valid_trace_from_to_app_split PreNonByzantine), proj1 in Hitem.
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

(** When replacing the byzantine components of a composite [valid_state] with
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
    apply limited_PreNonByzantine_valid_state_lift_not_heavy.
    eapply input_valid_transition_destination; split; eassumption.
Qed.

(** By replacing the byzantine components of a composite [valid_state] with
initial states for those machines and ignoring transitions for byzantine nodes
we obtain valid traces for the <<Limited>> equivocation composition.
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
      apply initial_message_is_valid.
      exists i, (exist _ m Him); intuition.
    + destruct Hseeded as [Hsigned [i [Hi [li [si Hpre_valid]]]]].
      apply set_diff_elim2 in Hi.
      eapply Hvalidator; eassumption.
Qed.

End fixed_limited_selection.

(**
Given a trace with the [fixed_limited_byzantine_trace_prop]erty for a selection
of <<byzantine>> nodes, there exists a valid trace for the <<Limited>>
equivocation composition such that the projection of the two traces to
the <<non-byzantine>> nodes coincide.
*)
Lemma validator_fixed_limited_non_byzantine_traces_are_limited_non_equivocating s tr byzantine
  (not_byzantine : set index := set_diff (enum index) byzantine)
  : fixed_limited_byzantine_trace_prop s tr byzantine ->
    exists bs btr,
      finite_valid_trace Limited bs btr /\
      composite_state_sub_projection IM not_byzantine s = composite_state_sub_projection IM not_byzantine bs /\
      finite_trace_sub_projection IM not_byzantine tr = finite_trace_sub_projection IM not_byzantine btr.
Proof.
  intros [Hlimit Hfixed].
  eexists _, _; split.
  - apply (VLSM_full_projection_finite_valid_trace
            (limited_PreNonByzantine_vlsm_lift byzantine Hlimit)).
    exact Hfixed.
  - unfold lift_sub_state.
    rewrite composite_state_sub_projection_lift_to.
    split; [reflexivity|].
    symmetry. apply composite_trace_sub_projection_lift.
Qed.

(** ** The main result

Given any trace with the [limited_byzantine_trace_prop]erty, there exists
a valid trace for the <<Limited>> equivocation composition and
a selection of nodes of limited weight such that the projection of the
two traces to the nodes not in the selection coincide.
*)
Lemma validator_limited_non_byzantine_traces_are_limited_non_equivocating s tr
  : limited_byzantine_trace_prop s tr ->
    exists bs btr,
      finite_valid_trace Limited bs btr /\
      exists selection (selection_complement := set_diff (enum index) selection),
      (sum_weights (remove_dups selection) <= `threshold)%R /\
      composite_state_sub_projection IM selection_complement s = composite_state_sub_projection IM selection_complement bs /\
      finite_trace_sub_projection IM selection_complement tr = finite_trace_sub_projection IM selection_complement btr.
Proof.
  intros [byzantine Hlimited].
  apply proj1 in Hlimited as Hlimit.
  apply validator_fixed_limited_non_byzantine_traces_are_limited_non_equivocating
    in Hlimited
    as [bs [btr [Hlimited [Hs_pr Htr_pr]]]].
  exists bs, btr. split; [assumption|].
  exists byzantine.
  repeat split; assumption.
Qed.

End limited_byzantine_traces.

Section sec_msg_dep_limited_byzantine_traces.

Context
  {message : Type}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  (Hbs : forall i, HasBeenSentCapability (IM i))
  (Hbr : forall i, HasBeenReceivedCapability (IM i))
  (Hbo := fun i => HasBeenObservedCapability_from_sent_received (IM i))
  (message_dependencies : message -> set message)
  (HMsgDep : forall i, MessageDependencies message_dependencies (IM i))
  (full_message_dependencies : message -> set message)
  (HFullMsgDep : FullMessageDependencies message_dependencies full_message_dependencies)
  `{ReachableThreshold index}
  (sender : message -> option index)
  (Limited := msg_dep_limited_equivocation_vlsm IM Hbs Hbr full_message_dependencies sender)
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  (Hchannel : channel_authentication_prop IM Datatypes.id sender)
  (Hsender_safety : sender_safety_alt_prop IM Datatypes.id sender :=
    channel_authentication_sender_safety _ _ _ Hchannel)
  (Hvalidator:
    forall i : index,
      msg_dep_limited_equivocation_message_validator_prop IM Hbs Hbr
        full_message_dependencies sender i)
  (Hfull : forall i, message_dependencies_full_node_condition_prop message_dependencies (IM i))
  .

(**
If the set of byzantine nodes is weight-limited and if an [input_valid_transition]
of the non-byzantine nodes from a state of weight-limited equivocation does not
introduce equivocators from the non-byzantine nodes, then the transition is valid
for weight-limited equivocation.
*)
Lemma lift_pre_loaded_fixed_non_byzantine_valid_transition_to_limited
  (byzantine: set index)
  (non_byzantine := set_diff (enum index) byzantine)
  (Hlimited: (sum_weights (remove_dups byzantine) <= `threshold)%R)
  sub_l sub_s iom sub_sf oom
  (Ht_sub : input_valid_transition
      (pre_loaded_fixed_non_byzantine_vlsm IM Hbs byzantine Datatypes.id sender)
      sub_l (sub_s, iom) (sub_sf, oom))
  ann_s
  (Hann_s : valid_state_prop Limited ann_s)
  (Hann_s_pr : original_state ann_s = lift_sub_state IM non_byzantine sub_s)
  (ann' := msg_dep_composite_transition_message_equivocators IM Hbs Hbr full_message_dependencies sender
      (lift_sub_label IM non_byzantine sub_l) (ann_s, iom))
  (Heqv_byzantine : ann' ⊆ byzantine)
  : input_valid_transition Limited
      (lift_sub_label IM non_byzantine sub_l) (ann_s, iom)
      (Build_annotated_state (free_composite_vlsm IM) (set index)
        (lift_sub_state IM non_byzantine sub_sf) ann',
      oom).
Proof.
  destruct sub_l as (sub_i, li).
  destruct_dec_sig sub_i i Hi Heqsub_i.
  subst.
  repeat split.
  - assumption.
  - destruct iom as [im|]; [|apply option_valid_message_None].
    eapply Hvalidator,
      pre_loaded_sub_composite_input_valid_projection,
      Ht_sub.
  - cbn.
    rewrite Hann_s_pr.
    unfold lift_sub_state.
    rewrite lift_sub_state_to_eq with (Hi0 := Hi).
    apply Ht_sub.
  - apply Rle_trans with (sum_weights (remove_dups byzantine))
    ; [|assumption].
    apply sum_weights_subseteq.
    + cut (NoDup (state_annotation ann_s)).
      { intro Hnodup.
        destruct iom as [im|]; [|assumption].
        apply set_union_nodup_left; assumption.
      }
      subst.
      eapply coeqv_limited_equivocation_state_annotation_nodup; eassumption.
    + apply NoDup_remove_dups.
    + intro eqv.
      rewrite elem_of_remove_dups.
      apply Heqv_byzantine.
  - clear -Ht_sub Hann_s_pr.
    cbn.
    unfold annotated_transition.
    cbn.
    apply proj2 in Ht_sub.
    revert Ht_sub.
    cbn.
    rewrite Hann_s_pr.
    unfold lift_sub_state at 1.
    rewrite lift_sub_state_to_eq with (Hi0 := Hi).
    unfold sub_IM at 2.
    cbn.
    destruct (vtransition _ _ _) as (si', om').
    intro Ht.
    inversion Ht.
    subst.
    clear Ht.
    f_equal.
    f_equal.
    extensionality j.
    destruct (decide (i = j)) as [Hij | Hij].
    + subst j.
      unfold lift_sub_state.
      rewrite lift_sub_state_to_eq with (Hi0 := Hi).
      rewrite !state_update_eq.
      reflexivity.
    + rewrite state_update_neq by congruence.
      destruct (decide (j ∈ set_diff (enum index) byzantine)) as [Hj|Hj].
      * unfold lift_sub_state.
        rewrite !lift_sub_state_to_eq with (Hi0 := Hj).
        rewrite sub_IM_state_update_neq by congruence.
        reflexivity.
      * unfold lift_sub_state.
        rewrite !lift_sub_state_to_neq by assumption.
        reflexivity.
Qed.

(** Considering a trace with the [fixed_byzantine_trace_alt_prop]erty for a
set <<byzantine>> of indices of bounded weight, its subtrace corresponding to
the non-byzantine nodes is of limited equivocation and its set of equivocators
is included in <<byzantine>>.
*)
Lemma lift_fixed_byzantine_traces_to_limited
  (s: composite_state IM)
  (tr: list (composite_transition_item IM))
  (byzantine: set index)
  (non_byzantine := set_diff (enum index) byzantine)
  (Hlimited: (sum_weights (remove_dups byzantine) <= `threshold)%R)
  (Hbyzantine:
    fixed_byzantine_trace_alt_prop IM Hbs byzantine Datatypes.id sender s tr)
  (s_reset_byzantine :=
    lift_sub_state IM non_byzantine
      (composite_state_sub_projection IM non_byzantine s))
  (bs := Build_annotated_state (free_composite_vlsm IM) (set index) s_reset_byzantine (` inhabitant))
  (btr :=
    msg_dep_annotate_trace_with_equivocators IM Hbs Hbr full_message_dependencies sender
      s_reset_byzantine
      (pre_VLSM_full_projection_finite_trace_project _ _
        (lift_sub_label IM non_byzantine) (lift_sub_state IM (set_diff (enum index) byzantine))
        (finite_trace_sub_projection IM non_byzantine tr)))
  : finite_valid_trace Limited bs btr /\
    state_annotation (@finite_trace_last _ (type Limited) bs btr) ⊆ byzantine.
Proof.
  subst non_byzantine.
  induction Hbyzantine using finite_valid_trace_rev_ind; [repeat split|].
  - constructor.
    apply initial_state_is_valid.
    repeat split.
    cbn.
    apply lift_sub_state_initial.
    assumption.
  - cbn; apply lift_sub_state_initial; assumption.
  - apply list_subseteq_nil.
  - subst s_reset_byzantine bs btr.
    unfold pre_VLSM_full_projection_finite_trace_project.
    rewrite !map_app.
    setoid_rewrite annotate_trace_from_app.
    cbn.
    rewrite finite_trace_last_is_last.
    cbn.
    destruct l as (sub_i, li).
    destruct_dec_sig sub_i i Hi Heqsub_i.
    subst sub_i.
    destruct IHHbyzantine as [[Htr0_ann Hsi_ann] Htr0_eqv_byzantine].
    cbn in Htr0_eqv_byzantine |- *.
    remember
      (@finite_trace_last _(annotated_type (free_composite_vlsm IM) (set index))
        _ _) as lst.
    assert (Hlsti : original_state lst = lift_sub_state IM (set_diff (enum index) byzantine) (finite_trace_last si tr0)).
    {
      subst lst.
      rewrite annotate_trace_from_last_original_state.
      symmetry.
      apply
        (pre_VLSM_full_projection_finite_trace_last _ _
          (lift_sub_label IM (set_diff (enum index) byzantine))
          (lift_sub_state IM (set_diff (enum index) byzantine))).
    }
    match goal with
    |- _ /\ ?B => cut B
    end.
    {
      intro Heqv_byzantine.
      split; [|assumption].
      split; [|assumption].
      apply finite_valid_trace_from_app_iff.
      split; [assumption|].
      subst x.
      cbn.
      apply finite_valid_trace_singleton.
      replace (finite_trace_last _ _) with lst.
      eapply lift_pre_loaded_fixed_non_byzantine_valid_transition_to_limited.
      1,2,4,5: eassumption.
      subst lst.
      apply finite_valid_trace_last_pstate.
      assumption.
    }
    destruct iom as [im|]; [|assumption].
    apply set_union_subseteq_iff.
    split; [assumption|].
    unfold coeqv_message_equivocators.
    case_decide as Hnobs; [apply list_subseteq_nil|].
    erewrite full_node_msg_dep_coequivocating_senders with (i0 := i) (li0 :=li).
    2-4: eassumption.
    2: cbn; rewrite Hlsti;
        eapply pre_loaded_sub_composite_input_valid_projection, Hx.
    rewrite app_nil_r.
    cbn.
    destruct (sender im) as [i_im|] eqn:Hsender
    ; [|apply list_subseteq_nil].
    intro _i_im. rewrite elem_of_list_singleton.
    intro; subst _i_im.
    apply proj1, proj2, proj2, proj2, proj1 in Hx
      as [Hsent | [Hsigned _]].
    + elim Hnobs.
      destruct Hsent as [sub_i_im Hsent].
      cbn in Hsent.
      cbn.
      destruct_dec_sig sub_i_im _i_im H_i_im Heqsub_i_im.
      subst sub_i_im.
      apply composite_has_been_observed_sent_received_iff.
      left.
      exists _i_im.
      rewrite Hlsti.
      unfold lift_sub_state.
      rewrite lift_sub_state_to_eq with (Hi0 := H_i_im).
      assumption.
    + clear -Hsender Hsigned.
      destruct Hsigned as (_i_im & H_i_im & Hauth).
      unfold channel_authenticated_message in Hauth.
      rewrite Hsender in Hauth.
      apply Some_inj in Hauth.
      subst _i_im.
      destruct (decide (i_im ∈ byzantine)) as [Hi_im|Hni_im]
      ; [assumption|].
      elim H_i_im.
      apply set_diff_intro; [apply elem_of_enum|assumption].
Qed.

(**
Under full-message dependencies and full node assumptions, if all components are
validators for the [msg_dep_limited_equivocation_vlsm] associated to their
composition, then the traces exposed limited Byzantine behaviour coincide with
the traces exposed to limited equivocation.
*)
Lemma msg_dep_validator_limited_non_byzantine_traces_are_limited_non_equivocating s tr
  : limited_byzantine_trace_prop IM Hbs sender s tr <->
    exists bs btr selection (selection_complement := set_diff (enum index) selection),
      finite_valid_trace Limited bs btr /\
      state_annotation (finite_trace_last bs btr) ⊆ selection /\
      (sum_weights (remove_dups selection) <= `threshold)%R /\
      composite_state_sub_projection IM selection_complement s =
        composite_state_sub_projection IM selection_complement (original_state bs) /\
      finite_trace_sub_projection IM selection_complement tr =
        finite_trace_sub_projection IM selection_complement
          (pre_VLSM_full_projection_finite_trace_project
            (type Limited) (composite_type IM) Datatypes.id original_state btr).
Proof.
  split.
  - intros (byzantine & Hlimited & Hbyzantine).
    apply lift_fixed_byzantine_traces_to_limited in Hbyzantine
      as [Hbtr Heqv_byzantine]
    ; [|assumption].
    eexists _,_, byzantine; repeat (split; [eassumption|]).
    split.
    + extensionality sub_i.
      destruct_dec_sig sub_i i Hi Heqsub_i.
      subst.
      cbn.
      unfold lift_sub_state.
      rewrite lift_sub_state_to_eq with (Hi0 := Hi).
      reflexivity.
    + subst Limited.
      rewrite msg_dep_annotate_trace_with_equivocators_project.
      symmetry.
      apply composite_trace_sub_projection_lift.
  - intros (bs & btr & byzantine & Hbtr & Heqv_byzantine & Hlimited & His_pr & Htr_pr).
    exists byzantine.
    split; [assumption|].
    unfold fixed_byzantine_trace_alt_prop.
    eapply VLSM_incl_finite_valid_trace
    ; [apply fixed_non_equivocating_incl_fixed_non_byzantine; assumption|].
    apply fixed_non_equivocating_traces_char.
    symmetry in His_pr, Htr_pr.
    eexists _,_; split; [|split; eassumption].
    eapply msg_dep_fixed_limited_equivocation_witnessed, proj2 in Hbtr.
    2-5: eassumption.
    revert Hbtr.
    apply VLSM_incl_finite_valid_trace.
    apply fixed_equivocation_vlsm_composition_index_incl; assumption.
Qed.

End sec_msg_dep_limited_byzantine_traces.
*)