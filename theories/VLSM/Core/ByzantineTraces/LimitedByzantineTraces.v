From stdpp Require Import prelude finite.
From Coq Require Import FunctionalExtensionality Reals.
From VLSM.Lib Require Import Preamble StdppListSet Measurable FinFunExtras StdppExtras ListSetExtras.
From VLSM.Core Require Import VLSM MessageDependencies VLSMProjections Composition ProjectionTraces.
From VLSM.Core Require Import SubProjectionTraces AnnotatedVLSM ByzantineTraces FixedSetByzantineTraces.
From VLSM.Core Require Import Validator Equivocation Equivocation.FixedSetEquivocation.
From VLSM.Core Require Import Equivocation.LimitedEquivocation Equivocation.LimitedEquivocation.
From VLSM.Core Require Import Equivocation.MsgDepLimitedEquivocation Equivocation.TraceWiseEquivocation.

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

Section limited_byzantine_traces.

Context
  {message : Type}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  `{forall i : index, HasBeenSentCapability (IM i)}
  `{forall i : index, HasBeenReceivedCapability (IM i)}
  (sender : message -> option index)
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
     fixed_byzantine_trace_alt_prop IM byzantine (fun i => i) sender s tr.

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
  (limited_constraint := tracewise_limited_equivocation_constraint IM sender)
  (Limited : VLSM message := composite_vlsm IM limited_constraint)
  (Hvalidator: forall i : index, component_message_validator_prop IM limited_constraint i)
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  (can_emit_signed : channel_authentication_prop IM Datatypes.id sender)
  (message_dependencies : message -> set message)
  `{forall i, MessageDependencies message_dependencies (IM i)}
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
  (PreNonByzantine := pre_loaded_fixed_non_byzantine_vlsm IM byzantine (λ i : index, i) sender)
  (Htracewise_BasicEquivocation : BasicEquivocation (composite_state IM) index
    := equivocation_dec_tracewise IM (fun i => i) sender)
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
    transitivity (sum_weights (remove_dups byzantine)); [| done].
    apply sum_weights_subseteq.
    - apply equivocating_validators_nodup.
    - apply NoDup_remove_dups.
    - intros i Hi. apply elem_of_remove_dups, Hincl, Hi.
  }
  apply valid_state_has_trace in Hs as [is [tr Htr]].
  specialize (preloaded_non_byzantine_vlsm_lift IM byzantine (fun i => i) sender)
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
    assert (Hsent : composite_has_been_sent IM
                      (lift_sub_state IM non_byzantine (finite_trace_last is pre)) m0).
    { exists i.
      unfold lift_sub_state.
      by rewrite (lift_sub_state_to_eq _ _ _ _ _ Hi).
    }
    apply (composite_proper_sent IM) in Hsent; [| done].
    apply (VLSM_full_projection_initial_state Hproj) in Hinit.
    by specialize (Hsent _ _ (conj Hpre_pre Hinit)).
  + specialize (proj1 Hemit) as [i [Hi Hsigned]].
    subst.
    destruct (decide (i ∈ byzantine)).
      * unfold channel_authenticated_message in Hsigned.
        rewrite Hsender0 in Hsigned.
        by apply Some_inj in Hsigned; subst.
      * by destruct Hi; apply set_diff_intro; [apply elem_of_enum|].
Qed.

Existing Instance Htracewise_BasicEquivocation.

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
  - reduce.
    destruct
      (composite_transition (sub_IM IM non_byzantine) l (s, om))
      as (s', om') eqn: Ht.
    apply (lift_sub_transition IM non_byzantine) in Ht
      as HtX.
    simpl in HtX |- *. rewrite HtX. simpl.
    change (is_equivocating_tracewise_no_has_been_sent _ _ _) with is_equivocating.
    by eapply tracewise_not_heavy_LimitedEquivocationProp_iff,
      limited_PreNonByzantine_valid_state_lift_not_heavy,
      input_valid_transition_destination.
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
  apply basic_VLSM_full_projection; intros ? *.
  - by intros; apply limited_PreNonByzantine_lift_valid.
  - by intros * []; rapply lift_sub_transition.
  - by intros; apply (lift_sub_state_initial IM).
  - intros Hv HsY [[sub_i [[im Him] Heqm]] | Hseeded].
    + cbn in Heqm; subst.
      destruct_dec_sig sub_i i Hi Heqsub_i; subst.
      unfold sub_IM in Him; cbn in Him; clear -Him.
      apply initial_message_is_valid.
      by exists i, (exist _ m Him).
    + destruct Hseeded as (Hsigned & i & Hi & li & si & Hpre_valid).
      apply set_diff_elim2 in Hi.
      by eapply Hvalidator.
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
  - by apply (VLSM_full_projection_finite_valid_trace
            (limited_PreNonByzantine_vlsm_lift byzantine Hlimit)).
  - unfold lift_sub_state.
    rewrite composite_state_sub_projection_lift_to.
    split; [done |].
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
  exists bs, btr; eauto.
Qed.

End limited_byzantine_traces.

Section sec_msg_dep_limited_byzantine_traces.

Context
  {message : Type}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  `{forall i, HasBeenSentCapability (IM i)}
  `{forall i, HasBeenReceivedCapability (IM i)}
  (message_dependencies : message -> set message)
  `{forall i, MessageDependencies message_dependencies (IM i)}
  (full_message_dependencies : message -> set message)
  `{FullMessageDependencies message message_dependencies full_message_dependencies}
  `{ReachableThreshold index}
  (sender : message -> option index)
  (Limited := msg_dep_limited_equivocation_vlsm IM full_message_dependencies sender)
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  (Hchannel : channel_authentication_prop IM Datatypes.id sender)
  (Hsender_safety : sender_safety_alt_prop IM Datatypes.id sender :=
    channel_authentication_sender_safety _ _ _ Hchannel)
  (Hvalidator:
    forall i : index,
      msg_dep_limited_equivocation_message_validator_prop IM
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
      (pre_loaded_fixed_non_byzantine_vlsm IM byzantine Datatypes.id sender)
      sub_l (sub_s, iom) (sub_sf, oom))
  ann_s
  (Hann_s : valid_state_prop Limited ann_s)
  (Hann_s_pr : original_state ann_s = lift_sub_state IM non_byzantine sub_s)
  (ann' := msg_dep_composite_transition_message_equivocators IM full_message_dependencies sender
      (lift_sub_label IM non_byzantine sub_l) (ann_s, iom))
  (Heqv_byzantine : ann' ⊆ byzantine)
  : input_valid_transition Limited
      (lift_sub_label IM non_byzantine sub_l) (ann_s, iom)
      (Build_annotated_state (free_composite_vlsm IM) (set index)
        (lift_sub_state IM non_byzantine sub_sf) ann',
      oom).
Proof.
  destruct sub_l as [sub_i li]; destruct_dec_sig sub_i i Hi Heqsub_i; subst.
  repeat split; cbn.
  - done.
  - destruct iom as [im |]; [| apply option_valid_message_None].
    eapply Hvalidator,
      pre_loaded_sub_composite_input_valid_projection, Ht_sub.
  - unfold lift_sub_state in Hann_s_pr.
    rewrite Hann_s_pr, (lift_sub_state_to_eq _ _ _ _ _ Hi).
    apply Ht_sub.
  - apply Rle_trans with (sum_weights (remove_dups byzantine))
    ; [| done].
    apply sum_weights_subseteq.
    + cut (NoDup (state_annotation ann_s)).
      {
        intro Hnodup.
        destruct iom as [im |]; [| done].
        by apply set_union_nodup_left.
      }
      by eapply coeqv_limited_equivocation_state_annotation_nodup.
    + apply NoDup_remove_dups.
    + intro; rewrite elem_of_remove_dups; apply Heqv_byzantine.
  - clear -Ht_sub Hann_s_pr.
    destruct Ht_sub as [_ Ht_sub]; revert Ht_sub
    ; unfold annotated_transition; cbn
    ; rewrite Hann_s_pr; unfold lift_sub_state at 1
    ; rewrite (lift_sub_state_to_eq _ _ _ _ _ Hi)
    ; unfold sub_IM at 2; cbn
    ; destruct (vtransition _ _ _) as (si', om')
    ; inversion_clear 1.
    do 2 f_equal; extensionality j.
    destruct (decide (i = j)) as [| Hij]; subst.
    + unfold lift_sub_state.
      by rewrite (lift_sub_state_to_eq _ _ _ _ _ Hi), !state_update_eq.
    + rewrite state_update_neq by congruence.
      unfold lift_sub_state.
      destruct (decide (j ∈ set_diff (enum index) byzantine)) as [Hj |].
      * by rewrite !(lift_sub_state_to_eq _ _ _ _ _ Hj), sub_IM_state_update_neq.
      * by rewrite !lift_sub_state_to_neq.
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
    fixed_byzantine_trace_alt_prop IM byzantine Datatypes.id sender s tr)
  (s_reset_byzantine :=
    lift_sub_state IM non_byzantine
      (composite_state_sub_projection IM non_byzantine s))
  (bs := Build_annotated_state (free_composite_vlsm IM) (set index) s_reset_byzantine (` inhabitant))
  (btr :=
    msg_dep_annotate_trace_with_equivocators IM full_message_dependencies sender
      s_reset_byzantine
      (pre_VLSM_full_projection_finite_trace_project _ _
        (lift_sub_label IM non_byzantine) (lift_sub_state IM (set_diff (enum index) byzantine))
        (finite_trace_sub_projection IM non_byzantine tr)))
  : finite_valid_trace Limited bs btr /\
    state_annotation (@finite_trace_last _ (type Limited) bs btr) ⊆ byzantine.
Proof.
  subst non_byzantine.
  induction Hbyzantine using finite_valid_trace_rev_ind; [repeat split |].
  - constructor; apply initial_state_is_valid.
    by repeat split; cbn; apply lift_sub_state_initial.
  - by cbn; apply lift_sub_state_initial.
  - apply list_subseteq_nil.
  - subst s_reset_byzantine bs btr.
    unfold pre_VLSM_full_projection_finite_trace_project
    ; rewrite !map_app; setoid_rewrite annotate_trace_from_app; cbn
    ; unfold annotate_trace_item; cbn
    ; rewrite finite_trace_last_is_last; cbn.
    destruct l as [sub_i li]; destruct_dec_sig sub_i i Hi Heqsub_i; subst sub_i
    ; destruct IHHbyzantine as [[Htr0_ann Hsi_ann] Htr0_eqv_byzantine]
    ; cbn in Htr0_eqv_byzantine |- *.
    remember (@finite_trace_last _(annotated_type (free_composite_vlsm IM) (set index)) _ _)
          as lst.
    assert (Hlsti : original_state lst = lift_sub_state IM (set_diff (enum index) byzantine)
                                          (finite_trace_last si tr0)).
    {
      subst lst; rewrite annotate_trace_from_last_original_state; symmetry.
      apply (pre_VLSM_full_projection_finite_trace_last _ _
              (lift_sub_label IM (set_diff (enum index) byzantine))
              (lift_sub_state IM (set_diff (enum index) byzantine))).
    }
    match goal with
    |- _ /\ ?B => cut B
    end.
    {
      intro Heqv_byzantine.
      do 2 (split; [| done]).
      apply finite_valid_trace_from_app_iff; split; [done |].
      subst x; cbn; apply finite_valid_trace_singleton.
      replace (finite_trace_last _ _) with lst.
      eapply lift_pre_loaded_fixed_non_byzantine_valid_transition_to_limited.
      1-2, 4-5: done.
      by subst lst; apply finite_valid_trace_last_pstate.
    }
    destruct iom as [im |]; [| done].
    apply set_union_subseteq_iff; split; [done |].
    unfold coeqv_message_equivocators
    ; case_decide as Hnobs; [apply list_subseteq_nil |].
    rewrite (full_node_msg_dep_coequivocating_senders _ _ _ _ Hfull _ _ i li).
    2: cbn; rewrite Hlsti
    ; eapply @pre_loaded_sub_composite_input_valid_projection, Hx.
    rewrite app_nil_r; cbn.
    destruct (sender im) as [i_im |] eqn: Hsender
    ; [| apply list_subseteq_nil].
    intro _i_im; rewrite elem_of_list_singleton; intro; subst _i_im.
    destruct Hx as [(_ & _ & _ & [Hsent | [Hsigned _]] & _) _].
    + contradict Hnobs.
      destruct Hsent as [sub_i_im Hsent]; cbn in Hsent |- *
      ; destruct_dec_sig sub_i_im _i_im H_i_im Heqsub_i_im; subst sub_i_im.
      apply composite_has_been_observed_sent_received_iff; left.
      exists _i_im.
      rewrite Hlsti; cbn; unfold lift_sub_state.
      by rewrite (lift_sub_state_to_eq _ _ _ _ _ H_i_im).
    + clear -Hsender Hsigned.
      destruct Hsigned as (_i_im & H_i_im & Hauth).
      unfold channel_authenticated_message in Hauth
      ; rewrite Hsender in Hauth.
      apply Some_inj in Hauth; subst _i_im.
      destruct (decide (i_im ∈ byzantine)) as [Hi_im | Hni_im]
      ; [done | contradict H_i_im].
      apply set_diff_intro; [apply elem_of_enum | done].
Qed.

(**
Under full-message dependencies and full node assumptions, if all components are
validators for the [msg_dep_limited_equivocation_vlsm] associated to their
composition, then the traces exposed limited Byzantine behaviour coincide with
the traces exposed to limited equivocation.
*)
Lemma msg_dep_validator_limited_non_byzantine_traces_are_limited_non_equivocating s tr
  : limited_byzantine_trace_prop IM sender s tr <->
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
       as [Hbtr Heqv_byzantine] ; [| done].
    eexists _,_, byzantine; do 3 (split; [done |]); split.
    + extensionality sub_i; destruct_dec_sig sub_i i Hi Heqsub_i; subst; cbn.
      unfold lift_sub_state.
      by rewrite (lift_sub_state_to_eq _ _ _ _ _ Hi).
    + subst Limited.
      rewrite msg_dep_annotate_trace_with_equivocators_project.
      symmetry; apply composite_trace_sub_projection_lift.
  - intros (bs & btr & byzantine & Hbtr & Heqv_byzantine & Hlimited & His_pr & Htr_pr).
    exists byzantine; split; [done |].
    eapply VLSM_incl_finite_valid_trace
    ; [by apply fixed_non_equivocating_incl_fixed_non_byzantine |].
    apply fixed_non_equivocating_traces_char.
    symmetry in His_pr, Htr_pr.
    eexists _,_; split; [| done].
    eapply msg_dep_fixed_limited_equivocation_witnessed, proj2 in Hbtr.
    2-5: done.
    revert Hbtr; apply VLSM_incl_finite_valid_trace.
    by apply fixed_equivocation_vlsm_composition_index_incl.
Qed.

End sec_msg_dep_limited_byzantine_traces.
