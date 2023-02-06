From stdpp Require Import prelude finite.
From Coq Require Import FunctionalExtensionality Reals.
From VLSM.Lib Require Import Preamble FinSetExtras ListFinSetExtras.
From VLSM.Lib Require Import Measurable RealsExtras.
From VLSM.Core Require Import VLSM MessageDependencies VLSMProjections Composition ProjectionTraces.
From VLSM.Core Require Import SubProjectionTraces AnnotatedVLSM Equivocation.
From VLSM.Core Require Import ByzantineTraces.FixedSetByzantineTraces.
From VLSM.Core Require Import Equivocation.FixedSetEquivocation.
From VLSM.Core Require Import Equivocation.LimitedMessageEquivocation.
From VLSM.Core Require Import Equivocation.MsgDepLimitedEquivocation.
From VLSM.Core Require Import Equivocation.TraceWiseEquivocation.

(** * VLSM Compositions with Byzantine nodes of limited weight

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
  `{FinSet index Ci}
  `{!finite.Finite index}
  (IM : index -> VLSM message)
  `{forall i : index, HasBeenSentCapability (IM i)}
  `{forall i : index, HasBeenReceivedCapability (IM i)}
  (threshold : R)
  `{ReachableThreshold validator Cv threshold}
  `{!finite.Finite validator}
  (A : validator -> index)
  `{!Inj (=) (=) A}
  (sender : message -> option validator)
  .

(**
  We define the [limited_byzantine_trace_prop]erty in two steps. First, we
  leverage the [fixed_byzantine_trace_alt_prop]erty by assuming a fixed selection
  of <<byzantine>> nodes whose added weight is below the [ReachableThreshold].
*)
Definition fixed_limited_byzantine_trace_prop
  (s : composite_state IM)
  (tr : list (composite_transition_item IM))
  (byzantine_vs : Cv)
  (byzantine := fin_sets.set_map A byzantine_vs : Ci)
  : Prop
  := (sum_weights byzantine_vs <= threshold)%R /\
     fixed_byzantine_trace_alt_prop (Ci := Ci) IM byzantine A sender s tr.

(**
  The union of traces with the [fixed_limited_byzantine_trace_prop]erty over
  all possible selections of (limited) byzantine nodes.
*)
Definition limited_byzantine_trace_prop
  (s : composite_state IM)
  (tr : list (composite_transition_item IM))
  : Prop :=
  exists byzantine, fixed_limited_byzantine_trace_prop s tr byzantine.

Context
  `{FinSet message Cm}
  {is_equivocating_tracewise_no_has_been_sent_dec :
    RelDecision (is_equivocating_tracewise_no_has_been_sent IM A sender)}
  (limited_constraint := tracewise_limited_equivocation_constraint (Cv := Cv) IM threshold A sender)
  (Limited : VLSM message := composite_vlsm IM limited_constraint)
  (Hvalidator : forall i : index, component_message_validator_prop IM limited_constraint i)
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  (can_emit_signed : channel_authentication_prop IM A sender)
  (message_dependencies : message -> Cm)
  `{!Irreflexive (msg_dep_happens_before message_dependencies)}
  `{forall i, MessageDependencies (IM i) message_dependencies}
  (Hfull : forall i, message_dependencies_full_node_condition_prop (IM i) message_dependencies)
  .

(** ** Assuming the byzantine nodes are known

  We will first fix a selection of <<byzantine>> nodes of limited weight and
  analyze traces with the [fixed_limited_byzantine_trace_prop]erty w.r.t. that
  selection.
*)

Section sec_fixed_limited_selection.

Context
  (byzantine_vs : Cv)
  (byzantine : Ci := fin_sets.set_map A byzantine_vs )
  (non_byzantine : Ci := difference (list_to_set (enum index)) byzantine)
  (Hlimit : (sum_weights byzantine_vs <= threshold)%R)
  (PreNonByzantine := pre_loaded_fixed_non_byzantine_vlsm IM byzantine A sender)
  (Htracewise_BasicEquivocation : BasicEquivocation (composite_state IM) validator Cv threshold
    := equivocation_dec_tracewise IM threshold A sender)
  (tracewise_not_heavy := not_heavy (1 := Htracewise_BasicEquivocation))
  (tracewise_equivocating_validators := equivocating_validators (1 := Htracewise_BasicEquivocation))
  .

(**
  When replacing the byzantine components of a composite [valid_state] with
  initial states for those machines we obtain a state which is [not_heavy].
*)
Lemma limited_PreNonByzantine_valid_state_lift_not_heavy s
  (Hs : valid_state_prop PreNonByzantine s)
  (sX := lift_sub_state IM (elements non_byzantine) s)
  : tracewise_not_heavy sX.
Proof.
  cut (tracewise_equivocating_validators sX ⊆ byzantine_vs).
  {
    intro Hincl.
    unfold tracewise_not_heavy, not_heavy.
    transitivity (sum_weights byzantine_vs); [| done].
    apply sum_weights_subseteq_list.
    - by apply NoDup_elements.
    - by apply NoDup_elements.
    - intros i Hi.
      by apply elem_of_elements, Hincl, elem_of_elements, Hi.
  }
  apply valid_state_has_trace in Hs as [is [tr Htr]].
  specialize (preloaded_non_byzantine_vlsm_lift IM byzantine A sender)
    as Hproj.
  apply (VLSM_embedding_finite_valid_trace_init_to Hproj) in Htr as Hpre_tr.
  intros v Hv.
  apply equivocating_validators_is_equivocating_tracewise_iff in Hv as Hvs'.
  specialize (Hvs' _ _ Hpre_tr).
  destruct Hvs' as [m0 [Hsender0 [preX [itemX [sufX [Htr_pr [Hm0 Heqv]]]]]]].
  apply map_eq_app in Htr_pr as [pre [item_suf [Heqtr [Hpre_pr Hitem_suf_pr]]]].
  apply map_eq_cons in Hitem_suf_pr as [item [suf [Heqitem_suf [Hitem_pr Hsuf_pr]]]].
  subst tr item_suf. clear Hsuf_pr.
  subst itemX. cbn in Hm0.
  change (pre ++ item :: suf) with (pre ++ [item] ++ suf) in Htr.
  destruct Htr as [Htr Hinit].
  apply (finite_valid_trace_from_to_app_split PreNonByzantine) in Htr.
  destruct Htr as [Hpre Hitem].
  apply (VLSM_embedding_finite_valid_trace_from_to Hproj) in Hpre as Hpre_pre.
  apply valid_trace_last_pstate in Hpre_pre as Hs_pre.
  apply (finite_valid_trace_from_to_app_split PreNonByzantine), proj1 in Hitem.
  inversion Hitem; subst; clear Htl Hitem. simpl in Hm0. subst.
  destruct Ht as [[_ [_ [_ [Hc _]]]] _].
  destruct Hc as [[sub_i Hsenti] | Hemit].
  - destruct_dec_sig sub_i i Hi Heqsub_i; subst sub_i.
    assert (Hsent : composite_has_been_sent IM
                      (lift_sub_state IM (elements non_byzantine) (finite_trace_last is pre)) m0).
    {
      exists i.
      unfold lift_sub_state.
      by rewrite (lift_sub_state_to_eq _ _ _ _ _ Hi).
    }
    apply (composite_proper_sent IM) in Hsent; [| done].
    apply (VLSM_embedding_initial_state Hproj) in Hinit.
    by specialize (Hsent _ _ (conj Hpre_pre Hinit)).
  - specialize (proj1 Hemit) as [i [Hi Hsigned]].
    subst.
    destruct (decide (i ∈ byzantine)).
    + unfold channel_authenticated_message in Hsigned.
      rewrite Hsender0 in Hsigned.
      apply Some_inj in Hsigned; subst.
      by revert e; apply elem_of_set_map_inj.
    + rewrite elem_of_elements in Hi.
      contradict Hi.
      apply elem_of_difference; split; [| done].
      by apply elem_of_list_to_set, elem_of_enum.
Qed.

Existing Instance Htracewise_BasicEquivocation.

(**
  When replacing the byzantine components of a composite [valid_state] with
  initial states for those machines validity of transitions for the non-byzantine
  components is preserved.
*)
Lemma limited_PreNonByzantine_lift_valid
  : weak_embedding_valid_preservation PreNonByzantine Limited
    (lift_sub_label IM (elements non_byzantine))
    (lift_sub_state IM (elements non_byzantine)).
Proof.
  intros l s om Hv HsY HomY.
  repeat split; [by apply lift_sub_valid, Hv |].
  hnf.
  destruct (composite_transition (sub_IM IM (elements non_byzantine)) l (s, om))
    as [s' om'] eqn: Ht.
  apply (lift_sub_transition IM (elements non_byzantine)) in Ht as HtX.
  simpl in HtX |- *; rewrite HtX; simpl.
  change (is_equivocating_tracewise_no_has_been_sent _ _ _) with is_equivocating.
  by eapply tracewise_not_heavy_LimitedEquivocationProp_iff,
    limited_PreNonByzantine_valid_state_lift_not_heavy,
    input_valid_transition_destination.
Qed.

(**
  By replacing the byzantine components of a composite [valid_state] with
  initial states for those machines and ignoring transitions for byzantine nodes
  we obtain valid traces for the <<Limited>> equivocation composition.
*)
Lemma limited_PreNonByzantine_vlsm_lift
  : VLSM_embedding PreNonByzantine Limited
      (lift_sub_label IM (elements non_byzantine))
      (lift_sub_state IM (elements non_byzantine)).
Proof.
  apply basic_VLSM_embedding; intros ? *.
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
      by eapply Hvalidator.
Qed.

End sec_fixed_limited_selection.

(**
  Given a trace with the [fixed_limited_byzantine_trace_prop]erty for a selection
  of <<byzantine>> nodes, there exists a valid trace for the <<Limited>>
  equivocation composition such that the projection of the two traces to
  the <<non-byzantine>> nodes coincide.
*)
Lemma validator_fixed_limited_non_byzantine_traces_are_limited_non_equivocating s tr byzantine_vs
  (byzantine : Ci := fin_sets.set_map A byzantine_vs)
  (not_byzantine : Ci := difference (list_to_set (enum index)) byzantine)
  : fixed_limited_byzantine_trace_prop s tr byzantine_vs ->
    exists bs btr,
      finite_valid_trace Limited bs btr /\
      composite_state_sub_projection IM (elements not_byzantine) s =
      composite_state_sub_projection IM (elements not_byzantine) bs /\
      finite_trace_sub_projection IM (elements not_byzantine) tr =
      finite_trace_sub_projection IM (elements not_byzantine) btr.
Proof.
  intros [Hlimit Hfixed].
  eexists _, _; split.
  - by apply (VLSM_embedding_finite_valid_trace
            (limited_PreNonByzantine_vlsm_lift byzantine_vs Hlimit)).
  - unfold lift_sub_state.
    rewrite composite_state_sub_projection_lift_to.
    split; [done |].
    by symmetry; apply composite_trace_sub_projection_lift.
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
      exists (selection_vs : Cv)
        (selection : Ci := fin_sets.set_map A selection_vs)
        (selection_complement := difference (list_to_set (enum index)) selection),
        (sum_weights selection_vs <= threshold)%R /\
        composite_state_sub_projection IM (elements selection_complement) s =
        composite_state_sub_projection IM (elements selection_complement) bs /\
        finite_trace_sub_projection IM (elements selection_complement) tr =
        finite_trace_sub_projection IM (elements selection_complement) btr.
Proof.
  intros [byzantine Hlimited].
  apply proj1 in Hlimited as Hlimit.
  apply validator_fixed_limited_non_byzantine_traces_are_limited_non_equivocating
    in Hlimited
    as [bs [btr [Hlimited [Hs_pr Htr_pr]]]].
  by exists bs, btr; eauto.
Qed.

End sec_limited_byzantine_traces.

Section sec_msg_dep_limited_byzantine_traces.

Context
  {message : Type}
  `{FinSet index Ci}
  `{!finite.Finite index}
  (IM : index -> VLSM message)
  `{forall i, HasBeenSentCapability (IM i)}
  `{forall i, HasBeenReceivedCapability (IM i)}
  (threshold : R)
  `{ReachableThreshold validator Cv threshold}
  `{!finite.Finite validator}
  `{FinSet message Cm}
  (message_dependencies : message -> Cm)
  (full_message_dependencies : message -> Cm)
  `{!FullMessageDependencies message_dependencies full_message_dependencies}
  `{forall i, MessageDependencies (IM i) message_dependencies}
  (sender : message -> option validator)
  (A : validator -> index)
  `{!Inj (=) (=) A}
  (Limited := msg_dep_limited_equivocation_vlsm (Cv := Cv)
    IM threshold full_message_dependencies sender)
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  (Hchannel : channel_authentication_prop IM A sender)
  (Hsender_safety : sender_safety_alt_prop IM A sender :=
    channel_authentication_sender_safety _ _ _ Hchannel)
  (Hvalidator :
    forall i : index,
      msg_dep_limited_equivocation_message_validator_prop (Cv := Cv)
        IM threshold full_message_dependencies sender i)
  (Hfull : forall i, message_dependencies_full_node_condition_prop (IM i) message_dependencies)
  .

(**
  If the set of byzantine nodes is weight-limited and if an [input_valid_transition]
  of the non-byzantine nodes from a state of weight-limited equivocation does not
  introduce equivocators from the non-byzantine nodes, then the transition is valid
  for weight-limited equivocation.
*)
Lemma lift_pre_loaded_fixed_non_byzantine_valid_transition_to_limited
  (byzantine_vs : Cv)
  (byzantine : Ci := fin_sets.set_map A byzantine_vs)
  (non_byzantine := difference (list_to_set (enum index)) byzantine)
  (Hlimited : (sum_weights byzantine_vs <= threshold)%R)
  sub_l sub_s iom sub_sf oom
  (Ht_sub : input_valid_transition
      (pre_loaded_fixed_non_byzantine_vlsm IM byzantine A sender)
      sub_l (sub_s, iom) (sub_sf, oom))
  ann_s
  (Hann_s : valid_state_prop Limited ann_s)
  (Hann_s_pr : original_state ann_s = lift_sub_state IM (elements non_byzantine) sub_s)
  (ann' := msg_dep_composite_transition_message_equivocators IM full_message_dependencies sender
      (lift_sub_label IM (elements non_byzantine) sub_l) (ann_s, iom))
  (Heqv_byzantine : ann' ⊆ byzantine_vs)
  : input_valid_transition Limited
      (lift_sub_label IM (elements non_byzantine) sub_l) (ann_s, iom)
      (Build_annotated_state (free_composite_vlsm IM) Cv
        (lift_sub_state IM (elements non_byzantine) sub_sf) ann',
      oom).
Proof.
  destruct sub_l as [sub_i li]; destruct_dec_sig sub_i i Hi Heqsub_i; subst.
  repeat split; cbn.
  - done.
  - destruct iom as [im |]; [| apply option_valid_message_None].
    by eapply Hvalidator, pre_loaded_sub_composite_input_valid_projection, Ht_sub.
  - unfold lift_sub_state in Hann_s_pr.
    rewrite Hann_s_pr, (lift_sub_state_to_eq _ _ _ _ _ Hi).
    by apply Ht_sub.
  - apply Rle_trans with (sum_weights byzantine_vs)
    ; [| done].
    apply sum_weights_subseteq.
    by intro; apply Heqv_byzantine.
  - clear -Ht_sub Hann_s_pr.
    destruct Ht_sub as [_ Ht_sub]; revert Ht_sub
    ; unfold annotated_transition; cbn
    ; rewrite Hann_s_pr; unfold lift_sub_state at 1
    ; rewrite (lift_sub_state_to_eq _ _ _ _ _ Hi)
    ; unfold sub_IM at 2; cbn
    ; destruct (vtransition _ _ _) as (si', om')
    ; inversion_clear 1.
    do 2 f_equal; extensionality j.
    unfold lift_sub_state.
    destruct (decide (i = j)); subst; state_update_simpl.
    + by rewrite (lift_sub_state_to_eq _ _ _ _ _ Hi), !state_update_eq.
    + unfold lift_sub_state_to.
      by case_decide; [rewrite sub_IM_state_update_neq |].
Qed.

Existing Instance elem_of_dec_slow.

(**
  Considering a trace with the [fixed_byzantine_trace_alt_prop]erty for a
  set <<byzantine>> of indices of bounded weight, its subtrace corresponding to
  the non-byzantine nodes is of limited equivocation and its set of equivocators
  is included in <<byzantine>>.
*)
Lemma lift_fixed_byzantine_traces_to_limited
  (s : composite_state IM)
  (tr : list (composite_transition_item IM))
  (byzantine_vs : Cv)
  (byzantine : Ci := fin_sets.set_map A byzantine_vs)
  (non_byzantine := difference (list_to_set (enum index)) byzantine)
  (Hlimited : (sum_weights byzantine_vs <= threshold)%R)
  (Hbyzantine :
    fixed_byzantine_trace_alt_prop IM byzantine A sender s tr)
  (s_reset_byzantine :=
    lift_sub_state IM (elements non_byzantine)
      (composite_state_sub_projection IM (elements non_byzantine) s))
  (bs := Build_annotated_state (free_composite_vlsm IM) Cv s_reset_byzantine (` inhabitant))
  (btr :=
    msg_dep_annotate_trace_with_equivocators (Cv := Cv) IM full_message_dependencies sender
      s_reset_byzantine
      (pre_VLSM_embedding_finite_trace_project _ _
        (lift_sub_label IM (elements non_byzantine)) (lift_sub_state IM (elements non_byzantine))
        (finite_trace_sub_projection IM (elements non_byzantine) tr)))
  : finite_valid_trace Limited bs btr /\
    state_annotation (@finite_trace_last _ (type Limited) bs btr) ⊆ byzantine_vs.
Proof.
  subst non_byzantine.
  induction Hbyzantine using finite_valid_trace_rev_ind; [repeat split |].
  - constructor; apply initial_state_is_valid.
    by repeat split; cbn; apply lift_sub_state_initial.
  - by cbn; apply lift_sub_state_initial.
  - by apply empty_subseteq.
  - subst s_reset_byzantine bs btr.
    unfold pre_VLSM_embedding_finite_trace_project; rewrite !map_app.
    rewrite @msg_dep_annotate_trace_with_equivocators_app; cbn.
    unfold annotate_trace_item; cbn; rewrite finite_trace_last_is_last; cbn.
    destruct l as [sub_i li]; destruct_dec_sig sub_i i Hi Heqsub_i; subst sub_i
    ; destruct IHHbyzantine as [[Htr0_ann Hsi_ann] Htr0_eqv_byzantine]
    ; cbn in Htr0_eqv_byzantine |- *.
    remember (@finite_trace_last _ (annotated_type (free_composite_vlsm IM) _) _ _)
     as lst in Htr0_eqv_byzantine at 1 |- * at 1 2 3 4 5 6.
    assert (Hlsti : original_state lst = lift_sub_state IM (elements (list_to_set (enum index) ∖ byzantine))
                                          (finite_trace_last si tr0)).
    {
      subst lst; rewrite msg_dep_annotate_trace_with_equivocators_last_original_state; symmetry.
      apply (pre_VLSM_embedding_finite_trace_last _ _
              (lift_sub_label IM _)
              (lift_sub_state IM _)).
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
      by eapply lift_pre_loaded_fixed_non_byzantine_valid_transition_to_limited;
        [| | subst lst; apply finite_valid_trace_last_pstate | |].
    }
    destruct iom as [im |]; [| done].
    apply set_union_subseteq_iff; split; [done |].
    unfold coeqv_message_equivocators
    ; case_decide as Hnobs; [by apply empty_subseteq |].
    rewrite (full_node_msg_dep_coequivocating_senders _ _ _ _ Hfull _ _ i li);
      [| by cbn; rewrite Hlsti; eapply @pre_loaded_sub_composite_input_valid_projection, Hx].
    rewrite elements_empty, app_nil_r; cbn.
    intro _i_im; rewrite elem_of_list_to_set.
    destruct (sender im) as [i_im |] eqn: Hsender; [| by inversion 1].
    rewrite elem_of_list_singleton; intro; subst _i_im.
    destruct Hx as [(_ & _ & _ & [Hsent | [Hsigned _]] & _) _].
    + contradict Hnobs.
      destruct Hsent as [sub_i_im Hsent]; cbn in Hsent |- *
      ; destruct_dec_sig sub_i_im _i_im H_i_im Heqsub_i_im; subst sub_i_im.
      apply composite_has_been_directly_observed_sent_received_iff; left.
      exists _i_im.
      rewrite Hlsti; cbn; unfold lift_sub_state.
      by rewrite (lift_sub_state_to_eq _ _ _ _ _ H_i_im).
    + destruct Hsigned as (_i_im & H_i_im & Hauth).
      unfold channel_authenticated_message in Hauth
      ; rewrite Hsender in Hauth.
      apply Some_inj in Hauth; subst _i_im.
      destruct (decide (i_im ∈ byzantine_vs)) as [Hi_im | Hni_im]; [done |].
      contradict H_i_im.
      apply elem_of_elements, elem_of_difference; cbn.
      split; [by apply elem_of_list_to_set, elem_of_enum |].
      by contradict Hni_im; revert Hni_im; apply elem_of_set_map_inj.
Qed.

(**
  Under full-message dependencies and full node assumptions, if all components are
  validators for the [msg_dep_limited_equivocation_vlsm] associated to their
  composition, then the traces exposed limited Byzantine behavior coincide with
  the traces exposed to limited equivocation.
*)
Lemma msg_dep_validator_limited_non_equivocating_byzantine_traces_are_limited_non_equivocating s tr
  : limited_byzantine_trace_prop (Ci := Ci) (Cv := Cv) IM threshold A sender s tr <->
    exists bs btr selection_vs
      (selection : Ci := fin_sets.set_map A selection_vs)
      (selection_complement := difference (list_to_set (enum index)) selection),
      finite_valid_trace Limited bs btr /\
      state_annotation (finite_trace_last bs btr) ⊆ selection_vs /\
      (sum_weights selection_vs <= threshold)%R /\
      composite_state_sub_projection IM (elements selection_complement) s =
        composite_state_sub_projection IM (elements selection_complement) (original_state bs) /\
      finite_trace_sub_projection IM (elements selection_complement) tr =
        finite_trace_sub_projection IM (elements selection_complement)
          (pre_VLSM_embedding_finite_trace_project
            (type Limited) (composite_type IM) Datatypes.id original_state btr).
Proof.
  split.
  - intros (byzantine & Hlimited & Hbyzantine).
    apply lift_fixed_byzantine_traces_to_limited in Hbyzantine
       as [Hbtr Heqv_byzantine] ; [| done].
    eexists _, _, byzantine; do 3 (split; [done |]); split.
    + extensionality sub_i; destruct_dec_sig sub_i i Hi Heqsub_i; subst; cbn.
      unfold lift_sub_state.
      by rewrite (lift_sub_state_to_eq _ _ _ _ _ Hi).
    + subst Limited.
      rewrite msg_dep_annotate_trace_with_equivocators_project.
      by symmetry; apply composite_trace_sub_projection_lift.
  - intros (bs & btr & byzantine & Hbtr & Heqv_byzantine & Hlimited & His_pr & Htr_pr).
    exists byzantine; split; [done |].
    eapply VLSM_incl_finite_valid_trace
    ; [by apply fixed_non_equivocating_incl_fixed_non_byzantine |].
    apply fixed_non_equivocating_traces_char.
    symmetry in His_pr, Htr_pr.
    eexists _, _; split; [| done].
    eapply @msg_dep_fixed_limited_equivocation_witnessed in Hbtr as [_ Hbtr]; [| done..].
    revert Hbtr; apply VLSM_incl_finite_valid_trace.
    apply fixed_equivocation_vlsm_composition_index_incl.
    intro; rewrite !elem_of_elements.
    by apply set_map_mono.
Qed.

End sec_msg_dep_limited_byzantine_traces.
