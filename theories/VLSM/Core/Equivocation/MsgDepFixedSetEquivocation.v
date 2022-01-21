From stdpp Require Import prelude finite.
From Coq Require Import Relations.Relation_Operators.
From VLSM.Lib Require Import Preamble StdppListSet FinFunExtras.
From VLSM.Core Require Import VLSM MessageDependencies VLSMProjections Composition Equivocation FixedSetEquivocation ProjectionTraces SubProjectionTraces.

Section msg_dep_fixed_set_equivocation.

Context
  {message : Type}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  (Hbs : forall i, HasBeenSentCapability (IM i))
  (Hbr : forall i, HasBeenReceivedCapability (IM i))
  (Hbo := fun i => HasBeenObservedCapability_from_sent_received (IM i))
  (message_dependencies : message -> set message)
  (HMsgDep : forall i, MessageDependencies message_dependencies (IM i))
  (equivocators : set index)
  (Hbs_sub : forall sub_i, HasBeenSentCapability (sub_IM IM equivocators sub_i) := sub_has_been_sent_capabilities IM equivocators Hbs)
  (Hbr_sub : forall sub_i, HasBeenReceivedCapability (sub_IM IM equivocators sub_i) := sub_has_been_received_capabilities IM equivocators Hbr)
  (Hbo_sub := fun sub_i => HasBeenObservedCapability_from_sent_received (sub_IM IM equivocators sub_i))
  .

Definition equivocator_can_emit (m : message) : Prop :=
  exists i, i ∈ equivocators /\ can_emit (pre_loaded_with_all_messages_vlsm (IM i)) m.

Definition dependencies_with_non_equivocating_senders_were_sent s m : Prop :=
  forall dm, msg_dep_happens_before message_dependencies dm m ->
    sent_by_non_equivocating IM _ equivocators s dm \/ equivocator_can_emit dm.

Definition msg_dep_fixed_set_equivocation (s : composite_state IM) (m : message) :=
  sent_by_non_equivocating IM _ equivocators s m \/
  equivocator_can_emit m /\
  dependencies_with_non_equivocating_senders_were_sent s m.

Definition msg_dep_fixed_set_equivocation_constraint
  (l : composite_label IM)
  (som : composite_state IM * option message)
  : Prop :=
  let (s, om) := som in
  from_option (msg_dep_fixed_set_equivocation s) True om.

Definition msg_dep_fixed_set_equivocation_vlsm : VLSM message :=
  composite_vlsm IM msg_dep_fixed_set_equivocation_constraint.

Lemma messages_with_valid_dependences_can_be_emitted s dm
  (Hdepm:
    forall dm0, msg_dep_rel message_dependencies dm0 dm ->
    valid_message_prop (equivocators_composition_for_sent IM Hbs equivocators s) dm0)
  (dm_i: index)
  (Hdm_i: dm_i ∈ equivocators)
  (Hemitted: can_emit (pre_loaded_with_all_messages_vlsm (IM dm_i)) dm)
  : can_emit (equivocators_composition_for_sent IM Hbs equivocators s) dm.
Proof.
  apply valid_preloaded_lifts_can_be_emitted with dm_i (fun m => m ∈ message_dependencies dm)
  ; [assumption|assumption|].
  apply message_dependencies_are_sufficient with (Hbs dm_i) (Hbr dm_i); [|assumption].
  intuition.
Qed.

Lemma msg_dep_rel_reflects_dependencies_with_non_equivocating_senders_were_sent s
  : forall dm m, msg_dep_rel message_dependencies dm m ->
    dependencies_with_non_equivocating_senders_were_sent s m ->
    dependencies_with_non_equivocating_senders_were_sent s dm.
Proof.
  intros dm m Hdm Hdeps dm0 Hdm0.
  apply Hdeps.
  transitivity dm; [assumption|].
  apply msg_dep_happens_before_iff_one.
  left.
  assumption.
Qed.

Lemma dependencies_are_valid s m
  (Hmsg_dep_happens_before_wf : well_founded (msg_dep_happens_before message_dependencies))
  : dependencies_with_non_equivocating_senders_were_sent s m ->
    forall dm, msg_dep_rel message_dependencies dm m ->
      valid_message_prop
        (equivocators_composition_for_sent IM Hbs equivocators s) dm.
Proof.
  induction m as [m Hind] using (well_founded_ind Hmsg_dep_happens_before_wf).
  intros Heqv dm Hdm.
  apply emitted_messages_are_valid_iff.
  assert (Hdm_hb : msg_dep_happens_before message_dependencies dm m)
    by (apply msg_dep_happens_before_iff_one; left; assumption).
  destruct (Heqv _ Hdm_hb) as [Hsent | [dm_i [Hdm_i Hemitted]]]
  ; [left; right; assumption|].
  right.
  apply messages_with_valid_dependences_can_be_emitted with dm_i
  ; [|assumption|assumption].
  intros dm0 Hdm0.
  apply Hind with dm; [assumption| |assumption].
  - clear -Heqv Hdm.
    revert dm m Hdm Heqv.
    apply msg_dep_rel_reflects_dependencies_with_non_equivocating_senders_were_sent.
Qed.

Lemma msg_dep_strong_fixed_equivocation_subsumption s m
  (Hmsg_dep_happens_before_wf : well_founded (msg_dep_happens_before message_dependencies))
  : msg_dep_fixed_set_equivocation s m ->
    strong_fixed_equivocation IM Hbs equivocators s m.
Proof.
  intros  [Hsent | [[i [Hi Hemit]] Heqv]]; [left; assumption|].
  cut (forall dm, msg_dep_rel message_dependencies dm m -> valid_message_prop (equivocators_composition_for_sent IM Hbs equivocators s) dm)
  ; [|apply dependencies_are_valid; assumption].
  intro Hdeps.
  right.
  apply messages_with_valid_dependences_can_be_emitted with i; [|assumption|assumption].
  intros dm0 Hdm0.
  apply Hdeps.
  assumption.
Qed.

Lemma msg_dep_strong_fixed_equivocation_constraint_subsumption
  (Hmsg_dep_happens_before_wf : well_founded (msg_dep_happens_before message_dependencies))
  : strong_constraint_subsumption IM
    msg_dep_fixed_set_equivocation_constraint
    (strong_fixed_equivocation_constraint IM Hbs equivocators).
Proof.
  intros l (s, [m|]) Hc; [|exact I].
  apply msg_dep_strong_fixed_equivocation_subsumption; assumption.
Qed.

Lemma single_equivocator_projection s j
  (Hj : j ∈ equivocators)
  : VLSM_projection
    (equivocators_composition_for_sent IM Hbs equivocators s)
    (pre_loaded_with_all_messages_vlsm (IM j))
    (sub_label_element_project IM equivocators j)
    (sub_state_element_project IM equivocators j Hj).
Proof.
  apply basic_VLSM_projection.
  - intros lX lY HlX_pr sX om [_ [_ [HvX _]]] HsY _.
    revert HvX.
    destruct lX as [sub_i li].
    destruct_dec_sig sub_i i Hi Heqsub_i.
    subst.
    unfold sub_label_element_project in HlX_pr.
    cbn in HlX_pr.
    case_decide as Heqij; [|congruence].
    subst i.
    cbv in HlX_pr.
    apply Some_inj in HlX_pr. subst li.
    unfold sub_IM, sub_state_element_project.
    cbn.
    match goal with
    |- vvalid _ _ (?s,_) -> vvalid _ _ (?s',_) =>
      replace s with s'
    end
    ; [exact id | apply sub_IM_state_pi].
  - intros lX lY HlX_pr sX om sX' om' [_ HtX].
    revert HtX.
    destruct lX as [sub_i li].
    destruct_dec_sig sub_i i Hi Heqsub_i.
    subst.
    unfold sub_label_element_project in HlX_pr.
    cbn in HlX_pr.
    case_decide as Heqij; [|congruence].
    subst i.
    cbv in HlX_pr.
    apply Some_inj in HlX_pr. subst li.
    cbn.
    unfold sub_IM, sub_state_element_project.
    cbn.
    match goal with
    |- (let (_, _) := vtransition _ _ (?s,_) in _) = _ -> vtransition _ _ (?s',_) = _ =>
      replace s with s'
    end
    ; [| apply sub_IM_state_pi].
    destruct (vtransition _ _ _) as (sj', _om').
    intro Ht. inversion Ht. subst _om' sX'. clear Ht.
    f_equal.
    symmetry.
    apply sub_IM_state_update_eq.
  - intros lX HlX_pr sX om sX' om' [_ HtX].
    destruct lX as [sub_i li].
    destruct_dec_sig sub_i i Hi Heqsub_i.
    subst.
    unfold sub_label_element_project in HlX_pr.
    cbn in HlX_pr.
    case_decide as Heqij; [congruence|].
    cbn in HtX.
    destruct (vtransition _ _ _) as (si', _om').
    inversion HtX. subst _om' sX'. clear HtX.
    unfold sub_state_element_project.
    rewrite sub_IM_state_update_neq by congruence.
    reflexivity.
  - intros sX HsX.
    specialize (HsX (dexist j Hj)).
    assumption.
  - intro; intros. apply any_message_is_valid_in_preloaded.
Qed.

Lemma equivocators_composition_can_emit_sender s m
  : can_emit (equivocators_composition_for_sent IM Hbs equivocators s) m ->
    equivocator_can_emit m.
Proof.
  intros [(sX, iom) [(sub_i, li) [sX' HtX]]].
  destruct_dec_sig sub_i i Hi Heqsub_i.
  subst.
  exists i. split; [assumption|]. apply can_emit_iff.
  apply
    (VLSM_projection_input_valid_transition
      (single_equivocator_projection s i Hi)) with (lY := li) in HtX
  ; [eexists _,_,_; eassumption|].
  unfold sub_label_element_project. cbn.
  case_decide as Heqi; [|contradiction].
  replace Heqi with (eq_refl (A := index) (x := i)); [reflexivity|].
  apply Eqdep_dec.UIP_dec.
  assumption.
Qed.

Lemma msg_dep_rel_reflects_strong_fixed_equivocation
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  : forall s, valid_state_prop (composite_vlsm IM (strong_fixed_equivocation_constraint IM Hbs equivocators)) s ->
    forall dm m, msg_dep_rel message_dependencies dm m ->
    strong_fixed_equivocation IM Hbs equivocators s m ->
    strong_fixed_equivocation IM Hbs equivocators s dm.
Proof.
  intros s Hs dm m Hdm [Hsent | Hemit].
  - destruct Hsent as [i [Hni Hsent]].
    apply valid_state_has_trace in Hs as Htr.
    destruct Htr as [is [tr Htr]].
    eapply VLSM_incl_finite_valid_trace_init_to in Htr as Hpre_tr
    ; [|apply constraint_preloaded_free_incl].
    apply
      (VLSM_projection_finite_valid_trace_init_to
        (preloaded_component_projection IM i))
      in Hpre_tr.
    apply valid_trace_last_pstate in Hpre_tr as Hsi.
    apply proper_sent in Hsent; [|assumption].
    specialize (Hsent _ _ Hpre_tr).
    apply Exists_exists in Hsent as [item [Hitem Hout]].
    apply elem_of_list_In in Hitem.
    apply pre_VLSM_projection_trace_project_in_iff in Hitem as HitemX.
    destruct HitemX as [itemX [HitemX HitemX_pr]].
    destruct itemX.
    unfold pre_VLSM_projection_transition_item_project, composite_project_label in HitemX_pr.
    cbn in HitemX_pr.
    case_decide as Hi; simpl in HitemX_pr; [|congruence].
    apply Some_inj in HitemX_pr.
    apply in_split in Hitem as [pre [suf Htr_pr]].
    change (pre ++ item :: suf) with (pre ++ [item] ++ suf) in Htr_pr.
    rewrite app_assoc in Htr_pr.
    rewrite Htr_pr in Hpre_tr.
    destruct Hpre_tr as [Hpre_tr Hinit].
    apply finite_valid_trace_from_to_app_split in Hpre_tr as [Hpre_tr Hsuf].
    rewrite finite_trace_last_is_last in Hsuf.
    apply finite_valid_trace_from_to_app_split in Hpre_tr as Hitem.
    apply proj2 in Hitem.
    rewrite finite_trace_last_is_last in Hpre_tr, Hitem.
    subst.
    destruct l as (i, li).
    cbn in *.
    subst output.
    inversion Hitem.
    subst.
    assert
      (Hproduce :
        can_produce (pre_loaded_with_all_messages_vlsm (IM i)) (destination i) m)
      by (eexists _,_; eassumption).
    eapply message_dependencies_are_necessary in Hproduce
    ; [|apply HMsgDep|eassumption].
    eapply has_been_observed_sent_received_iff in Hproduce
    ; [|revert Ht; apply input_valid_transition_destination].
    destruct Hproduce as [Hreceived | Hsent]; cycle 1.
    + left. exists i. split; [assumption|].
      revert Hsent.
      eapply in_futures_preserving_oracle_from_stepwise.
      * apply has_been_sent_stepwise_from_trace.
      * eexists; eassumption.
    + apply pre_VLSM_projection_trace_project_app_rev in Htr_pr
        as [preX [sufX [Heqtr [HpreX_pr HsufX_pr]]]].
      apply valid_trace_last_pstate in Hpre_tr as Hdestinationi.
      apply proper_received in Hreceived; [|assumption].
      specialize (Hreceived _ _ (conj Hpre_tr Hinit)).
      apply Exists_exists in Hreceived as [item_dm [Hitem_dm Hreceived]].
      apply elem_of_list_In in Hitem_dm.
      rewrite <- HpreX_pr in Hitem_dm.
      apply pre_VLSM_projection_trace_project_in_iff in Hitem_dm as HitemX_dm.
      destruct HitemX_dm as [itemX_dm [HitemX_dm HitemX_dm_pr]].
      subst tr.
      apply proj1 in Htr.
      apply
        (finite_valid_trace_from_to_app_split (composite_vlsm IM _))
        in Htr as [HpreX HsufX].
      apply in_split in HitemX_dm as [preX_dm [sufX_dm HpreX_dm_pr]].
      change (preX_dm ++ itemX_dm :: sufX_dm) with (preX_dm ++ [itemX_dm] ++ sufX_dm) in HpreX_dm_pr.
      rewrite app_assoc in HpreX_dm_pr.
      rewrite HpreX_dm_pr in HpreX.
      apply
        (finite_valid_trace_from_to_app_split (composite_vlsm IM _))
        in HpreX as [HpreX_dm HsufX_dm].
      apply
        (finite_valid_trace_from_to_app_split (composite_vlsm IM _)), proj2
        in HpreX_dm.
      rewrite finite_trace_last_is_last in HpreX_dm, HsufX_dm.
      subst.
      assert
        (Hfutures :
          in_futures (composite_vlsm IM (strong_fixed_equivocation_constraint IM Hbs equivocators))
            (@finite_trace_last _ (composite_type IM) is preX_dm) s).
      { clear -HpreX_dm HsufX_dm HsufX.
        exists ([itemX_dm] ++ sufX_dm ++ sufX).
        apply (finite_valid_trace_from_to_app (composite_vlsm IM _)) with (VLSM.destination itemX_dm)
        ; [assumption|].
        eapply (finite_valid_trace_from_to_app (composite_vlsm IM _)); eassumption.
      }
      destruct itemX_dm.
      unfold pre_VLSM_projection_transition_item_project, composite_project_label in HitemX_dm_pr.
      cbn in HitemX_dm_pr.
      case_decide as Hi; simpl in HitemX_dm_pr; [|congruence].
      apply Some_inj in HitemX_dm_pr.
      subst.
      destruct l as (i, li_dm).
      cbn in *.
      subst.
      clear -HpreX_dm Hfutures.
      inversion HpreX_dm.
      subst.
      destruct Ht as [[_ [_ [_ Hc]]] _].
      revert Hc.
      apply in_futures_preserves_strong_fixed_equivocation.
      eapply VLSM_incl_in_futures
      ; [apply constraint_preloaded_free_incl with (constraint := (strong_fixed_equivocation_constraint IM Hbs equivocators))|].
      assumption.
  - destruct Hemit as [(sX, iom) [(sub_i, li) [sX' HtX]]].
    apply input_valid_transition_destination in HtX as HsX'.
    destruct_dec_sig sub_i i Hi Heqsub_i.
    subst.
    assert
      (Hproduce :can_produce (pre_loaded_with_all_messages_vlsm (IM i)) (sX' (dexist i Hi)) m).
    {
      apply
        (VLSM_projection_input_valid_transition
          (single_equivocator_projection s i Hi)) with (lY := li) in HtX
      ; [eexists _,_; eassumption|].
      unfold sub_label_element_project. cbn.
      case_decide as Heqi; [|contradiction].
      replace Heqi with (eq_refl (A := index) (x := i)); [reflexivity|].
      apply Eqdep_dec.UIP_dec.
      assumption.
    }
    eapply message_dependencies_are_necessary in Hproduce
    ; [|apply HMsgDep|eassumption].
    assert (Hsent_comp : composite_has_been_observed (sub_IM IM equivocators) Hbo_sub sX' dm)
      by (exists (dexist i Hi); assumption).
    eapply preloaded_composite_observed_valid in Hsent_comp; [| apply listing_from_finite| eassumption..].
    apply emitted_messages_are_valid_iff in Hsent_comp as [[[sub_j [[_im Him] Heqim]] | Hsent] | Hemit]
    ; [|left; assumption|right; assumption].
    destruct_dec_sig sub_j j Hj Heqsub_j. subst.
    elim (no_initial_messages_in_IM j _im); assumption.
Qed.

Lemma strong_fixed_equivocation_msg_dep_constraint_subsumption
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  : input_valid_constraint_subsumption IM
    (strong_fixed_equivocation_constraint IM Hbs equivocators)
    msg_dep_fixed_set_equivocation_constraint.
Proof.
  intros l (s, [m|]) [Hs [_ [_ Hc]]]; [|exact I].
  cut (dependencies_with_non_equivocating_senders_were_sent s m).
  { intros Hassume.
    destruct Hc as [Hsent | Hemit]; [left; assumption|].
    right.
    split; [|assumption].
    revert Hemit. apply equivocators_composition_can_emit_sender.
  }
  intros dm Hdm.
  cut (strong_fixed_equivocation IM Hbs equivocators s dm).
  {
    intros [Hsent | Hemit]; [left; assumption|].
    right.
    apply equivocators_composition_can_emit_sender with s.
    assumption.
  }
  cbn in Hc.
  revert Hdm Hc.
  apply msg_dep_happens_before_reflect.
  apply msg_dep_rel_reflects_strong_fixed_equivocation; assumption.
Qed.

Lemma msg_dep_strong_fixed_equivocation_incl
  (Hmsg_dep_happens_before_wf : well_founded (msg_dep_happens_before message_dependencies))
  : VLSM_incl
    (composite_vlsm IM msg_dep_fixed_set_equivocation_constraint)
    (composite_vlsm IM (strong_fixed_equivocation_constraint IM Hbs equivocators)).
Proof.
  apply constraint_subsumption_incl.
  apply preloaded_constraint_subsumption_stronger.
  apply strong_constraint_subsumption_strongest.
  apply msg_dep_strong_fixed_equivocation_constraint_subsumption.
  assumption.
Qed.

Lemma strong_msg_dep_fixed_equivocation_incl
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  : VLSM_incl
    (composite_vlsm IM (strong_fixed_equivocation_constraint IM Hbs equivocators))
    (composite_vlsm IM msg_dep_fixed_set_equivocation_constraint).
Proof.
  apply constraint_subsumption_incl
    with (constraint1 := strong_fixed_equivocation_constraint IM Hbs equivocators).
  apply strong_fixed_equivocation_msg_dep_constraint_subsumption.
  assumption.
Qed.

Lemma msg_dep_strong_fixed_equivocation_eq
  (Hmsg_dep_happens_before_wf : well_founded (msg_dep_happens_before message_dependencies))
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  : VLSM_eq
    (composite_vlsm IM msg_dep_fixed_set_equivocation_constraint)
    (composite_vlsm IM (strong_fixed_equivocation_constraint IM Hbs equivocators)).
Proof.
  apply VLSM_eq_incl_iff; split.
  - apply msg_dep_strong_fixed_equivocation_incl. assumption.
  - apply strong_msg_dep_fixed_equivocation_incl. assumption.
Qed.

End msg_dep_fixed_set_equivocation.

Section sec_full_node_fixed_set_equivocation.

Context
  {message : Type}
  `{EqDecision index}
  (IM : index -> VLSM message)
  (Hbs : forall i, HasBeenSentCapability (IM i))
  (message_dependencies : message -> set message)
  (equivocators : set index)
  {validator : Type}
  (A : validator -> index)
  (sender : message -> option validator)
  .

Definition has_equivocating_sender (m : message)
  := exists v, sender m = Some v /\ A v ∈ equivocators.


Definition full_node_fixed_set_equivocation (s : composite_state IM) (m : message) :=
  sent_by_non_equivocating IM _ equivocators s m \/ has_equivocating_sender m.

Definition full_node_fixed_set_equivocation_constraint
  (l : composite_label IM)
  (som : composite_state IM * option message)
  : Prop :=
  let (s, om) := som in
  from_option (full_node_fixed_set_equivocation s) True om.

Lemma msg_dep_full_node_fixed_set_equivocation_constraint_subsumption
  (Hchannel : channel_authentication_prop IM A sender)
  : strong_constraint_subsumption IM
    (msg_dep_fixed_set_equivocation_constraint IM Hbs message_dependencies equivocators)
    full_node_fixed_set_equivocation_constraint.
Proof.
  intros l (s, [m|]); [|intuition].
  intros [Hsent | [[i [Hi Hemit]] Hdeps]]; [left; assumption|].
  right.
  apply Hchannel in Hemit.
  cbv in Hemit |- *.
  destruct (sender m) as [v|]; [|congruence].
  eexists. split; [reflexivity|].
  replace (A v) with i; [assumption|].
  congruence.
Qed.

Context
  (Hbr : forall i, HasBeenReceivedCapability (IM i))
  (Hbo := fun i => HasBeenObservedCapability_from_sent_received (IM i))
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  (HMsgDep : forall i, MessageDependencies message_dependencies (IM i))
  .

Lemma fixed_full_node_equivocation_incl
  {finite_index : finite.Finite index}
  (Hchannel : channel_authentication_prop IM A sender)
  : VLSM_incl
    (composite_vlsm IM (fixed_equivocation_constraint IM Hbs Hbr equivocators))
    (composite_vlsm IM full_node_fixed_set_equivocation_constraint).
Proof.
  eapply VLSM_incl_trans.
  - apply Fixed_incl_StrongFixed with (enum index).
    apply listing_from_finite.
  - eapply VLSM_incl_trans.
    + apply strong_msg_dep_fixed_equivocation_incl with Hbr; eassumption.
    + apply constraint_subsumption_incl
        with (constraint1 := msg_dep_fixed_set_equivocation_constraint IM Hbs message_dependencies equivocators).
      apply preloaded_constraint_subsumption_stronger.
      apply strong_constraint_subsumption_strongest.
      apply msg_dep_full_node_fixed_set_equivocation_constraint_subsumption.
      assumption.
Qed.

Lemma full_node_fixed_equivocation_constraint_subsumption
  (Hfull : forall i, message_dependencies_full_node_condition_prop message_dependencies (IM i))
  (Hsender_safety : sender_safety_alt_prop IM A sender)
  : input_valid_constraint_subsumption IM
    full_node_fixed_set_equivocation_constraint
    (fixed_equivocation_constraint IM Hbs Hbr equivocators).
Proof.
  intros l (s, [m|]) [_ [Hm [Hv Hc]]]; [|intuition].
  destruct Hc as [Hsent | Heqv].
  - left. revert Hsent. apply sent_by_non_equivocating_are_observed.
  - right.
    destruct l as (i, li).
    destruct Heqv as [j [Hsender HAj]].
    apply Hfull in Hv.
    eapply VLSM_incl_can_emit.
    {
      apply pre_loaded_vlsm_incl_relaxed
        with (P := fun dm => composite_has_been_observed IM Hbo s dm \/ dm ∈ message_dependencies m).
      intros m0 [Hsent_m0| Hdep_m0]; [intuition|].
      left.
      exists i.
      specialize (Hv _ Hdep_m0) as [Hsent | Hreceived]
      ; [left | right]; assumption.
    }
    eapply VLSM_full_projection_can_emit.
    {
      apply preloaded_sub_element_full_projection with (P := fun dm => dm ∈ message_dependencies m).
      intuition.
    }
    apply message_dependencies_are_sufficient with (Hbs (A j)) (Hbr (A j)); [apply HMsgDep|].
    cut (exists k, can_emit (pre_loaded_with_all_messages_vlsm (IM k)) m).
    {
      intros [k Hk].
      replace (A j) with k; [assumption|].
      symmetry.
      eapply Hsender_safety; eassumption.
    }
    eapply @can_emit_composite_project
      with (constraint := full_node_fixed_set_equivocation_constraint).
    apply
      (VLSM_incl_can_emit
        (vlsm_incl_pre_loaded_with_all_messages_vlsm (composite_vlsm IM _))).
    apply emitted_messages_are_valid_iff in Hm as [[k [[im Him] Heqm]] | Hemit]
    ; [|assumption].
    elim (no_initial_messages_in_IM k im).
    assumption.
    Unshelve.
    assumption.
Qed.

Lemma full_node_fixed_equivocation_incl
  (Hfull : forall i, message_dependencies_full_node_condition_prop message_dependencies (IM i))
  (Hsender_safety : sender_safety_alt_prop IM A sender)
  : VLSM_incl
    (composite_vlsm IM full_node_fixed_set_equivocation_constraint)
    (composite_vlsm IM (fixed_equivocation_constraint IM Hbs Hbr equivocators)).
Proof.
  apply constraint_subsumption_incl.
  apply full_node_fixed_equivocation_constraint_subsumption; assumption.
Qed.

Lemma full_node_fixed_equivocation_eq
  {finite_index : finite.Finite index}
  (Hchannel : channel_authentication_prop IM A sender)
  (Hfull : forall i, message_dependencies_full_node_condition_prop message_dependencies (IM i))
  : VLSM_eq
    (composite_vlsm IM full_node_fixed_set_equivocation_constraint)
    (composite_vlsm IM (fixed_equivocation_constraint IM Hbs Hbr equivocators)).
Proof.
  apply VLSM_eq_incl_iff; split.
  - apply full_node_fixed_equivocation_incl; [assumption|].
    apply channel_authentication_sender_safety.
    assumption.
  - apply fixed_full_node_equivocation_incl.
    assumption.
Qed.

End sec_full_node_fixed_set_equivocation.
