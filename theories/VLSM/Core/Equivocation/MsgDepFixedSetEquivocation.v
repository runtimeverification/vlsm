From stdpp Require Import prelude finite.
From Coq Require Import Relations.Relation_Operators.
From VLSM.Lib Require Import Preamble StdppListSet FinFunExtras.
From VLSM.Core Require Import VLSM MessageDependencies VLSMProjections Composition Equivocation FixedSetEquivocation ProjectionTraces SubProjectionTraces.

Section msg_dep_fixed_set_equivocation.

Context
  {message : Type}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  `{forall i, HasBeenSentCapability (IM i)}
  `{forall i, HasBeenReceivedCapability (IM i)}
  (message_dependencies : message -> set message)
  `{forall i, MessageDependencies message_dependencies (IM i)}
  (equivocators : set index)
  .

Definition equivocator_can_emit (m : message) : Prop :=
  exists i, i ∈ equivocators /\ can_emit (pre_loaded_with_all_messages_vlsm (IM i)) m.

Definition dependencies_with_non_equivocating_senders_were_sent s m : Prop :=
  forall dm, msg_dep_happens_before message_dependencies dm m ->
    sent_by_non_equivocating IM equivocators s dm \/ equivocator_can_emit dm.

Definition msg_dep_fixed_set_equivocation (s : composite_state IM) (m : message) :=
  sent_by_non_equivocating IM equivocators s m \/
  equivocator_can_emit m /\
  dependencies_with_non_equivocating_senders_were_sent s m.

Definition msg_dep_fixed_set_equivocation_constraint
  (l : composite_label IM)
  (som : composite_state IM * option message)
  : Prop :=
  from_option (msg_dep_fixed_set_equivocation som.1) True som.2.

Definition msg_dep_fixed_set_equivocation_vlsm : VLSM message :=
  composite_vlsm IM msg_dep_fixed_set_equivocation_constraint.

Lemma messages_with_valid_dependences_can_be_emitted s dm
  (Hdepm:
    forall dm0, msg_dep_rel message_dependencies dm0 dm ->
    valid_message_prop (equivocators_composition_for_sent IM equivocators s) dm0)
  (dm_i: index)
  (Hdm_i: dm_i ∈ equivocators)
  (Hemitted: can_emit (pre_loaded_with_all_messages_vlsm (IM dm_i)) dm)
  : can_emit (equivocators_composition_for_sent IM equivocators s) dm.
Proof.
  eapply valid_preloaded_lifts_can_be_emitted, message_dependencies_are_sufficient
  ; intuition eauto.
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
  intuition.
Qed.

Lemma dependencies_are_valid s m
  (Hmsg_dep_happens_before_wf : well_founded (msg_dep_happens_before message_dependencies))
  : dependencies_with_non_equivocating_senders_were_sent s m ->
    forall dm, msg_dep_rel message_dependencies dm m ->
      valid_message_prop
        (equivocators_composition_for_sent IM equivocators s) dm.
Proof.
  induction m as [m Hind] using (well_founded_ind Hmsg_dep_happens_before_wf).
  intros Heqv dm Hdm.
  apply emitted_messages_are_valid_iff.
  assert (Hdm_hb : msg_dep_happens_before message_dependencies dm m)
    by (apply msg_dep_happens_before_iff_one; intuition).
  destruct (Heqv _ Hdm_hb) as [Hsent | (dm_i & Hdm_i & Hemitted)]
  ; [left; right; assumption | right].
  apply messages_with_valid_dependences_can_be_emitted with dm_i
  ; [| assumption | assumption].
  intros dm0 Hdm0.
  apply Hind with dm; [assumption | | assumption].
  - clear -Heqv Hdm; revert dm m Hdm Heqv.
    apply msg_dep_rel_reflects_dependencies_with_non_equivocating_senders_were_sent.
Qed.

Lemma msg_dep_strong_fixed_equivocation_subsumption s m
  (Hmsg_dep_happens_before_wf : well_founded (msg_dep_happens_before message_dependencies))
  : msg_dep_fixed_set_equivocation s m ->
    strong_fixed_equivocation IM equivocators s m.
Proof.
  intros  [Hsent | [[i [Hi Hemit]] Heqv]]; [left; assumption|].
  cut (forall dm, msg_dep_rel message_dependencies dm m -> valid_message_prop (equivocators_composition_for_sent IM equivocators s) dm)
  ; [| apply dependencies_are_valid; assumption].
  intro Hdeps; right.
  apply messages_with_valid_dependences_can_be_emitted with i; intuition.
Qed.

Lemma msg_dep_strong_fixed_equivocation_constraint_subsumption
  (Hmsg_dep_happens_before_wf : well_founded (msg_dep_happens_before message_dependencies))
  : strong_constraint_subsumption IM
      msg_dep_fixed_set_equivocation_constraint
      (strong_fixed_equivocation_constraint IM equivocators).
Proof.
  intros l [s [m |]] Hc; [| trivial].
  apply msg_dep_strong_fixed_equivocation_subsumption; assumption.
Qed.

Lemma single_equivocator_projection s j
  (Hj : j ∈ equivocators)
  : VLSM_projection
      (equivocators_composition_for_sent IM equivocators s)
      (pre_loaded_with_all_messages_vlsm (IM j))
      (sub_label_element_project IM equivocators j)
      (sub_state_element_project IM equivocators j Hj).
Proof.
  apply basic_VLSM_projection.
  - intros [sub_i li] lY HlX_pr sX om (_ & _ & HvX & _) HsY _; revert HvX.
    destruct_dec_sig sub_i i Hi Heqsub_i; subst.
    unfold sub_label_element_project in HlX_pr; cbn in HlX_pr.
    case_decide as Heqij; [| congruence].
    subst i; cbv in HlX_pr; apply Some_inj in HlX_pr; subst li.
    unfold sub_IM, sub_state_element_project; cbn.
    rewrite (sub_IM_state_pi sX Hj Hi); trivial.
  - intros [sub_i li] lY HlX_pr sX om sX' om' [_ HtX]; revert HtX.
    destruct_dec_sig sub_i i Hi Heqsub_i; subst.
    unfold sub_label_element_project in HlX_pr; cbn in HlX_pr.
    case_decide as Heqij; [|congruence].
    subst i; cbv in HlX_pr; apply Some_inj in HlX_pr; subst li.
    cbn; unfold sub_IM, sub_state_element_project; cbn.
    rewrite (sub_IM_state_pi sX Hj Hi).
    destruct (vtransition _ _ _) as (sj', _om'); inversion_clear 1.
    f_equal; symmetry; apply sub_IM_state_update_eq.
  - intros [sub_i li] HlX_pr sX om sX' om' [_ HtX].
    destruct_dec_sig sub_i i Hi Heqsub_i; subst.
    unfold sub_label_element_project in HlX_pr; cbn in HlX_pr.
    case_decide as Heqij; [congruence|].
    cbn in HtX; destruct (vtransition _ _ _) as (si', _om').
    inversion_clear HtX.
    unfold sub_state_element_project.
    rewrite sub_IM_state_update_neq; congruence.
  - intros sX HsX; specialize (HsX (dexist j Hj)); assumption.
  - intro; intros; apply any_message_is_valid_in_preloaded.
Qed.

Lemma equivocators_composition_can_emit_sender s m
  : can_emit (equivocators_composition_for_sent IM equivocators s) m ->
    equivocator_can_emit m.
Proof.
  intros [(sX, iom) [(sub_i, li) [sX' HtX]]].
  destruct_dec_sig sub_i i Hi Heqsub_i; subst.
  exists i; split; [assumption |].
  apply can_emit_iff.
  apply (VLSM_projection_input_valid_transition
          (single_equivocator_projection s i Hi)) with (lY := li) in HtX
  ; [eexists _,_,_; eassumption |].
  unfold sub_label_element_project; cbn.
  rewrite (decide_True_pi eq_refl).
  reflexivity.
Qed.

Lemma sent_by_non_equivocating_msg_dep_rel_strong_fixed_equivocation
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  : forall s, valid_state_prop (composite_vlsm IM (strong_fixed_equivocation_constraint IM equivocators)) s ->
    forall dm m, msg_dep_rel message_dependencies dm m ->
    sent_by_non_equivocating  IM equivocators s m ->
    strong_fixed_equivocation IM equivocators s dm.
Proof.
  intros s Hs dm m Hdm [i [Hni Hsent]].
  apply (messages_sent_from_component_produced_previously IM Hs) in Hsent
    as (destination & Hfutures & Hproduce).
  eapply VLSM_incl_in_futures in Hfutures as Hpre_futures
  ; [| apply constraint_preloaded_free_incl].
  apply (VLSM_projection_in_futures (preloaded_component_projection IM i)) in Hpre_futures.
  eapply message_dependencies_are_necessary, has_been_observed_sent_received_iff
    in Hproduce as [Hreceived| Hsent]; [..|eassumption|typeclasses eauto]; cycle 1.
  + left; exists i; split; [assumption |].
    eapply in_futures_preserving_oracle_from_stepwise
    ; [apply has_been_sent_stepwise_from_trace | eassumption | eassumption].
  + eapply in_futures_valid_fst; eassumption.
  + apply in_futures_valid_fst in Hfutures as Hdestination.
    specialize (received_component_received_previously IM Hdestination Hreceived)
      as (s_item_dm & [] & Ht & Hfutures_dm & <- & Hinput);
      destruct l as (i, li); cbn in Hinput; subst input; cbn in *.
      apply input_valid_transition_in_futures in Ht as Hfutures_t; cbn in Hfutures_t
      ; destruct Ht as [(_ & _ & _ & Hc) _].
      eapply in_futures_preserves_strong_fixed_equivocation; [| apply Hc].
      eapply VLSM_incl_in_futures.
      * apply constraint_preloaded_free_incl
         with (constraint := strong_fixed_equivocation_constraint IM equivocators).
      * do 2 (eapply in_futures_trans; [eassumption |]); assumption.
Qed.

Lemma msg_dep_rel_reflects_strong_fixed_equivocation
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  : forall s, valid_state_prop (composite_vlsm IM (strong_fixed_equivocation_constraint IM equivocators)) s ->
    forall dm m, msg_dep_rel message_dependencies dm m ->
    strong_fixed_equivocation IM equivocators s m ->
    strong_fixed_equivocation IM equivocators s dm.
Proof.
  intros s Hs dm m Hdm [Hsent | Hemit].
  - eapply sent_by_non_equivocating_msg_dep_rel_strong_fixed_equivocation; eassumption.
  - cut (valid_message_prop (equivocators_composition_for_sent IM equivocators s) dm).
    {
      intro Hsent_comp; apply emitted_messages_are_valid_iff in Hsent_comp
        as [[[sub_j [[_im Him] Heqim]] | ] | ]
      ; [| left; assumption| right; assumption].
      destruct_dec_sig sub_j j Hj Heqsub_j; subst.
      clear -Him no_initial_messages_in_IM; contradict Him.
      apply no_initial_messages_in_IM.
    }
    destruct Hemit as ((sX, iom) & (sub_i, li) & sX' & HtX).
    eapply (preloaded_composite_observed_valid _ _ _ sX').
    + eapply input_valid_transition_destination; eassumption.
    + exists sub_i. destruct_dec_sig sub_i i Hi Heqsub_i; subst.
      eapply message_dependencies_are_necessary; [typeclasses eauto| |eassumption].
      exists (sX (dexist i Hi), iom), li.
      eapply (VLSM_projection_input_valid_transition (single_equivocator_projection s i Hi))
      ; [| eassumption].
      unfold sub_label_element_project; cbn.
      rewrite (decide_True_pi eq_refl); reflexivity.
Qed.

Lemma strong_fixed_equivocation_msg_dep_constraint_subsumption
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  : input_valid_constraint_subsumption IM
      (strong_fixed_equivocation_constraint IM equivocators)
      msg_dep_fixed_set_equivocation_constraint.
Proof.
  intros l [s [m |]] (Hs & _ & _ & Hc); [| trivial].
  cut (dependencies_with_non_equivocating_senders_were_sent s m).
  {
    intros Hassume.
    destruct Hc as [Hsent | Hemit]; [left; assumption | right].
    split; [| assumption].
    eapply equivocators_composition_can_emit_sender; eassumption.
  }
  intros dm Hdm.
  cut (strong_fixed_equivocation IM equivocators s dm).
  {
    intros [Hsent | Hemit]; [left; assumption | right].
    eapply equivocators_composition_can_emit_sender; eassumption.
  }
  eapply msg_dep_happens_before_reflect; [| eassumption | eassumption].
  apply msg_dep_rel_reflects_strong_fixed_equivocation; assumption.
Qed.

Lemma msg_dep_strong_fixed_equivocation_incl
  (Hmsg_dep_happens_before_wf : well_founded (msg_dep_happens_before message_dependencies))
  : VLSM_incl
      (composite_vlsm IM msg_dep_fixed_set_equivocation_constraint)
      (composite_vlsm IM (strong_fixed_equivocation_constraint IM equivocators)).
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
      (composite_vlsm IM (strong_fixed_equivocation_constraint IM equivocators))
      (composite_vlsm IM msg_dep_fixed_set_equivocation_constraint).
Proof.
  apply constraint_subsumption_incl.
  apply strong_fixed_equivocation_msg_dep_constraint_subsumption.
  assumption.
Qed.

Lemma msg_dep_strong_fixed_equivocation_eq
  (Hmsg_dep_happens_before_wf : well_founded (msg_dep_happens_before message_dependencies))
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  : VLSM_eq
      (composite_vlsm IM msg_dep_fixed_set_equivocation_constraint)
      (composite_vlsm IM (strong_fixed_equivocation_constraint IM equivocators)).
Proof.
  apply VLSM_eq_incl_iff; split.
  - apply msg_dep_strong_fixed_equivocation_incl; assumption.
  - apply strong_msg_dep_fixed_equivocation_incl; assumption.
Qed.

End msg_dep_fixed_set_equivocation.

Section sec_full_node_fixed_set_equivocation.

Context
  {message : Type}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  `{forall i, HasBeenSentCapability (IM i)}
  (message_dependencies : message -> set message)
  (equivocators : set index)
  {validator : Type}
  (A : validator -> index)
  (sender : message -> option validator)
  .

Definition has_equivocating_sender (m : message)
  := exists v, sender m = Some v /\ A v ∈ equivocators.

Definition full_node_fixed_set_equivocation (s : composite_state IM) (m : message) :=
  sent_by_non_equivocating IM equivocators s m \/ has_equivocating_sender m.

Definition full_node_fixed_set_equivocation_constraint
  (l : composite_label IM)
  (som : composite_state IM * option message)
  : Prop :=
  from_option (full_node_fixed_set_equivocation som.1) True som.2.

Lemma msg_dep_full_node_fixed_set_equivocation_constraint_subsumption
  (Hchannel : channel_authentication_prop IM A sender)
  : strong_constraint_subsumption IM
      (msg_dep_fixed_set_equivocation_constraint IM message_dependencies equivocators)
      full_node_fixed_set_equivocation_constraint.
Proof.
  intros l [s [m |]]; [| trivial]
  ; intros [Hsent | [[i [Hi Hemit]] Hdeps]]; [left; assumption | right].
  apply Hchannel in Hemit; cbv in Hemit |- *.
  destruct (sender m) as [v |]; [| congruence].
  eexists; split; [reflexivity|].
  replace (A v) with i; [assumption |].
  congruence.
Qed.

Context
  `{forall i, HasBeenReceivedCapability (IM i)}
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  `{forall i, MessageDependencies message_dependencies (IM i)}
  .

Lemma fixed_full_node_equivocation_incl
  (Hchannel : channel_authentication_prop IM A sender)
  : VLSM_incl
      (composite_vlsm IM (fixed_equivocation_constraint IM equivocators))
      (composite_vlsm IM full_node_fixed_set_equivocation_constraint).
Proof.
  eapply VLSM_incl_trans.
  - apply Fixed_incl_StrongFixed.
  - eapply VLSM_incl_trans.
    + eapply strong_msg_dep_fixed_equivocation_incl; eassumption.
    + apply constraint_subsumption_incl
       with (constraint1 := msg_dep_fixed_set_equivocation_constraint IM message_dependencies equivocators).
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
      (fixed_equivocation_constraint IM equivocators).
Proof.
  intros l [s [m |]] (_ & Hm & Hv & Hc); [| intuition]
  ; destruct Hc as [Hsent | Heqv]; [left | right].
  - revert Hsent; apply sent_by_non_equivocating_are_observed.
  - destruct l as [i li], Heqv as (j & Hsender & HAj).
    apply Hfull in Hv.
    eapply VLSM_incl_can_emit.
    {
      apply pre_loaded_vlsm_incl_relaxed
        with (P := fun dm => composite_has_been_observed IM s dm \/ dm ∈ message_dependencies m).
      intros m0 [Hsent_m0 | Hdep_m0]; [intuition |].
      left; exists i.
      specialize (Hv _ Hdep_m0) as [Hsent | Hreceived]
      ; [left | right]; assumption.
    }
    eapply VLSM_full_projection_can_emit.
    {
      apply @preloaded_sub_element_full_projection
        with (Hj := HAj) (P := fun dm => dm ∈ message_dependencies m).
      intuition.
    }
    eapply message_dependencies_are_sufficient with (X := IM (A j)); [typeclasses eauto |].
    cut (exists k, can_emit (pre_loaded_with_all_messages_vlsm (IM k)) m).
    {
      intros [k Hk].
      replace (A j) with k; [assumption|].
      symmetry; eapply Hsender_safety; eassumption.
    }
    eapply @can_emit_composite_project
      with (constraint := full_node_fixed_set_equivocation_constraint).
    apply (VLSM_incl_can_emit
            (vlsm_incl_pre_loaded_with_all_messages_vlsm (composite_vlsm IM _))).
    apply emitted_messages_are_valid_iff in Hm as [[k [[im Him] Heqm]] | Hemit]
    ; [| assumption].
    clear Heqm; contradict Him; apply no_initial_messages_in_IM.
Qed.

Lemma full_node_fixed_equivocation_incl
  (Hfull : forall i, message_dependencies_full_node_condition_prop message_dependencies (IM i))
  (Hsender_safety : sender_safety_alt_prop IM A sender)
  : VLSM_incl
      (composite_vlsm IM full_node_fixed_set_equivocation_constraint)
      (composite_vlsm IM (fixed_equivocation_constraint IM equivocators)).
Proof.
  apply constraint_subsumption_incl.
  apply full_node_fixed_equivocation_constraint_subsumption; assumption.
Qed.

Lemma full_node_fixed_equivocation_eq
  (Hchannel : channel_authentication_prop IM A sender)
  (Hfull : forall i, message_dependencies_full_node_condition_prop message_dependencies (IM i))
  : VLSM_eq
      (composite_vlsm IM full_node_fixed_set_equivocation_constraint)
      (composite_vlsm IM (fixed_equivocation_constraint IM equivocators)).
Proof.
  apply VLSM_eq_incl_iff; split.
  - apply full_node_fixed_equivocation_incl; [assumption |].
    apply channel_authentication_sender_safety; assumption.
  - apply fixed_full_node_equivocation_incl; assumption.
Qed.

End sec_full_node_fixed_set_equivocation.
