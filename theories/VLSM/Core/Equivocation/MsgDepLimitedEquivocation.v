From stdpp Require Import prelude finite.
From Coq Require Import Reals.
From VLSM.Lib Require Import Preamble ListExtras StdppListSet ListSetExtras FinFunExtras Measurable.
From VLSM.Core Require Import VLSM AnnotatedVLSM MessageDependencies VLSMProjections Composition  ProjectionTraces SubProjectionTraces.
From VLSM.Core Require Import Equivocation Equivocation.FixedSetEquivocation Equivocation.TraceWiseEquivocation Equivocation.LimitedEquivocation Equivocation.MsgDepFixedSetEquivocation.

Section sec_coequivocating_senders_limited_equivocation.

Context
  {message : Type}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  (Hbs : forall i, HasBeenSentCapability (IM i))
  (Hbr : forall i, HasBeenReceivedCapability (IM i))
  (Hbo := fun i => HasBeenObservedCapability_from_sent_received (IM i))
  `{EqDecision validator}
  `{ReachableThreshold validator}
  (A : validator -> index)
  (sender : message -> option validator)
  (coequivocating_senders : composite_state IM -> message -> set validator)
  .

Definition coeqv_message_equivocators (s : composite_state IM) (m : message)
  : set validator :=
  if (decide (composite_has_been_observed IM Hbo s m))
  then [] (* no additional equivocation *)
  else map_option sender [m] ++ coequivocating_senders s m.
  (* m itself and all its non-observed dependencies are equivocating. *)

Definition coeqv_composite_transition_message_equivocators
  (l : composite_label IM)
  (som : annotated_state (free_composite_vlsm IM) (set validator) * option message)
  : set validator :=
  match som.2 with
  | None => state_annotation som.1
  | Some m =>
    set_union (state_annotation som.1) (coeqv_message_equivocators (original_state som.1) m)
  end.

Definition coeqv_limited_equivocation_constraint
  (l : composite_label IM)
  (som : annotated_state (free_composite_vlsm IM) (set validator) * option message)
  : Prop :=
  (sum_weights (coeqv_composite_transition_message_equivocators l som) <= proj1_sig threshold)%R.

Global Instance empty_validators_inhabited : Inhabited {s : set validator | s = empty_set}
  := populate (exist _ _ eq_refl).

Definition coeqv_limited_equivocation_vlsm : VLSM message :=
  annotated_vlsm (free_composite_vlsm IM) (set validator) (fun s => s = empty_set)
  coeqv_limited_equivocation_constraint coeqv_composite_transition_message_equivocators.

Definition coeqv_annotate_trace_with_equivocators :=
  annotate_trace (free_composite_vlsm IM) (set validator) (fun s => s = empty_set)
  coeqv_composite_transition_message_equivocators.

Lemma coeqv_limited_equivocation_transition_state_annotation_incl [l s iom s' oom]
  : vtransition coeqv_limited_equivocation_vlsm l (s, iom) = (s', oom) ->
    state_annotation s ⊆ state_annotation s'.
Proof.
  cbn.
  unfold annotated_transition.
  destruct (vtransition _ _ _) as (_s', _om').
  inversion 1.
  cbn.
  destruct iom as [m|]; [|reflexivity].
  apply set_union_subseteq_left.
Qed.

Lemma coeqv_limited_equivocation_state_annotation_nodup s
  : valid_state_prop coeqv_limited_equivocation_vlsm s ->
    NoDup (state_annotation s).
Proof.
  induction 1 using valid_state_prop_ind.
  - destruct s.
    cbn.
    replace state_annotation with (@nil validator); [constructor|].
    symmetry.
    apply Hs.
  - apply proj2 in Ht.
    cbn in Ht.
    unfold annotated_transition in Ht.
    destruct (vtransition _ _ _).
    inversion Ht.
    destruct om as [m|]; [|assumption].
    cbn.
    apply set_union_nodup_left.
    assumption.
Qed.

Lemma coeqv_limited_equivocation_state_not_heavy s
  : valid_state_prop coeqv_limited_equivocation_vlsm s ->
    (sum_weights (state_annotation s) <= proj1_sig threshold)%R.
Proof.
  induction 1 using valid_state_prop_ind.
  - destruct s.
    cbn.
    replace state_annotation with (@nil validator)
      by (symmetry; apply Hs).
    destruct threshold. simpl. apply Rge_le. assumption.
  - destruct Ht as [[_ [_ [_ Hc]]] Ht].
    cbn in Ht.
    unfold annotated_transition in Ht.
    destruct (vtransition _ _ _).
    inversion Ht.
    destruct om as [m|]; assumption.
Qed.

End sec_coequivocating_senders_limited_equivocation.

Section sec_msg_dep_limited_equivocation.

Context
  {message : Type}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  (Hbs : forall i, HasBeenSentCapability (IM i))
  (Hbr : forall i, HasBeenReceivedCapability (IM i))
  (Hbo := fun i => HasBeenObservedCapability_from_sent_received (IM i))
  (full_message_dependencies : message -> set message)
  `{EqDecision validator}
  `{ReachableThreshold validator}
  (A : validator -> index)
  (sender : message -> option validator)
  .

Definition not_observed_happens_before_dependencies (s : composite_state IM) (m : message)
  : set message :=
  filter (fun dm => ~composite_has_been_observed IM Hbo s dm) (full_message_dependencies m).

Definition msg_dep_coequivocating_senders (s : composite_state IM) (m : message)
  : set validator :=
  map_option sender (not_observed_happens_before_dependencies s m).

Definition msg_dep_limited_equivocation_vlsm : VLSM message :=
  coeqv_limited_equivocation_vlsm IM Hbs Hbr sender msg_dep_coequivocating_senders.

Definition msg_dep_message_equivocators :=
  coeqv_message_equivocators IM Hbs Hbr sender msg_dep_coequivocating_senders.

Definition msg_dep_annotate_trace_with_equivocators :=
  coeqv_annotate_trace_with_equivocators IM Hbs Hbr sender msg_dep_coequivocating_senders.

Definition msg_dep_composite_transition_message_equivocators :=
  coeqv_composite_transition_message_equivocators IM Hbs Hbr sender msg_dep_coequivocating_senders.

End sec_msg_dep_limited_equivocation.

Section sec_full_node_limited_equivocation.

Context
  {message : Type}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  (Hbs : forall i, HasBeenSentCapability (IM i))
  (Hbr : forall i, HasBeenReceivedCapability (IM i))
  (Hbo := fun i => HasBeenObservedCapability_from_sent_received (IM i))
  `{EqDecision validator}
  `{ReachableThreshold validator}
  (A : validator -> index)
  (sender : message -> option validator)
  .

Definition full_node_coequivocating_senders (s : composite_state IM) (m : message)
  : set validator :=
  [].

Definition full_node_limited_equivocation_vlsm : VLSM message :=
  coeqv_limited_equivocation_vlsm IM Hbs Hbr sender full_node_coequivocating_senders.

Definition full_node_composite_transition_message_equivocators :=
  coeqv_composite_transition_message_equivocators IM Hbs Hbr sender full_node_coequivocating_senders.

End sec_full_node_limited_equivocation.

Section sec_full_node_msg_dep_limited_equivocation_equivalence.

Context
  {message : Type}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  (Hbs : forall i, HasBeenSentCapability (IM i))
  (Hbr : forall i, HasBeenReceivedCapability (IM i))
  (Hbo := fun i => HasBeenObservedCapability_from_sent_received (IM i))
  (full_message_dependencies : message -> set message)
  `{EqDecision validator}
  `{ReachableThreshold validator}
  (A : validator -> index)
  (sender : message -> option validator)
  (message_dependencies : message -> set message)
  (HMsgDep : forall i, MessageDependencies message_dependencies (IM i))
  (HFullMsgDep : FullMessageDependencies message_dependencies full_message_dependencies)
  (Hfull : forall i, message_dependencies_full_node_condition_prop message_dependencies (IM i))
  .

Lemma full_node_msg_dep_coequivocating_senders s m i li
  (Hvalid : input_valid (pre_loaded_with_all_messages_vlsm (IM i)) li (s i, Some m))
  : msg_dep_coequivocating_senders IM Hbs Hbr full_message_dependencies sender s m = [].
Proof.
  cut (forall v, ~ v ∈ msg_dep_coequivocating_senders IM Hbs Hbr full_message_dependencies sender s m ).
  {
    intros Hv.
    destruct (msg_dep_coequivocating_senders IM Hbs Hbr full_message_dependencies sender s m)
    ; [reflexivity|].
    elim (Hv v).
    left.
  }
  intros v.
  setoid_rewrite elem_of_map_option.
  setoid_rewrite elem_of_list_filter.
  intros [dm [[Hnobs Hdm] Hsender]].
  unfold msg_dep_coequivocating_senders.
  elim Hnobs.
  exists i.
  clear -Hbo HMsgDep HFullMsgDep Hfull Hvalid Hdm.
  revert dm Hdm.
  cut
    (forall dm m, msg_dep_rel message_dependencies dm m ->
      @has_been_observed _ (IM i) (Hbo i) (s i) m ->
      @has_been_observed _ (IM i) (Hbo i) (s i) dm).
  {
    intros Hdeps dm.
    rewrite full_message_dependencies_happens_before.
    rewrite msg_dep_happens_before_iff_one.
    intros [Hdm | [dm' [Hdm' Hdm]]]; [|].
    - eapply Hfull; [apply Hvalid|eassumption].
    - eapply msg_dep_happens_before_reflect; [eassumption|eassumption|].
      eapply Hfull; [apply Hvalid|eassumption].
  }
  clear -HMsgDep Hfull Hvalid.
  apply msg_dep_full_node_reflects_has_been_observed; [apply HMsgDep|apply Hfull|].
  apply Hvalid.
Qed.

Lemma full_node_msg_dep_composite_transition_message_equivocators
  iprop `{Inhabited (sig iprop)} constr trans
  l (s : @state _ (annotated_type (free_composite_vlsm IM) (set validator))) om
  (Hvalid : input_valid (annotated_vlsm (free_composite_vlsm IM) (set validator) iprop constr trans) l (s, om))
  : full_node_composite_transition_message_equivocators IM Hbs Hbr sender l (s, om) =
    msg_dep_composite_transition_message_equivocators IM Hbs Hbr full_message_dependencies sender l (s, om).
Proof.
  destruct om as [m|]; [|reflexivity].
  cbn.
  f_equal.
  unfold coeqv_message_equivocators.
  case_decide as Hobs; [reflexivity|].
  f_equal.
  symmetry.
  destruct l as (i, li).
  eapply full_node_msg_dep_coequivocating_senders.
  eapply
    (VLSM_projection_input_valid (preloaded_component_projection IM i))
    with (lX := existT i li)
  ; [apply (composite_project_label_eq IM)|].
  apply (VLSM_incl_input_valid (vlsm_incl_pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM))).
  revert Hvalid.
  apply
    (VLSM_full_projection_input_valid
      (forget_annotations_projection (free_composite_vlsm IM) _ _ _)).
Qed.

Lemma msg_dep_full_node_limited_equivocation_vlsm_incl
  : VLSM_incl
    (msg_dep_limited_equivocation_vlsm IM Hbs Hbr full_message_dependencies sender)
    (full_node_limited_equivocation_vlsm IM Hbs Hbr sender).
Proof.
  apply basic_VLSM_incl.
  - intros s Hs.
    assumption.
  - intros _ _ m _ _ Hinit.
    apply initial_message_is_valid.
    assumption.
  - intros l s om HvX HsY HomY.
    split; [apply HvX|].
    unfold coeqv_limited_equivocation_constraint.
    setoid_rewrite full_node_msg_dep_composite_transition_message_equivocators
    ; [apply HvX|eassumption].
  - intros (i, li) s iom s' oom [Hv Ht].
    revert Ht. cbn.
    unfold annotated_transition.
    cbn.
    destruct (vtransition _ _ _) as (si', om').
    inversion 1.
    subst.
    clear Ht.
    setoid_rewrite full_node_msg_dep_composite_transition_message_equivocators
    ; [reflexivity|eassumption].
Qed.

Lemma full_node_msg_dep_limited_equivocation_vlsm_incl
  : VLSM_incl
    (full_node_limited_equivocation_vlsm IM Hbs Hbr sender)
    (msg_dep_limited_equivocation_vlsm IM Hbs Hbr full_message_dependencies sender).
Proof.
  apply basic_VLSM_incl.
  - intros s Hs.
    assumption.
  - intros _ _ m _ _ Hinit.
    apply initial_message_is_valid.
    assumption.
  - intros l s om HvX HsY HomY.
    split; [apply HvX|].
    unfold coeqv_limited_equivocation_constraint.
    setoid_rewrite <- full_node_msg_dep_composite_transition_message_equivocators
    ; [apply HvX|eassumption].
  - intros (i, li) s iom s' oom [Hv Ht].
    revert Ht. cbn.
    unfold annotated_transition.
    cbn.
    destruct (vtransition _ _ _) as (si', om').
    inversion 1.
    subst.
    clear Ht.
    setoid_rewrite full_node_msg_dep_composite_transition_message_equivocators
    ; [reflexivity|eassumption].
Qed.

Lemma full_node_msg_dep_limited_equivocation_vlsm_eq
  : VLSM_eq
    (full_node_limited_equivocation_vlsm IM Hbs Hbr sender)
    (msg_dep_limited_equivocation_vlsm IM Hbs Hbr full_message_dependencies sender).
Proof.
  apply VLSM_eq_incl_iff.
  split.
  - apply full_node_msg_dep_limited_equivocation_vlsm_incl.
  - apply msg_dep_full_node_limited_equivocation_vlsm_incl.
Qed.

End sec_full_node_msg_dep_limited_equivocation_equivalence.

Section sec_msg_dep_fixed_limited_equivocation.

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
  .

Lemma message_equivocators_can_emit (s : vstate Limited) im
  (Hs :
    valid_state_prop
      (fixed_equivocation_vlsm_composition IM Hbs Hbr (state_annotation s))
      (original_state s))
  (Hnobserved: ¬ composite_has_been_observed IM Hbo (original_state s) im)
  (HLemit: can_emit Limited im)
  : can_emit
      (equivocators_composition_for_observed IM Hbs Hbr
        (set_union (state_annotation s)
          (msg_dep_message_equivocators IM Hbs Hbr full_message_dependencies sender
            (original_state s) im))
        (original_state s))
      im.
Proof.
  unfold msg_dep_message_equivocators, coeqv_message_equivocators.
  rewrite decide_False by assumption.
  remember (map_option sender _ ++ _) as equivocating_senders.
  assert
    (Hsenders :
      forall dm, msg_dep_happens_before message_dependencies dm im ->
      composite_has_been_observed IM Hbo (original_state s) dm \/
      exists dm_i, dm_i ∈ equivocating_senders /\
        can_emit (pre_loaded_with_all_messages_vlsm (IM dm_i)) dm).
  {
    intros dm Hdm.
    destruct (decide (composite_has_been_observed IM Hbo (original_state s) dm))
      as [Hobs | Hnobs]
    ; [left; assumption|].
    right.
    cut
      (exists i, sender dm = Some i /\
        can_emit (pre_loaded_with_all_messages_vlsm (IM i)) dm).
    {
      intros [i [Hsender Hemit]].
      exists i.
      split; [|assumption].
      subst.
      apply elem_of_app.
      right.
      apply elem_of_map_option.
      exists dm.
      split; [|assumption].
      apply elem_of_list_filter.
      split; [assumption|].
      rewrite full_message_dependencies_happens_before.
      assumption.
    }
    eapply msg_dep_happens_before_composite_no_initial_valid_messages_emitted_by_sender
    ; [eassumption|eassumption|eassumption|eassumption|..|eassumption].
    apply emitted_messages_are_valid_iff.
    right.
    revert HLemit.
    eapply VLSM_full_projection_can_emit.
    apply forget_annotations_projection.
  }
  eapply VLSM_full_projection_can_emit.
  {
    apply equivocators_composition_for_observed_index_incl_full_projection
      with (indices1 := equivocating_senders).
  }
  assert
    (Hemitj : exists j, j ∈ equivocating_senders /\
      can_emit
        (pre_loaded_vlsm (IM j)
          (fun dm => msg_dep_happens_before message_dependencies dm im))
          im).
  {
    eapply VLSM_full_projection_can_emit in HLemit
    ; [|apply forget_annotations_projection].
    eapply VLSM_incl_can_emit in HLemit
    ; [| apply vlsm_incl_pre_loaded_with_all_messages_vlsm].
    apply can_emit_composite_project in HLemit as [j Hemit].
    apply Hchannel in Hemit as Hsender.
    unfold channel_authenticated_message in Hsender.
    exists j.
    subst equivocating_senders.
    cbn.
    destruct (sender im) as [_j|]; [|inversion Hsender].
    apply Some_inj in Hsender.
    cbn in Hsender.
    subst _j.
    split; [left|].
    apply HMsgDep in Hemit.
    revert Hemit.
    apply VLSM_incl_can_emit.
    apply pre_loaded_vlsm_incl.
    intros m Hdm.
    apply msg_dep_happens_before_iff_one.
    left.
    assumption.
  }
  destruct Hemitj as [j [Heqv_j Hemitj]].
  apply valid_preloaded_lifts_can_be_emitted with j (fun m => msg_dep_happens_before message_dependencies m im)
  ; [assumption| |assumption].
  clear Heqequivocating_senders.
  induction dm as [dm Hind]
    using (well_founded_ind (msg_dep_happens_before_wf _ _ HFullMsgDep)).
  intros Hdm.
  apply emitted_messages_are_valid_iff.
  destruct (Hsenders _ Hdm) as [Hobs_dm | [dm_i [Hdm_i Hemit_dm]]]
  ; [left; right; assumption|].
  right.
  apply valid_preloaded_lifts_can_be_emitted with dm_i (fun m => m ∈ message_dependencies dm)
  ; [assumption|..]; cycle 1.
  - eapply message_dependencies_are_sufficient; [apply HMsgDep|assumption].
  - intros dm' Hdm'.
    apply Hind.
    + apply msg_dep_happens_before_iff_one. left. assumption.
    + transitivity dm; [|assumption].
      apply msg_dep_happens_before_iff_one. left. assumption.
Unshelve.
  apply set_union_subseteq_right.
Qed.

Lemma msg_dep_fixed_limited_equivocation is tr
  : finite_valid_trace Limited is tr ->
    fixed_limited_equivocation_prop IM Hbs Hbr
      (original_state is)
      (pre_VLSM_full_projection_finite_trace_project
        (type Limited) (composite_type IM) Datatypes.id original_state
        tr).
Proof.
  intro Htr.
  exists (state_annotation (finite_trace_last is tr)).
  split.
  - rewrite set_eq_nodup_sum_weight_eq
      with (lv2 := state_annotation (finite_trace_last is tr)).
    + apply coeqv_limited_equivocation_state_not_heavy.
      apply finite_valid_trace_last_pstate.
      apply Htr.
    + apply NoDup_remove_dups.
    + apply coeqv_limited_equivocation_state_annotation_nodup.
      apply finite_valid_trace_last_pstate.
      apply Htr.
    + apply set_eq_extract_forall.
      setoid_rewrite elem_of_remove_dups.
      intuition.
  - split; [|apply Htr].
    apply valid_trace_add_default_last in Htr.
    induction Htr using finite_valid_trace_init_to_rev_ind
    ; [constructor; apply initial_state_is_valid; apply Hsi|].
    setoid_rewrite map_app.
    apply finite_valid_trace_from_app_iff.
    split.
    + revert IHHtr.
      apply VLSM_incl_finite_valid_trace_from.
      apply fixed_equivocation_vlsm_composition_index_incl.
      eapply coeqv_limited_equivocation_transition_state_annotation_incl.
      apply Ht.
    + apply finite_valid_trace_singleton.
      unfold input_valid_transition, input_valid.
      change (map _ _) with (pre_VLSM_full_projection_finite_trace_project  (type Limited) (composite_type IM) Datatypes.id original_state tr).
      rewrite <- pre_VLSM_full_projection_finite_trace_last.
      assert
        (Hs :
          valid_state_prop
            (fixed_equivocation_vlsm_composition IM Hbs Hbr (state_annotation s))
            (original_state s)).
      {
        replace s with (finite_trace_last si tr) at 2
          by (apply valid_trace_get_last in Htr; assumption).
        rewrite
          (pre_VLSM_full_projection_finite_trace_last
            (type Limited) (composite_type IM) Datatypes.id original_state
            si tr).
        apply finite_valid_trace_last_pstate.
        assumption.
      }
      destruct Ht as [[HLs [HLim HLv]] HLt].
      cbn in HLt.
      unfold annotated_transition in HLt.
      cbn.
      replace (finite_trace_last si _) with s
        by (apply valid_trace_get_last in Htr; congruence).
      cbn in HLt.
      destruct l as (i, li).
      destruct (vtransition _ _ _) as (si', om').
      inversion HLt.
      subst.
      clear HLt.
      cbn.
      repeat split.
      * revert Hs.
        apply VLSM_incl_valid_state.
        apply fixed_equivocation_vlsm_composition_index_incl.
        destruct iom as [im|]; [apply set_union_subseteq_left|reflexivity].
      * destruct iom as [im|]; [apply option_valid_message_Some|apply option_valid_message_None].
        destruct (decide (composite_has_been_observed IM Hbo (original_state s) im))
          as [Hobs|Hnobs].
        -- revert Hobs.
          apply composite_observed_valid with (enum index).
          ++ apply listing_from_finite.
          ++ assumption.
          ++ assumption.
          ++ revert Hs.
            apply VLSM_incl_valid_state.
            apply fixed_equivocation_vlsm_composition_index_incl.
            apply set_union_subseteq_left.
        -- revert HLim.
          setoid_rewrite emitted_messages_are_valid_iff.
          intros [Hinit | Hemit]; [left; assumption|].
          right.
          eapply VLSM_weak_full_projection_can_emit.
          {
            eapply EquivPreloadedBase_Fixed_weak_full_projection
              with (base_s := original_state s).
            - apply listing_from_finite.
            - revert Hs.
              apply VLSM_incl_valid_state.
              apply fixed_equivocation_vlsm_composition_index_incl.
              apply set_union_subseteq_left.
            - intros.  apply no_initial_messages_in_IM.
          }
          cbn.
          eapply VLSM_incl_can_emit.
          {
            apply Equivocators_Fixed_Strong_incl with (enum index).
            - apply listing_from_finite.
            - revert Hs.
              apply VLSM_incl_valid_state.
              apply fixed_equivocation_vlsm_composition_index_incl.
              apply set_union_subseteq_left.
          }
          apply message_equivocators_can_emit; assumption.
        * apply HLv.
        * destruct iom as [im|]; [|exact I].
          destruct (decide (composite_has_been_observed IM Hbo (original_state s) im))
            as [Hobs|Hnobs];
          [left; assumption|].
          right.
          cbn.
          apply message_equivocators_can_emit; [assumption|assumption|].
          cut (vinitial_message_prop Limited im \/ can_emit Limited im);
          [|apply emitted_messages_are_valid_iff; assumption].
          intros [[j [[mj Hmj] Heqim]] | Hemit]; [|assumption].
          elim (no_initial_messages_in_IM j mj).
          assumption.
Qed.

Lemma fixed_transition_preserves_annotation_equivocators
  equivocators
  (is : vstate (free_composite_vlsm IM)) s tr
  (Htr1 :
    finite_valid_trace_init_to (fixed_equivocation_vlsm_composition IM Hbs Hbr equivocators)
    is s tr)
  l iom sf oom
  (Ht :
    input_valid_transition
      (fixed_equivocation_vlsm_composition IM Hbs Hbr equivocators) l
      (s, iom) (sf, oom))
  (Hsub_equivocators :
    state_annotation
      (@finite_trace_last _ (type Limited)
        {| original_state := is; state_annotation := `inhabitant |}
        (msg_dep_annotate_trace_with_equivocators IM Hbs Hbr full_message_dependencies sender is tr))
    ⊆ equivocators)
  : msg_dep_composite_transition_message_equivocators IM Hbs Hbr
      full_message_dependencies sender l
      (@finite_trace_last _ (type Limited)
        {| original_state := is; state_annotation := empty_set |}
        (annotate_trace_from (free_composite_vlsm IM)
          (set index)
          (msg_dep_composite_transition_message_equivocators IM Hbs Hbr full_message_dependencies sender)
          {| original_state := is; state_annotation := empty_set |} tr), iom)
    ⊆ equivocators.
Proof.
  destruct iom as [im|]; [|assumption].
  apply set_union_subseteq_iff.
  split; [assumption|].
  cbn.
  rewrite annotate_trace_from_last_original_state.
  cbn.
  replace (finite_trace_last _ _) with s
    by (apply valid_trace_get_last in Htr1; congruence).
  unfold coeqv_message_equivocators.
  case_decide as Hnobserved; [apply list_subseteq_nil|].
  destruct Ht as [[Hs [Him [Hv [Hobs | Hemitted]]]] Ht]; [contradiction|].
  intros eqv Heqv.
  apply elem_of_app in Heqv as [Heqv|Heqv]
  ; apply elem_of_map_option in Heqv as [msg [Hmsg Hsender]].
  - apply elem_of_list_singleton in Hmsg.
    subst msg.
    eapply VLSM_incl_can_emit in Hemitted
    ; [|apply pre_loaded_vlsm_incl_pre_loaded_with_all_messages].
    apply can_emit_composite_project in Hemitted as [sub_eqv Hemitted].
    destruct_dec_sig sub_eqv _eqv H_eqv Heqsub_eqv.
    subst.
    unfold sub_IM in Hemitted.
    cbn in Hemitted.
    eapply Hsender_safety in Hemitted; [|eassumption].
    subst.
    assumption.
  - apply elem_of_list_filter in Hmsg as [Hnobserved_msg Hdep_msg].
    cut (strong_fixed_equivocation IM Hbs equivocators s msg).
    {
      intros [Hobserved | Hemitted_msg].
      - elim Hnobserved_msg.
        eapply sent_by_non_equivocating_are_observed.
        eassumption.
      - eapply VLSM_incl_can_emit in Hemitted_msg
        ; [|apply pre_loaded_vlsm_incl_pre_loaded_with_all_messages].
        apply can_emit_composite_project in Hemitted_msg as [sub_i Hemitted_msg].
        destruct_dec_sig sub_i i Hi Heqsub_i.
        subst.
        eapply Hsender_safety in Hemitted_msg; [|eassumption].
        cbn in Hemitted_msg.
        subst.
        assumption.
    }
    eapply msg_dep_happens_before_reflect
    ; [|eapply full_message_dependencies_happens_before; eassumption|]; cycle 1.
    + right.
      revert Hemitted.
      apply VLSM_incl_can_emit.
      apply Equivocators_Fixed_Strong_incl with (enum index)
      ; [apply listing_from_finite|assumption].
    + eapply msg_dep_rel_reflects_strong_fixed_equivocation
      ; [assumption|assumption|..].
      revert Hs.
      apply VLSM_incl_valid_state.
      apply Fixed_incl_StrongFixed with (enum index).
      apply listing_from_finite.
Qed.

Lemma msg_dep_limited_fixed_equivocation
  (is : vstate (free_composite_vlsm IM)) (tr : list (composite_transition_item IM))
  : fixed_limited_equivocation_prop IM Hbs Hbr is tr ->
    finite_valid_trace Limited
      {| original_state := is; state_annotation := ` inhabitant |}
      (msg_dep_annotate_trace_with_equivocators IM Hbs Hbr full_message_dependencies sender is tr).
Proof.
  intros [equivocators [Hlimited Htr]].
  split; [|split; [apply Htr|reflexivity]].
  apply valid_trace_add_default_last in Htr.
  match goal with
  |- finite_valid_trace_from Limited ?is ?tr =>
    cut
      (finite_valid_trace_from Limited is tr /\
        (state_annotation (@finite_trace_last _ (type Limited) is tr) ⊆ equivocators))
  end
  ; [intuition|].
  induction Htr using finite_valid_trace_init_to_rev_strong_ind.
  - split.
    + constructor.
      apply initial_state_is_valid.
      split; [assumption|reflexivity].
    + apply list_subseteq_nil.
  - setoid_rewrite annotate_trace_from_app.
    cbn.
    rewrite finite_trace_last_is_last.
    cbn.
    split.
    + apply finite_valid_trace_from_app_iff.
      split; [apply IHHtr1|].
      apply finite_valid_trace_singleton.
      repeat split.
      * apply finite_valid_trace_last_pstate.
        apply IHHtr1.
      * clear -Heqiom IHHtr2.
        apply proj1 in IHHtr2.
        unfold empty_initial_message_or_final_output in Heqiom.
        destruct_list_last iom_tr iom_tr' iom_item Heqiom_tr
        ; [apply option_initial_message_is_valid; assumption|].
        destruct iom as [im|]; [|apply option_valid_message_None].
        eapply valid_trace_output_is_valid; [eassumption|].
        setoid_rewrite annotate_trace_from_app.
        apply Exists_app.
        right.
        destruct iom_item.
        apply Exists_exists.
        eexists.
        split; [left|].
        assumption.
      * cbn.
        rewrite annotate_trace_from_last_original_state.
        destruct l as (i, li).
        cbn.
        replace (finite_trace_last _ _) with s
          by (apply valid_trace_get_last in Htr1; congruence).
        apply Ht.
      * apply Rle_trans with (sum_weights (remove_dups equivocators))
        ; [|assumption].
        apply sum_weights_subseteq.
        -- destruct iom as [im|]; cycle 1.
          ++ eapply coeqv_limited_equivocation_state_annotation_nodup.
            apply finite_valid_trace_last_pstate.
            apply IHHtr1.
          ++ apply set_union_nodup_left.
            eapply coeqv_limited_equivocation_state_annotation_nodup.
            apply finite_valid_trace_last_pstate.
            apply IHHtr1.
        -- apply NoDup_remove_dups.
        -- transitivity equivocators.
          ++ eapply fixed_transition_preserves_annotation_equivocators
            ; [eassumption|eassumption|apply IHHtr1].
          ++ intro. apply elem_of_remove_dups.
      * cbn.
        unfold annotated_transition.
        cbn.
        rewrite !annotate_trace_from_last_original_state.
        destruct l as (i, li).
        cbn.
        replace (finite_trace_last _ _) with s
          by (apply valid_trace_get_last in Htr1; congruence).
        apply proj2 in Ht.
        cbn in Ht.
        destruct (vtransition _ _ _) as (si', om').
        inversion Ht.
        reflexivity.
    + eapply fixed_transition_preserves_annotation_equivocators
      ; [eassumption|eassumption|apply IHHtr1].
Qed.

Lemma annotated_limited_incl_constrained_limited
  {is_equivocating_tracewise_no_has_been_sent_dec : RelDecision (is_equivocating_tracewise_no_has_been_sent IM (fun i => i) sender)}
  : VLSM_full_projection
    Limited
    (limited_equivocation_vlsm_composition IM (listing_from_finite index) sender)
    Datatypes.id original_state.
Proof.
  constructor.
  intros sX trX HtrX.
  eapply traces_exhibiting_limited_equivocation_are_valid
  ; [apply Hsender_safety|].
  apply msg_dep_fixed_limited_equivocation.
  assumption.
Qed.

End sec_msg_dep_fixed_limited_equivocation.
