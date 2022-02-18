From stdpp Require Import prelude finite.
From Coq Require Import Reals.
From VLSM.Lib Require Import Preamble ListExtras StdppListSet ListSetExtras FinFunExtras Measurable.
From VLSM.Core Require Import VLSM AnnotatedVLSM MessageDependencies VLSMProjections Composition  ProjectionTraces SubProjectionTraces.
From VLSM.Core Require Import Equivocation Equivocation.FixedSetEquivocation Equivocation.TraceWiseEquivocation Equivocation.LimitedEquivocation Equivocation.MsgDepFixedSetEquivocation.

(** To allow capturing the two models of limited equivocation described in the
    sections below, we first define a notion of limited equivocation parameterized
    on a function yielding the set of equivocators induced by a received message,
    other that the message sender.
*)

Section sec_coequivocating_senders_limited_equivocation.

Context
  {message : Type}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  `{forall i, HasBeenSentCapability (IM i)}
  `{forall i, HasBeenReceivedCapability (IM i)}
  `{EqDecision validator}
  `{ReachableThreshold validator}
  (A : validator -> index)
  (sender : message -> option validator)
  (coequivocating_senders : composite_state IM -> message -> set validator)
  .

Definition coeqv_message_equivocators (s : composite_state IM) (m : message)
  : set validator :=
  if decide (composite_has_been_observed IM s m)
  then (* no additional equivocation *)
    []
  else (* m itself and all its non-observed dependencies are equivocating. *)
    map_option sender [m] ++ coequivocating_senders s m.

Definition coeqv_composite_transition_message_equivocators
  (l : composite_label IM)
  (som : annotated_state (free_composite_vlsm IM) (set validator) * option message)
  : set validator :=
  match som with
  | (sa, None) => state_annotation sa
  | (sa, Some m) =>
    set_union (state_annotation sa) (coeqv_message_equivocators (original_state sa) m)
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
  cbn; unfold annotated_transition; destruct (vtransition _ _ _) as (_s', _om').
  inversion 1; cbn.
  destruct iom as [m |]; [apply set_union_subseteq_left | reflexivity].
Qed.

Lemma coeqv_limited_equivocation_state_annotation_nodup s
  : valid_state_prop coeqv_limited_equivocation_vlsm s ->
    NoDup (state_annotation s).
Proof.
  induction 1 using valid_state_prop_ind.
  - destruct s, Hs as [_ ->]; cbn in *; constructor.
  - destruct Ht as [_ Ht]; cbn in Ht.
    unfold annotated_transition in Ht
    ; destruct (vtransition _ _ _); inversion Ht.
    destruct om as [m |]; cbn; [apply set_union_nodup_left |]; assumption.
Qed.

Lemma coeqv_limited_equivocation_state_not_heavy s
  : valid_state_prop coeqv_limited_equivocation_vlsm s ->
    (sum_weights (state_annotation s) <= proj1_sig threshold)%R.
Proof.
  induction 1 using valid_state_prop_ind.
  - destruct s, Hs as [_ ->], threshold; cbn in *.
    apply Rge_le; assumption.
  - destruct Ht as [(_ & _ & _ & Hc) Ht]
    ; cbn in Ht; unfold annotated_transition in Ht; destruct (vtransition _ _ _)
    ; inversion_clear Ht.
    destruct om as [m |]; assumption.
Qed.

Definition coeqv_limited_equivocation_projection_validator_prop : index -> Prop :=
  annotated_projection_validator_prop IM (fun s => s = empty_set)
    coeqv_limited_equivocation_constraint coeqv_composite_transition_message_equivocators.

Definition coeqv_limited_equivocation_message_validator_prop : index -> Prop :=
  annotated_message_validator_prop IM (fun s => s = empty_set)
    coeqv_limited_equivocation_constraint coeqv_composite_transition_message_equivocators.

Definition coeqv_limited_equivocation_projection_validator_prop_alt : index -> Prop :=
  annotated_projection_validator_prop_alt IM (fun s => s = empty_set)
    coeqv_limited_equivocation_constraint coeqv_composite_transition_message_equivocators.

End sec_coequivocating_senders_limited_equivocation.

Section sec_msg_dep_limited_equivocation.

Context
  {message : Type}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  `{forall i, HasBeenSentCapability (IM i)}
  `{forall i, HasBeenReceivedCapability (IM i)}
  (full_message_dependencies : message -> set message)
  `{EqDecision validator}
  `{ReachableThreshold validator}
  (A : validator -> index)
  (sender : message -> option validator)
  .

Definition not_observed_happens_before_dependencies (s : composite_state IM) (m : message)
  : set message :=
  filter (fun dm => ~composite_has_been_observed IM s dm) (full_message_dependencies m).

Definition msg_dep_coequivocating_senders (s : composite_state IM) (m : message)
  : set validator :=
  map_option sender (not_observed_happens_before_dependencies s m).

Definition msg_dep_limited_equivocation_vlsm : VLSM message :=
  coeqv_limited_equivocation_vlsm IM sender msg_dep_coequivocating_senders.

Definition msg_dep_message_equivocators :=
  coeqv_message_equivocators IM sender msg_dep_coequivocating_senders.

Definition msg_dep_annotate_trace_with_equivocators :=
  coeqv_annotate_trace_with_equivocators IM sender msg_dep_coequivocating_senders.

Definition msg_dep_composite_transition_message_equivocators :=
  coeqv_composite_transition_message_equivocators IM sender msg_dep_coequivocating_senders.

Definition msg_dep_limited_equivocation_projection_validator_prop :=
  coeqv_limited_equivocation_projection_validator_prop IM sender msg_dep_coequivocating_senders.

Definition msg_dep_limited_equivocation_message_validator_prop :=
  coeqv_limited_equivocation_message_validator_prop IM sender msg_dep_coequivocating_senders.

Definition msg_dep_limited_equivocation_projection_validator_prop_alt :=
  coeqv_limited_equivocation_projection_validator_prop_alt IM sender msg_dep_coequivocating_senders.

Lemma msg_dep_annotate_trace_with_equivocators_project s tr
  : pre_VLSM_full_projection_finite_trace_project (type msg_dep_limited_equivocation_vlsm)
    (composite_type IM) Datatypes.id original_state
    (msg_dep_annotate_trace_with_equivocators s tr) = tr.
Proof.
  apply (annotate_trace_project (free_composite_vlsm IM) (set validator)).
Qed.

End sec_msg_dep_limited_equivocation.

Section sec_full_node_limited_equivocation.

Context
  {message : Type}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  `{forall i, HasBeenSentCapability (IM i)}
  `{forall i, HasBeenReceivedCapability (IM i)}
  `{EqDecision validator}
  `{ReachableThreshold validator}
  (A : validator -> index)
  (sender : message -> option validator)
  .

Definition full_node_coequivocating_senders (s : composite_state IM) (m : message)
  : set validator := [].

Definition full_node_limited_equivocation_vlsm : VLSM message :=
  coeqv_limited_equivocation_vlsm IM sender full_node_coequivocating_senders.

Definition full_node_composite_transition_message_equivocators :=
  coeqv_composite_transition_message_equivocators IM sender full_node_coequivocating_senders.

End sec_full_node_limited_equivocation.

Section sec_full_node_msg_dep_limited_equivocation_equivalence.

Context
  {message : Type}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  `{forall i, HasBeenSentCapability (IM i)}
  `{forall i, HasBeenReceivedCapability (IM i)}
  (full_message_dependencies : message -> set message)
  `{EqDecision validator}
  `{ReachableThreshold validator}
  (A : validator -> index)
  (sender : message -> option validator)
  (message_dependencies : message -> set message)
  `{forall i, MessageDependencies message_dependencies (IM i)}
  `{FullMessageDependencies message message_dependencies full_message_dependencies}
  (Hfull : forall i, message_dependencies_full_node_condition_prop message_dependencies (IM i))
  .

Lemma full_node_msg_dep_coequivocating_senders s m i li
  (Hvalid : input_valid (pre_loaded_with_all_messages_vlsm (IM i)) li (s i, Some m))
  : msg_dep_coequivocating_senders IM full_message_dependencies sender s m = [].
Proof.
  cut (forall v, v ∉ msg_dep_coequivocating_senders IM full_message_dependencies sender s m).
  {
    intros Hv.
    destruct (msg_dep_coequivocating_senders IM full_message_dependencies sender s m)
    ; [reflexivity | contradiction (Hv v); left].
  }
  setoid_rewrite elem_of_map_option; setoid_rewrite elem_of_list_filter.
  intros v [dm [[Hnobs Hdm] Hsender]].
  contradict Hnobs; exists i; clear Hsender; revert dm Hdm.
  cut (forall dm m, msg_dep_rel message_dependencies dm m ->
        has_been_observed (IM i) (s i) m ->
        has_been_observed (IM i) (s i) dm).
  {
    setoid_rewrite full_message_dependencies_happens_before
    ; setoid_rewrite msg_dep_happens_before_iff_one.
    intros Hdeps dm [Hdm | [dm' [Hdm' Hdm]]].
    - eapply Hfull; [apply Hvalid | eassumption].
    - eapply msg_dep_happens_before_reflect; [eassumption | eassumption |].
      eapply Hfull; [apply Hvalid | eassumption].
  }
  apply msg_dep_full_node_reflects_has_been_observed
  ; [typeclasses eauto | apply Hfull | apply Hvalid].
Qed.

Lemma annotated_free_input_valid_projection
  iprop `{Inhabited (sig iprop)} constr trans
  i li s om
  : input_valid (annotated_vlsm (free_composite_vlsm IM) (set validator) iprop constr trans) (existT i li) (s, om) ->
    input_valid (pre_loaded_with_all_messages_vlsm (IM i)) li (original_state s i, om).
Proof.
  intro Hvalid.
  eapply (VLSM_projection_input_valid (preloaded_component_projection IM i))
  ; [apply (composite_project_label_eq IM) |].
  apply (VLSM_incl_input_valid (vlsm_incl_pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM))),
        (VLSM_full_projection_input_valid (forget_annotations_projection (free_composite_vlsm IM) _ _ _))
  ; assumption.
Qed.

Lemma full_node_msg_dep_composite_transition_message_equivocators
  i li (s : @state _ (annotated_type (free_composite_vlsm IM) (set validator))) om
  (Hvalid : input_valid (pre_loaded_with_all_messages_vlsm (IM i)) li (original_state s i, om))
  : full_node_composite_transition_message_equivocators IM sender (existT i li) (s, om)
      =
    msg_dep_composite_transition_message_equivocators IM full_message_dependencies sender (existT i li) (s, om).
Proof.
  destruct om as [m |]; [| reflexivity]; cbn; f_equal.
  unfold coeqv_message_equivocators.
  case_decide as Hobs; [reflexivity |]; f_equal.
  symmetry; eapply full_node_msg_dep_coequivocating_senders; eassumption.
Qed.

Lemma msg_dep_full_node_valid_iff l (s : @state _ (annotated_type (free_composite_vlsm IM) (set validator))) om
  (Hvi : input_valid (pre_loaded_with_all_messages_vlsm (IM (projT1 l))) (projT2 l) (original_state s (projT1 l), om))
  : vvalid (msg_dep_limited_equivocation_vlsm IM full_message_dependencies sender) l (s, om) <->
    vvalid (full_node_limited_equivocation_vlsm IM sender) l (s, om).
Proof.
  cbn; unfold annotated_valid, coeqv_limited_equivocation_constraint; destruct l as [i li].
  setoid_rewrite full_node_msg_dep_composite_transition_message_equivocators; intuition.
Qed.

Lemma msg_dep_full_node_transition_iff l (s : @state _ (annotated_type (free_composite_vlsm IM) (set validator))) om
  (Hvi : input_valid (pre_loaded_with_all_messages_vlsm (IM (projT1 l))) (projT2 l) (original_state s (projT1 l), om))
  : vtransition (msg_dep_limited_equivocation_vlsm IM full_message_dependencies sender) l (s, om) =
    vtransition (full_node_limited_equivocation_vlsm IM sender) l (s, om).
Proof.
  cbn; unfold annotated_transition;
    destruct (vtransition _ _ _) as (s', om'), l as (i, li).
  setoid_rewrite full_node_msg_dep_composite_transition_message_equivocators; intuition.
Qed.

Lemma msg_dep_full_node_limited_equivocation_vlsm_incl :
  VLSM_incl
    (msg_dep_limited_equivocation_vlsm IM full_message_dependencies sender)
    (full_node_limited_equivocation_vlsm IM sender).
Proof.
  apply basic_VLSM_incl.
  - intros s Hs; assumption.
  - intros _ _ m _ _ Hinit; apply initial_message_is_valid; assumption.
  - intros [i li] s om HvX _ _.
    apply msg_dep_full_node_valid_iff; [| apply HvX].
    eapply annotated_free_input_valid_projection; eassumption.
  - intros [i li] s iom s' oom [Hv Ht]; cbn in Ht |- *; rewrite <- Ht.
    symmetry; rapply msg_dep_full_node_transition_iff.
    eapply annotated_free_input_valid_projection; eassumption.
Qed.

Lemma full_node_msg_dep_limited_equivocation_vlsm_incl :
  VLSM_incl
    (full_node_limited_equivocation_vlsm IM sender)
    (msg_dep_limited_equivocation_vlsm IM full_message_dependencies sender).
Proof.
  apply basic_VLSM_incl.
  - intros s Hs; assumption.
  - intros _ _ m _ _ Hinit; apply initial_message_is_valid; assumption.
  - intros [i li] s om HvX _ _.
    apply msg_dep_full_node_valid_iff; [| apply HvX].
    eapply annotated_free_input_valid_projection; eassumption.
  - intros [i li] s iom s' oom [Hv Ht]; cbn in Ht |- *; rewrite <- Ht.
    rapply msg_dep_full_node_transition_iff.
    eapply annotated_free_input_valid_projection; eassumption.
Qed.

Lemma full_node_msg_dep_limited_equivocation_vlsm_eq :
  VLSM_eq
    (full_node_limited_equivocation_vlsm IM sender)
    (msg_dep_limited_equivocation_vlsm IM full_message_dependencies sender).
Proof.
  apply VLSM_eq_incl_iff; split.
  - apply full_node_msg_dep_limited_equivocation_vlsm_incl.
  - apply msg_dep_full_node_limited_equivocation_vlsm_incl.
Qed.

End sec_full_node_msg_dep_limited_equivocation_equivalence.

Section sec_msg_dep_fixed_limited_equivocation.

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
  .

Lemma message_equivocators_can_emit (s : vstate Limited) im
  (Hs : valid_state_prop
          (fixed_equivocation_vlsm_composition IM (state_annotation s))
          (original_state s))
  (Hnobserved: ¬ composite_has_been_observed IM (original_state s) im)
  (HLemit: can_emit Limited im)
  : can_emit
      (equivocators_composition_for_observed IM
        (set_union (state_annotation s)
          (msg_dep_message_equivocators IM full_message_dependencies sender
            (original_state s) im))
        (original_state s))
      im.
Proof.
  unfold msg_dep_message_equivocators, coeqv_message_equivocators
  ; rewrite decide_False by assumption
  ; remember (map_option sender _ ++ _) as equivocating_senders.
  assert (Hsenders :
    forall dm, msg_dep_happens_before message_dependencies dm im ->
    composite_has_been_observed IM (original_state s) dm \/
    exists dm_i, dm_i ∈ equivocating_senders /\
      can_emit (pre_loaded_with_all_messages_vlsm (IM dm_i)) dm).
  {
    intros dm Hdm.
    destruct (decide (composite_has_been_observed IM (original_state s) dm))
      as [Hobs | Hnobs]; [left; assumption | right].
    cut (exists i, sender dm = Some i /\
          can_emit (pre_loaded_with_all_messages_vlsm (IM i)) dm).
    {
      intros (i & Hsender & Hemit).
      exists i; split; [subst | assumption].
      unfold msg_dep_coequivocating_senders, not_observed_happens_before_dependencies
      ; rewrite elem_of_app, !elem_of_map_option
      ; setoid_rewrite elem_of_list_filter
      ; setoid_rewrite full_message_dependencies_happens_before.
      right; exists dm; intuition.
    }
    eapply msg_dep_happens_before_composite_no_initial_valid_messages_emitted_by_sender.
    1-4, 6: eassumption.
    apply emitted_messages_are_valid_iff; right.
    eapply VLSM_full_projection_can_emit; [| eassumption].
    apply forget_annotations_projection.
  }
  eapply VLSM_full_projection_can_emit.
  {
    apply equivocators_composition_for_observed_index_incl_full_projection
     with (Hincl := set_union_subseteq_right (state_annotation s) equivocating_senders).
  }
  assert (Hemitj :
    exists j, j ∈ equivocating_senders /\
      can_emit
        (pre_loaded_vlsm (IM j) (fun dm => msg_dep_happens_before message_dependencies dm im))
        im).
  {
    eapply VLSM_full_projection_can_emit in HLemit
    ; [| apply forget_annotations_projection].
    eapply (VLSM_incl_can_emit (vlsm_incl_pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM)))
        in HLemit.
    apply can_emit_composite_project in HLemit as [j Hemit].
    apply Hchannel in Hemit as Hsender.
    exists j; subst; cbn.
    unfold channel_authenticated_message in Hsender; destruct (sender im) as [_j |];
      [| inversion Hsender].
    apply Some_inj in Hsender; cbn in Hsender; subst.
    split; [left |].
    eapply message_dependencies_are_sufficient in Hemit; [| typeclasses eauto].
    revert Hemit; apply VLSM_incl_can_emit.
    apply pre_loaded_vlsm_incl; intros m Hdm.
    apply msg_dep_happens_before_iff_one; left; assumption.
  }
  destruct Hemitj as [j [Heqv_j Hemitj]].
  eapply valid_preloaded_lifts_can_be_emitted
  ; [eassumption | | eassumption]; clear Heqequivocating_senders.
  induction dm as [dm Hind]
    using (well_founded_ind (msg_dep_happens_before_wf message_dependencies full_message_dependencies))
  ; intros Hdm.
  apply emitted_messages_are_valid_iff.
  destruct (Hsenders _ Hdm) as [Hobs_dm | [dm_i [Hdm_i Hemit_dm]]]
  ; [left; right; assumption | right].
  eapply valid_preloaded_lifts_can_be_emitted
  ; [eassumption | |]; cycle 1.
  - eapply message_dependencies_are_sufficient; [typeclasses eauto | assumption].
  - intros dm' Hdm'; apply Hind.
    + apply msg_dep_happens_before_iff_one; left; assumption.
    + transitivity dm; [| assumption].
      apply msg_dep_happens_before_iff_one; left; assumption.
Qed.

Lemma msg_dep_fixed_limited_equivocation_witnessed is tr
  (Htr : finite_valid_trace Limited is tr)
  (equivocators := state_annotation (finite_trace_last is tr))
  (Fixed := fixed_equivocation_vlsm_composition IM equivocators)
  : (sum_weights (remove_dups equivocators) <= `threshold)%R /\
    finite_valid_trace Fixed
      (original_state is)
      (pre_VLSM_full_projection_finite_trace_project
        (type Limited) (composite_type IM) Datatypes.id original_state
        tr).
Proof.
  split.
  - rewrite set_eq_nodup_sum_weight_eq
      with (lv2 := state_annotation (finite_trace_last is tr)).
    + apply coeqv_limited_equivocation_state_not_heavy,
            finite_valid_trace_last_pstate, Htr.
    + apply NoDup_remove_dups.
    + apply coeqv_limited_equivocation_state_annotation_nodup,
            finite_valid_trace_last_pstate, Htr.
    + apply set_eq_extract_forall.
      setoid_rewrite elem_of_remove_dups.
      intuition.
  - split; [| apply Htr].
    apply valid_trace_add_default_last in Htr.
    induction Htr using finite_valid_trace_init_to_rev_ind
    ; [constructor; apply initial_state_is_valid; apply Hsi |].
    setoid_rewrite map_app.
    apply finite_valid_trace_from_app_iff; split.
    + revert IHHtr.
      eapply VLSM_incl_finite_valid_trace_from,
             fixed_equivocation_vlsm_composition_index_incl,
             coeqv_limited_equivocation_transition_state_annotation_incl,
             Ht.
    + apply finite_valid_trace_singleton.
      unfold input_valid_transition, input_valid.
      change (map _ _) with (pre_VLSM_full_projection_finite_trace_project  (type Limited) (composite_type IM) Datatypes.id original_state tr).
      rewrite <- pre_VLSM_full_projection_finite_trace_last.
      assert (Hs :
        valid_state_prop
          (fixed_equivocation_vlsm_composition IM (state_annotation s))
          (original_state s)).
      {
        replace s with (finite_trace_last si tr) at 2
          by (apply valid_trace_get_last in Htr; assumption).
        rewrite
          (pre_VLSM_full_projection_finite_trace_last
            (type Limited) (composite_type IM) Datatypes.id original_state
            si tr).
        apply finite_valid_trace_last_pstate; assumption.
      }
      destruct Ht as [[HLs [HLim HLv]] HLt].
      cbn in HLt |- *; unfold annotated_transition in HLt; cbn in HLt.
      replace (finite_trace_last si _) with s
        by (apply valid_trace_get_last in Htr; congruence).
      destruct l as [i li], (vtransition _ _ _) as (si', om').
      inversion HLt; subst; clear HLt; cbn.
      repeat split.
      * revert Hs; apply VLSM_incl_valid_state.
        apply fixed_equivocation_vlsm_composition_index_incl.
        destruct iom as [im |]
        ; [apply set_union_subseteq_left | reflexivity].
      * destruct iom as [im |]
        ; [apply option_valid_message_Some|apply option_valid_message_None].
        destruct (decide (composite_has_been_observed IM (original_state s) im))
              as [Hobs | Hnobs].
        -- eapply composite_observed_valid; [| eassumption].
           revert Hs; apply VLSM_incl_valid_state.
           apply fixed_equivocation_vlsm_composition_index_incl,
                 set_union_subseteq_left.
        -- revert HLim.
           setoid_rewrite emitted_messages_are_valid_iff.
           intros [Hinit | Hemit]; [left; assumption | right].
           eapply VLSM_weak_full_projection_can_emit.
           {
             eapply EquivPreloadedBase_Fixed_weak_full_projection
               with (base_s := original_state s).
             - revert Hs; apply VLSM_incl_valid_state.
               apply fixed_equivocation_vlsm_composition_index_incl,
                 set_union_subseteq_left.
             - intros; apply no_initial_messages_in_IM.
           }
           eapply VLSM_incl_can_emit.
           {
             apply Equivocators_Fixed_Strong_incl.
             revert Hs; apply VLSM_incl_valid_state.
             apply fixed_equivocation_vlsm_composition_index_incl,
               set_union_subseteq_left.
           }
           apply message_equivocators_can_emit; assumption.
      * apply HLv.
      * destruct iom as [im |]; [| exact I].
        destruct (decide (composite_has_been_observed IM (original_state s) im))
              as [Hobs | Hnobs]; [left; assumption | right; cbn].
        apply message_equivocators_can_emit; [assumption | assumption|].
        cut (vinitial_message_prop Limited im \/ can_emit Limited im)
        ; [| apply emitted_messages_are_valid_iff; assumption].
        intros [[j [[mj Hmj] Heqim]] | Hemit]; [| assumption].
        contradiction (no_initial_messages_in_IM j mj).
Qed.

Corollary msg_dep_fixed_limited_equivocation is tr
  : finite_valid_trace Limited is tr ->
    fixed_limited_equivocation_prop IM
      (original_state is)
      (pre_VLSM_full_projection_finite_trace_project
        (type Limited) (composite_type IM) Datatypes.id original_state
        tr).
Proof.
  intro Htr.
  exists (state_annotation (finite_trace_last is tr)).
  apply msg_dep_fixed_limited_equivocation_witnessed; assumption.
Qed.

Lemma fixed_transition_preserves_annotation_equivocators
  equivocators
  (is : vstate (free_composite_vlsm IM)) s tr
  (Htr1 :
    finite_valid_trace_init_to (fixed_equivocation_vlsm_composition IM equivocators)
    is s tr)
  l iom sf oom
  (Ht :
    input_valid_transition
      (fixed_equivocation_vlsm_composition IM equivocators) l
      (s, iom) (sf, oom))
  (Hsub_equivocators :
    state_annotation
      (@finite_trace_last _ (type Limited)
        {| original_state := is; state_annotation := `inhabitant |}
        (msg_dep_annotate_trace_with_equivocators IM full_message_dependencies sender is tr))
    ⊆ equivocators)
  : msg_dep_composite_transition_message_equivocators IM
      full_message_dependencies sender l
      (@finite_trace_last _ (type Limited)
        {| original_state := is; state_annotation := empty_set |}
        (annotate_trace_from (free_composite_vlsm IM)
          (set index)
          (msg_dep_composite_transition_message_equivocators IM full_message_dependencies sender)
          {| original_state := is; state_annotation := empty_set |} tr), iom)
    ⊆ equivocators.
Proof.
  destruct iom as [im |]; [| assumption].
  apply set_union_subseteq_iff; split; [assumption | cbn].
  rewrite annotate_trace_from_last_original_state; cbn.
  replace (finite_trace_last _ _) with s
       by (apply valid_trace_get_last in Htr1; congruence).
  unfold coeqv_message_equivocators.
  case_decide as Hnobserved; [apply list_subseteq_nil |].
  destruct Ht as [(Hs & Him & Hv & [Hobs | Hemitted]) Ht]
  ; [contradiction | intros eqv Heqv].
  unfold msg_dep_coequivocating_senders,
         not_observed_happens_before_dependencies in Heqv
  ; rewrite elem_of_app, !elem_of_map_option in Heqv
  ; setoid_rewrite elem_of_list_singleton in Heqv
  ; setoid_rewrite elem_of_list_filter in Heqv.
  destruct Heqv as [(msg & Hmsg & Hsender) | (msg & [Hnobserved_msg Hdep_msg] & Hsender)].
  - subst msg.
    eapply VLSM_incl_can_emit in Hemitted
    ; [| apply pre_loaded_vlsm_incl_pre_loaded_with_all_messages].
    apply can_emit_composite_project in Hemitted as [sub_eqv Hemitted].
    destruct_dec_sig sub_eqv _eqv H_eqv Heqsub_eqv; subst.
    unfold sub_IM in Hemitted; cbn in Hemitted.
    eapply Hsender_safety in Hemitted; [| eassumption].
    subst; assumption.
  - cut (strong_fixed_equivocation IM equivocators s msg).
    {
      intros [Hobserved | Hemitted_msg].
      - contradict Hnobserved_msg.
        eapply sent_by_non_equivocating_are_observed; eassumption.
      - eapply VLSM_incl_can_emit in Hemitted_msg
        ; [| apply pre_loaded_vlsm_incl_pre_loaded_with_all_messages].
        apply can_emit_composite_project in Hemitted_msg as [sub_i Hemitted_msg].
        destruct_dec_sig sub_i i Hi Heqsub_i; subst.
        eapply Hsender_safety in Hemitted_msg; [| eassumption].
        cbn in Hemitted_msg; subst; assumption.
    }
    eapply msg_dep_happens_before_reflect
    ; [| eapply full_message_dependencies_happens_before; eassumption | right]
    ; cycle 1.
    + eapply VLSM_incl_can_emit; [| eassumption].
      apply Equivocators_Fixed_Strong_incl; assumption.
    + eapply msg_dep_rel_reflects_strong_fixed_equivocation
      ; [assumption | assumption |].
      apply VLSM_incl_valid_state; [| assumption].
      apply Fixed_incl_StrongFixed.
Qed.

Lemma msg_dep_limited_fixed_equivocation
  (is : vstate (free_composite_vlsm IM)) (tr : list (composite_transition_item IM))
  : fixed_limited_equivocation_prop IM is tr ->
    finite_valid_trace Limited
      {| original_state := is; state_annotation := ` inhabitant |}
      (msg_dep_annotate_trace_with_equivocators IM full_message_dependencies sender is tr).
Proof.
  intros (equivocators & Hlimited & Htr).
  split; [| split; [apply Htr | reflexivity]].
  apply valid_trace_add_default_last in Htr.
  match goal with
  |- finite_valid_trace_from Limited ?is ?tr =>
    cut
      (finite_valid_trace_from Limited is tr /\
        (state_annotation (@finite_trace_last _ (type Limited) is tr) ⊆ equivocators))
  end
  ; [intuition |].
  induction Htr using finite_valid_trace_init_to_rev_strong_ind.
  - split; [| apply list_subseteq_nil].
    constructor; apply initial_state_is_valid; split; [assumption | reflexivity].
  - setoid_rewrite annotate_trace_from_app; cbn
    ; unfold annotate_trace_item; rewrite !finite_trace_last_is_last; cbn.
    split; cycle 1.
    + eapply fixed_transition_preserves_annotation_equivocators
      ; [eassumption | eassumption | apply IHHtr1].
    + apply finite_valid_trace_from_app_iff.
      split; [apply IHHtr1 |].
      apply finite_valid_trace_singleton.
      repeat split.
      * apply finite_valid_trace_last_pstate, IHHtr1.
      * clear -Heqiom IHHtr2.
        destruct IHHtr2 as [IHHtr2 _].
        unfold empty_initial_message_or_final_output in Heqiom.
        destruct_list_last iom_tr iom_tr' iom_item Heqiom_tr
        ; [apply option_initial_message_is_valid; assumption|].
        destruct iom as [im |]; [| apply option_valid_message_None].
        eapply valid_trace_output_is_valid; [eassumption |].
        setoid_rewrite annotate_trace_from_app.
        apply Exists_app; right.
        destruct iom_item.
        apply Exists_exists; eexists; split; [left | assumption].
      * destruct l as [i li]; cbn
        ; rewrite annotate_trace_from_last_original_state; cbn.
        replace (finite_trace_last _ _) with s
             by (apply valid_trace_get_last in Htr1; congruence).
        apply Ht.
      * apply Rle_trans with (sum_weights (remove_dups equivocators))
        ; [| assumption].
        apply sum_weights_subseteq.
        -- destruct iom as [im|]; cycle 1.
           ++ eapply coeqv_limited_equivocation_state_annotation_nodup.
              apply finite_valid_trace_last_pstate, IHHtr1.
           ++ apply set_union_nodup_left.
              eapply coeqv_limited_equivocation_state_annotation_nodup.
              apply finite_valid_trace_last_pstate, IHHtr1.
        -- apply NoDup_remove_dups.
        -- transitivity equivocators.
           ++ eapply fixed_transition_preserves_annotation_equivocators
              ; [eassumption | eassumption | apply IHHtr1].
           ++ intro; apply elem_of_remove_dups.
      * destruct l as [i li]; cbn; unfold annotated_transition; cbn.
        rewrite !annotate_trace_from_last_original_state; cbn.
        replace (finite_trace_last _ _) with s
             by (apply valid_trace_get_last in Htr1; congruence).
        destruct Ht as [_ Ht]; cbn in Ht
        ; destruct (vtransition _ _ _) as (si', om')
        ; inversion Ht; reflexivity.
Qed.

Lemma annotated_limited_incl_constrained_limited
  {is_equivocating_tracewise_no_has_been_sent_dec : RelDecision (is_equivocating_tracewise_no_has_been_sent IM (fun i => i) sender)}
  : VLSM_full_projection
      Limited
      (limited_equivocation_vlsm_composition IM sender)
      Datatypes.id original_state.
Proof.
  constructor; intros sX trX HtrX.
  eapply traces_exhibiting_limited_equivocation_are_valid.
  - apply Hsender_safety.
  - apply msg_dep_fixed_limited_equivocation; assumption.
Qed.

End sec_msg_dep_fixed_limited_equivocation.