From VLSM.Lib Require Import Itauto.
From Coq Require Import FinFun FunctionalExtensionality.
From stdpp Require Import prelude finite.
From VLSM.Lib Require Import Preamble.
From VLSM.Core Require Import VLSM VLSMProjections Composition Validator ProjectionTraces.
From VLSM.Core Require Import SubProjectionTraces Equivocation Equivocation.NoEquivocation.

(** * Fixed Set Equivocation

  In this section we define fixed equivocation for the regular composition.

  Assuming that a only a fixed subset of the nodes (here called equivocating)
  are allowed to equivocate, inspired by the results leading to
  Lemma [equivocators_valid_trace_from_project] which links state equivocation
  to free composition, we can say that a message can be produced by a network
  of nodes allowed to equivocate, if it can be produced by their free composition
  [free_equivocating_vlsm_composition] preloaded with the current information
  (messages) available to it at the moment of production.
*)

Section sec_fixed_equivocation_without_fullnode.

Context
  {message : Type}
  `{FinSet index Ci}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  `{forall i : index, HasBeenSentCapability (IM i)}
  `{forall i : index, HasBeenReceivedCapability (IM i)}
  (equivocating : Ci)
  (Free := free_composite_vlsm IM)
  (index_equivocating_prop : index -> Prop := sub_index_prop (elements equivocating))
  (equivocating_index : Type := sub_index (elements equivocating))
  (equivocating_IM := sub_IM IM (elements equivocating))
  .

(**
  [free_equivocating_vlsm_composition] is the free composition of the subset of
  nodes which are allowed to equivocate.
*)
Definition free_equivocating_vlsm_composition : VLSM message :=
  free_composite_vlsm equivocating_IM.

(**
  [pre_loaded_free_equivocating_vlsm_composition] preloads the free composition
  of equivocating nodes all with the messages given by the <<messageSet>>.
*)
Definition pre_loaded_free_equivocating_vlsm_composition
  (messageSet : message -> Prop)
  := pre_loaded_vlsm free_equivocating_vlsm_composition messageSet.

(**
  Given a composite state <<s>>, we define the composition of equivocators
  preloaded with the messages directly observed in <<s>>.
*)
Definition equivocators_composition_for_directly_observed s
  := pre_loaded_free_equivocating_vlsm_composition (composite_has_been_directly_observed IM s).

(**
  The fixed equivocation constraint for the regular composition of nodes
  stipulates that a message can be received either if it [has_been_directly_observed]
  or it can be emitted by the free composition of equivocators pre-loaded with
  the messages directly observed in the current state.
*)
Definition fixed_equivocation s m
  := composite_has_been_directly_observed IM s m \/
    can_emit (equivocators_composition_for_directly_observed s) m.

Definition fixed_equivocation_constraint
  (l : composite_label IM)
  (som : composite_state IM * option message)
  : Prop
  :=
  let (s, om) := som in
  from_option (fixed_equivocation s) True om.

(**
  Composition of regular VLSMs under the [fixed_equivocation_constraint]s.

  In the remainder of this module we will refer to this as the <<Fixed>> VLSM.
*)
Definition fixed_equivocation_vlsm_composition : VLSM message
  := composite_vlsm IM fixed_equivocation_constraint.

Lemma fixed_equivocation_vlsm_composition_incl_free
  : VLSM_incl fixed_equivocation_vlsm_composition Free.
Proof.
  by apply constraint_free_incl.
Qed.

Lemma fixed_equivocation_vlsm_composition_incl_preloaded_free
  : VLSM_incl fixed_equivocation_vlsm_composition (pre_loaded_with_all_messages_vlsm Free).
Proof.
  apply VLSM_incl_trans with Free.
  - by apply fixed_equivocation_vlsm_composition_incl_free.
  - by apply vlsm_incl_pre_loaded_with_all_messages_vlsm.
Qed.

(** ** A (seemingly) stronger definition for fixed-set equivocation

  A seemingly stronger fixed equivocation constraint requires that a received
  message either [has_been_sent] by a non-equivocating node
  or it can be emitted by the free composition of equivocators pre-loaded with
  messages which have been sent by non-equivocating nodes.

  We say seemingly because, as shown by the [Fixed_eq_StrongFixed] result,
  the compositions constrained by the two [fixed_equivocation_constraint]s
  are trace-equivalent.
*)

Section sec_strong_fixed_equivocation.

Definition sent_by_non_equivocating s m
  := exists i, i ∉ elements equivocating /\ has_been_sent (IM i) (s i) m.

#[export] Instance sent_by_non_equivocating_dec : RelDecision sent_by_non_equivocating.
Proof.
  intros s m.
  apply @Decision_iff with (P := Exists (fun i => has_been_sent (IM i) (s i) m)
    (filter (fun i => i ∉ elements equivocating) (enum index))).
  - rewrite Exists_exists. apply exist_proper. intro i.
    rewrite elem_of_list_filter. apply and_iff_compat_r.
    split; [intros [Hi Hl]; done | split; [done |]].
    by apply elem_of_enum.
  - by apply Exists_dec; intro i; apply has_been_sent_dec.
Qed.

Lemma sent_by_non_equivocating_are_sent s m
  (Hsent : sent_by_non_equivocating s m)
  : composite_has_been_sent IM s m.
Proof.
  by destruct Hsent as [i [Hi Hsent]]; exists i.
Qed.

Lemma sent_by_non_equivocating_are_directly_observed s m
  (Hsent : sent_by_non_equivocating s m)
  : composite_has_been_directly_observed IM s m.
Proof.
  apply composite_has_been_directly_observed_sent_received_iff; left.
  by apply sent_by_non_equivocating_are_sent.
Qed.

(**
  Given a composite state <<s>>, we define the composition of equivocators
  preloaded with the messages sent by non-equivocating nodes in <<s>>.
*)
Definition equivocators_composition_for_sent s
  := pre_loaded_free_equivocating_vlsm_composition (sent_by_non_equivocating s).

Definition strong_fixed_equivocation s m
  := sent_by_non_equivocating s m \/
    can_emit (equivocators_composition_for_sent s) m.

Definition strong_fixed_equivocation_constraint
  (l : composite_label IM)
  (som : composite_state IM * option message)
  : Prop
  :=
  let (s, om) := som in
  from_option (strong_fixed_equivocation s) True om.

Definition strong_fixed_equivocation_vlsm_composition : VLSM message
  := composite_vlsm IM strong_fixed_equivocation_constraint.

(**
  The composition of equivocators pre-loaded with only the messages sent by
  non-equivocators is included in that pre-loaded with all the directly observed
  messages.
*)
Lemma Equivocators_Strong_Fixed_incl base_s
  : VLSM_incl
      (equivocators_composition_for_sent base_s)
      (equivocators_composition_for_directly_observed base_s).
Proof.
  apply pre_loaded_vlsm_incl.
  by apply sent_by_non_equivocating_are_directly_observed.
Qed.

(**
  [strong_fixed_equivocation_constraint] is stronger than
  the [fixed_equivocation_constraint].
*)
Lemma strong_fixed_equivocation_subsumption s m
  : strong_fixed_equivocation s m -> fixed_equivocation s m.
Proof.
  intros [Hobs | Hemit]; [left | right].
  - by apply sent_by_non_equivocating_are_directly_observed.
  - revert Hemit. apply VLSM_incl_can_emit.
    by apply Equivocators_Strong_Fixed_incl.
Qed.

Lemma strong_fixed_equivocation_constraint_subsumption
  : strong_constraint_subsumption IM
    strong_fixed_equivocation_constraint
    fixed_equivocation_constraint.
Proof.
  intros l [s [m |]] Hc; [| done].
  by apply strong_fixed_equivocation_subsumption.
Qed.

Lemma StrongFixed_incl_Fixed
  : VLSM_incl strong_fixed_equivocation_vlsm_composition fixed_equivocation_vlsm_composition.
Proof.
  apply constraint_subsumption_incl.
  apply preloaded_constraint_subsumption_stronger.
  apply strong_constraint_subsumption_strongest.
  by apply strong_fixed_equivocation_constraint_subsumption.
Qed.

End sec_strong_fixed_equivocation.

End sec_fixed_equivocation_without_fullnode.

(** ** Extending the set of nodes allowed to equivocate *)

Section sec_fixed_equivocation_index_incl.

Context
  {message : Type}
  `{FinSet index Ci}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  `{forall i : index, HasBeenSentCapability (IM i)}
  `{forall i : index, HasBeenReceivedCapability (IM i)}
  (indices1 indices2 : Ci)
  (Hincl : elements indices1 ⊆ elements indices2)
  .

Lemma equivocators_composition_for_directly_observed_index_incl_embedding
  (s : state (composite_type IM))
  : VLSM_embedding
    (equivocators_composition_for_directly_observed IM indices1 s)
    (equivocators_composition_for_directly_observed IM indices2 s)
    (lift_sub_incl_label IM _ _ Hincl) (lift_sub_incl_state IM _ _).
Proof.
  by apply lift_sub_incl_preloaded_embedding.
Qed.

Lemma fixed_equivocation_index_incl_subsumption
  : forall s m,
    fixed_equivocation IM indices1 s m ->
    fixed_equivocation IM indices2 s m.
Proof.
  intros s m [Hobs | Hemit]; [by left |].
  right.
  specialize
    (equivocators_composition_for_directly_observed_index_incl_embedding s)
    as Hproj.
  by apply (VLSM_embedding_can_emit Hproj) in Hemit.
Qed.

Lemma fixed_equivocation_constraint_index_incl_subsumption
  : strong_constraint_subsumption IM
    (fixed_equivocation_constraint IM indices1)
    (fixed_equivocation_constraint IM indices2).
Proof.
  intros l (s, [m |]); [| done].
  by apply fixed_equivocation_index_incl_subsumption.
Qed.

Lemma fixed_equivocation_vlsm_composition_index_incl
  : VLSM_incl
    (fixed_equivocation_vlsm_composition IM indices1)
    (fixed_equivocation_vlsm_composition IM indices2).
Proof.
  apply constraint_subsumption_incl.
  apply preloaded_constraint_subsumption_stronger.
  apply strong_constraint_subsumption_strongest.
  by apply fixed_equivocation_constraint_index_incl_subsumption.
Qed.

End sec_fixed_equivocation_index_incl.

(** ** Restricting Fixed valid traces to only the equivocators

  In this section we study the properties of Fixed valid traces
  when projected to the composition of equivocator nodes.

  The main result, Lemma [fixed_finite_valid_trace_sub_projection]
  is a strengthening of Lemma [finite_valid_trace_sub_projection] for the
  [fixed_equivocation_constraint], showing that, when restricting
  a Fixed valid trace to only the transitions belonging to the equivocators,
  the obtained trace is valid for the composition of equivocators pre-loaded
  only with those messages sent by the non-equivocators in the original trace.
*)

Section sec_fixed_equivocator_sub_projection.

Context
  {message : Type}
  `{FinSet index Ci}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  `{forall i, HasBeenSentCapability (IM i)}
  `{forall i, HasBeenReceivedCapability (IM i)}
  (equivocators : Ci)
  (Fixed := fixed_equivocation_vlsm_composition IM equivocators)
  (StrongFixed := strong_fixed_equivocation_vlsm_composition IM equivocators)
  (Free := free_composite_vlsm IM)
  (PreFree := pre_loaded_with_all_messages_vlsm Free)
  .

Definition Fixed_incl_Free : VLSM_incl Fixed Free := constraint_free_incl _ _.

Lemma Fixed_incl_Preloaded : VLSM_incl Fixed (pre_loaded_with_all_messages_vlsm Free).
Proof.
  eapply VLSM_incl_trans; [by apply Fixed_incl_Free |].
  by apply (vlsm_incl_pre_loaded_with_all_messages_vlsm Free).
Qed.

Lemma preloaded_Fixed_incl_Preloaded :
  VLSM_incl (pre_loaded_with_all_messages_vlsm Fixed) (pre_loaded_with_all_messages_vlsm Free).
Proof.
  exact (preloaded_constraint_free_incl _ _).
Qed.

Lemma StrongFixed_incl_Free : VLSM_incl StrongFixed Free.
Proof.
  exact (constraint_free_incl _ _).
Qed.

Lemma StrongFixed_incl_Preloaded :
  VLSM_incl StrongFixed (pre_loaded_with_all_messages_vlsm Free).
Proof.
  eapply VLSM_incl_trans; [by apply StrongFixed_incl_Free |].
  by apply (vlsm_incl_pre_loaded_with_all_messages_vlsm Free).
Qed.

Lemma in_futures_preserves_sent_by_non_equivocating s base_s
  (Hfuture_s : in_futures PreFree s base_s)
  : forall m : message,
    sent_by_non_equivocating IM equivocators s m ->
    sent_by_non_equivocating IM equivocators base_s m.
Proof.
  intros m (i & Hi & Hsent).
  exists i; split; [done |].
  eapply in_futures_preserving_oracle_from_stepwise; [| | done].
  - by apply has_been_sent_stepwise_props.
  - by apply (VLSM_projection_in_futures (preloaded_component_projection IM i)).
Qed.

Lemma in_futures_preserves_can_emit_by_equivocators_composition_for_sent s base_s
  (Hfuture_s : in_futures PreFree s base_s)
  : forall m : message,
    can_emit (equivocators_composition_for_sent IM equivocators s) m ->
    can_emit (equivocators_composition_for_sent IM equivocators base_s) m.
Proof.
  by apply VLSM_incl_can_emit, pre_loaded_vlsm_incl,
        in_futures_preserves_sent_by_non_equivocating.
Qed.

Lemma in_futures_preserves_strong_fixed_equivocation s base_s
  (Hfuture_s : in_futures PreFree s base_s)
  m
  (Hstrong : strong_fixed_equivocation IM equivocators s m)
  : strong_fixed_equivocation IM equivocators base_s m.
Proof.
  destruct Hstrong as [Hsent | Hemit]; [left | right].
  - by eapply in_futures_preserves_sent_by_non_equivocating.
  - by eapply in_futures_preserves_can_emit_by_equivocators_composition_for_sent.
Qed.

Lemma strong_fixed_equivocation_eqv_valid_message base_s m
  (Hstrong : strong_fixed_equivocation IM equivocators base_s m)
  : valid_message_prop (equivocators_composition_for_sent IM equivocators base_s) m.
Proof.
   destruct Hstrong as [Hobs | Hemit].
  - by apply initial_message_is_valid; right.
  - by apply emitted_messages_are_valid in Hemit.
Qed.

Lemma strong_fixed_equivocation_eqv_valid_message_in_futures base_s s
  (Hfuture_s : in_futures PreFree s base_s)
  m
  (Hstrong : strong_fixed_equivocation IM equivocators s m)
  : valid_message_prop (equivocators_composition_for_sent IM equivocators base_s) m.
Proof.
  destruct (in_futures_preserves_strong_fixed_equivocation _ _ Hfuture_s _ Hstrong)
    as [Hobs | Hemit].
  - by apply initial_message_is_valid; right.
  - by apply emitted_messages_are_valid in Hemit.
Qed.

Section sec_fixed_finite_valid_trace_sub_projection_helper_lemmas.

(**
  The results in this section are not meant to be used directly. They are just
  sub-lemmas of [fixed_finite_valid_trace_sub_projection_helper].

  We make an assumption (<<Hobs_s_protocol>>) which is later shown to hold
  for all Fixed valid states.

  We then restate (some of) these lemmas without the extra assumption.
*)

Context
  (base_s s : composite_state IM)
  (Hobs_s_protocol : forall m, composite_has_been_directly_observed IM s m ->
    strong_fixed_equivocation IM equivocators base_s m)
  .

(** See the lemma [fixed_input_has_strong_fixed_equivocation] below. *)
#[local] Lemma fixed_input_has_strong_fixed_equivocation_helper
  l m
  (Hv : input_valid Fixed l (s, Some m))
  : strong_fixed_equivocation IM equivocators base_s m.
Proof.
  destruct Hv as [_ [_ [_ [Hobs | Hemit]]]].
  - by apply Hobs_s_protocol.
  - right.
    clear -Hemit Hobs_s_protocol. revert Hemit.
    apply VLSM_incl_can_emit; simpl.
    apply basic_VLSM_incl; intros s0 **; [done | | by apply Hv | by apply H].
    destruct HmX as [Him | Hobs].
    + by apply initial_message_is_valid; left.
    + apply Hobs_s_protocol in Hobs as [Hsent | Hemit].
      * by apply initial_message_is_valid; right.
      * by apply emitted_messages_are_valid.
Qed.

#[local] Lemma fixed_input_valid_transition_sub_projection_helper
  (Hs_pr : valid_state_prop (equivocators_composition_for_sent IM equivocators base_s)
    (composite_state_sub_projection IM (elements equivocators) s))
  l
  (e : sub_index_prop (elements equivocators) (projT1 l))
  iom oom sf
  (Ht : input_valid_transition Fixed l (s, iom) (sf, oom))
  : input_valid_transition (equivocators_composition_for_sent IM equivocators base_s)
      (composite_label_sub_projection IM (elements equivocators) l e)
      (composite_state_sub_projection IM (elements equivocators) s, iom)
      (composite_state_sub_projection IM (elements equivocators) sf, oom).
Proof.
  destruct l as (i, li). simpl in *.
  repeat split.
  - done.
  - apply proj1 in Ht.
    destruct iom as [im |]; [| by apply option_valid_message_None].
    apply strong_fixed_equivocation_eqv_valid_message.
    by apply (fixed_input_has_strong_fixed_equivocation_helper _ _ Ht).
  - by apply Ht.
  - destruct Ht as [_ Ht]; cbn in Ht.
    cbn; unfold sub_IM at 2; cbn; unfold composite_state_sub_projection at 1; cbn.
    destruct (transition li _) as (si', om').
    inversion_clear Ht. f_equal.
    clear.
    apply functional_extensionality_dep. intro sub_j.
    destruct_dec_sig sub_j j Hj Heqsub_j. subst.
    unfold composite_state_sub_projection at 2.
    by destruct (decide (i = j)); subst; state_update_simpl.
Qed.

(** See the lemma [fixed_output_has_strong_fixed_equivocation] below. *)
#[local] Lemma fixed_output_has_strong_fixed_equivocation_helper
  (Hs_pr : valid_state_prop (equivocators_composition_for_sent IM equivocators base_s)
    (composite_state_sub_projection IM (elements equivocators) s))
  sf
  (Hfuture : in_futures PreFree sf base_s)
  l iom om
  (Ht : input_valid_transition Fixed l (s, iom) (sf, Some om))
  : strong_fixed_equivocation IM equivocators base_s om.
Proof.
  destruct (decide (projT1 l ∈ elements equivocators)).
  - apply
      (fixed_input_valid_transition_sub_projection_helper Hs_pr _ e) in Ht.
    by right; eexists _, _, _.
  - left.
    exists (projT1 l). split; [done |].
    apply (VLSM_projection_in_futures
      (preloaded_component_projection IM (projT1 l))) in Hfuture.
    apply in_futures_preserving_oracle_from_stepwise with (field_selector output) (sf (projT1 l))
    ; [by apply has_been_sent_stepwise_props | done |].
    apply (VLSM_incl_input_valid_transition Fixed_incl_Preloaded) in Ht.
    specialize (VLSM_projection_input_valid_transition
      (preloaded_component_projection IM (projT1 l)) l (projT2 l)) as Hproject.
    spec Hproject.
    { unfold composite_project_label.
      destruct (decide _); [| by elim n0].
      replace e with (eq_refl (A := index) (x := projT1 l)); [done |].
      by apply Eqdep_dec.UIP_dec.
    }
    specialize (Hproject _ _ _ _ Ht).
    by apply (has_been_sent_step_update Hproject); left.
Qed.

End sec_fixed_finite_valid_trace_sub_projection_helper_lemmas.

(**
  Using the lemmas above we can now prove (by induction) a generic result,
  which has as part of the conclusion the "observability implies strong_fixed_equivocation"
  hypothesis assumed in the above section.
*)
Lemma fixed_finite_valid_trace_sub_projection_helper
  si s tr
  (Htr : finite_valid_trace_init_to Fixed si s tr)
  base_s
  (Hfuture : in_futures PreFree s base_s)
  : finite_valid_trace_from_to (equivocators_composition_for_sent IM equivocators base_s)
    (composite_state_sub_projection IM (elements equivocators) si)
    (composite_state_sub_projection IM (elements equivocators) s)
    (finite_trace_sub_projection IM (elements equivocators) tr) /\
    forall m, composite_has_been_directly_observed IM s m ->
      strong_fixed_equivocation IM equivocators base_s m.
Proof.
  induction Htr using finite_valid_trace_init_to_rev_ind.
  - split.
    + apply finite_valid_trace_from_to_empty.
      apply (composite_initial_state_sub_projection IM (elements equivocators) si) in Hsi.
      by apply initial_state_is_valid.
    + intros m Hobs; exfalso.
      eapply (@has_been_directly_observed_no_inits _ Free); [done |].
      by apply composite_has_been_directly_observed_free_iff.
  - apply (VLSM_incl_input_valid_transition Fixed_incl_Preloaded) in Ht as Hpre_t.
    assert (Hfuture_s : in_futures PreFree s base_s).
    {
      destruct Hfuture as [tr' Htr'].
      specialize (finite_valid_trace_from_to_extend _ _ _ _ Htr' _ _ _ _ Hpre_t) as Htr''.
      by eexists.
    }
    specialize (IHHtr Hfuture_s) as [Htr_pr Htr_obs].
    split; cycle 1.
    + intros m Hobs.
      eapply @has_been_directly_observed_step_update with (msg := m) (vlsm := Free) in Hpre_t.
      apply composite_has_been_directly_observed_free_iff, Hpre_t in Hobs.
      destruct Hobs as [Hitem | Hobs]
      ; [| by apply composite_has_been_directly_observed_free_iff, Htr_obs in Hobs].
      apply valid_trace_last_pstate in Htr.
      apply valid_trace_last_pstate in Htr_pr.
      destruct Hitem as [Hm | Hm]; subst.
      * by eapply fixed_input_has_strong_fixed_equivocation_helper; destruct Ht.
      * by eapply fixed_output_has_strong_fixed_equivocation_helper; cycle 3.
    + rewrite (finite_trace_sub_projection_app IM (elements equivocators));
      cbn; unfold pre_VLSM_projection_transition_item_project;
      cbn; unfold composite_label_sub_projection_option.
      case_decide as Hl.
      * eapply finite_valid_trace_from_to_app; [by apply Htr_pr |].
        apply finite_valid_trace_from_to_singleton.
        apply valid_trace_last_pstate in Htr_pr.
        by apply fixed_input_valid_transition_sub_projection_helper.
      * rewrite app_nil_r;
        replace (composite_state_sub_projection _ _ sf)
           with (composite_state_sub_projection IM (elements equivocators) s)
        ; [done |].
        destruct Ht as [_ Ht]; cbn in Ht;
        destruct l as (i, li), (transition _ _ _) as (si', om');
        inversion_clear Ht; clear -Hl.
        extensionality sub_j; destruct_dec_sig sub_j j Hj Heqsub_j;
        subst; unfold composite_state_sub_projection.
        by destruct (decide (i = j)); subst; state_update_simpl.
Qed.

(**
  Main result of this section: when restricting a Fixed valid trace to only
  the transitions belonging to the equivocators, the obtained trace is valid
  for the composition of equivocators pre-loaded with messages sent by the
  non-equivocators in the original trace.

  This is a simple corollary of Lemma [fixed_finite_valid_trace_sub_projection_helper]
  proved above.
*)
Lemma fixed_finite_valid_trace_sub_projection is f tr
  (Htr : finite_valid_trace_init_to Fixed is f tr)
  : finite_valid_trace_init_to
              (equivocators_composition_for_sent IM equivocators f)
              (composite_state_sub_projection IM (elements equivocators) is)
              (composite_state_sub_projection IM (elements equivocators) f)
              (finite_trace_sub_projection IM (elements equivocators) tr).
Proof.
  apply fixed_finite_valid_trace_sub_projection_helper with (base_s := f) in Htr as Htr_pr.
  - split; [by apply Htr_pr |].
    apply proj2 in Htr.
    by specialize (composite_initial_state_sub_projection IM (elements equivocators) is Htr).
  - apply in_futures_refl. apply valid_trace_last_pstate in Htr.
    by apply (VLSM_incl_valid_state Fixed_incl_Preloaded).
Qed.

(**
  Any message directly observed in a Fixed valid state has either been sent by the
  non-equivocating nodes, or it can be generated by the equivocating nodes
  using only the messages sent by the non-equivocating nodes.
*)
Lemma fixed_directly_observed_has_strong_fixed_equivocation f
  (Hf : valid_state_prop Fixed f)
  m
  (Hobs : composite_has_been_directly_observed IM f m)
  : strong_fixed_equivocation IM equivocators f m.
Proof.
  apply (VLSM_incl_valid_state Fixed_incl_Preloaded) in Hf as Hfuture.
  apply in_futures_refl in Hfuture.
  apply valid_state_has_trace in Hf as [is [tr Htr]].
  eapply fixed_finite_valid_trace_sub_projection_helper in Htr as Htr_pr; [| done].
  by apply Htr_pr.
Qed.

Lemma fixed_valid_state_sub_projection s f
  (Hsf : in_futures Fixed s f)
  : valid_state_prop
    (equivocators_composition_for_sent IM equivocators f)
    (composite_state_sub_projection IM (elements equivocators) s).
Proof.
  destruct Hsf as [tr Htr].
  apply finite_valid_trace_from_to_complete_left in Htr as [is [trs [Htr Hs]]].
  apply fixed_finite_valid_trace_sub_projection in Htr as Hpr_tr.
  apply proj1, finite_valid_trace_from_to_app_split, proj1, valid_trace_forget_last in Htr.
  rewrite (finite_trace_sub_projection_app IM (elements equivocators)) in Hpr_tr.
  apply proj1, finite_valid_trace_from_to_app_split, proj1, valid_trace_last_pstate in Hpr_tr.
  subst s. simpl.
  by rewrite <- (finite_trace_sub_projection_last_state IM _ _ _ _ Htr).
Qed.

(**
  The input of a Fixed input valid transition has the [strong_fixed_equivocation]
  property.
*)
Lemma fixed_input_has_strong_fixed_equivocation
  l s m
  (Ht : input_valid Fixed l (s, Some m))
  : strong_fixed_equivocation IM equivocators s m.
Proof.
  apply fixed_input_has_strong_fixed_equivocation_helper with (base_s := s) in Ht
  ; [done |].
  by apply fixed_directly_observed_has_strong_fixed_equivocation, Ht.
Qed.

(**
  The output of a Fixed input valid transition has the [strong_fixed_equivocation]
  property for its destination.
*)
Lemma fixed_output_has_strong_fixed_equivocation
  l s iom sf om
  (Ht : input_valid_transition Fixed l (s, iom) (sf, Some om))
  : strong_fixed_equivocation IM equivocators sf om.
Proof.
  apply input_valid_transition_origin in Ht as Hs.
  apply fixed_output_has_strong_fixed_equivocation_helper with s sf l iom.
  - intros m Hobs. apply in_futures_preserves_strong_fixed_equivocation with s.
    + apply (VLSM_incl_input_valid_transition Fixed_incl_Preloaded) in Ht.
      by eapply (input_valid_transition_in_futures PreFree).
    + by apply fixed_directly_observed_has_strong_fixed_equivocation.
  - apply input_valid_transition_in_futures in Ht.
    by apply fixed_valid_state_sub_projection.
  - apply in_futures_refl. apply input_valid_transition_destination in Ht.
    by apply (VLSM_incl_valid_state Fixed_incl_Preloaded).
  - done.
Qed.

End sec_fixed_equivocator_sub_projection.

(**
  [strong_fixed_equivocation_constraint] is not actually stronger/

  In this section we show that the compositions of nodes using
  the [fixed_equivocation_constraint] and the [strong_fixed_equivocation]
  are trace-equivalent.

  The importance of this result is that we can reduce the complexity of proofs
  involving fixed equivocation by using the [strong_fixed_equivocation] constraint
  in the hypotheses of a lemma and the "weaker" [fixed_equivocation_constraint]
  in the conclusion.
*)

Section sec_Fixed_eq_StrongFixed.

Context
  {message : Type}
  `{FinSet index Ci}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  `{forall i, HasBeenSentCapability (IM i)}
  `{forall i, HasBeenReceivedCapability (IM i)}
  (equivocators : Ci)
  (Fixed := fixed_equivocation_vlsm_composition IM equivocators)
  (StrongFixed := strong_fixed_equivocation_vlsm_composition IM equivocators)
  (Free := free_composite_vlsm IM)
  (PreFree := pre_loaded_with_all_messages_vlsm Free)
  .

(**
  Given a Fixed valid state, the composition of the equivocators
  preloaded with all the directly observed messages in the state is not stronger
  than that preloaded with only the messages sent by non-equivocators.
*)
Lemma Equivocators_Fixed_Strong_incl base_s
  (Hbase_s : valid_state_prop Fixed base_s)
  : VLSM_incl
      (equivocators_composition_for_directly_observed IM equivocators base_s)
      (equivocators_composition_for_sent IM equivocators base_s).
Proof.
  apply basic_VLSM_incl.
  - by intros s Hincl.
  - intros l s m Hv HsY [Hinit | Hobs]
    ; [by apply initial_message_is_valid; left |].
    apply strong_fixed_equivocation_eqv_valid_message.
    by apply fixed_directly_observed_has_strong_fixed_equivocation.
  - by intros l s om (_ & _ & Hv) _ _.
  - by destruct 1.
Qed.

Lemma Equivocators_Fixed_Strong_eq base_s
  (Hbase_s : valid_state_prop Fixed base_s)
  : VLSM_eq
      (equivocators_composition_for_directly_observed IM equivocators base_s)
      (equivocators_composition_for_sent IM equivocators base_s).
Proof.
  split.
  - by apply Equivocators_Fixed_Strong_incl.
  - by apply Equivocators_Strong_Fixed_incl.
Qed.

(**
  The subsumption between [fixed_equivocation_constraint] and
  [strong_fixed_equivocation_constraint] holds under [input_valid] assumptions.
*)
Lemma fixed_strong_equivocation_subsumption
  : input_valid_constraint_subsumption IM
    (fixed_equivocation_constraint IM equivocators)
    (strong_fixed_equivocation_constraint IM equivocators).
Proof.
  intros l (s, om) Hv.
  destruct om as [m |]; [| done].
  apply proj1 in Hv as Hs.
  by eapply fixed_input_has_strong_fixed_equivocation.
Qed.

Lemma Fixed_incl_StrongFixed : VLSM_incl Fixed StrongFixed.
Proof.
  apply constraint_subsumption_incl. apply fixed_strong_equivocation_subsumption.
Qed.

Lemma Fixed_eq_StrongFixed : VLSM_eq Fixed StrongFixed.
Proof.
  split.
  - by apply Fixed_incl_StrongFixed.
  - by apply StrongFixed_incl_Fixed.
Qed.

End sec_Fixed_eq_StrongFixed.

(** ** Changing the behavior of equivocators within a trace

  By noting that the satisfaction of the [fixed_equivocation_constraint] actually
  only depends on the messages sent by non-equivocating nodes, it makes it much
  easier to establish results related to changing the behavior of equivocating
  nodes.

  In this section we essentially prove that given a Fixed valid state <<s>>,
  any valid trace over the composition of equivocators pre-loaded with the
  messages directly observed in <<s>> can be "lifted" to a Fixed valid trace in which
  the non-equivocators remain in their corresponding component-state given by <<s>>
  (lemma [EquivPreloadedBase_Fixed_weak_embedding]).
*)

Section sec_fixed_equivocator_lifting.

Context
  {message : Type}
  `{FinSet index Ci}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  `{forall i, HasBeenSentCapability (IM i)}
  `{forall i, HasBeenReceivedCapability (IM i)}
  (equivocators : Ci)
  (Free := free_composite_vlsm IM)
  (Fixed := fixed_equivocation_vlsm_composition IM equivocators)
  (StrongFixed := strong_fixed_equivocation_vlsm_composition IM equivocators)
  (PreFree := pre_loaded_with_all_messages_vlsm Free)
  .

(**
  Replacing the state corresponding to the equivocators does not affect the
  [sent_by_non_equivocating] property.
*)
Lemma lift_sub_state_to_sent_by_non_equivocating_iff s eqv_is m
  : sent_by_non_equivocating IM equivocators s m <->
    sent_by_non_equivocating IM equivocators (lift_sub_state_to IM (elements equivocators) s eqv_is) m.
Proof.
  by split; intros [i [Hi Hsent]]; exists i; split; [done | | done |]
  ; revert Hsent; rewrite lift_sub_state_to_neq.
Qed.

(**
  The property above induces trace-equality for the corresponding
  [equivocators_composition_for_sent] compositions.
*)
Lemma restrict_observed_to_non_equivocating_incl s eqv_is
  : VLSM_incl
    (equivocators_composition_for_sent IM equivocators s)
    (equivocators_composition_for_sent IM equivocators
      (lift_sub_state_to IM (elements equivocators) s eqv_is)).
Proof.
  apply pre_loaded_vlsm_incl.
  by apply lift_sub_state_to_sent_by_non_equivocating_iff.
Qed.

Lemma restrict_observed_to_non_equivocating_incl_rev s eqv_is
  : VLSM_incl
    (equivocators_composition_for_sent IM equivocators
      (lift_sub_state_to IM (elements equivocators) s eqv_is))
    (equivocators_composition_for_sent IM equivocators s).
Proof.
  apply pre_loaded_vlsm_incl.
  by apply lift_sub_state_to_sent_by_non_equivocating_iff.
Qed.

(**
  Replacing the state corresponding to the equivocators does not affect the
  [strong_fixed_equivocation] property.
*)
Lemma lift_sub_state_to_strong_fixed_equivocation s eqv_is m
  : strong_fixed_equivocation IM equivocators s m <->
    strong_fixed_equivocation IM equivocators (lift_sub_state_to IM (elements equivocators) s eqv_is) m.
Proof.
  split; intros [Hs | Hs]; [left | right | left | right]; revert Hs.
  - by apply lift_sub_state_to_sent_by_non_equivocating_iff.
  - apply VLSM_incl_can_emit.
    by apply restrict_observed_to_non_equivocating_incl.
  - by apply lift_sub_state_to_sent_by_non_equivocating_iff.
  - apply VLSM_incl_can_emit.
    by apply restrict_observed_to_non_equivocating_incl_rev.
Qed.

(**
  The operation of replacing the state corresponding to the equivocators
  with a given initial state and removing all transitions belonging to
  non-equivocators in a trace induces a self-[VLSM_projection] on the
  fixed equivocation composition VLSM.
*)
Lemma remove_equivocating_transitions_fixed_projection eqv_is
  (Heqv_is : composite_initial_state_prop (sub_IM IM (elements equivocators)) eqv_is)
  : VLSM_projection StrongFixed StrongFixed
      (remove_equivocating_label_project IM (elements equivocators))
      (remove_equivocating_state_project IM (elements equivocators) eqv_is).
Proof.
  apply basic_VLSM_strong_projection.
  - intros [i liX] lY.
    unfold remove_equivocating_state_project;
    unfold remove_equivocating_label_project; cbn.
    case_decide as Hi; inversion_clear 1.
    intros s om [Hv Hc].
    split.
    + by cbn; rewrite lift_sub_state_to_neq.
    + destruct om as [m |]; [| done].
      by apply lift_sub_state_to_strong_fixed_equivocation.
  - intros [i liX] lY.
    unfold remove_equivocating_state_project;
    unfold remove_equivocating_label_project; cbn.
    case_decide as Hi; inversion_clear 1.
    intros s om s' om';
    rewrite lift_sub_state_to_neq by done;
    destruct (transition _ _ _) as (si', _om');
    inversion_clear 1.
    f_equal; extensionality j.
    by destruct (decide (i = j)); subst; state_update_simpl.
  - intros [i liX].
    unfold remove_equivocating_state_project;
    unfold remove_equivocating_label_project; cbn.
    case_decide as Hi; [| by congruence].
    intros _ s om s' om';
    destruct (transition _ _ _) as (si', _om') eqn: Hti;
    inversion_clear 1.
    extensionality j.
    unfold lift_sub_state_to.
    case_decide; [done |].
    by destruct (decide (i = j)); subst; state_update_simpl.
  - intros s Hs i.
    unfold remove_equivocating_state_project, lift_sub_state_to.
    case_decide as Hi.
    + by apply (Heqv_is (dexist i Hi)).
    + by apply Hs.
  - by intros m HFixed.
Qed.

Context
  (base_s : composite_state IM)
  (Hbase_s : valid_state_prop Fixed base_s)
  (EquivPreloadedBase := equivocators_composition_for_sent IM equivocators base_s)
  .

(**
  As a corollary of the above projection result, the state obtained by replacing
  the equivocator component of a Fixed valid state with initial states is
  still a Fixed valid state.
*)
Lemma fixed_equivocator_lifting_initial_state :
  weak_projection_initial_state_preservation EquivPreloadedBase Fixed
    (lift_sub_state_to IM (elements equivocators) base_s).
Proof.
  intros eqv_is Heqv_is.
  apply (VLSM_incl_valid_state (StrongFixed_incl_Fixed IM equivocators)).
  apply (VLSM_projection_valid_state (remove_equivocating_transitions_fixed_projection _ Heqv_is)).
  by apply (VLSM_incl_valid_state (Fixed_incl_StrongFixed IM equivocators)).
Qed.

Lemma lift_sub_state_to_sent_are_directly_observed s
  : forall m, sent_by_non_equivocating IM equivocators base_s m ->
    composite_has_been_directly_observed IM (lift_sub_state_to IM (elements equivocators) base_s s) m.
Proof.
  intros m Hsent.
  apply (lift_sub_state_to_sent_by_non_equivocating_iff base_s s m) in Hsent.
  by eapply sent_by_non_equivocating_are_directly_observed.
Qed.

Lemma strong_fixed_equivocation_lift_sub_state_to s
  : forall m, strong_fixed_equivocation IM equivocators base_s m ->
    fixed_equivocation IM equivocators (lift_sub_state_to IM (elements equivocators) base_s s) m.
Proof.
  intros.
  apply strong_fixed_equivocation_subsumption.
  by apply lift_sub_state_to_strong_fixed_equivocation.
Qed.

(** *** Main result of the section

  Given a valid state <<s>> for the <<Fixed>> composition (composition of
  nodes where only the <<equivocators>> are allowed to message-equivocate),
  we can "lift" any trace of the free composition of just the equivocators
  pre-loaded with the messages observed in <<s>> to a trace over the <<Fixed>>
  composition by simply setting the non-equivocating state components to those
  of <<s>>.

  This result is important for establishing the connection between limited
  equivocation and fixed equivocation (Lemma [strong_witness_has_fixed_equivocation]).

  We prove this as a [VLSM_weak_embedding] between the free composition of
  equivocators pre-loaded with the messages observed in <<s>> and the <<Fixed>>
  composition of all nodes. Note that this is a strengthening of Lemma
  [PreSubFree_PreFree_weak_embedding].
*)
Lemma EquivPreloadedBase_Fixed_weak_embedding
  (no_initial_messages_for_equivocators :
    forall i m, i ∈ equivocators -> ~ initial_message_prop (IM i) m)
  : VLSM_weak_embedding EquivPreloadedBase Fixed
      (lift_sub_label IM (elements equivocators)) (lift_sub_state_to IM (elements equivocators) base_s).
Proof.
  apply basic_VLSM_weak_embedding.
  - intros l s om Hv HsY HomY. split.
    + destruct Hv as [_ [_ [Hv _]]]; revert Hv; destruct l as (i, li).
      destruct_dec_sig i j Hj Heq; subst i; cbn; unfold sub_IM; cbn.
      by rewrite lift_sub_state_to_eq with (Hi := Hj).
    + destruct om as [m |]; [| done]; cbn.
      destruct Hv as (_ & Hm & _).
      apply emitted_messages_are_valid_iff in Hm.
      destruct Hm as [[Hinit | Hobs] | Hemit].
      * destruct Hinit as [i [[im Him] Heqm]].
        destruct_dec_sig i j Hj Heqi; subst; cbn.
        clear HomY; contradict Him.
        apply no_initial_messages_for_equivocators; cbn.
        by apply elem_of_elements, Hj.
      * by apply strong_fixed_equivocation_lift_sub_state_to; left.
      * by apply strong_fixed_equivocation_lift_sub_state_to; right.
  - intros (sub_i, li) s om s' om'.
    destruct_dec_sig sub_i j Hj Heq; subst;
    unfold input_valid_transition; cbn; unfold sub_IM; cbn;
    rewrite lift_sub_state_to_eq with (Hi := Hj);
    destruct (transition _ _ _) as (si', _om');
    intros [_ Ht]; inversion_clear Ht.
    f_equal; extensionality i.
    destruct (decide (i = j)); subst; state_update_simpl.
    + by rewrite lift_sub_state_to_eq with (Hi := Hj), !state_update_eq.
    + destruct (decide (i ∈ elements equivocators)).
      * rewrite !lift_sub_state_to_eq with (Hi := e), state_update_neq; [done |].
        by intros Hcontra%dsig_eq.
      * by state_update_simpl.
  - by intros s Hweak_proj; apply fixed_equivocator_lifting_initial_state.
  - intros l s m Hv HsY [[(i, Hi) [[im Him] Heqm]] | Hm].
    + apply initial_message_is_valid.
      by exists i, (exist _ im Him).
    + clear HsY. eapply composite_directly_observed_valid; [done |].
      by eapply sent_by_non_equivocating_are_directly_observed.
Qed.

End sec_fixed_equivocator_lifting.

(** ** Fixed equivocation over an empty set

  If the set of nodes allowed to equivocate is empty, intuitively, it follows
  that no message equivocation is allowed, since that would mean that at least
  one node would equivocate.
*)
Section sec_fixed_equivocation_no_equivocators.

Context
  {message : Type}
  `{FinSet index Ci}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  `{forall i : index, HasBeenSentCapability (IM i)}
  `{forall i : index, HasBeenReceivedCapability (IM i)}
  .

Lemma strong_fixed_equivocation_no_equivocators
  : forall s m,
  strong_fixed_equivocation IM (@empty Ci _) s m <-> composite_has_been_sent IM s m.
Proof.
  intros s m.
  split.
  - intros [Hsent | Hemit].
    + by apply sent_by_non_equivocating_are_sent in Hsent.
    + by apply sub_no_indices_no_can_emit in Hemit; [| apply elements_empty].
  - intros Hsent.
    left.
    destruct Hsent as [i Hsent].
    exists i; split; [| done].
    by rewrite elem_of_elements; apply not_elem_of_empty.
Qed.

Lemma strong_fixed_equivocation_constraint_no_equivocators
  : forall l som,
    strong_fixed_equivocation_constraint IM (@empty Ci _) l som <->
    composite_no_equivocations IM l som.
Proof.
  intros.
  destruct som as (s, [m |]); [| done].
  simpl.
  specialize (strong_fixed_equivocation_no_equivocators s m).
  unfold composite_no_equivocations, composite_no_equivocations_except_from, sent_except_from.
  by cbn; itauto.
Qed.

Lemma strong_fixed_equivocation_vlsm_composition_no_equivocators
  : VLSM_eq (strong_fixed_equivocation_vlsm_composition IM (@empty Ci _))
      (composite_vlsm IM (composite_no_equivocations IM)).
Proof.
  split.
  - apply constraint_subsumption_incl.
    apply preloaded_constraint_subsumption_stronger.
    apply strong_constraint_subsumption_strongest.
    intros l som.
    by rewrite strong_fixed_equivocation_constraint_no_equivocators.
  - apply constraint_subsumption_incl.
    apply preloaded_constraint_subsumption_stronger.
    apply strong_constraint_subsumption_strongest.
    intros l som.
    by rewrite strong_fixed_equivocation_constraint_no_equivocators.
Qed.

Lemma fixed_equivocation_vlsm_composition_no_equivocators
  : VLSM_eq (fixed_equivocation_vlsm_composition IM (@empty Ci _))
      (composite_vlsm IM (composite_no_equivocations IM)).
Proof.
  eapply VLSM_eq_trans.
  - by apply Fixed_eq_StrongFixed.
  - by apply strong_fixed_equivocation_vlsm_composition_no_equivocators.
Qed.

End sec_fixed_equivocation_no_equivocators.

Section sec_fixed_non_equivocator_lifting.

Context
  {message : Type}
  `{FinSet index Ci}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  `{forall i, HasBeenSentCapability (IM i)}
  `{forall i, HasBeenReceivedCapability (IM i)}
  (equivocators : Ci)
  (non_equivocators := list_to_set (enum index) ∖ equivocators)
  (Free := free_composite_vlsm IM)
  (Fixed := fixed_equivocation_vlsm_composition IM equivocators)
  (FixedNonEquivocating := pre_induced_sub_projection IM (elements non_equivocators)
                                (fixed_equivocation_constraint IM equivocators))
  (StrongFixed := strong_fixed_equivocation_vlsm_composition IM equivocators)
  (StrongFixedNonEquivocating := pre_induced_sub_projection IM (elements non_equivocators)
                                (strong_fixed_equivocation_constraint IM equivocators))
  (PreFree := pre_loaded_with_all_messages_vlsm Free)
  .

(**
  All valid traces in the induced projection of the composition under the
  strong fixed-equivocation constraint to the non-equivocating nodes can be lifted
  to valid traces of the constrained composition.
*)
Lemma lift_strong_fixed_non_equivocating
  : VLSM_embedding StrongFixedNonEquivocating StrongFixed
    (lift_sub_label IM (elements non_equivocators))
    (lift_sub_state IM (elements non_equivocators)).
Proof.
  apply induced_sub_projection_lift.
  intros s1 s2 Heq l om.
  destruct om as [m |]; [| by itauto].
  cut
    (forall m, sent_by_non_equivocating IM equivocators s1 m ->
      sent_by_non_equivocating IM equivocators s2 m).
  {
    intros Hsent_impl [[j [Hj Hsent]] | Hemit].
    - by left; apply Hsent_impl; exists j.
    - right. revert Hemit.
      by apply VLSM_incl_can_emit, pre_loaded_vlsm_incl.
  }
  clear m.
  intros m [i [Hi Hsent]].
  exists i. split; [done |].
  replace (s2 i) with (s1 i); [done |].
  assert (Hi' : i ∈ elements non_equivocators).
  {
    apply elem_of_elements, elem_of_difference.
    rewrite elem_of_list_to_set.
    split.
    - by apply elem_of_enum.
    - by rewrite <- elem_of_elements.
  }
  by eapply f_equal_dep with (x := dexist i Hi') in Heq.
Qed.

(**
  All valid traces in the induced projection of the composition under the
  fixed-equivocation constraint to the non-equivocating nodes can be lifted
  to valid traces of the constrained composition.
*)
Lemma lift_fixed_non_equivocating
  : VLSM_embedding FixedNonEquivocating Fixed
    (lift_sub_label IM (elements non_equivocators))
    (lift_sub_state IM (elements non_equivocators)).
Proof.
  constructor.
  intros sX trX Htr.
  apply
    (VLSM_incl_finite_valid_trace
      (StrongFixed_incl_Fixed IM equivocators)).
  apply (VLSM_embedding_finite_valid_trace lift_strong_fixed_non_equivocating).
  revert Htr.
  apply VLSM_incl_finite_valid_trace.
  apply induced_sub_projection_constraint_subsumption_incl.
  by apply fixed_strong_equivocation_subsumption.
Qed.

Lemma fixed_non_equivocating_projection_friendliness
  : projection_friendly_prop
      (induced_sub_projection_is_projection IM (elements non_equivocators)
        (fixed_equivocation_constraint IM equivocators)).
Proof.
  apply induced_sub_projection_friendliness.
  by apply lift_fixed_non_equivocating.
Qed.

(**
  The valid traces of the induced projection of the composition under the
  fixed-equivocation constraint to the non-equivocating nodes are precisely
  projections of traces of the constrained composition.
*)
Lemma fixed_non_equivocating_traces_char is tr
  : finite_valid_trace FixedNonEquivocating is tr <->
    exists eis etr,
    finite_valid_trace Fixed eis etr /\
    composite_state_sub_projection IM (elements non_equivocators) eis = is /\
    finite_trace_sub_projection IM (elements non_equivocators) etr = tr.
Proof.
  apply (projection_friendly_trace_char (induced_sub_projection_is_projection _ _ _)).
  by apply fixed_non_equivocating_projection_friendliness.
Qed.

End sec_fixed_non_equivocator_lifting.
