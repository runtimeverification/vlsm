From VLSM.Lib Require Import Itauto.
From stdpp Require Import prelude.
From VLSM.Lib Require Import Preamble ListExtras.
From VLSM.Core Require Import VLSM VLSMProjections Composition ProjectionTraces SubProjectionTraces.
From VLSM.Core Require Import Equivocation EquivocationProjections.
From VLSM.Core Require Import Equivocation.FixedSetEquivocation Equivocation.NoEquivocation.
From VLSM.Core Require Import Equivocators.Equivocators Equivocators.EquivocatorsProjections.
From VLSM.Core Require Import Equivocators.MessageProperties.
From VLSM.Core Require Import Equivocators.EquivocatorsComposition.
From VLSM.Core Require Import Equivocators.EquivocatorsCompositionProjections.
From VLSM.Core Require Import Equivocators.FullReplayTraces.
From VLSM.Core Require Import Equivocators.FixedEquivocation.
From VLSM.Core Require Import Equivocators.SimulatingFree.

(** * Core: VLSM Equivocators Simulating Fixed Set Equivocation Composition

  In this module, we show that the composition of equivocators with no
  message-equivocation and fixed-set state-equivocation can simulate the
  fixed-set message-equivocation composition of regular components.

  The proof is based on [generalized_equivocators_finite_valid_trace_init_to_rev],
  but also reuses [seeded_equivocators_finite_valid_trace_init_to_rev] to
  lift a trace of the free subcomposition of equivocating components generating a
  message (given by the fixed message-equivocation constraint) to a trace of the
  subcomposition of equivocating equivocators with no message-equivocation,
  which is then used to satisfy the [replayable_message_prop]erty.
*)

Section sec_fixed_equivocating.

Context
  {message : Type}
  {index : Type}
  `{FinSet index Ci}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  (Free := free_composite_vlsm IM)
  `{forall i : index, HasBeenSentCapability (IM i)}
  (equivocating : Ci)
  (X : VLSM message := strong_fixed_equivocation_vlsm_composition IM equivocating)
  (XE : VLSM message := equivocators_fixed_equivocations_vlsm IM (elements equivocating))
  (FreeE := free_composite_vlsm (equivocator_IM IM))
  (PreFreeE := pre_loaded_with_all_messages_vlsm FreeE)
  (SubFreeE := free_composite_vlsm (sub_IM (equivocator_IM IM) (elements equivocating)))
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  .

Lemma no_initial_messages_in_sub_IM
  : forall i m, ~ initial_message_prop (sub_IM IM (elements equivocating) i) m.
Proof.
  intros [i Hi] m Hinit.
  by apply (no_initial_messages_in_IM i m).
Qed.

(**
  Messages [sent_by_non_equivocating] components in the projection of a valid
  state for the fixed-set state-equivocation composition of equivocators with no
  message-equivocation are valid for that composition of equivocators.
*)
Lemma fixed_equivocating_messages_sent_by_non_equivocating_are_valid
  eqv_state_s
  (Heqv_state_s : valid_state_prop XE eqv_state_s)
  (s := equivocators_total_state_project IM eqv_state_s)
  (Hs : valid_state_prop X s)
  m
  (Hm : sent_by_non_equivocating IM equivocating s m)
  : valid_message_prop XE m.
Proof.
  pose proof (HinclE :=
    equivocators_fixed_equivocations_vlsm_incl_PreFree IM (elements equivocating)).
  apply sent_by_non_equivocating_are_sent in Hm.
  eapply VLSM_incl_valid_state in Hs; [| by apply constrained_preloaded_incl].
  eapply sent_valid; [done |].
  revert Hm; apply (VLSM_incl_valid_state HinclE) in Heqv_state_s.
  by specialize
    (VLSM_projection_has_been_sent_reflect
      (preloaded_equivocators_no_equivocations_vlsm_X_vlsm_projection IM)
      _ Heqv_state_s m).
Qed.

(**
  This is the constraint counterpart of the [weak_embedding_valid_preservation]
  property (for the [equivocators_fixed_equivocations_constraint]).
*)
Lemma fixed_equivocating_non_equivocating_constraint_lifting
  eqv_state_s
  (Heqv_state_s : valid_state_prop XE eqv_state_s)
  l s om
  (Hv :
    input_valid
      (seeded_equivocators_no_equivocation_vlsm IM (elements equivocating)
        (sent_by_non_equivocating IM equivocating (equivocators_total_state_project IM eqv_state_s)))
        l (s, om))
  (Hlift_s : valid_state_prop XE (lift_equivocators_sub_state_to IM (elements equivocating) eqv_state_s s))
  : equivocators_fixed_equivocations_constraint IM (elements equivocating)
        (lift_equivocators_sub_label_to IM (elements equivocating) eqv_state_s l)
        (lift_equivocators_sub_state_to IM (elements equivocating) eqv_state_s s, om).
Proof.
  specialize (equivocators_fixed_equivocations_vlsm_incl_PreFree IM (elements equivocating))
    as HinclE.
  destruct Hv as [Hs [Hom [_ Hc]]].
  apply valid_state_has_fixed_equivocation in Hlift_s.
  split.
  - split; [| done].
    destruct om as [m |]; [| done].
    left.
    apply proj1 in Hc as [Hsent | Hseed].
    + revert Hsent. simpl.
      apply (VLSM_incl_valid_state HinclE) in Heqv_state_s.
      apply (VLSM_incl_valid_state (seeded_no_equivocation_incl_preloaded IM (elements equivocating) _)) in Hs.
      by specialize
        (VLSM_weak_embedding_has_been_sent
          (PreFreeSubE_PreFreeE_weak_embedding IM _ _ Heqv_state_s)
          _ Hs m).
    + destruct Hseed as [i [Hi Hsent]].
      simpl.
      exists i.
      unfold lift_equivocators_sub_state_to.
      case_decide; [done |].
      unfold equivocator_IM.
      change (equivocators_total_state_project _ _ _)
        with (equivocator_state_zero (eqv_state_s i)) in Hsent.
      revert Hsent.
      apply
        (VLSM_projection_has_been_sent_reflect
          (preloaded_equivocator_zero_projection (IM i))).
      apply (VLSM_incl_valid_state HinclE) in Heqv_state_s.
      revert Heqv_state_s.
      by apply (VLSM_projection_valid_state (preloaded_component_projection (equivocator_IM IM) i)).
  - destruct (composite_transition _ _ _) as (s', om') eqn: Ht'.
    apply
      (equivocating_transition_preserves_fixed_equivocation
        IM (elements equivocating) _ _ _ _ _ Ht' Hlift_s).
    destruct l as (sub_i, li).
    destruct_dec_sig sub_i i Hi Hsub_i.
    by subst.
Qed.

(**
  A message that can be generated from a state <<s>> of the free composition
  of equivocating equivocators pre-loaded with all messages has the
  [composite_has_been_sent] property for the state obtained upon "appending"
  state <<s>> to valid state for the composition of all equivocators.

  This result plays an important role in satisfying the no-message equivocation
  constraint.
*)
Lemma fixed_equivocation_replay_has_message
  eqv_state_s
  (Heqv_state_s : valid_state_prop PreFreeE eqv_state_s)
  im s
  (Him :
    can_produce
    (pre_loaded_with_all_messages_vlsm
      (free_composite_vlsm (equivocator_IM (sub_IM IM (elements equivocating)))))
    s im)
  : composite_has_been_sent (equivocator_IM IM)
      (lift_equivocators_sub_state_to IM (elements equivocating) eqv_state_s s) im.
Proof.
  apply non_empty_valid_trace_from_can_produce in Him
     as (im_eis & im_etr & item & Him_etr & Hlast & Heqs & Him).
  specialize
    (PreFreeSubE_PreFreeE_weak_embedding IM (elements equivocating) _ Heqv_state_s)
    as Hproj.
  apply valid_trace_add_default_last in Him_etr.
  apply valid_trace_last_pstate in Him_etr as Him_etr_lst.
  specialize
    (VLSM_weak_embedding_has_been_sent Hproj _ Him_etr_lst im) as Hsent.
  unfold has_been_sent in Hsent. simpl in Hsent.
  replace s with (finite_trace_last im_eis im_etr).
  - apply Hsent.
    specialize (has_been_sent_examine_one_trace _ _ _ Him_etr im)
      as Hrew.
    unfold has_been_sent in Hrew; cbn; apply Hrew.
    apply Exists_exists. exists item. split; [| done].
    apply elem_of_list_lookup.
    rewrite StdppExtras.last_last_error in Hlast.
    replace (Some _) with (last im_etr).
    exists (pred (length im_etr)).
    by rewrite list.last_lookup.
  - apply last_error_destination_last.
    by rewrite Hlast; simpl; f_equal.
Qed.

(**
  Messages satisfying the [strong_fixed_equivocation_constraint] have the
  [replayable_message_prop]erty for the [equivocators_fixed_equivocations_constraint].
*)
Lemma fixed_equivocation_has_replayable_message_prop
  : replayable_message_prop IM (fun _ : message => False)
    (strong_fixed_equivocation_constraint IM equivocating)
    (equivocators_fixed_equivocations_constraint IM (elements equivocating)).
Proof.
  specialize (vlsm_is_pre_loaded_with_False XE) as HeqXE.
  specialize (vlsm_is_pre_loaded_with_False X) as HeqX.
  specialize (equivocators_fixed_equivocations_vlsm_incl_PreFree IM (elements equivocating)) as HinclE.
  intro; intros.
  destruct iom as [im |]; swap 1 2; [| destruct HcX as [Hsent | Hemitted]].
  - exists [], eqv_state_s.
    by split; [constructor | eauto].
  - exists []. exists eqv_state_s.
    split; [by constructor |].
    split; [done |].
    split; [done |].
    apply sent_by_non_equivocating_are_sent in Hsent.
    apply (VLSM_eq_valid_state HeqXE) in Hstate_valid.
    apply (VLSM_incl_valid_state HinclE) in Hstate_valid.
    left.
    revert Hsent. subst.
    by specialize
      (VLSM_projection_has_been_sent_reflect
        (preloaded_equivocators_no_equivocations_vlsm_X_vlsm_projection IM)
        eqv_state_s Hstate_valid im) as Hsent.
  - (*
      If <<im>> can be emitted by the free composition of equivocating components
      seeded with the messages [sent_by_non_equivocating] in <<s>>, then we can
      use Lemma [seeded_equivocators_finite_valid_trace_init_to_rev] to
      simulate that trace in the equivocator-composition of equivocating
      components with no-messages equivocation.
    *)
    apply can_emit_has_trace in Hemitted
        as [im_is [im_tr [im_item [Him_tr Him_item]]]].
    apply valid_trace_add_default_last in Him_tr.
    rewrite finite_trace_last_is_last in Him_tr.
    apply
      (seeded_equivocators_finite_valid_trace_init_to_rev
        (sub_IM IM (elements equivocating)) _ no_initial_messages_in_sub_IM)
      in Him_tr
      as (im_eis & Him_eis & im_es & Him_es & im_etr & Him_etr_pr & Him_etr & Him_output).
    rewrite finite_trace_last_output_is_last in Him_output.
    rewrite Him_item in Him_output.
    (*
      We will use Lemma
      [sub_preloaded_replayed_trace_from_valid_equivocating] to replay
      the trace obtained above on top of the given state, thus ensuring that
      state-equivocation is only introduced for the equivocating components.
      We will used Lemmas [fixed_equivocating_messages_sent_by_non_equivocating_are_valid]
      and [fixed_equivocating_non_equivocating_constraint_lifting] to satisfy
      the hypotheses of the replay lemma.
    *)
    pose proof (Hreplay :=
      (sub_preloaded_replayed_trace_from_valid_equivocating
        IM (sent_by_non_equivocating IM equivocating s)
        (elements equivocating)
        (equivocators_fixed_equivocations_constraint IM (elements equivocating))
        (fun m => False))).
    spec Hreplay.
    { clear -HeqXE. intros i ns s Hi Hs.
      split; [by split |].
      apply (VLSM_eq_valid_state HeqXE) in Hs.
      apply valid_state_has_fixed_equivocation in Hs.
      destruct (composite_transition _ _ _) as (s', om') eqn: Ht.
      by apply
        (equivocating_transition_preserves_fixed_equivocation
          IM (elements equivocating) _ _ _ _ _ Ht Hs).
    }
    spec Hreplay.
    {
      subst s.
      apply valid_trace_last_pstate in HtrX.
      apply (VLSM_eq_valid_state HeqXE) in Hstate_valid.
      apply (VLSM_eq_valid_state HeqX) in HtrX.
      intros m Hsent.
      apply (VLSM_incl_valid_message (proj1 HeqXE)); [by left |].
      by apply (fixed_equivocating_messages_sent_by_non_equivocating_are_valid eqv_state_s).
    }
    specialize (Hreplay eqv_state_s).
    spec Hreplay.
    { by apply (VLSM_eq_valid_state HeqXE), (VLSM_eq_valid_state HeqXE). }
    spec Hreplay.
    { subst s.
      clear -HeqXE Hstate_valid.
      intros l s om Hv Hlift_s.
      apply (VLSM_eq_valid_state HeqXE) in Hstate_valid.
      apply (VLSM_eq_valid_state HeqXE) in Hlift_s.
      by apply fixed_equivocating_non_equivocating_constraint_lifting.
    }
    apply valid_trace_get_last in Him_etr as Him_etr_lst.
    apply valid_trace_forget_last in Him_etr.
    specialize (Hreplay _ _ Him_etr).
    apply valid_trace_add_default_last in Hreplay.
    eexists _, _; split; [done |].
    (*
      Having verified the validity part of the conclusion, now we only
      need to show two projection properties, and the no message-equivocation
      constraint for which we employ Lemma [fixed_equivocation_replay_has_message].
    *)
    repeat split.
    + by apply
      (equivocators_total_trace_project_replayed_trace_from
        IM (elements equivocating) eqv_state_s im_eis im_etr).
    + subst s.
      by apply
        (equivocators_total_state_project_replayed_trace_from
          IM (elements equivocating) eqv_state_s im_eis im_etr).
    + apply (VLSM_eq_valid_state HeqXE) in Hstate_valid.
      apply (VLSM_incl_valid_state HinclE) in Hstate_valid as Hstate_pre.
      specialize (NoEquivocation.seeded_no_equivocation_incl_preloaded
        (equivocator_IM (sub_IM IM (elements equivocating)))
        (free_constraint _)
          (sent_by_non_equivocating IM equivocating s))
        as Hsub_incl.
      apply (VLSM_incl_finite_valid_trace Hsub_incl) in Him_etr.
      left.
      specialize (replayed_trace_from_finite_trace_last IM (elements equivocating) eqv_state_s
        im_eis im_etr (proj2 Him_etr)).
      simpl. intro Hrew. rewrite Hrew. clear Hrew.
      apply fixed_equivocation_replay_has_message; [done |].
      clear -Him_etr Him_output.
      destruct_list_last im_etr im_ert' item Heqim_etr; [by inversion Him_output |].
      apply proj1 in Him_etr.
      replace (im_ert' ++ [item]) with (im_ert' ++ [item] ++ []) in Him_etr
        by (rewrite app_assoc; apply app_nil_r).
      specialize (input_valid_transition_to (pre_loaded_with_all_messages_vlsm
        (free_composite_vlsm (equivocator_IM (sub_IM IM (elements equivocating)))))
        _ _ _ _ _ Him_etr eq_refl)
        as Ht.
      rewrite finite_trace_last_is_last.
      rewrite finite_trace_last_output_is_last in Him_output.
      replace (output _) with (Some im) in Ht.
      by eexists _, _.
Qed.

(** ** The main result

  The main result, showing that fixed-set message-equivocation traces can be
  simulated by fixed-set state-equivocation traces is obtained by instantiating
  Lemma [generalized_equivocators_finite_valid_trace_init_to_rev], discharging
  the most complex assumption of the lemma (about [replayable_message_prop])
  with Lemma [fixed_equivocation_has_replayable_message_prop].
*)
Lemma fixed_equivocators_finite_valid_trace_init_to_rev
  isX sX trX
  (HtrX : finite_valid_trace_init_to X isX sX trX)
  : exists is s tr,
      equivocators_total_state_project IM is = isX /\
      equivocators_total_state_project IM s = sX /\
      equivocators_total_trace_project IM tr = trX /\
      finite_valid_trace_init_to XE is s tr /\
      finite_trace_last_output trX = finite_trace_last_output tr.
Proof.
  (*
    Since the base result works with pre-loaded vlsms, some massaging of the
    hypothesis and conclusion is done to fit the applied lemma.
  *)
  assert (no_initial_messages_in_XE :
    forall m, ~ initial_message_prop (pre_loaded_vlsm XE (fun _ => False)) m).
  { intros m [[i [[mi Hmi] Him]] | Hseeded]; [| done].
    by elim (no_initial_messages_in_IM i mi).
  }
  specialize (vlsm_is_pre_loaded_with_False X) as HeqX.
  specialize (vlsm_is_pre_loaded_with_False XE) as HeqXE.
  apply (VLSM_eq_finite_valid_trace_init_to HeqX) in HtrX.
  apply
    (generalized_equivocators_finite_valid_trace_init_to_rev
      IM _ _ (equivocators_fixed_equivocations_constraint IM (elements equivocating)))
    in HtrX
    as (is & His & s & Hs & tr & Htr & Hptr & Houtput).
  - exists is, s, tr; split_and!; try itauto.
    by apply (VLSM_eq_finite_valid_trace_init_to HeqXE).
  - intro; intros.
    apply (VLSM_eq_valid_state HeqXE) in Hes.
    split.
    + split; [| done].  destruct om as [im |]; [| done].
      destruct Hom as [Hom | Hinitial]; [by left | exfalso].
      by apply no_initial_messages_in_XE in Hinitial.
    + apply valid_state_has_fixed_equivocation in Hes.
      destruct (composite_transition _ _ _) as (es', om') eqn: Het.
      simpl.
      by apply
        (zero_descriptor_transition_preserves_fixed_equivocation
          IM (elements equivocating) _ _ _ _ _ Het Hes li).
  - by apply fixed_equivocation_has_replayable_message_prop.
Qed.

End sec_fixed_equivocating.

(** ** No-equivocation simulation as a particular case of fixed set simulation

  In this section we show that traces of the composition of components with no
  message equivocation can be simulated by the composition of equivocators with
  no message equivocation in which no component is allowed to state-equivocate.
*)

Section sec_no_equivocation.

Context
  {message : Type}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  (Free := free_composite_vlsm IM)
  `{forall i : index, HasBeenSentCapability (IM i)}
  (X : VLSM message := composite_vlsm IM (composite_no_equivocations IM))
  (XE : VLSM message := equivocators_fixed_equivocations_vlsm IM [])
  (FreeE := free_composite_vlsm (equivocator_IM IM))
  (PreFreeE := pre_loaded_with_all_messages_vlsm FreeE)
  .

Lemma no_equivocating_equivocators_finite_valid_trace_init_to_rev
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  isX sX trX
  (HtrX : finite_valid_trace_init_to X isX sX trX)
  : exists is, equivocators_total_state_project IM is = isX /\
    exists s, equivocators_total_state_project IM s = sX /\
    exists tr, equivocators_total_trace_project IM tr = trX /\
    finite_valid_trace_init_to XE is s tr /\
    finite_trace_last_output trX = finite_trace_last_output tr.
Proof.
  assert (no_initial_messages_in_XE :
    forall m, ~ initial_message_prop (pre_loaded_vlsm XE (fun _ => False)) m).
  {
    intros m [[i [[mi Hmi] Him]] | Hseeded]; [| done].
    by elim (no_initial_messages_in_IM i mi).
  }
  specialize (vlsm_is_pre_loaded_with_False X) as HeqX.
  specialize (vlsm_is_pre_loaded_with_False XE) as HeqXE.
  apply (VLSM_eq_finite_valid_trace_init_to HeqX) in HtrX.
  apply
    (generalized_equivocators_finite_valid_trace_init_to_rev
      IM _ _ (equivocators_fixed_equivocations_constraint IM []))
    in HtrX
    as [is [His [s [Hs [tr [Htr [Hptr Houtput]]]]]]].
  - exists is. split; [done |].
    exists s. split; [done |].
    exists tr. split; [done |].
    split; [| done].
    by apply (VLSM_eq_finite_valid_trace_init_to HeqXE).
  - intro; intros.
    apply (VLSM_eq_valid_state HeqXE) in Hes.
    split.
    + split; [| done]. destruct om as [im |]; [| done].
      destruct Hom as [Hom | Hinitial]; [by left | exfalso].
      by apply no_initial_messages_in_XE in Hinitial.
    + apply valid_state_has_fixed_equivocation in Hes.
      destruct (composite_transition _ _ _) as (es', om') eqn: Het.
      simpl.
      by apply
        (zero_descriptor_transition_preserves_fixed_equivocation
          IM [] _ _ _ _ _ Het Hes li).
  - clear isX sX trX HtrX. intro; intros.
    specialize (equivocators_fixed_equivocations_vlsm_incl_PreFree IM []) as HinclE.
    destruct iom as [im |]; [| by exists [], eqv_state_s; split; constructor].
    destruct HcX as [Hsent | Hemitted]; [| done].
    exists []. exists eqv_state_s.
    split; [by constructor |].
    split; [done |].
    split; [done |].
    apply (VLSM_eq_valid_state HeqXE) in Hstate_valid.
    apply (VLSM_incl_valid_state HinclE) in Hstate_valid.
    left.
    revert Hsent. subst.
    by specialize
      (VLSM_projection_has_been_sent_reflect
        (preloaded_equivocators_no_equivocations_vlsm_X_vlsm_projection IM)
        eqv_state_s Hstate_valid im) as Hsent.
Qed.

End sec_no_equivocation.
