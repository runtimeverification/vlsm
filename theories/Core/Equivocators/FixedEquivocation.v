From VLSM.Lib Require Import Itauto.
From stdpp Require Import prelude finite.
From VLSM.Lib Require Import Preamble ListExtras StdppListSet.
From VLSM.Core Require Import VLSM VLSMProjections Composition Equivocation.
From VLSM.Core Require Import Equivocation.NoEquivocation Equivocation.FullNode.
From VLSM.Core Require Import Equivocation.FixedSetEquivocation.
From VLSM.Core Require Import SubProjectionTraces ProjectionTraces.
From VLSM.Core Require Import Equivocators.Equivocators Equivocators.EquivocatorsProjections.
From VLSM.Core Require Import Equivocators.MessageProperties.
From VLSM.Core Require Import Equivocators.EquivocatorsComposition.
From VLSM.Core Require Import Equivocators.EquivocatorsCompositionProjections.

(** * Core: VLSM Equivocators Fixed Equivocation *)

Section sec_equivocators_fixed_equivocations_vlsm.

Context
  {message : Type}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  `{forall i : index, HasBeenSentCapability (IM i)}
  (equivocator_IM := equivocator_IM IM)
  (equivocating : set index)
  .

(** Definition of fixed-equivocation for states of the composition of equivocators. *)
Definition state_has_fixed_equivocation
  (s : composite_state equivocator_IM)
  : Prop
  :=
  equivocating_indices IM (enum index) s ⊆ equivocating.

Definition equivocators_fixed_equivocations_constraint
  (l : composite_label equivocator_IM)
  (som : composite_state equivocator_IM * option message)
  (som' := composite_transition equivocator_IM l som)
  : Prop
  := equivocators_no_equivocations_constraint IM l som
  /\ state_has_fixed_equivocation (fst som').

(**
  If the starting [state_has_fixed_equivocation] and the transition is made
  on an equivocating index, then the resulting [state_has_fixed_equivocation].
*)
Lemma equivocating_transition_preserves_fixed_equivocation l s om s' om'
  (Ht : composite_transition equivocator_IM l (s, om) = (s', om'))
  (Hs : state_has_fixed_equivocation s)
  (Heqv : projT1 l ∈ equivocating)
  : state_has_fixed_equivocation s'.
Proof.
  intros i Hi.
  destruct (decide (i = projT1 l)); subst; [done |].
  destruct l; cbn in *.
  destruct (equivocator_transition _ _ _).
  inversion Ht; subst.
  apply elem_of_list_filter, proj1 in Hi.
  state_update_simpl.
  by apply Hs, elem_of_list_filter; split; [| apply elem_of_enum].
Qed.

(**
  If the starting [state_has_fixed_equivocation] and the transition is made
  on the original copy, then the resulting [state_has_fixed_equivocation].
*)
Lemma zero_descriptor_transition_preserves_fixed_equivocation l s om s' om'
  (Ht : composite_transition equivocator_IM l (s, om) = (s', om'))
  (Hs : state_has_fixed_equivocation s)
  li
  (Hzero : projT2 l = ContinueWith 0 li)
  : state_has_fixed_equivocation s'.
Proof.
  intros i Hi. apply Hs.
  apply elem_of_list_filter, proj1 in Hi.
  apply elem_of_list_filter.
  split; [| by apply elem_of_enum].
  cbn in Ht.
  destruct l as (eqv, leqv).
  destruct (equivocator_transition _ _ _) as (si', _om') eqn: Hti.
  inversion Ht. subst. clear Ht.
  destruct (decide (i = eqv)); subst; state_update_simpl; [| done].
  by apply (zero_descriptor_transition_reflects_equivocating_state (IM eqv) _ _ _ _ _ Hti _ Hzero Hi).
Qed.

(** If a future state has fixed equivocation, then so must the current state. *)
Lemma in_futures_reflects_fixed_equivocation
  (s1 s2 : composite_state equivocator_IM)
  (Hfutures :
    in_futures (pre_loaded_with_all_messages_vlsm (free_composite_vlsm equivocator_IM)) s1 s2)
  : state_has_fixed_equivocation s2 -> state_has_fixed_equivocation s1.
Proof.
  destruct Hfutures as [tr Htr].
  induction Htr; [done |].
  intros Hf. specialize (IHHtr Hf). revert IHHtr.
  apply transitivity.
  destruct Ht as [_ Ht].
  revert Ht.
  by rapply @equivocators_transition_preserves_equivocating_indices.
Qed.

(**
  Composition of equivocators with no message equivocation and a
  fixed set of machines allowed to state-equivocate.
*)
Definition equivocators_fixed_equivocations_vlsm
  : VLSM message
  :=
  composite_vlsm equivocator_IM equivocators_fixed_equivocations_constraint.

Lemma not_equivocating_index_has_singleton_state
  (s : composite_state equivocator_IM)
  (Hs : valid_state_prop equivocators_fixed_equivocations_vlsm s)
  (i : index)
  (Hi : i ∉ equivocating)
  : is_singleton_state (IM i) (s i).
Proof.
  apply valid_state_has_trace in Hs as (is & tr & Htr & His).
  assert (is_singleton_state (IM i) (is i)) by apply His; clear His.
  induction Htr; [done |].
  apply IHHtr; clear IHHtr.
  destruct Ht as [(_ & _ & _ & _ & Hfixed) Ht].
  cbn in *; rewrite Ht in Hfixed; clear Ht; cbn in *.
  destruct (decide (equivocator_state_n (s i) = 1)); [done |].
  elim Hi. apply Hfixed.
  by apply elem_of_list_filter; split; [| apply elem_of_enum].
Qed.

Lemma valid_state_has_fixed_equivocation
  (s : composite_state equivocator_IM)
  (Hs : valid_state_prop equivocators_fixed_equivocations_vlsm s)
  : state_has_fixed_equivocation s.
Proof.
  apply valid_state_has_trace in Hs.
  destruct Hs as [is [tr [Htr Hinit]]].
  assert (state_has_fixed_equivocation is) as His. {
    intros i Hin.
    apply elem_of_list_filter in Hin.
    destruct Hin as [His Hin].
    unfold is_equivocating_state in His.
    contradict His.
    by apply Hinit.
  }
  clear Hinit.
  induction Htr; [done |].
  apply IHHtr; clear IHHtr.
  destruct Ht as [(_ & _ & _ & _ & Hv) Ht].
  by setoid_rewrite Ht in Hv.
Qed.

(** Inclusion in the free composition. *)
Lemma equivocators_fixed_equivocations_vlsm_incl_free
  : VLSM_incl equivocators_fixed_equivocations_vlsm (free_composite_vlsm equivocator_IM).
Proof.
  by apply VLSM_incl_constrained_vlsm.
Qed.

(** Inclusion into the preloaded free composition. *)
Lemma equivocators_fixed_equivocations_vlsm_incl_PreFree :
  VLSM_incl equivocators_fixed_equivocations_vlsm
    (pre_loaded_with_all_messages_vlsm (free_composite_vlsm equivocator_IM)).
Proof.
  by apply constrained_preloaded_incl.
Qed.

(** Inclusion of preloaded machine into the preloaded free composition. *)
Lemma preloaded_equivocators_fixed_equivocations_vlsm_incl_free :
  VLSM_incl
    (pre_loaded_with_all_messages_vlsm equivocators_fixed_equivocations_vlsm)
    (pre_loaded_with_all_messages_vlsm (free_composite_vlsm equivocator_IM)).
Proof.
  by apply basic_VLSM_incl_preloaded; [intro | inversion 1 | intro].
Qed.

(**
  Inclusion in the composition of equivocators with no message equivocation
  (no restriction on state equivocation).
*)
Lemma equivocators_fixed_equivocations_vlsm_incl_no_equivocations
  : VLSM_incl equivocators_fixed_equivocations_vlsm (equivocators_no_equivocations_vlsm IM).
Proof.
  apply constraint_subsumption_incl.
  by intros l [s om] Hv; apply Hv.
Qed.

End sec_equivocators_fixed_equivocations_vlsm.

Lemma equivocators_fixed_equivocations_vlsm_subset_incl
  {message : Type}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  `{forall i : index, HasBeenSentCapability (IM i)}
  (equivocator_IM := equivocator_IM IM)
  (equivocating1 equivocating2 : set index)
  (Hincl : equivocating1 ⊆ equivocating2) :
  VLSM_incl
    (equivocators_fixed_equivocations_vlsm IM equivocating1)
    (equivocators_fixed_equivocations_vlsm IM equivocating2).
Proof.
  apply constraint_subsumption_incl.
  apply preloaded_constraint_subsumption_stronger,
    strong_constraint_subsumption_strongest.
  intros l (_s, om) [Hmsg Hfixed].
  split; [done |].
  unfold state_has_fixed_equivocation.
  by set_solver.
Qed.

Section sec_fixed_equivocation_with_fullnode.

(**
  This section instantiates the [full_node_condition_for_admissible_equivocators]
  by choosing the admissible indices to be the fixed set of components allowed to
  equivocate, and then shows that this constraint is stronger than the
  [fixed_equivocation_constraint].

  Context setting the stage for, and instantiating the
  [full_node_condition_for_admissible_equivocators].
  It requires that the components have [has_been_sent] and [has_been_received]
  capabilities, that the number of components is finite.

  Additionally to the above we require that equality on messages is decidable
  and that the set of VLSMs allowed to equivocate is non-empty.
*)
Context
  `{EqDecision message}
  `{FinSet index Ci}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  `{forall i : index, HasBeenSentCapability (IM i)}
  `{forall i : index, HasBeenReceivedCapability (IM i)}
  (equivocating : Ci)
  .

(** The [full_node_constraint_alt] is stronger than the [fixed_equivocation_constraint]. *)
Lemma fixed_equivocation_constraint_subsumption_alt :
  strong_constraint_subsumption (free_composite_vlsm IM)
    (full_node_condition_for_admissible_equivocators_alt IM (fun _ i => i ∈ equivocating))
    (fixed_equivocation_constraint IM equivocating).
Proof.
  intros l (s, [m |]) Hc ; [| done].
  destruct Hc as [Hno_equiv | [i [Hi Hm]]]; [by left |].
  unfold node_generated_without_further_equivocation_alt in Hm.
  right.
  apply elem_of_elements in Hi.
  eapply can_emit_composite_free_lift with (j := dexist i Hi); [| done].
  by eauto.
Qed.

(**
  If all components have the [cannot_resend_message_stepwise_prop]erty, then the
  full node condition is stronger than the [fixed_equivocation_constraint]
  (by reduction to the result above).
*)
Lemma fixed_equivocation_constraint_subsumption
  (Hno_resend : forall i : index, cannot_resend_message_stepwise_prop (IM i))
  : preloaded_constraint_subsumption (free_composite_vlsm IM)
      (full_node_condition_for_admissible_equivocators IM (fun _ i => i ∈ equivocating))
      (fixed_equivocation_constraint IM equivocating).
Proof.
  intros l (s, om) Hv.
  apply fixed_equivocation_constraint_subsumption_alt.
  by eapply full_node_condition_for_admissible_equivocators_subsumption.
Qed.

End sec_fixed_equivocation_with_fullnode.

Section sec_from_equivocators_to_components.

(** ** From composition of equivocators to composition of simple components

  In this section we show that the projection of [valid_trace]s of a
  composition of equivocators with a fixed equivocation constraint are
  [valid_trace]s for the composition with a similar fixed equivocation
  constraint.
*)

Context
  `{EqDecision message}
  {index : Type}
  `{FinSet index Ci}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  `{forall i : index, HasBeenSentCapability (IM i)}
  `{forall i : index, HasBeenReceivedCapability (IM i)}
  (equivocating : Ci)
  (XE : VLSM message := equivocators_fixed_equivocations_vlsm IM (elements equivocating))
  (X : VLSM message := fixed_equivocation_vlsm_composition IM equivocating)
  (FreeE : VLSM message := free_composite_vlsm (equivocator_IM IM))
  (Hdec_init : forall i, decidable_initial_messages_prop (IM i))
  (Free := free_composite_vlsm IM)
  .

(**
  [proper_equivocator_descriptors] strengthen for fixed-equivocation.
  We require that if the index is not equivocating, than the corresponding
  descriptor is a [zero_descriptor].
*)
Definition proper_fixed_equivocator_descriptors
  (eqv_descriptors : equivocator_descriptors IM)
  (s : state (free_composite_vlsm (equivocator_IM IM)))
  : Prop
  := proper_equivocator_descriptors IM eqv_descriptors s /\
    forall i, i ∉ equivocating -> eqv_descriptors i = Existing 0.

(**
  [not_equivocating_equivocator_descriptors] satisfy the
  [proper_fixed_equivocator_descriptors] property.
*)
Lemma not_equivocating_equivocator_descriptors_proper_fixed
  (s : composite_state (equivocator_IM IM))
  (Hs : valid_state_prop XE s)
  (eqv_descriptors : equivocator_descriptors IM)
  (Heqv_descriptors : not_equivocating_equivocator_descriptors IM eqv_descriptors s)
  : proper_fixed_equivocator_descriptors eqv_descriptors s.
Proof.
  apply not_equivocating_equivocator_descriptors_proper in Heqv_descriptors as Hproper.
  split; [done |].
  intros i Hi; rewrite <- elem_of_elements in Hi.
  pose proof (Hzero := not_equivocating_index_has_singleton_state
    IM (elements equivocating) _ Hs _ Hi); unfold is_singleton_state in Hzero.
  specialize (Heqv_descriptors i); destruct (eqv_descriptors i); [done |].
  destruct Heqv_descriptors as [s_i_n Heqv_descriptors].
  apply equivocator_state_project_Some_rev in Heqv_descriptors.
  by f_equal; lia.
Qed.

(**
  Projections of (valid) traces of the composition of equivocators preserve
  [proper_fixed_equivocator_descriptors].
*)
Lemma equivocators_trace_project_preserves_proper_fixed_equivocator_descriptors
  (is : composite_state (equivocator_IM IM))
  (tr : list (composite_transition_item (equivocator_IM IM)))
  (Htr : finite_valid_trace_from (pre_loaded_with_all_messages_vlsm FreeE) is tr)
  (s := finite_trace_last is tr)
  (descriptors : equivocator_descriptors IM)
  (idescriptors : equivocator_descriptors IM)
  (trX : list (composite_transition_item IM))
  (HtrX : equivocators_trace_project IM descriptors tr = Some (trX, idescriptors))
  : proper_fixed_equivocator_descriptors descriptors s ->
      proper_fixed_equivocator_descriptors idescriptors is.
Proof.
  intros [Hproper Hfixed].
  specialize
    (preloaded_equivocators_valid_trace_project_proper_initial IM
      _ _ Htr _ _ _ HtrX Hproper)
    as Hiproper.
  split; [done |].
  intros i Hi. specialize (Hfixed i Hi).
  revert Hfixed. clear Hi. revert i.
  by eapply equivocators_trace_project_preserves_zero_descriptors.
Qed.

Lemma fixed_equivocators_initial_state_project
  (es : state XE)
  (Hes : initial_state_prop XE es)
  (eqv_descriptors : equivocator_descriptors IM)
  (Heqv : proper_equivocator_descriptors IM eqv_descriptors es)
  : initial_state_prop X (equivocators_state_project IM eqv_descriptors es).
Proof.
  intro eqv. specialize (Hes eqv).
  unfold equivocator_IM in Hes.
  unfold equivocators_state_project.
  specialize (Heqv eqv).
  destruct (eqv_descriptors eqv) as [sn | i]; [done |].
  destruct Heqv as [esi Heqsi].
  simpl. rewrite Heqsi.
  by eapply equivocator_vlsm_initial_state_preservation_rev.
Qed.

(**
  This is a property of the [fixed_equivocation_constraint] which also
  trivially holds for the free constraint.  This property is sufficient for
  proving the [_equivocators_valid_trace_project] lemma,
  which lets that lemma be used for both the composition of equivocators with
  fixed state-equivocation and the free composition.

  It basically says that if a message has_been_sent for a state of the
  composition of equivocators with no-message equivocations and fixed
  state-equivocations, then any of its projections should be allowed to receive it.
*)
Definition constraint_has_been_sent_prop
  (constraint : composite_label IM -> composite_state IM * option message -> Prop)
  : Prop :=
  forall
    (s : composite_state (equivocator_IM IM))
    (Hs : valid_state_prop XE s)
    (descriptors : equivocator_descriptors IM)
    (Hdescriptors : proper_fixed_equivocator_descriptors descriptors s)
    (sX := equivocators_state_project IM descriptors s)
    (m : message)
    (Hm : has_been_sent FreeE s m)
    l,
  constraint l (sX, Some m).

(**
  Generic proof that the projection of a trace of the composition of equivocators
  with no message equivocation and fixed state equivocation is valid w.r.t.
  the composition of the regular components constrained by any constraint satisfying
  several properties, including the [constraint_has_been_sent_prop]erty.

  The proof proceeds by well founded induction on the length of the trace,
  performing an analysis on the final transition item of the trace.

  It uses the fact that the trace has no message equivocation to extract a
  subtrace producing the message being received at the last transition and
  proves that it's a valid message for the destination machine by using
  the induction hypothesis (that is why well-founded induction is used rather
  than a simpler induction principle).

  The constraint satisfaction for the projection of the final transition is
  for now assumes as hypothesis <<Hconstraint_hbs>>.
*)
Lemma _equivocators_valid_trace_project
  (final_descriptors : equivocator_descriptors IM)
  (is : composite_state (equivocator_IM IM))
  (tr : list (composite_transition_item (equivocator_IM IM)))
  (final_state := finite_trace_last is tr)
  (Hproper : proper_fixed_equivocator_descriptors final_descriptors final_state)
  (Htr : finite_valid_trace XE is tr)
  (constraint : composite_label IM -> composite_state IM * option message -> Prop)
  (HconstraintNone : forall l s, constraint l (s, None))
  (Hconstraint_hbs :  constraint_has_been_sent_prop constraint)
  (X' := composite_vlsm IM constraint)
  : exists
    (trX : list (composite_transition_item IM))
    (initial_descriptors : equivocator_descriptors IM)
    (isX := equivocators_state_project IM initial_descriptors is)
    (final_stateX := finite_trace_last isX trX),
    proper_fixed_equivocator_descriptors initial_descriptors is /\
    equivocators_trace_project IM final_descriptors tr = Some (trX, initial_descriptors) /\
    equivocators_state_project IM final_descriptors final_state = final_stateX /\
    finite_valid_trace X' isX trX.
Proof.
  remember (length tr) as len_tr.
  revert tr Htr Heqlen_tr final_state final_descriptors Hproper.
  induction len_tr as [len_tr IHlen] using (well_founded_induction Wf_nat.lt_wf); intros.
  subst len_tr.
  destruct_list_last tr tr' lst Htr_lst.
  - clear IHlen. subst. exists [], final_descriptors.
    split; [done |]. split; [done |]. split; [done |].
    remember (equivocators_state_project IM final_descriptors is) as isx.
    cut (initial_state_prop X' isx).
    { intro His. split; [| done]. constructor.
      apply valid_state_prop_iff. left.
      by exists (exist _ _ His).
    }
    by subst; apply fixed_equivocators_initial_state_project; [apply Htr | apply Hproper].
  - specialize (IHlen (length tr')) as IH'.
    spec IH'; [by rewrite app_length; cbn; lia |].
    destruct Htr as [Htr Hinit].
    apply finite_valid_trace_from_app_iff in Htr.
    destruct Htr as [Htr Hlst].
    specialize (IH' tr' (conj Htr Hinit) eq_refl).
    specialize (equivocators_transition_item_project_proper_characterization IM final_descriptors lst)
      as Hproperx.
    specialize
      (equivocators_transition_item_project_preserves_zero_descriptors IM final_descriptors lst)
      as Hzero.
    unfold final_state in Hproper.
    rewrite Htr_lst, finite_trace_last_is_last in Hproper.
    specialize (Hproperx (proj1 Hproper)).
    destruct Hproperx as [oitem [final_descriptors' [Hprojectx [Hitemx Hproperx]]]].
    specialize (Hproperx (finite_trace_last is tr')).
    unfold equivocators_trace_project.
    rewrite fold_right_app.
    match goal with
    |- context [fold_right _ ?fld _] => remember fld as foldx
    end.
    simpl in Heqfoldx.
    rewrite Hprojectx in Heqfoldx.
    apply first_transition_valid in Hlst. destruct lst as (l, iom, s, oom). simpl in *.
    destruct Hlst as [[Hs [Hiom [Hv Hc]]] Ht].
    specialize (Hzero oitem final_descriptors' _ Ht Hv Hprojectx).
    specialize (Hproperx Hv Ht).
    destruct Hproperx as [_Hproper' [_ [_ [_ Hx]]]].
    assert (Hproper' :
      proper_fixed_equivocator_descriptors final_descriptors' (finite_trace_last is tr')).
    { split; [done |].
      intros i Hi. apply Hzero. clear Hzero. destruct Hproper as [_ Hzero].
      by apply Hzero.
    }
    clear _Hproper' Hzero.
    specialize (IH' _ Hproper')
      as (trX' & initial_descriptors & _ & Htr_project & Hstate_project & HtrX').
    assert
      (Htr' : finite_valid_trace FreeE is tr').
    {
      split; [| done].
      revert Htr; apply VLSM_incl_finite_valid_trace_from.
      by apply equivocators_fixed_equivocations_vlsm_incl_free.
    }
    assert
      (Htr'pre : finite_valid_trace (pre_loaded_with_all_messages_vlsm FreeE) is tr').
    {
      split; [| done].
      specialize (vlsm_incl_pre_loaded_with_all_messages_vlsm FreeE) as Hincl.
      by apply (VLSM_incl_finite_valid_trace_from Hincl), Htr'.
    }
    specialize (equivocators_trace_project_preserves_proper_fixed_equivocator_descriptors
      _ _ (proj1 Htr'pre) _ _ _ Htr_project Hproper')
      as Hproper_initial.
    destruct oitem as [item |].
    +  simpl in Hitemx. destruct Hitemx as [Hl [Hinput [Houtput [Hdestination _]]]].
      specialize (Hx _ eq_refl).
      destruct Hx as [Hvx Htx].
      exists (trX' ++ [item]), initial_descriptors. subst foldx.
      rewrite equivocators_trace_project_folder_additive
        with (trX := trX') (eqv_descriptors := initial_descriptors)
      ; [| done].
      split; [done |].
      split; [done |].
      rewrite finite_trace_last_is_last.
      unfold final_state. subst tr.
      rewrite finite_trace_last_is_last.
      split; [done |].
      destruct HtrX' as [HtrX' His].
      split; [| done].
      apply finite_valid_trace_from_app_iff.
      split; [done |].
      change [item] with ([] ++ [item]).
      match goal with
      |- finite_valid_trace_from _ ?l _ => remember l as lst
      end.
      destruct item.
      assert (Hplst : valid_state_prop X' lst)
        by (apply finite_valid_trace_last_pstate in HtrX'; subst; done).
      apply (extend_right_finite_trace_from X'); [by constructor |].
      simpl in Hl. subst.
      simpl in Hc.
      destruct Hc as [[Hno_equiv _] _].
      simpl in Htx, Hvx, Hstate_project.
      rewrite Hstate_project in Hvx, Htx.
      destruct input as [input |]; [| by repeat split;
        [| apply option_valid_message_None | | apply HconstraintNone |]].
      simpl in Hno_equiv.
      apply or_comm in Hno_equiv.
      destruct Hno_equiv as [Hinit_input | Hno_equiv]
      ; [done |].
      assert
        (Hs_free : valid_state_prop FreeE (finite_trace_last is tr')).
      {
        destruct Hs as [_om Hs].
        exists _om.
        eapply VLSM_incl_valid_state_message; [by apply free_composite_vlsm_spec | by do 2 red |].
        by eapply (constraint_subsumption_valid_state_message_preservation (free_composite_vlsm _)).
      }
      specialize
        (specialized_proper_sent_rev FreeE _ Hs_free _ Hno_equiv) as Hall.
      specialize (Hall is tr' (valid_trace_add_default_last Htr')).
      destruct (equivocators_trace_project_output_reflecting_inv IM _ _ (proj1 Htr'pre) _ Hall)
        as [final_descriptors_m [initial_descriptors_m [trXm [_Hfinal_descriptors_m
            [Hproject_trXm Hex]]]]].
      assert (Hfinal_descriptors_m :
        proper_fixed_equivocator_descriptors final_descriptors_m (finite_trace_last is tr')).
      { apply not_equivocating_equivocator_descriptors_proper_fixed; [| done].
        by apply finite_valid_trace_last_pstate.
      }
      specialize (IHlen (length tr')).
      spec IHlen. { rewrite app_length. simpl. lia. }
      specialize (IHlen tr' (conj Htr Hinit) eq_refl final_descriptors_m Hfinal_descriptors_m)
        as (trXm' & initial_descriptors_m' & Hproper_initial_m &
            Hproject_trXm' & Hpr_fin_tr' & HtrXm).
      simpl in *. rewrite Hproject_trXm in Hproject_trXm'.
      inversion Hproject_trXm'. subst trXm' initial_descriptors_m'. clear Hproject_trXm'.
      repeat split; [done | | done | | done].
      * by eapply valid_trace_output_is_valid; [apply HtrXm |].
      * rewrite <- Hstate_project.
        apply Hconstraint_hbs; [done | apply Hproper' |].
        assert (Hlst'pre : constrained_state_prop FreeE (finite_trace_last is tr'))
            by (apply finite_valid_trace_last_pstate, Htr'pre).
        apply proper_sent; [done |].
        apply has_been_sent_consistency; [typeclasses eauto | done |].
        by exists is, tr', (valid_trace_add_default_last Htr'pre).
    + exists trX'. exists initial_descriptors. subst foldx. split; [done |].
      split; [by apply Htr_project |].
      split; [| done].
      subst tr. clear -Hstate_project Hx.
      unfold final_state.
      by rewrite <- Hstate_project, <- Hx, finite_trace_last_is_last.
Qed.

(** Instantiating the lemma above with the free constraint. *)
Lemma free_equivocators_valid_trace_project
  (final_descriptors : equivocator_descriptors IM)
  (is : composite_state (equivocator_IM IM))
  (tr : list (composite_transition_item (equivocator_IM IM)))
  (final_state := @finite_trace_last _ XE is tr)
  (Hproper : proper_fixed_equivocator_descriptors final_descriptors final_state)
  (Htr : finite_valid_trace XE is tr)
  : exists
    (trX : list (composite_transition_item IM))
    (initial_descriptors : equivocator_descriptors IM)
    (isX := equivocators_state_project IM initial_descriptors is)
    (final_stateX := finite_trace_last isX trX),
    proper_fixed_equivocator_descriptors initial_descriptors is /\
    equivocators_trace_project IM final_descriptors tr = Some (trX, initial_descriptors) /\
    equivocators_state_project IM final_descriptors final_state = final_stateX /\
    finite_valid_trace (free_composite_vlsm IM) isX trX.
Proof.
  destruct (_equivocators_valid_trace_project final_descriptors is tr Hproper Htr
    (free_constraint IM)) as (trX & idesc & Hex); [done.. |].
  exists trX, idesc.
  split_and!; [by itauto.. |].
  apply (@VLSM_incl_finite_valid_trace _ _ (composite_vlsm IM (free_constraint IM))); [| by itauto].
  by apply free_composite_vlsm_spec.
Qed.

(**
  A message sent by a non-state-equivocating machine can be directly observed
  in any projection of the final state.
*)
Lemma not_equivocating_sent_message_has_been_directly_observed_in_projection
  (is : state XE)
  (tr : list (composite_transition_item (equivocator_IM IM)))
  (Htr : finite_valid_trace XE is tr)
  (lst := finite_trace_last is tr)
  (item : transition_item)
  (Hitem : item ∈ tr)
  (Hitem_not_equiv : projT1 (l item) ∉ equivocating)
  (m : message)
  (Hm : field_selector output m item)
  (descriptors : equivocator_descriptors IM)
  (Hdescriptors : proper_fixed_equivocator_descriptors descriptors lst)
  : has_been_directly_observed Free (equivocators_state_project IM descriptors lst) m.
Proof.
  destruct (free_equivocators_valid_trace_project descriptors is tr Hdescriptors Htr)
    as [trX [initial_descriptors [_ [Htr_project [Hfinal_state HtrX_Free]]]]].
  subst lst.
  rewrite Hfinal_state.

  assert (Htr_Pre : finite_valid_trace (pre_loaded_with_all_messages_vlsm FreeE) is tr).
  {
    apply VLSM_incl_finite_valid_trace; [| done].
    by apply constrained_preloaded_incl.
  }

  assert (HtrX_Pre : finite_valid_trace (pre_loaded_with_all_messages_vlsm Free)
                      (equivocators_state_project IM initial_descriptors is) trX).
  {
    revert HtrX_Free; apply VLSM_incl_finite_valid_trace.
    by apply vlsm_incl_pre_loaded_with_all_messages_vlsm.
  }

  assert (Hlst_preX : constrained_state_prop Free
    (finite_trace_last (equivocators_state_project IM initial_descriptors is) trX)).
  {
    apply (finite_valid_trace_last_pstate (pre_loaded_with_all_messages_vlsm Free)).
    by apply HtrX_Pre.
  }
  rewrite (has_been_directly_observed_sent_received_iff Free) by done.
  right. apply proper_sent; [done |].
  apply has_been_sent_consistency; [by typeclasses eauto | done |].
  exists (equivocators_state_project IM initial_descriptors is), trX,
    (valid_trace_add_default_last HtrX_Pre).

  apply elem_of_list_split in Hitem.
  destruct Hitem as [pre [suf Hitem]].
  change (item :: suf) with ([item] ++ suf) in Hitem.
  subst tr.

  assert (Hsingleton_d_item :
    is_singleton_state (IM (projT1 (VLSM.l item))) (destination item (projT1 (VLSM.l item)))).
  {
    apply (not_equivocating_index_has_singleton_state IM (elements equivocating));
      [| by rewrite elem_of_elements].
    apply proj1 in Htr.
    rewrite app_assoc in Htr.
    apply finite_valid_trace_from_app_iff in Htr.
    destruct Htr as [Htr _].
    apply finite_valid_trace_last_pstate in Htr.
    by rewrite finite_trace_last_is_last in Htr.
  }

  apply equivocators_trace_project_app_iff in Htr_project.
  destruct Htr_project as [preX' [sufX' [eqv_descriptors' [Hpr_suf [Hpr_pre HpreX]]]]].
  subst trX. apply Exists_app. right.

  apply proj1 in Htr_Pre.
  apply finite_valid_trace_from_app_iff in Htr_Pre.
  destruct Htr_Pre as [Hpre'_free Hsuf'_free].

  apply equivocators_trace_project_app_iff in Hpr_suf.
  destruct Hpr_suf as [pre_itemX [sufX'' [eqv_descriptors'' [Hpr_suf' [Hpr_pre_item HsufX']]]]].
  subst sufX'. apply Exists_app. left.

  apply finite_valid_trace_from_app_iff in Hsuf'_free.
  destruct Hsuf'_free as [Hpre_item_free Hsuf'_free].
  assert (Heqv_descriptors'' : forall i, i ∉ equivocating -> eqv_descriptors'' i = Existing 0).
  {
    by intros i Hi; eapply equivocators_trace_project_preserves_zero_descriptors, Hdescriptors.
  }

  specialize (Heqv_descriptors'' _ Hitem_not_equiv).
  simpl in *.
  destruct (equivocators_transition_item_project IM eqv_descriptors'' item)
    as [(o, odescriptor) |] eqn: Hpr
  ; [| by congruence].
  destruct item. simpl in *.
  apply first_transition_valid in Hpre_item_free. simpl in Hpre_item_free.
  destruct Hpre_item_free as [[_ [_ Hv]] Ht].
  destruct l as [x l].
  cbn in *.
  destruct (equivocator_transition (IM x) l _) as [si' om'] eqn: Hti.
  inversion Ht; subst; clear Ht.
  state_update_simpl.
  destruct (equivocator_transition_no_equivocation_zero_descriptor
    (IM x) _ _ _ _ _ Hv Hti Hsingleton_d_item) as [li Hsndv].
  unfold equivocators_transition_item_project in Hpr.
  simpl in Hpr.
  subst l.
  unfold ProjectionTraces.composite_transition_item_projection in Hpr.
  unfold ProjectionTraces.composite_transition_item_projection_from_eq in Hpr.
  simpl in Hpr.
  unfold eq_rect_r in Hpr. simpl in Hpr.
  rewrite Heqv_descriptors'' in Hpr.
  unfold equivocator_vlsm_transition_item_project in Hpr.
  state_update_simpl.
  rewrite equivocator_state_project_zero in Hpr.
  rewrite decide_True in Hpr by done.
  inversion Hpr. subst. clear Hpr.
  inversion Hpr_pre_item. subst. clear Hpr_pre_item.
  by constructor.
Qed.

(**
  Consider a [valid_trace] for the composition of equivocators with
  no message equivocation and fixed state equivocation.

  Because any of its projections to the composition of original components contains
  all transitions from components not allowed to equivocate, then a final state of
  such a projection will be able to observe all messages sent or received by
  non-equivocating components in the initial trace.

  Therefore if seeding the composition of equivocating components with these
  messages, the restriction of the initial trace to only the equivocating
  components will satisfy the [trace_sub_item_input_is_seeded_or_sub_previously_sent]
  property w.r.t. these messages, a sufficient condition for it being
  valid ([finite_valid_trace_sub_projection]).
*)
Lemma equivocators_trace_sub_item_input_is_seeded_or_sub_previously_sent
  (is : state XE)
  (tr : list (transition_item XE))
  (s := finite_trace_last is tr)
  (Htr : finite_valid_trace XE is tr)
  (descriptors : equivocator_descriptors IM)
  (Hproper : proper_fixed_equivocator_descriptors descriptors s)
  (lst_trX := equivocators_state_project IM descriptors s)
  : trace_sub_item_input_is_seeded_or_sub_previously_sent
    (equivocator_IM IM) (elements equivocating)
    (composite_has_been_directly_observed IM lst_trX) tr.
Proof.
  intros pre item suf m Heq Hm Hitem.
  destruct (free_equivocators_valid_trace_project descriptors is tr Hproper Htr)
    as [trX [initial_descriptors [Hinitial_descriptors [Htr_project [Hfinal_state HtrXFree]]]]].
  assert (HtrXPre : finite_valid_trace (pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM))
    (equivocators_state_project IM initial_descriptors is) trX).
  {
    revert HtrXFree; apply VLSM_incl_finite_valid_trace.
    by apply vlsm_incl_pre_loaded_with_all_messages_vlsm.
  }
  assert (Hlst_trX : constrained_state_prop Free lst_trX).
  {
    subst lst_trX s; cbn in Hfinal_state |- *; rewrite Hfinal_state.
    by apply finite_valid_trace_last_pstate, HtrXPre.
  }
  assert (Htr_free : finite_valid_trace  (pre_loaded_with_all_messages_vlsm FreeE) is tr).
  {
    apply VLSM_incl_finite_valid_trace; [| done].
    by apply constrained_preloaded_incl.
  }
  subst tr.
  destruct Htr as [Htr His].
  apply finite_valid_trace_from_app_iff in Htr as Hsuf. destruct Hsuf as [_ Hsuf].
  rewrite app_assoc in Htr.
  apply finite_valid_trace_from_app_iff in Htr as Hpre. destruct Hpre as [Hpre _].
  apply finite_valid_trace_from_app_iff in Hpre. destruct Hpre as [Hpre Hivt].
  apply first_transition_valid in Hivt.
  destruct (composite_has_been_directly_observed_dec IM lst_trX m) as [| Heqv]
  ; [by left | right].
  assert (Hsuf_free : finite_valid_trace_from (pre_loaded_with_all_messages_vlsm FreeE)
    (finite_trace_last is pre) ([item] ++ suf)).
  {
    apply VLSM_incl_finite_valid_trace_from; [| done].
    by apply constrained_preloaded_incl.
  }
  assert (Hs_free : valid_state_prop  (pre_loaded_with_all_messages_vlsm FreeE) s).
  { apply finite_valid_trace_last_pstate in Hsuf_free. subst s.
    by rewrite finite_trace_last_app.
  }
  destruct item as (l, iom, s0, oom).
  simpl in Hm. subst iom.
  destruct Hivt as [[_ [_ [_ [[Hc _] Hfixed]]]] Ht].
  cbn in Ht, Hfixed; rewrite Ht in Hfixed.
  clear Ht.
  destruct Hc as [Hc | Hinit]; [| done].
  assert (Hpre_free : finite_valid_trace FreeE is pre).
  {
    split; [| done].
    revert Hpre; apply VLSM_incl_finite_valid_trace_from.
    by apply equivocators_fixed_equivocations_vlsm_incl_free.
  }
  assert (Hpre_lst_free : valid_state_prop FreeE (finite_trace_last is pre))
    by (apply (finite_valid_trace_last_pstate FreeE), Hpre_free; done).
  specialize (specialized_proper_sent_rev FreeE _ Hpre_lst_free m) as Hproper_sent.
  apply Hproper_sent in Hc. clear Hproper_sent.
  specialize (Hc  is pre (valid_trace_add_default_last Hpre_free)).
  apply Exists_exists in Hc.
  destruct Hc as [pre_item [Hpre_item Hpre_m]].
  exists pre_item. split; [done |]. split; [done |].

  apply equivocators_trace_project_app_iff in Htr_project.
  destruct Htr_project as [preX [sufX [final_descriptors' [Hsuf_project [Htr_project Heq]]]]].

  assert (Hfinal' :
    proper_fixed_equivocator_descriptors final_descriptors' (finite_trace_last is pre)).
  { split.
    - apply proj1 in Hproper. subst s. rewrite finite_trace_last_app in Hproper.
      destruct (preloaded_equivocators_valid_trace_from_project IM _ _ _ Hproper Hsuf_free)
        as [_sufX [_final_descriptors' [_Hsuf_project [Hproper' _]]]].
      rewrite Hsuf_project in _Hsuf_project.
      by inversion _Hsuf_project; subst.
    - specialize (equivocators_trace_project_preserves_zero_descriptors IM _ _ Hsuf_free descriptors)
        as Hpr.
      specialize (Hpr _ _ Hsuf_project).
      by intros i Hi; apply Hpr, (proj2 Hproper).
  }
  assert
    (Hfutures : in_futures (pre_loaded_with_all_messages_vlsm FreeE)
      (destination pre_item) s0).
  { apply elem_of_list_split in Hpre_item.
    destruct Hpre_item as [pre_pre [pre_suf Hpre_item]].
    change (pre_item :: pre_suf) with ([pre_item] ++ pre_suf) in Hpre_item.
    rewrite app_assoc in Hpre_item.
    rewrite app_assoc in Htr_free.
    destruct Htr_free as [Htr_free _].
    apply finite_valid_trace_from_app_iff in Htr_free.
    destruct Htr_free as [Htr_s0 _].
    subst pre. clear -Htr_s0.
    rewrite <- app_assoc in Htr_s0.
    apply (finite_valid_trace_from_app_iff (pre_loaded_with_all_messages_vlsm FreeE)) in Htr_s0.
    destruct Htr_s0 as [_ Hfuture].
    rewrite finite_trace_last_is_last in Hfuture.
    eexists.
    apply valid_trace_add_last; [by apply Hfuture |].
    by rewrite finite_trace_last_is_last.
  }
  eapply (in_futures_reflects_fixed_equivocation) in Hfutures; [| done].
  destruct (free_equivocators_valid_trace_project final_descriptors' is pre Hfinal' (conj Hpre His))
    as [_preX [_initial_descriptors [_ [_Htr_project [Hpre_final_state _]]]]].
  rewrite Htr_project in _Htr_project. inversion _Htr_project. subst _preX _initial_descriptors.
  clear _Htr_project.
  unfold from_sub_projection, pre_VLSM_projection_in_projection,
    composite_label_sub_projection_option.
  case_decide as Hl; [by eexists |].
  contradict Heqv.
  apply composite_has_been_directly_observed_free_iff.
  eapply in_futures_preserving_oracle_from_stepwise; cycle 2
  ; [| by apply has_been_directly_observed_stepwise_props |].
  - by eapply not_equivocating_sent_message_has_been_directly_observed_in_projection;
      only 3: rewrite <- elem_of_elements.
  - subst lst_trX. subst s. simpl. simpl in Hfinal_state.
    rewrite Hfinal_state. subst trX.
    rewrite finite_trace_last_app.
    exists sufX.
    apply proj1 in HtrXPre.
    apply finite_valid_trace_from_app_iff in HtrXPre.
    simpl in *. rewrite Hpre_final_state.
    apply valid_trace_add_default_last.
    by apply HtrXPre.
Qed.

(**
  Because any of its projections to the composition of original components contains
  all transitions from components not allowed to equivocate, all messages
  sent by non-equivocating components in the original trace will also be sent
  in any projection.
*)
Lemma equivocator_vlsm_trace_project_reflect_non_equivocating
  (is : composite_state (equivocator_IM IM))
  (tr : list (composite_transition_item (equivocator_IM IM)))
  (Htr : finite_valid_trace XE is tr)
  (m : message)
  (final_descriptors : equivocator_descriptors IM)
  (Hproper : proper_fixed_equivocator_descriptors final_descriptors (finite_trace_last is tr))
  (trX : list (composite_transition_item IM))
  (initial_descriptors : equivocator_descriptors IM)
  (Htr_project : equivocators_trace_project IM final_descriptors tr = Some (trX, initial_descriptors))
  (item : composite_transition_item (equivocator_IM IM))
  (Hitem : item ∈ tr)
  (Houtput : output item = Some m)
  (Hno_equiv_item : projT1 (l item) ∉ equivocating)
  : trace_has_message (field_selector output) m trX.
Proof.
  apply elem_of_list_split in Hitem.
  destruct Hitem as [pre [suf Heq_tr]].
  change (item :: suf) with ([item] ++ suf) in Heq_tr.
  subst tr.
  apply equivocators_trace_project_app_iff in Htr_project.
  destruct Htr_project as [preX [item_sufX [eqv_pre [Hpr_item_suf [Hpr_pre Heq_trX]]]]].
  subst trX.
  apply Exists_app. right.
  apply equivocators_trace_project_app_iff in Hpr_item_suf.
  destruct Hpr_item_suf as [itemXs [sufX [eqv_item [Hpr_suf [Hpr_item Heq_item_sufX]]]]].
  subst item_sufX.
  apply Exists_app. left.
  destruct Htr as [Htr _].
  rewrite app_assoc in Htr.
  apply finite_valid_trace_from_app_iff in Htr.
  destruct Htr as [Hpre Hsuf].
  apply finite_valid_trace_from_app_iff in Hpre.
  destruct Hpre as [_ Hitem].
  rewrite app_assoc, finite_trace_last_app in Hproper.
  rewrite finite_trace_last_is_last in Hsuf, Hproper.
  assert (Hsufpre :
    finite_valid_trace_from (pre_loaded_with_all_messages_vlsm FreeE) (destination item) suf).
  {
    eapply VLSM_incl_finite_valid_trace_from; [| done].
    by apply constrained_preloaded_incl.
  }
  specialize
    (equivocators_trace_project_preserves_proper_fixed_equivocator_descriptors _ _ Hsufpre
      final_descriptors eqv_item _ Hpr_suf Hproper)
    as Hproper_item.
  destruct Hproper_item as [Hproper_item Hproper_fixed_item].
  specialize (Hproper_fixed_item _ Hno_equiv_item).
  specialize
    (no_equivocating_equivocators_transition_item_project IM eqv_item item
      Hproper_fixed_item)
    as Hex.
  spec Hex.
  {
    apply (not_equivocating_index_has_singleton_state _ (elements equivocating));
      [| by rewrite elem_of_elements].
    by apply finite_valid_trace_last_pstate in Hitem.
  }
  destruct item as (l, iom, s, oom). apply first_transition_valid in Hitem. simpl in Hitem.
  destruct Hitem as [[Hs [Hiom [Hv Hc]]] Ht].
  simpl in Hex.
  specialize (Hex _ Hv Ht) as [Hex' Hex]. simpl in Hex.
  simpl in Hpr_item. rewrite Hex in Hpr_item.
  inversion_clear Hpr_item.
  by constructor.
Qed.

(**
  As a consequence of the [equivocator_vlsm_trace_project_reflect_non_equivocating]
  lemma, if a message emmitted by a trace cannot be directly observed in a
  projection of the trace's final state, then it must be that it was emitted by
  one of the components allowed to equivocate.
*)
Lemma projection_has_not_been_directly_observed_is_equivocating
  (is : composite_state (equivocator_IM IM))
  (tr : list (composite_transition_item (equivocator_IM IM)))
  (Htr : finite_valid_trace XE is tr)
  (s := @finite_trace_last _ (composite_type (equivocator_IM IM)) is tr)
  (descriptors : equivocator_descriptors IM)
  (Hproper : proper_fixed_equivocator_descriptors descriptors s)
  (sX := equivocators_state_project IM descriptors s)
  (m : message)
  (Hno : ~ composite_has_been_directly_observed IM sX m)
  : forall item : composite_transition_item (equivocator_IM IM),
      item ∈ tr -> output item = Some m -> projT1 (l item) ∈ equivocating.
Proof.
  destruct (free_equivocators_valid_trace_project descriptors is tr Hproper Htr)
    as [trX [initial_descriptors [_ [Htr_project [Hlast_state HtrX]]]]].
  intros item Hitem Houtput.
  destruct (decide (projT1 (l item) ∈ elements equivocating));
    [by apply elem_of_elements |].
  elim Hno. clear Hno.
  apply composite_has_been_directly_observed_sent_received_iff.
  left.
  assert (HtrX_free : finite_valid_trace (pre_loaded_with_all_messages_vlsm Free)
    (equivocators_state_project IM initial_descriptors is) trX).
  {
    revert HtrX; apply VLSM_incl_finite_valid_trace.
    by apply vlsm_incl_pre_loaded_with_all_messages_vlsm.
  }
  specialize (finite_valid_trace_last_pstate _ _ _ (proj1 HtrX_free)) as Hfree_lst.
  subst sX s.
  simpl in *.
  rewrite Hlast_state.
  apply (composite_proper_sent IM); [done |].
  apply has_been_sent_consistency; [by typeclasses eauto | done |].
  exists (equivocators_state_project IM initial_descriptors is), trX,
    (valid_trace_add_default_last HtrX_free).
  clear HtrX HtrX_free Hfree_lst.
  by eapply equivocator_vlsm_trace_project_reflect_non_equivocating;
    [.. | contradict n; apply elem_of_elements].
Qed.

(**
  The next two lemmas are rather technical, but their basic meaning is that
  if we take the composition of a subset of equivocators, it doesn't matter
  the way we do it (either first obtain the indexed subset of components and then
  transform that into equivocators and take their composition, or we first
  start with the indexed full set of equivocators and then select a subset
  of them and take their composition).
*)
Lemma pre_loaded_equivocators_composition_sub_projection_commute
  (seed1 : message -> Prop)
  (seed2 : message -> Prop)
  (Hseed12 : forall m, seed1 m -> seed2 m)
  : VLSM_incl
    (composite_no_equivocation_vlsm_with_pre_loaded
      (sub_IM (equivocator_IM IM) (elements equivocating))
      (free_constraint _)
      seed1)
    (composite_no_equivocation_vlsm_with_pre_loaded
      (equivocator_IM (sub_IM IM (elements equivocating)))
      (free_constraint _)
      seed2).
Proof.
  apply basic_VLSM_incl.
  - by intro; intros.
  - intro; intros.
    apply initial_message_is_valid; cbn.
    by destruct HmX; auto.
  - intros l s om [Hs [_ [Hv Hc]]].
    split; [done |].
    destruct Hc as [Hc _].
    split; [| done].
    destruct om; [| done].
    simpl in Hc. simpl.
    destruct Hc as [Hc | Hc]
    ; [| by right; apply Hseed12].
    left.
    destruct Hc as [subi Hibs].
    exists subi. revert Hibs.
    apply has_been_sent_irrelevance.
    simpl.
    apply (preloaded_valid_state_projection (equivocator_IM (sub_IM IM (elements equivocating))) subi).
    revert Hs.
    apply VLSM_incl_valid_state.
    by apply constrained_pre_loaded_vlsm_incl_pre_loaded_with_all_messages.
  - by destruct 1.
Qed.

Lemma pre_loaded_equivocators_composition_sub_projection_commute_inv
  (seed1 : message -> Prop)
  (seed2 : message -> Prop)
  (Hseed12 : forall m, seed1 m -> seed2 m)
  : VLSM_incl
    (composite_no_equivocation_vlsm_with_pre_loaded
      (equivocator_IM (sub_IM IM (elements equivocating)))
      (free_constraint _)
      seed1)
    (composite_no_equivocation_vlsm_with_pre_loaded
      (sub_IM (equivocator_IM IM) (elements equivocating))
      (free_constraint _)
      seed2).
Proof.
  apply basic_VLSM_incl; intros ? *; [done | | | by destruct 1].
  - intros.
    apply initial_message_is_valid; cbn.
    by destruct HmX; auto.
  - intros (Hs & _ & Hv & Hc & _) _ _.
    split; [done |].
    split; [| done].
    destruct om; [| done].
    simpl in Hc. simpl.
    destruct Hc as [Hc | Hc]
    ; [| by right; apply Hseed12].
    left.
    destruct Hc as [subi Hibs].
    exists subi. revert Hibs.
    apply has_been_sent_irrelevance.
    simpl.
    apply (preloaded_valid_state_projection (equivocator_IM (sub_IM IM (elements equivocating))) subi).
    revert Hs.
    apply VLSM_incl_valid_state.
    by apply constrained_pre_loaded_vlsm_incl_pre_loaded_with_all_messages.
Qed.

(**
  The intermediary results above allow us to prove that the
  [fixed_equivocation_constraint] has the [constraint_has_been_sent_prop]erty.

  The core of this result is proving that given a [valid_state] <<s>> of the
  composition of equivocators with no message equivocation and fixed state
  equivocation, a message which [has_been_sent] for that state but not
  [has_been_directly_observed] for a projection of that state <<sx>>, can nevertheless be
  generated by the composition of the components allowed to equivocate, pre-loaded with
  the messages directly observed in the state <<sx>>.

  To prove that, we consider a trace witness for the message having been sent,
  we use [projection_has_not_been_directly_observed_is_equivocating] to derive that
  it must have been sent by one of the machines allowed to equivocate, from this
  we derive that it can be sent by the restriction of the composition of
  equivocators to just the equivocating components, pre-loaded with the messages
  directly observed in the projection, then we use
  the [seeded_equivocators_valid_trace_project] result to reach our conclusion.
*)
Lemma fixed_equivocation_constraint_has_constraint_has_been_sent_prop
  : constraint_has_been_sent_prop
    (fixed_equivocation_constraint IM equivocating).
Proof.
  unfold constraint_has_been_sent_prop. intros.
  remember (equivocators_state_project _ _ _) as sX.
  destruct (composite_has_been_directly_observed_dec IM sX m)
  ; [by left | right].
  clear l.
  unfold no_additional_equivocations in n.
  (* Phase I: exhibiting a [valid_trace] ending in tr s and sending m *)
  apply valid_state_has_trace in Hs.
  destruct Hs as [is [tr Htr]].
  assert (Htr'pre : finite_valid_trace_init_to (pre_loaded_with_all_messages_vlsm FreeE) is s tr).
  {
    apply VLSM_incl_finite_valid_trace_init_to; [| done].
    by apply constrained_preloaded_incl.
  }
  assert (Hplst : constrained_state_prop FreeE s)
    by (apply valid_trace_last_pstate in Htr'pre; done).
  apply proper_sent in Hm; [| done]. clear Hplst.
  specialize (Hm is tr Htr'pre).
  (*
    Phase II (a): The restriction of tr to the equivocators allowed to
    state-equivocate is valid for the corresponding composition
    pre-loaded with the messages directly observed in the projection sX of s.
  *)
  specialize
    (finite_valid_trace_sub_projection (equivocator_IM IM) (elements equivocating)
      (equivocators_fixed_equivocations_constraint IM (elements equivocating))
      (composite_has_been_directly_observed IM sX))
    as Hproject.
  specialize (Hproject is tr).
  spec Hproject.
  { subst sX.
    rewrite <- (valid_trace_get_last Htr) in Hdescriptors |- *.
    apply
      (equivocators_trace_sub_item_input_is_seeded_or_sub_previously_sent
        _ _ (valid_trace_forget_last Htr) descriptors Hdescriptors).
  }
  specialize (Hproject (valid_trace_forget_last Htr)).

  rewrite HeqsX in n.
  clear HeqsX.
  (* Phase III (a): Obtain a projection trXm of tr outputing m using a final_descriptor_m *)

  apply (equivocators_trace_project_output_reflecting_iff _ _ _
    (proj1 (valid_trace_forget_last Htr'pre))) in Hm
    as (final_descriptors_m & initial_descriptors_m & trXm & Hfinal_descriptors_m &
        Hproject_trXm & Hex).

  (* Identify the item outputing m in trXm an its corresponding item in tr. *)

  apply Exists_exists in Hex.
  destruct Hex as [output_itemX [Hin Houtput_select]].
  apply elem_of_list_split in Hin.
  destruct Hin as [preX [sufX Heq_trXm]].
  change (output_itemX :: sufX) with ([output_itemX] ++ sufX) in Heq_trXm.
  assert (Hpr_item := Hproject_trXm).
  rewrite Heq_trXm in Hpr_item.
  apply equivocators_trace_project_app_inv_item in Hpr_item.
  destruct Hpr_item as [pre [suf [item [item_descriptors [pre_descriptors
    [_ [Hpr_item [_ Heqtr]]]]]]]].
  unfold equivocators_transition_item_project in Hpr_item.
  destruct
    (equivocator_vlsm_transition_item_project (IM (projT1 (l item)))
      (composite_transition_item_projection (equivocator_IM IM) item)
      (item_descriptors (projT1 (l item))))
    as [(o, deqv') |]
    ; [| by congruence].
  destruct o as [item' |]; [| by congruence].
  inversion Hpr_item. subst output_itemX pre_descriptors. clear Hpr_item deqv'.
  simpl in Houtput_select.

  (* show that that item must be specifying a transition for an equivocating component *)

  rewrite <- (valid_trace_get_last Htr) in Hdescriptors, n.
  specialize
    (projection_has_not_been_directly_observed_is_equivocating _ _ (valid_trace_forget_last Htr)
      _ Hdescriptors
      _ n item)
    as Hitem_equivocating.
  clear Hdescriptors n.
  spec Hitem_equivocating; [by rewrite Heqtr, !elem_of_app, elem_of_cons; auto |].
  specialize (Hitem_equivocating Houtput_select).
  (*
    Phase III (b):
    Consider a projection trX' obtained using the final_descriptor_m as above,
    but first restricting the components to just the equivocators allowed to equivocate.
    We will show that we can use [seeded_equivocators_valid_trace_project]
    and leverage the result from Phase II (a)
    to derive that the resulting projection is valid.
  *)
  unfold equivocators_composition_for_directly_observed,
    pre_loaded_free_equivocating_vlsm_composition.
  specialize
    (seeded_equivocators_valid_trace_project IM (elements equivocating)
      (composite_has_been_directly_observed IM sX)
      (composite_state_sub_projection (equivocator_IM IM) (elements equivocating) is)
      (finite_trace_sub_projection (equivocator_IM IM) (elements equivocating) tr)
      Hproject
      (fun i => final_descriptors_m (proj1_sig i)))
    as Hsub_project.
  simpl in Hsub_project.
  spec Hsub_project.
  {
    specialize (finite_trace_sub_projection_last_state (equivocator_IM IM) (elements equivocating)
      (equivocators_fixed_equivocations_constraint IM (elements equivocating)) _ _
        (proj1 (valid_trace_forget_last Htr)))
      as Heq_lst.
    simpl in Heq_lst.
    rewrite Heq_lst.
    intros e.
    destruct e.
    apply not_equivocating_equivocator_descriptors_proper in Hfinal_descriptors_m.
    by apply Hfinal_descriptors_m.
  }
  destruct Hsub_project
    as [trX' [initial_descriptors' [_ [Hpr_tr' [_ HtrX]]]]].
  clear Htr'pre Hproject.

  (*
    State that by restricting trXm to the subset of equivocating components
    we obtain the same trX' trace.
  *)

  destruct
    (equivocators_trace_project_finite_trace_sub_projection_commute IM (elements equivocating)
      final_descriptors_m initial_descriptors_m initial_descriptors' tr trXm trX'
      Hproject_trXm Hpr_tr')
    as [_ HeqtrX].
  clear Hproject_trXm Hpr_tr'.

  (* reduce the goal to showing that the message appears in trX'. *)

  remember
    (equivocators_state_project (sub_IM IM (elements equivocating)) initial_descriptors'
      (composite_state_sub_projection (equivocator_IM IM) (elements equivocating) is))
    as isX. clear HeqisX.
  eapply can_emit_from_valid_trace; [done |].

  subst.
  rewrite! (finite_trace_sub_projection_app IM).
  unfold trace_has_message.
  rewrite! Exists_app. right. left. simpl.

  unfold pre_VLSM_projection_transition_item_project,
    composite_label_sub_projection_option.
  apply elem_of_elements in Hitem_equivocating.
  by case_decide; [constructor |].
Qed.

(**
  Main result of this section, stating that traces which are valid for the
  equivocator-based definition of fixed equivocation project to traces which are
  valid for the simple-components definition of fixed equivocation.
*)
Theorem fixed_equivocators_valid_trace_project
  (final_descriptors : equivocator_descriptors IM)
  (is : composite_state (equivocator_IM IM))
  (tr : list (composite_transition_item (equivocator_IM IM)))
  (final_state := finite_trace_last is tr)
  (Hproper : proper_fixed_equivocator_descriptors final_descriptors final_state)
  (Htr : finite_valid_trace XE is tr)
  : exists
    (trX : list (composite_transition_item IM))
    (initial_descriptors : equivocator_descriptors IM)
    (isX := equivocators_state_project IM initial_descriptors is)
    (final_stateX := finite_trace_last isX trX),
    proper_fixed_equivocator_descriptors initial_descriptors is /\
    equivocators_trace_project IM final_descriptors tr = Some (trX, initial_descriptors) /\
    equivocators_state_project IM final_descriptors final_state = final_stateX /\
    finite_valid_trace X isX trX.
Proof.
  apply _equivocators_valid_trace_project; [done | done | done |]; intros.
  by apply fixed_equivocation_constraint_has_constraint_has_been_sent_prop.
Qed.

Lemma fixed_equivocators_vlsm_partial_projection
  (final_descriptors : equivocator_descriptors IM)
  : VLSM_partial_projection XE X (equivocators_partial_trace_project IM final_descriptors).
Proof.
  split; [split |].
  - intros s tr sX trX Hpr_tr s_pre pre Hs_lst Hpre_tr.
    assert (HPreFree_pre_tr :
      finite_valid_trace_from (pre_loaded_with_all_messages_vlsm FreeE) s_pre (pre ++ tr)).
    {
      revert Hpre_tr; apply VLSM_incl_finite_valid_trace_from.
      by apply equivocators_fixed_equivocations_vlsm_incl_PreFree.
    }
    clear Hpre_tr.  revert s tr sX trX Hpr_tr s_pre pre Hs_lst HPreFree_pre_tr.
    apply equivocators_partial_trace_project_extends_left.
  - intros s tr sX trX Hpr_tr Htr.
    destruct (destruct_equivocators_partial_trace_project IM Hpr_tr)
      as [Hnot_equiv [initial_descriptors [Htr_project Hs_project]]].

    specialize (finite_valid_trace_last_pstate XE _ _ (proj1 Htr)) as Hlst.
    apply not_equivocating_equivocator_descriptors_proper_fixed in Hnot_equiv as Hproper
    ; [| done].
    destruct (fixed_equivocators_valid_trace_project  _ _ _ Hproper Htr)
      as [_trX [_initial_descriptors [_ [_Htr_project [_ HtrX]]]]].
    rewrite Htr_project in _Htr_project.
    by inversion _Htr_project; subst.
Qed.

Lemma fixed_equivocators_vlsm_projection
  : VLSM_projection XE X (equivocators_total_label_project IM) (equivocators_total_state_project IM).
Proof.
  constructor; [constructor |]; intros sX trX HtrX.
  - apply PreFreeE_Free_vlsm_projection_type.
    apply VLSM_incl_finite_valid_trace_from; [| done].
    by apply equivocators_fixed_equivocations_vlsm_incl_PreFree.
  - assert (Hpre_tr : finite_valid_trace (pre_loaded_with_all_messages_vlsm FreeE) sX trX).
    {
      apply VLSM_incl_finite_valid_trace; [| done].
      by apply equivocators_fixed_equivocations_vlsm_incl_PreFree.
    }
    specialize (VLSM_partial_projection_finite_valid_trace
      (fixed_equivocators_vlsm_partial_projection (zero_descriptor IM))
      sX trX (equivocators_state_project IM (zero_descriptor IM) sX)
      (equivocators_total_trace_project IM trX)) as Hsim.
    spec Hsim.
    { simpl. rewrite decide_True by apply zero_descriptor_not_equivocating.
      by rewrite (equivocators_total_trace_project_characterization IM (proj1 Hpre_tr)).
    }
    apply Hsim in HtrX.
    remember (pre_VLSM_projection_finite_trace_project _ _ _ _ _) as tr.
    replace tr with (equivocators_total_trace_project IM trX); [done |].
    subst. symmetry.
    by apply (equivocators_total_VLSM_projection_finite_trace_project IM (proj1 Hpre_tr)).
Qed.

End sec_from_equivocators_to_components.

Section sec_all_equivocating.

(** ** Fixed Equivocation for all Equivocators

  In this section we show that if the set of components allowed to equivocate in the
  fixed set equivocation is the entire set of components, then the composition
  under the fixed-set equivocation constraint is the same as the composition
  with only the no-message-equivocation constraint.
*)

Context
  {message : Type}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  `{forall i : index, HasBeenSentCapability (IM i)}
  (XE : VLSM message := equivocators_fixed_equivocations_vlsm IM (enum index))
  (NE : VLSM message := equivocators_no_equivocations_vlsm IM)
  .

Lemma strong_constraint_subsumption_fixed_all
  : strong_constraint_subsumption (free_composite_vlsm (equivocator_IM IM))
    (equivocators_no_equivocations_constraint IM)
    (equivocators_fixed_equivocations_constraint IM (enum index)).
Proof.
  by split; [| intro; intros; apply elem_of_enum].
Qed.

Lemma strong_constraint_subsumption_all_fixed
  : strong_constraint_subsumption (free_composite_vlsm (equivocator_IM IM))
    (equivocators_fixed_equivocations_constraint IM (enum index))
    (equivocators_no_equivocations_constraint IM).
Proof.
  by intros l [s om] Hv; apply Hv.
Qed.

Lemma equivocators_fixed_equivocations_all_eq : VLSM_eq XE NE.
Proof.
  split.
  - apply (constraint_subsumption_incl (free_composite_vlsm _)).
    apply preloaded_constraint_subsumption_stronger.
    apply strong_constraint_subsumption_strongest.
    by apply strong_constraint_subsumption_all_fixed.
  - apply
      (constraint_subsumption_incl (free_composite_vlsm (equivocator_IM IM))
        (equivocators_no_equivocations_constraint IM)
        (equivocators_fixed_equivocations_constraint IM (enum index))).
    apply preloaded_constraint_subsumption_stronger.
    apply strong_constraint_subsumption_strongest.
    by apply strong_constraint_subsumption_fixed_all.
Qed.

End sec_all_equivocating.
