From VLSM.Lib Require Import Itauto.
From stdpp Require Import prelude finite.
From Coq Require Import FinFun Reals Lra.
From VLSM.Lib Require Import Preamble Measurable RealsExtras FinSetExtras.
From VLSM.Core Require Import VLSM VLSMProjections Composition AnnotatedVLSM.
From VLSM.Core Require Import Equivocation Equivocation.TraceWiseEquivocation MessageDependencies.
From VLSM.Core Require Import Equivocation.NoEquivocation Equivocation.LimitedMessageEquivocation.
From VLSM.Core Require Import FixedSetEquivocation MsgDepLimitedEquivocation.
From VLSM.Core Require Import Equivocators.Equivocators.
From VLSM.Core Require Import Equivocators.MessageProperties.
From VLSM.Core Require Import Equivocators.EquivocatorsComposition.
From VLSM.Core Require Import Equivocators.EquivocatorsCompositionProjections.
From VLSM.Core Require Import Equivocators.LimitedEquivocation.FixedEquivocation.

(** * VLSM Limited Equivocation *)
Definition composite_constraint
  {index message} (IM : index -> VLSM message) : Type :=
  composite_label IM -> composite_state IM * option message -> Prop.

Lemma equivocator_initial_state_project
  {message}
  (X : VLSM message)
  (es : vstate (equivocator_vlsm X))
  (eqv_descriptor : MachineDescriptor X)
  (Heqv : proper_descriptor X eqv_descriptor es)
  (Hes : vinitial_state_prop (equivocator_vlsm X) es) :
  vinitial_state_prop X (equivocator_state_descriptor_project es eqv_descriptor).
Proof.
  destruct eqv_descriptor; [done |].
  destruct Heqv as [esn Hesn].
  simpl. rewrite Hesn.
  by eapply equivocator_vlsm_initial_state_preservation_rev.
Qed.

Lemma composite_equivocators_initial_state_project
  {message}
  `{EqDecision index}
  (IM : index -> VLSM message)
  (es : composite_state (equivocator_IM IM))
  (eqv_descriptors : equivocator_descriptors IM)
  {eqv_constraint : composite_constraint (equivocator_IM IM)}
  {constraint : composite_constraint IM}
  (Heqv : proper_equivocator_descriptors IM eqv_descriptors es)
  (Hes : vinitial_state_prop (composite_vlsm (equivocator_IM IM) eqv_constraint) es)
  : vinitial_state_prop (composite_vlsm IM constraint)
      (equivocators_state_project IM eqv_descriptors es).
Proof.
  refine (fun i => equivocator_initial_state_project _ _ _ (Heqv i) (Hes i)).
Qed.

Section sec_limited_state_equivocation.

Context {message index : Type}
  (IM : index -> VLSM message)
  `{forall i : index, HasBeenSentCapability (IM i)}
  `{forall i : index, HasBeenReceivedCapability (IM i)}
  (threshold : R)
  `{ReachableThreshold index Ci threshold}
  `{!finite.Finite index}
  (Free := free_composite_vlsm IM)
  (equivocator_descriptors := equivocator_descriptors IM)
  (equivocators_state_project := equivocators_state_project IM)
  (equivocator_IM := equivocator_IM IM)
  (equivocator_descriptors_update := equivocator_descriptors_update IM)
  (proper_equivocator_descriptors := proper_equivocator_descriptors IM)
  (sender : message -> option index)
  (Heqv_idx_BasicEquivocation : BasicEquivocation (composite_state equivocator_IM) index Ci threshold
    := equivocating_indices_BasicEquivocation IM threshold)
  (FreeE : VLSM message := free_composite_vlsm equivocator_IM)
  (PreFreeE := pre_loaded_with_all_messages_vlsm FreeE)
  (not_heavy := not_heavy (1 := Heqv_idx_BasicEquivocation))
  (equivocating_validators := equivocating_validators (1 := Heqv_idx_BasicEquivocation))
  (equivocation_fault := equivocation_fault (1 := Heqv_idx_BasicEquivocation))
  .

Definition equivocators_limited_equivocations_constraint
  (l : composite_label equivocator_IM)
  (som : composite_state equivocator_IM * option message)
  (som' := composite_transition equivocator_IM l som)
  : Prop
  := equivocators_no_equivocations_constraint IM l som
  /\ not_heavy (fst som').

Definition equivocators_limited_equivocations_vlsm
  : VLSM message
  :=
  composite_vlsm equivocator_IM equivocators_limited_equivocations_constraint.

(** Inclusion in the free composition. *)
Lemma equivocators_limited_equivocations_vlsm_incl_free
  : VLSM_incl equivocators_limited_equivocations_vlsm FreeE.
Proof.
  by apply constraint_subsumption_incl.
Qed.

(** Inclusion in the preloaded free composition. *)
Lemma equivocators_limited_equivocations_vlsm_incl_preloaded_free
  : VLSM_incl equivocators_limited_equivocations_vlsm PreFreeE.
Proof.
  specialize equivocators_limited_equivocations_vlsm_incl_free as Hincl1.
  specialize (vlsm_incl_pre_loaded_with_all_messages_vlsm FreeE)
    as Hincl2.
  by eapply VLSM_incl_trans.
Qed.

(** Inclusion of preloaded machine in the preloaded free composition. *)
Lemma preloaded_equivocators_limited_equivocations_vlsm_incl_free
  : VLSM_incl (pre_loaded_with_all_messages_vlsm equivocators_limited_equivocations_vlsm) PreFreeE.
Proof.
  by apply basic_VLSM_incl_preloaded; intros ? *; [intro | inversion 1 | intro].
Qed.

(**
  Inclusion in the composition of equivocators with no message equivocation
  (no restriction on state equivocation).
*)
Lemma equivocators_limited_equivocations_vlsm_incl_no_equivocations
  : VLSM_incl equivocators_limited_equivocations_vlsm (equivocators_no_equivocations_vlsm IM).
Proof.
  apply constraint_subsumption_incl.
  by intros l [s om] (_ & _ & _ & Hc & _).
Qed.

(**
  A valid state for a VLSM satisfying the limited equivocation assumption
  has limited equivocation.
*)
Lemma valid_state_limited_equivocation
  (s : composite_state equivocator_IM)
  (Hs : valid_state_prop equivocators_limited_equivocations_vlsm s)
  : not_heavy s.
Proof.
  apply valid_state_prop_iff in Hs.
  destruct Hs as [[(is, His) Heq_s] | [l [(s0, oim) [oom' [[_ [_ [_ [_ Hlimited]]]] Ht]]]]].
  - subst s.
    unfold not_heavy, Equivocation.not_heavy,
      equivocation_fault, Equivocation.equivocation_fault; simpl.
    pose proof (Heqv_is := @equivocating_indices_equivocating_validators _ _ _ _
        IM _ _ _ H1 _ _ _ _ _ _ _ _ H9 is).
    rewrite equivocating_indices_initially_empty in Heqv_is by done.
    simpl in Heqv_is; apply sum_weights_empty in Heqv_is.
    pose proof (rt_positive (H6 := H8)).
    by cbv in Heqv_is |- *; lra.
  - by replace s with (fst (composite_transition equivocator_IM l (s0, oim))); [done |]
    ; cbn in *; rewrite Ht.
Qed.

(**
  A valid valid trace for the composition of equivocators with limited
  state-equivocation and no message-equivocation is also a valid valid trace
  for the composition of equivocators with no message-equivocation and fixed-set
  state-equivocation, where the fixed set is given by the state-equivocators
  measured for the final state of the trace.
*)
Lemma equivocators_limited_valid_trace_is_fixed is s tr
  : finite_valid_trace_init_to equivocators_limited_equivocations_vlsm is s tr ->
  finite_valid_trace_init_to
   (equivocators_fixed_equivocations_vlsm IM (elements(equivocating_validators s)))
   is s tr.
Proof.
  intro Htr.
  split; [| apply Htr].
  cut
    (forall equivocating, elements(equivocating_validators s) ⊆ equivocating ->
      finite_valid_trace_from_to (equivocators_fixed_equivocations_vlsm IM equivocating) is s tr);
    [by intros H'; apply H' |].
  induction Htr using finite_valid_trace_init_to_rev_ind; intros equivocating Hincl.
  - apply (finite_valid_trace_from_to_empty (equivocators_fixed_equivocations_vlsm IM equivocating)).
    by apply initial_state_is_valid.
  - specialize (IHHtr equivocating).
    spec IHHtr.
    { apply proj2 in Ht.
      specialize (equivocators_transition_preserves_equivocating_indices
        IM (enum index)  _ _ _ _ _ Ht) as Hincl'.
      clear -Hincl Hincl'.
      transitivity (elements (equivocating_validators sf)); [| done].
      intro x; rewrite! elem_of_elements; intro Hx.
      apply equivocating_indices_equivocating_validators, elem_of_list_to_set, Hincl'.
      by apply equivocating_indices_equivocating_validators, elem_of_list_to_set in Hx.
    }
    apply
      (finite_valid_trace_from_to_app
        (equivocators_fixed_equivocations_vlsm IM equivocating))
      with s; [done |].
    apply valid_trace_add_last; [| done].
      apply (finite_valid_trace_singleton (equivocators_fixed_equivocations_vlsm IM equivocating)).
      apply valid_trace_last_pstate in IHHtr.
      destruct Ht as [[_ [_ [Hv [[Hno_equiv _] Hno_heavy]]]] Ht].
      repeat split; [done | | done | done | | done].
      + destruct iom as [m |]; [| by apply option_valid_message_None].
        destruct Hno_equiv as [Hsent | Hfalse]; [| done].
        simpl in Hsent.
        by eapply composite_sent_valid.
      + replace (composite_transition _ _ _) with (sf, oom).
        unfold state_has_fixed_equivocation.
        transitivity (elements (equivocating_validators sf)); [| done].
        by intros x Hx; apply elem_of_elements, equivocating_indices_equivocating_validators,
          elem_of_list_to_set.
Qed.

(**
  Projections of valid traces for the composition of equivocators
  with limited state-equivocation and no message-equivocation have the
  [fixed_limited_equivocation_prop]erty.
*)
Lemma equivocators_limited_valid_trace_projects_to_fixed_limited_equivocation
  (final_descriptors : equivocator_descriptors)
  (is : composite_state equivocator_IM)
  (tr : list (composite_transition_item equivocator_IM))
  (final_state := finite_trace_last is tr)
  (Hproper : not_equivocating_equivocator_descriptors IM final_descriptors final_state)
  (Htr : finite_valid_trace equivocators_limited_equivocations_vlsm is tr)
  : exists
    (trX : list (composite_transition_item IM))
    (initial_descriptors : equivocator_descriptors)
    (isX := equivocators_state_project initial_descriptors is)
    (final_stateX := finite_trace_last isX trX),
    proper_equivocator_descriptors initial_descriptors is /\
    equivocators_trace_project IM final_descriptors tr = Some (trX, initial_descriptors) /\
    equivocators_state_project final_descriptors final_state = final_stateX /\
    fixed_limited_equivocation_prop (Cv := Ci) (Ci := Ci) IM threshold Datatypes.id isX trX.
Proof.
  apply valid_trace_add_default_last in Htr as Hfixed_tr.
  apply equivocators_limited_valid_trace_is_fixed in Hfixed_tr.
  apply valid_trace_last_pstate in Hfixed_tr as Hfixed_last.
  apply valid_trace_forget_last in Hfixed_tr.
  specialize (fixed_equivocators_valid_trace_project IM
    (equivocating_validators (finite_trace_last is tr)) final_descriptors is tr) as Hpr.
  feed specialize Hpr; [| done |].
  - by eapply not_equivocating_equivocator_descriptors_proper_fixed.
  - destruct Hpr as (trX & initial_descriptors & Hinitial_descriptors & Hpr & Hlst_pr & Hpr_fixed).
    exists trX, initial_descriptors.
    split_and!; [by apply Hinitial_descriptors | done | done |].
    exists (equivocating_validators (finite_trace_last is tr)).
    split.
    + apply valid_trace_add_default_last, valid_trace_last_pstate,
        valid_state_limited_equivocation in Htr.
      transitivity (equivocation_fault (finite_trace_last is tr)); [| done].
      by unfold equivocation_fault; apply sum_weights_subseteq.
    + revert Hpr_fixed.
      apply VLSM_incl_finite_valid_trace, constraint_subsumption_incl.
      apply preloaded_constraint_subsumption_stronger, strong_constraint_subsumption_strongest.
      intros l (s, [m |]); [| done]; cbn.
      intros [| Hemit]; [by left |].
      right; revert Hemit.
      unshelve eapply VLSM_embedding_can_emit, equivocators_composition_for_directly_observed_index_incl_embedding.
      apply elements_subseteq.
      by intros v Hv; apply elem_of_map; eexists.
Qed.

Section sec_equivocators_projection_annotated_limited.

Context
  `{FinSet message Cm}
  (message_dependencies : message -> Cm)
  (full_message_dependencies : message -> Cm)
  (HFullMsgDep : FullMessageDependencies message_dependencies full_message_dependencies)
  (HMsgDep : forall i, MessageDependencies (IM i) message_dependencies)
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  (Hchannel : channel_authentication_prop IM Datatypes.id sender)
  .

(**
  Projections of valid traces for the composition of equivocators
  with limited state-equivocation and no message-equivocation can be
  annotated with equivocators to obtain a limited-message equivocation trace.
*)
Lemma equivocators_limited_valid_trace_projects_to_annotated_limited_equivocation
  (final_descriptors : equivocator_descriptors)
  (is : composite_state equivocator_IM)
  (tr : list (composite_transition_item equivocator_IM))
  (final_state := finite_trace_last is tr)
  (Hproper : not_equivocating_equivocator_descriptors IM final_descriptors final_state)
  (Htr : finite_valid_trace equivocators_limited_equivocations_vlsm is tr)
  : exists
    (trX : list (composite_transition_item IM))
    (initial_descriptors : equivocator_descriptors)
    (isX := equivocators_state_project initial_descriptors is)
    (final_stateX := finite_trace_last isX trX),
    proper_equivocator_descriptors initial_descriptors is /\
    equivocators_trace_project IM final_descriptors tr = Some (trX, initial_descriptors) /\
    equivocators_state_project final_descriptors final_state = final_stateX /\
    finite_valid_trace (msg_dep_limited_equivocation_vlsm IM threshold full_message_dependencies sender (Cv := Ci))
      {| original_state := isX; state_annotation := ` inhabitant |}
      (msg_dep_annotate_trace_with_equivocators IM full_message_dependencies sender isX trX).
Proof.
  eapply equivocators_limited_valid_trace_projects_to_fixed_limited_equivocation
      in Htr as (trX & initial_descriptors & Hinitial_descriptors & Hpr & Hlst_pr & Hpr_limited)
  ; [| done].
  exists trX, initial_descriptors.
  cbn; split_and!; [itauto.. |].
  by eapply @msg_dep_limited_fixed_equivocation; [| | | typeclasses eauto |..].
Qed.

End sec_equivocators_projection_annotated_limited.

Section sec_equivocators_projection_constrained_limited.

Context
  `{FinSet message Cm}
  `{RelDecision _ _ (is_equivocating_tracewise_no_has_been_sent IM Datatypes.id sender)}
  (Limited : VLSM message := tracewise_limited_equivocation_vlsm_composition IM (Cv := Ci) threshold Datatypes.id sender)
  (Hsender_safety : sender_safety_alt_prop IM Datatypes.id sender)
  (message_dependencies : message -> Cm)
  (Hfull : forall i, message_dependencies_full_node_condition_prop (IM i) message_dependencies)
  .

(**
  If each of the nodes satisfy the [message_dependencies_full_node_condition_prop]erty,
  then projections of valid traces for the composition of equivocators
  with limited state-equivocation and no message-equivocation are also valid
  traces for the composition of regular nodes with limited
  message-equivocation.
*)
Lemma limited_equivocators_valid_trace_project
  (final_descriptors : equivocator_descriptors)
  (is : composite_state equivocator_IM)
  (tr : list (composite_transition_item equivocator_IM))
  (final_state := finite_trace_last is tr)
  (Hproper : not_equivocating_equivocator_descriptors IM final_descriptors final_state)
  (Htr : finite_valid_trace equivocators_limited_equivocations_vlsm is tr)
  : exists
    (trX : list (composite_transition_item IM))
    (initial_descriptors : equivocator_descriptors)
    (isX := equivocators_state_project initial_descriptors is)
    (final_stateX := finite_trace_last isX trX),
    proper_equivocator_descriptors initial_descriptors is /\
    equivocators_trace_project IM final_descriptors tr = Some (trX, initial_descriptors) /\
    equivocators_state_project final_descriptors final_state = final_stateX /\
    finite_valid_trace Limited isX trX.
Proof.
  specialize
    (equivocators_limited_valid_trace_projects_to_fixed_limited_equivocation
      final_descriptors is tr Hproper Htr)
      as [trX [initial_descriptors [Hinitial_descriptors [Hpr [Hlst_pr Hpr_limited]]]]].
  exists trX, initial_descriptors.
  repeat split; [done.. | |].
  - by eapply @traces_exhibiting_limited_equivocation_are_valid; [| | typeclasses eauto | |].
  - by destruct Hpr_limited as [equivs Hpr_limited]; apply Hpr_limited.
Qed.

(**
  The above result formalized as a relation between the corresponding
  composite VLSMs. It yields a [VLSM_partial_projection] because for invalid
  [equivocator_descriptors] one might not be able to obtain a trace projection.
*)
Lemma limited_equivocators_vlsm_partial_projection
  (final_descriptors : equivocator_descriptors)
  : VLSM_partial_projection equivocators_limited_equivocations_vlsm Limited
      (equivocators_partial_trace_project IM final_descriptors).
Proof.
  split; [split |].
  - intros s tr sX trX Hpr_tr s_pre pre Hs_lst Hpre_tr.
    assert (HPreFree_pre_tr :
      finite_valid_trace_from (pre_loaded_with_all_messages_vlsm FreeE) s_pre (pre ++ tr)).
    {
      revert Hpre_tr; apply VLSM_incl_finite_valid_trace_from.
      by apply equivocators_limited_equivocations_vlsm_incl_preloaded_free.
    }
    clear Hpre_tr.  revert s tr sX trX Hpr_tr s_pre pre Hs_lst HPreFree_pre_tr.
    by apply equivocators_partial_trace_project_extends_left.
  - intros s tr sX trX Hpr_tr Htr.
    destruct (destruct_equivocators_partial_trace_project IM Hpr_tr)
      as [Hnot_equiv [initial_descriptors [Htr_project Hs_project]]].

    destruct (limited_equivocators_valid_trace_project _ _ _ Hnot_equiv Htr)
      as (_trX & _initial_descriptors & _ & _Htr_project & _ & HtrX).
    rewrite Htr_project in _Htr_project.
    by inversion _Htr_project; subst.
Qed.

(**
  In the case of using the original machine copy for projecting each node, we
  are guaranteed to obtain a trace projection for each trace, hence the relation
  above strengthens to a [VLSM_projection].
*)
Lemma limited_equivocators_vlsm_projection
  : VLSM_projection equivocators_limited_equivocations_vlsm Limited
    (equivocators_total_label_project IM) (equivocators_total_state_project IM).
Proof.
  constructor; [constructor |]; intros ? *.
  - intros HtrX. apply PreFreeE_Free_vlsm_projection_type.
    revert HtrX. apply VLSM_incl_finite_valid_trace_from.
    by apply equivocators_limited_equivocations_vlsm_incl_preloaded_free.
  - intro HtrX.
    assert (Hpre_tr : finite_valid_trace (pre_loaded_with_all_messages_vlsm FreeE) sX trX).
    {
      revert HtrX; apply VLSM_incl_finite_valid_trace.
      by apply equivocators_limited_equivocations_vlsm_incl_preloaded_free.
    }
    specialize (VLSM_partial_projection_finite_valid_trace
      (limited_equivocators_vlsm_partial_projection (zero_descriptor IM))
       sX trX (equivocators_state_project (zero_descriptor IM) sX)
       (equivocators_total_trace_project IM trX))
       as Hsim.
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

End sec_equivocators_projection_constrained_limited.

End sec_limited_state_equivocation.
