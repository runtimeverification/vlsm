From Cdcl Require Import Itauto. Local Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude finite.
From Coq Require Import FinFun Lia Reals Lra.
From VLSM.Lib Require Import Preamble ListExtras StdppListSet ListSetExtras FinExtras FinFunExtras Measurable.
From VLSM Require Import Core.VLSM Core.VLSMProjections Core.Composition Core.ProjectionTraces Core.AnnotatedVLSM.
From VLSM Require Import Core.Equivocation Core.Equivocation.TraceWiseEquivocation.
From VLSM Require Import Core.Equivocation.NoEquivocation Core.Equivocation.LimitedEquivocation Core.Equivocation.MsgDepLimitedEquivocation.
From VLSM Require Import Core.Equivocators.Common Core.Equivocators.Projections.
From VLSM Require Import Core.Equivocators.MessageProperties Core.Equivocators.Composition.Common.
From VLSM Require Import Core.Equivocators.Composition.Projections Core.MessageDependencies.
From VLSM Require Import Core.Equivocators.Composition.LimitedEquivocation.FixedEquivocation.

(** * VLSM Limited Equivocation *)
Definition composite_constraint
  {index message} (IM : index -> VLSM message) : Type :=
  composite_label IM -> composite_state IM * option message -> Prop.

Lemma equivocator_initial_state_project
  {message}
  (X : VLSM message)
  (es : vstate (equivocator_vlsm X))
  (eqv_descriptor: MachineDescriptor X)
  (Heqv: proper_descriptor X eqv_descriptor es)
  (Hes: vinitial_state_prop (equivocator_vlsm X) es):
  vinitial_state_prop X (equivocator_state_descriptor_project es eqv_descriptor).
Proof.
  destruct eqv_descriptor;[exact Heqv|].
  destruct Heqv as [esn Hesn].
  simpl. rewrite Hesn.
  apply equivocator_vlsm_initial_state_preservation_rev with es n; assumption.
Qed.

Lemma composite_equivocators_initial_state_project
  {message}
  `{EqDecision index}
  (IM : index -> VLSM message)
  (es : composite_state (equivocator_IM IM))
  (eqv_descriptors : equivocator_descriptors IM)
  {eqv_constraint: composite_constraint (equivocator_IM IM)}
  {constraint: composite_constraint IM}
  (Heqv : proper_equivocator_descriptors IM eqv_descriptors es)
  (Hes : vinitial_state_prop (composite_vlsm (equivocator_IM IM) eqv_constraint) es)
  : vinitial_state_prop (composite_vlsm IM constraint) (equivocators_state_project IM eqv_descriptors es).
Proof.
  refine (fun i => equivocator_initial_state_project _ _ _ (Heqv i) (Hes i)).
Qed.

Section limited_state_equivocation.

Context {message : Type}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  `{forall i : index, HasBeenSentCapability (IM i)}
  `{forall i : index, HasBeenReceivedCapability (IM i)}
  (Free := free_composite_vlsm IM)
  (equivocator_descriptors := equivocator_descriptors IM)
  (equivocators_state_project := equivocators_state_project IM)
  (equivocator_IM := equivocator_IM IM)
  (equivocator_descriptors_update := equivocator_descriptors_update IM)
  (proper_equivocator_descriptors := proper_equivocator_descriptors IM)
  (sender : message -> option index)
  `{ReachableThreshold index}
  (Heqv_idx_BasicEquivocation : BasicEquivocation (composite_state equivocator_IM) index
    := equivocating_indices_BasicEquivocation IM)
  (FreeE : VLSM message := free_composite_vlsm equivocator_IM)
  (PreFreeE := pre_loaded_with_all_messages_vlsm FreeE)
  (not_heavy := @not_heavy _ _ _ _ Heqv_idx_BasicEquivocation)
  (equivocating_validators := @equivocating_validators _ _ _ _ Heqv_idx_BasicEquivocation)
  (equivocation_fault := @equivocation_fault _ _ _ _ Heqv_idx_BasicEquivocation)
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
  apply constraint_subsumption_incl.
  intro; intros. exact I.
Qed.

(** Inclusion in the preloaded free composition. *)
Lemma equivocators_limited_equivocations_vlsm_incl_preloaded_free
  : VLSM_incl equivocators_limited_equivocations_vlsm PreFreeE.
Proof.
  specialize equivocators_limited_equivocations_vlsm_incl_free as Hincl1.
  specialize (vlsm_incl_pre_loaded_with_all_messages_vlsm FreeE)
    as Hincl2.
  revert Hincl1 Hincl2.
  apply VLSM_incl_trans.
Qed.

(** Inclusion of preloaded machine in the preloaded free composition. *)
Lemma preloaded_equivocators_limited_equivocations_vlsm_incl_free
  : VLSM_incl (pre_loaded_with_all_messages_vlsm equivocators_limited_equivocations_vlsm) PreFreeE.
Proof.
  apply basic_VLSM_incl_preloaded; intros ? *.
  1, 3: itauto.
  intros [Hv _]. split; [assumption|exact I].
Qed.

(**
Inclusion in the composition of equivocators with no message equivocation
(no restriction on state equivocation).
*)
Lemma equivocators_limited_equivocations_vlsm_incl_no_equivocations
  : VLSM_incl equivocators_limited_equivocations_vlsm (equivocators_no_equivocations_vlsm IM).
Proof.
  apply constraint_subsumption_incl.
  intros l (s,om) (_ & _ & _ & Hc & _). assumption.
Qed.

(** A valid state for a VLSM satisfying the limited equivocation assumption
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
      equivocation_fault, Equivocation.equivocation_fault.
    replace (Equivocation.equivocating_validators is) with (@nil index).
    + destruct threshold as [t Ht]. simpl. apply Rge_le. assumption.
    + symmetry. apply set_eq_empty_iff.
      specialize (equivocating_indices_equivocating_validators IM is).
      rewrite equivocating_indices_initially_empty; [|assumption].
      intro. assumption.
  - replace s with
    (fst (composite_transition equivocator_IM l (s0, oim))); [assumption|].
    by simpl in *; rewrite Ht.
Qed.

(** A valid valid trace for the composition of equivocators with limited
state-equivocation and no message-equivocation is also a valid valid trace
for the composition of equivocators with no message-equivocation and fixed-set
state-equivocation, where the fixed set is given by the state-equivocators
measured for the final state of the trace.
*)
Lemma equivocators_limited_valid_trace_is_fixed is s tr
  : finite_valid_trace_init_to equivocators_limited_equivocations_vlsm is s tr ->
  finite_valid_trace_init_to
   (equivocators_fixed_equivocations_vlsm IM (equivocating_validators s))
   is s tr.
Proof.
  intro Htr.
  split; [| exact (proj2  Htr)].
  cut
    (forall equivocating, equivocating_validators s ⊆ equivocating ->
      finite_valid_trace_from_to (equivocators_fixed_equivocations_vlsm IM equivocating) is s tr).
  { by intros H'; apply H'. }
  induction Htr using finite_valid_trace_init_to_rev_ind; intros equivocating Hincl.
  - apply (finite_valid_trace_from_to_empty (equivocators_fixed_equivocations_vlsm IM equivocating)).
    apply initial_state_is_valid. assumption.
  - specialize (equivocating_indices_equivocating_validators IM)
      as Heq.
    destruct (Heq sf) as [_ Hsf_incl].
    specialize (IHHtr equivocating).
    spec IHHtr.
    { apply proj2 in Ht.
      specialize (equivocators_transition_preserves_equivocating_indices IM (enum index)  _ _ _ _ _ Ht)
        as Hincl'.
      clear -Hincl Hincl' Heq Hsf_incl.
      specialize (Heq s) as [Hincl_s _].
      transitivity (equivocating_validators sf); [|assumption].
      transitivity (equivocating_indices IM (enum index) sf); [|assumption].
      transitivity (equivocating_indices IM (enum index) s); assumption.
    }
    apply
      (finite_valid_trace_from_to_app
        (equivocators_fixed_equivocations_vlsm IM equivocating))
      with s; [assumption|].
    apply valid_trace_add_last; [| done].
      apply (finite_valid_trace_singleton (equivocators_fixed_equivocations_vlsm IM equivocating)).
      apply valid_trace_last_pstate in IHHtr.
      destruct Ht as [[_ [_ [Hv [[Hno_equiv _] Hno_heavy]]]] Ht].
      repeat split; [assumption| |assumption|assumption| |assumption].
      + destruct iom as [m|]; [|apply option_valid_message_None].
        destruct Hno_equiv as [Hsent | Hfalse]; [| done].
        simpl in Hsent.
        eapply composite_sent_valid; eassumption.
      + replace (composite_transition _ _ _) with (sf, oom).
        unfold state_has_fixed_equivocation.
        transitivity (equivocating_validators sf); assumption.
Qed.

(** Projections of valid traces for the composition of equivocators
with limited state-equivocation and no message-equivocation have the
[fixed_limited_equivocation_prop]erty.
*)
Lemma equivocators_limited_valid_trace_projects_to_fixed_limited_equivocation
  (final_descriptors : equivocator_descriptors)
  (is : composite_state equivocator_IM)
  (tr : list (composite_transition_item equivocator_IM))
  (final_state := finite_trace_last is tr)
  (Hproper: not_equivocating_equivocator_descriptors IM final_descriptors final_state)
  (Htr : finite_valid_trace equivocators_limited_equivocations_vlsm is tr)
  : exists
    (trX : list (composite_transition_item IM))
    (initial_descriptors : equivocator_descriptors)
    (isX := equivocators_state_project initial_descriptors is)
    (final_stateX := finite_trace_last isX trX),
    proper_equivocator_descriptors initial_descriptors is /\
    equivocators_trace_project IM final_descriptors tr = Some (trX, initial_descriptors) /\
    equivocators_state_project final_descriptors final_state = final_stateX /\
    fixed_limited_equivocation_prop IM isX trX.
Proof.
  apply valid_trace_add_default_last in Htr as Hfixed_tr.
  apply equivocators_limited_valid_trace_is_fixed in Hfixed_tr.
  apply valid_trace_last_pstate in Hfixed_tr as Hfixed_last.
  apply valid_trace_forget_last in Hfixed_tr.
  specialize
    (fixed_equivocators_valid_trace_project IM (equivocating_validators (finite_trace_last is tr))
      final_descriptors is tr) as Hpr.
  feed specialize Hpr; [| assumption |].
  - eapply not_equivocating_equivocator_descriptors_proper_fixed; eassumption.
  - destruct Hpr as [trX [initial_descriptors [Hinitial_descriptors [Hpr [Hlst_pr Hpr_fixed]]]]].
    exists trX, initial_descriptors.
    repeat split; try assumption.
    + apply Hinitial_descriptors.
    + exists (equivocating_validators (finite_trace_last is tr)).
      split; [| assumption].
      apply valid_trace_add_default_last, valid_trace_last_pstate, valid_state_limited_equivocation in Htr.
      transitivity (equivocation_fault (finite_trace_last is tr)); [|assumption].
      specialize (equivocating_indices_equivocating_validators IM
                   (finite_trace_last is tr)) as Heq.
      apply sum_weights_subseteq.
      * apply NoDup_remove_dups.
      * apply equivocating_validators_nodup.
      * intros i Hi. apply elem_of_remove_dups. assumption.
Qed.

Section sec_equivocators_projection_annotated_limited.

Context
  (message_dependencies : message -> set message)
  (HMsgDep : forall i, MessageDependencies message_dependencies (IM i))
  (full_message_dependencies : message -> set message)
  (HFullMsgDep : FullMessageDependencies message_dependencies full_message_dependencies)
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  (Hchannel : channel_authentication_prop IM Datatypes.id sender)
  .

(** Projections of valid traces for the composition of equivocators
with limited state-equivocation and no message-equivocation can be
annotated with equivocators to obtain a limited-message equivocation trace.
*)
Lemma equivocators_limited_valid_trace_projects_to_annotated_limited_equivocation
  (final_descriptors : equivocator_descriptors)
  (is : composite_state equivocator_IM)
  (tr : list (composite_transition_item equivocator_IM))
  (final_state := finite_trace_last is tr)
  (Hproper: not_equivocating_equivocator_descriptors IM final_descriptors final_state)
  (Htr : finite_valid_trace equivocators_limited_equivocations_vlsm is tr)
  : exists
    (trX : list (composite_transition_item IM))
    (initial_descriptors : equivocator_descriptors)
    (isX := equivocators_state_project initial_descriptors is)
    (final_stateX := finite_trace_last isX trX),
    proper_equivocator_descriptors initial_descriptors is /\
    equivocators_trace_project IM final_descriptors tr = Some (trX, initial_descriptors) /\
    equivocators_state_project final_descriptors final_state = final_stateX /\
    finite_valid_trace (msg_dep_limited_equivocation_vlsm IM full_message_dependencies sender)
      {| original_state := isX; state_annotation := ` inhabitant |}
      (msg_dep_annotate_trace_with_equivocators IM full_message_dependencies sender isX trX).
Proof.
  eapply equivocators_limited_valid_trace_projects_to_fixed_limited_equivocation
      in Htr as (trX & initial_descriptors & Hinitial_descriptors & Hpr & Hlst_pr & Hpr_limited)
  ; [| eassumption].
  exists trX, initial_descriptors.
  cbn; split_and?; try itauto.
  eapply msg_dep_limited_fixed_equivocation; eassumption.
Qed.

End sec_equivocators_projection_annotated_limited.

Section sec_equivocators_projection_constrained_limited.

Context
  `{RelDecision _ _ (is_equivocating_tracewise_no_has_been_sent IM (fun i => i) sender)}
  (Limited : VLSM message := limited_equivocation_vlsm_composition IM sender)
  (Hsender_safety : sender_safety_alt_prop IM (fun i => i) sender)
  (message_dependencies : message -> set message)
  (Hfull : forall i, message_dependencies_full_node_condition_prop message_dependencies (IM i))
  .

(** If each of the nodes satisfy the [message_dependencies_full_node_condition_prop]erty,
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
  (Hproper: not_equivocating_equivocator_descriptors IM final_descriptors final_state)
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
  repeat split; [assumption..| |].
  - eapply traces_exhibiting_limited_equivocation_are_valid; eassumption.
  - destruct Hpr_limited as [equivs Hpr_limited]. apply Hpr_limited.
Qed.

(** The above result formalized as a relation between the corresponding
composite VLSMs. It yields a [VLSM_partial_projection] because for invalid
[equivocator_descriptors] one might not be able to obtain a trace projection.
*)
Lemma limited_equivocators_vlsm_partial_projection
  (final_descriptors : equivocator_descriptors)
  : VLSM_partial_projection equivocators_limited_equivocations_vlsm Limited (equivocators_partial_trace_project IM final_descriptors).
Proof.
  split; [split|].
  - intros s tr sX trX Hpr_tr s_pre pre Hs_lst Hpre_tr.
    assert
      (HPreFree_pre_tr : finite_valid_trace_from (pre_loaded_with_all_messages_vlsm FreeE) s_pre (pre ++ tr)).
    { revert Hpre_tr. apply VLSM_incl_finite_valid_trace_from.
      apply equivocators_limited_equivocations_vlsm_incl_preloaded_free.
    }
    clear Hpre_tr.  revert s tr sX trX Hpr_tr s_pre pre Hs_lst HPreFree_pre_tr.
    apply equivocators_partial_trace_project_extends_left.
  - intros s tr sX trX Hpr_tr Htr.
    destruct (destruct_equivocators_partial_trace_project IM Hpr_tr)
      as [Hnot_equiv [initial_descriptors [Htr_project Hs_project]]].

    destruct (limited_equivocators_valid_trace_project _ _ _ Hnot_equiv Htr)
      as (_trX & _initial_descriptors & _ & _Htr_project & _ & HtrX).
    rewrite Htr_project in _Htr_project.
    inversion _Htr_project. subst.  assumption.
Qed.

(** In the case of using the original machine copy for projecting each node, we
are guaranteed to obtain a trace projection for each trace, hence the relation
above strengthens to a [VLSM_projection].
*)
Lemma limited_equivocators_vlsm_projection
  : VLSM_projection equivocators_limited_equivocations_vlsm Limited
    (equivocators_total_label_project IM) (equivocators_total_state_project IM).
Proof.
  constructor; [constructor|]; intros ? *.
  - intros HtrX. apply PreFreeE_Free_vlsm_projection_type.
    revert HtrX. apply VLSM_incl_finite_valid_trace_from.
    apply equivocators_limited_equivocations_vlsm_incl_preloaded_free.
  - intro HtrX. assert (Hpre_tr : finite_valid_trace (pre_loaded_with_all_messages_vlsm FreeE) sX trX).
    { revert HtrX. apply VLSM_incl_finite_valid_trace.
      apply equivocators_limited_equivocations_vlsm_incl_preloaded_free.
    }
    specialize
     (VLSM_partial_projection_finite_valid_trace (limited_equivocators_vlsm_partial_projection (zero_descriptor IM))
       sX trX (equivocators_state_project (zero_descriptor IM) sX) (equivocators_total_trace_project IM trX))
       as Hsim.
    spec Hsim.
    { simpl. rewrite decide_True by apply zero_descriptor_not_equivocating.
      by rewrite (equivocators_total_trace_project_characterization IM (proj1 Hpre_tr)).
    }
    apply Hsim in HtrX.
    remember (pre_VLSM_projection_trace_project _ _ _ _ _) as tr.
    replace tr with (equivocators_total_trace_project IM trX); [assumption|].
    subst. symmetry.
    apply (equivocators_total_VLSM_projection_trace_project IM (proj1 Hpre_tr)).
Qed.

End sec_equivocators_projection_constrained_limited.

End limited_state_equivocation.
