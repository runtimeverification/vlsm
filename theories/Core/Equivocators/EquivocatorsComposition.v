From VLSM.Lib Require Import Itauto.
From stdpp Require Import prelude finite.
From Coq Require Import FinFun FunctionalExtensionality Reals.
From VLSM.Lib Require Import Preamble ListSetExtras StdppExtras.
From VLSM.Lib Require Import NatExtras Measurable.
From VLSM.Core Require Import VLSM VLSMProjections Plans Composition Equivocation.
From VLSM.Core Require Import SubProjectionTraces.
From VLSM.Core Require Import Equivocation.NoEquivocation.
From VLSM.Core Require Import Equivocators.Equivocators.
From VLSM.Core Require Import Equivocators.MessageProperties.

(** * Core: VLSM Equivocator Composition

  Given a composition <<X>> of VLSMs, we can model equivocator behavior by
  creating an _equivocator composition_ which replaces each component of <<X>>
  with its equivocator version and strengthens the composition constraint to
  allow no (additional) equivocations, that is, all messages being received
  must have been previously sent by one of the (equivocator) VLSMs in the
  composition.
*)

(** ** Extracting equivocator traces from equivocator composition traces

  To recover the equivocator trace for the regular composition <<X>> from
  the traces of the equivocator composition, we'll assume that only the
  first state copy of each machine is observable in the composition
  and we ignore the activity corresponding to any other state copy,
  including the forks.

  This amounts to removing from the trace all transitions in which the
  state copy index is not 1, forgetting the additional components of
  the label, and keeping only the copy of index 1 for each machine.
*)

Section sec_fully_equivocating_composition.

Context
  {message : Type}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  `{forall i : index, HasBeenSentCapability (IM i)}
  `{forall i : index, HasBeenReceivedCapability (IM i)}
  (Free := free_composite_vlsm IM)
  .

Definition equivocator_IM
  (i : index)
  : VLSM message
  :=
  equivocator_vlsm (IM i).

Definition equivocating_indices
  (index_listing : list index)
  (s : composite_state equivocator_IM)
  : list index
  :=
  filter (fun i => is_equivocating_state (IM i) (s i)) index_listing.

Lemma equivocating_indices_initially_empty
  (index_listing : list index)
  (s : composite_state equivocator_IM)
  (Hs : composite_initial_state_prop equivocator_IM s)
  : equivocating_indices index_listing s = [].
Proof.
  apply Forall_filter_nil.
  apply Forall_forall.
  intros i _.
  specialize (Hs i).
  destruct Hs as [Hs _].
  by congruence.
Qed.

Section sec_equivocating_indices_BasicEquivocation.

Context
  (threshold : R)
  `{ReachableThreshold index Ci threshold}
  .

Program Instance equivocating_indices_BasicEquivocation :
  BasicEquivocation (composite_state equivocator_IM) index Ci threshold
  := {
    is_equivocating := fun s v => v ∈ equivocating_indices (enum index) s ;
    state_validators := fun s => list_to_set(enum index)
  }.
Next Obligation.
Proof.
  by typeclasses eauto.
Qed.

Lemma equivocating_indices_equivocating_validators
  : forall s, equivocating_validators s ≡@{Ci} list_to_set(equivocating_indices (enum index) s).
Proof.
  intros s.
  apply set_eq_fin_set.
  unfold equivocating_validators, is_equivocating.
  simpl.
  split; intro Hin
  ; rewrite !elem_of_elements, elem_of_filter, !elem_of_list_to_set.
  - by intros [].
  - by split; auto using elem_of_enum.
Qed.

Lemma eq_equivocating_indices_equivocation_fault :
  forall s1 s2,
    list_to_set (equivocating_indices (enum index) s1) ≡@{Ci}
    list_to_set (equivocating_indices (enum index) s2) ->
      equivocation_fault s1 = equivocation_fault s2.
Proof.
  intros s1 s2 Heq.
  rewrite <- !equivocating_indices_equivocating_validators in Heq.
  unfold equivocation_fault.
  apply set_eq_fin_set in Heq as [Heq1 Heq2].
  apply sum_weights_subseteq_list in Heq1, Heq2;
    [| by apply NoDup_elements..].
  by apply Rle_antisym.
Qed.

Lemma eq_equivocating_indices_equivocation_fault' :
  forall s1 s2,
    list_to_set (equivocating_indices (enum index) s1)
      ≡@{Ci}
    list_to_set (equivocating_indices (enum index) s2) ->
      equivocation_fault s1 = equivocation_fault s2.
Proof.
  intros s1 s2 Heq.
  rewrite <- !equivocating_indices_equivocating_validators in Heq.
  apply set_equiv_subseteq in Heq as [Heq1 Heq2].
  by apply Rle_antisym; apply sum_weights_subseteq.
Qed.

End sec_equivocating_indices_BasicEquivocation.

(**
  The statement below is obvious a transition cannot make an already equivocating
  component non-equivocating.
*)
Lemma equivocators_transition_preserves_equivocating_indices
  (index_listing : list index)
  (s : composite_state equivocator_IM)
  (iom oom : option message)
  (l : composite_label equivocator_IM)
  (s0 : composite_state equivocator_IM)
  (Ht : composite_transition equivocator_IM l (s0, iom) = (s, oom))
  : equivocating_indices index_listing s0 ⊆ equivocating_indices index_listing s.
Proof.
  intros i Hi.
  apply elem_of_list_filter.
  apply elem_of_list_filter in Hi.
  split; [| by apply Hi].
  destruct Hi as [Hi _].
  intro Hsi. elim Hi. clear Hi. unfold is_singleton_state in *.
  simpl in *.
  destruct l as (j, lj).
  case_match; inversion Ht; subst; clear Ht.
  destruct (decide (i = j)); subst; state_update_simpl; [| done].
  by revert Hsi; apply equivocator_transition_reflects_singleton_state with iom oom lj.
Qed.

Lemma equivocators_transition_cannot_decrease_state_size
  l s iom s' oom
  (Ht : composite_transition equivocator_IM l (s, iom) = (s', oom))
  : forall eqv, equivocator_state_n (s eqv) <= equivocator_state_n (s' eqv).
Proof.
  intro eqv.
  destruct l as [j lj]; cbn in Ht.
  destruct (equivocator_transition _ _ _) as [sj' om'] eqn: Htj.
  apply equivocator_transition_cannot_decrease_state_size in Htj.
  inversion Ht; subst; clear Ht.
  by destruct (decide (j = eqv)); subst; state_update_simpl.
Qed.

Lemma equivocators_plan_cannot_decrease_state_size
  (s : composite_state equivocator_IM)
  (plan : list (composite_plan_item equivocator_IM))
  (s' := snd (composite_apply_plan equivocator_IM s plan))
  : forall eqv, equivocator_state_n (s eqv) <= equivocator_state_n (s' eqv).
Proof.
  intro eqv. subst s'.
  induction plan using rev_ind.
  - by cbn; lia.
  - rewrite (composite_apply_plan_app equivocator_IM s plan).
    destruct (composite_apply_plan equivocator_IM s plan) as [junk s1].
    destruct x as [l im].
    unfold composite_apply_plan.
    unfold _apply_plan.
    cbn -[composite_transition].
    match goal with
      |- context [composite_transition equivocator_IM l ?som] =>
      destruct (composite_transition equivocator_IM l som) eqn: Htrans
    end.
    apply equivocators_transition_cannot_decrease_state_size with (eqv := eqv) in Htrans.
    by cbn in *; lia.
Qed.

Lemma equivocators_pre_trace_cannot_decrease_state_size
  (Pre := pre_loaded_with_all_messages_vlsm (free_composite_vlsm equivocator_IM))
  s s' tr
  (Htr : finite_valid_trace_from_to Pre s s' tr)
  : forall eqv, equivocator_state_n (s eqv) <= equivocator_state_n (s' eqv).
Proof.
  apply trace_to_plan_to_trace_from_to in Htr.
  specialize (equivocators_plan_cannot_decrease_state_size s (trace_to_plan Pre tr)) as Hmon.
  by replace (composite_apply_plan _ _ _) with (tr, s') in Hmon.
Qed.

Lemma equivocators_pre_trace_preserves_equivocating_state
  (Pre := pre_loaded_with_all_messages_vlsm (free_composite_vlsm equivocator_IM))
  s s' tr
  (Htr : finite_valid_trace_from_to Pre s s' tr)
  : forall eqv, is_equivocating_state (IM eqv) (s eqv) -> is_equivocating_state (IM eqv) (s' eqv).
Proof.
  unfold is_equivocating_state, is_singleton_state.
  intros eqv Hseqv.
  apply equivocators_pre_trace_cannot_decrease_state_size  with (eqv := eqv) in Htr.
  by cbv in *; lia.
Qed.

Context
  (equivocators_free_vlsm := free_composite_vlsm equivocator_IM)
  .

Definition equivocators_no_equivocations_constraint
  :=
  no_equivocations_additional_constraint equivocator_IM (free_constraint equivocator_IM).

Definition equivocators_no_equivocations_vlsm
  : VLSM message
  :=
  composite_vlsm equivocator_IM equivocators_no_equivocations_constraint.

Lemma equivocators_no_equivocations_vlsm_incl_equivocators_free
  : VLSM_incl equivocators_no_equivocations_vlsm equivocators_free_vlsm.
Proof.
  apply basic_VLSM_incl.
  - by cbv; intros s Hn n; specialize (Hn n); split_and!; itauto.
  - by intro; intros; apply initial_message_is_valid.
  - by intros l s om Hiv _ _; apply Hiv.
  - by destruct 1.
Qed.

Lemma preloaded_equivocators_no_equivocations_vlsm_incl_PreFree :
  VLSM_incl
    (pre_loaded_with_all_messages_vlsm equivocators_no_equivocations_vlsm)
    (pre_loaded_with_all_messages_vlsm equivocators_free_vlsm).
Proof.
  by apply basic_VLSM_incl_preloaded; [intro | inversion 1 | intro].
Qed.

Lemma equivocators_initial_state_size
  (is : composite_state equivocator_IM)
  (His : composite_initial_state_prop equivocator_IM is)
  (eqv : index)
  : equivocator_state_n (is eqv) = 1.
Proof.
  by destruct (His eqv).
Qed.

(**
  An indexed set of [MachineDescriptor]s, one for each equivocating machine in
  the composition.

  This will be used to project [composite_state]s and [composite_transition_item]s
  from the composition of equivocators to the composition of their corresponding
  nodes.
*)
Definition equivocator_descriptors : Type := forall (eqv : index), MachineDescriptor (IM eqv).

(**
  Generalizes the [proper_descriptor] definition to [equivocator_descriptors].
  Basically, an indexed set is proper w.r.t. a [composite_state] one can obtain
  through it a valid projection of the [composite_state] to the non-equivocating
  universe.
*)
Definition proper_equivocator_descriptors
  (eqv_descriptors : equivocator_descriptors)
  (s : state equivocators_free_vlsm)
  : Prop
  := forall
    (eqv : index),
    proper_descriptor (IM eqv) (eqv_descriptors eqv) (s eqv).

(** Same as above, but disallowing equivocation. *)
Definition not_equivocating_equivocator_descriptors
  (eqv_descriptors : equivocator_descriptors)
  (s : state equivocators_free_vlsm)
  : Prop
  := forall
    (eqv : index),
    existing_descriptor (IM eqv) (eqv_descriptors eqv) (s eqv).

#[export] Instance not_equivocating_equivocator_descriptors_dec
  : RelDecision not_equivocating_equivocator_descriptors.
Proof.
  intros eqv_descriptors s.
  apply @Decision_iff with (P :=
    Forall (fun eqv => existing_descriptor (IM eqv) (eqv_descriptors eqv) (s eqv)) (enum index)).
  - rewrite Forall_forall. apply forall_proper. intros.
    split; [| done].
    by intro Henum; apply Henum, elem_of_enum.
  - apply Forall_dec. intro eqv.
    by apply existing_descriptor_dec.
Qed.

Lemma not_equivocating_equivocator_descriptors_proper
  (eqv_descriptors : equivocator_descriptors)
  (s : state equivocators_free_vlsm)
  (Hne : not_equivocating_equivocator_descriptors eqv_descriptors s)
  : proper_equivocator_descriptors eqv_descriptors s.
Proof.
  by intro eqv; apply existing_descriptor_proper, Hne.
Qed.

Definition zero_descriptor
  (eqv : index)
  : MachineDescriptor (IM eqv)
  := Existing 0.

Lemma zero_descriptor_not_equivocating
  (s : state equivocators_free_vlsm)
  : not_equivocating_equivocator_descriptors zero_descriptor s.
Proof.
  by intro eqv; eexists.
Qed.

Lemma zero_descriptor_proper
  (s : state equivocators_free_vlsm)
  : proper_equivocator_descriptors zero_descriptor s.
Proof.
  apply not_equivocating_equivocator_descriptors_proper.
  by apply zero_descriptor_not_equivocating.
Qed.

Lemma proper_equivocator_descriptors_state_update_eqv
  (eqv_descriptors : equivocator_descriptors)
  (s : state equivocators_free_vlsm)
  (eqv : index)
  (si : state (equivocator_IM eqv))
  (Hsi_proper : proper_descriptor (IM eqv) (eqv_descriptors eqv) (s eqv))
  (Hproper : proper_equivocator_descriptors eqv_descriptors (state_update equivocator_IM s eqv si))
  : proper_equivocator_descriptors eqv_descriptors s.
Proof.
  intro eqv'.
  specialize (Hproper eqv').
  by destruct (decide (eqv = eqv')); subst; state_update_simpl.
Qed.

Definition equivocators_state_project
  (eqv_descriptors : equivocator_descriptors)
  (s : state equivocators_free_vlsm)
  : state Free
  :=
  fun (eqv : index) =>
  equivocator_state_descriptor_project (s eqv) (eqv_descriptors eqv).

Definition lift_to_equivocators_state
  (s : state Free)
  (eqv : index)
  : state (equivocator_IM eqv)
  :=
  mk_singleton_state _ (s eqv).

Lemma lift_initial_to_equivocators_state
  (s : state Free)
  (Hs : initial_state_prop Free s)
  : initial_state_prop equivocators_no_equivocations_vlsm (lift_to_equivocators_state s).
Proof.
  cbn in Hs |- *; unfold composite_initial_state_prop in Hs |- *.
  by intro i; specialize (Hs i).
Qed.

Definition newmachine_descriptors_list
  (index_listing : list index)
  (descriptors : equivocator_descriptors)
  : list index
  := @filter _ _ _ (fun i => is_newmachine_descriptor (IM i) (descriptors i))
   (fun i => newmachine_descriptor_dec (IM i) (descriptors i)) index_listing.

(**
  A very useful operation on [equivocator_descriptors]s is updating the state corresponding
  to a component.
*)
Definition equivocator_descriptors_update
  (s : equivocator_descriptors)
  (i : index)
  (si : MachineDescriptor (IM i))
  (j : index)
  : MachineDescriptor (IM j)
  :=
  match decide (j = i) with
  | left e => eq_rect_r (fun i => MachineDescriptor (IM i)) si e
  | _ => s j
  end.

(**
  The next few results describe several properties of the
  [equivocator_descriptors_update] operation.
*)

Lemma equivocator_descriptors_update_neq
  (s : equivocator_descriptors)
  (i : index)
  (si : MachineDescriptor (IM i))
  (j : index)
  (Hneq : j <> i)
  : equivocator_descriptors_update s i si j = s j.
Proof.
  by unfold equivocator_descriptors_update; case_decide.
Qed.

(**
  A generalized version of [equivocator_descriptors_update_eq] parametric on the
  hypothesis equating the indices.
*)
Lemma equivocator_descriptors_update_eq_rew
  (s : equivocator_descriptors)
  (i : index)
  (si : MachineDescriptor (IM i))
  (j : index)
  (Heq : j = i)
  : equivocator_descriptors_update s i si j = eq_rect_r (fun i => MachineDescriptor (IM i)) si Heq.
Proof.
  unfold equivocator_descriptors_update.
  case_decide; [| done].
  by f_equal; apply Eqdep_dec.UIP_dec.
Qed.

Lemma equivocator_descriptors_update_eq
  (s : equivocator_descriptors)
  (i : index)
  (si : MachineDescriptor (IM i))
  : equivocator_descriptors_update s i si i = si.
Proof.
  by rewrite equivocator_descriptors_update_eq_rew with (Heq := eq_refl).
Qed.

Lemma equivocator_descriptors_update_id
  (s : equivocator_descriptors)
  (i : index)
  (si : MachineDescriptor (IM i))
  (Heq : s i = si)
  : equivocator_descriptors_update s i si = s.
Proof.
  apply functional_extensionality_dep_good.
  intro j.
  destruct (decide (j = i)); subst.
  - by apply equivocator_descriptors_update_eq.
  - by apply equivocator_descriptors_update_neq.
Qed.

Lemma equivocator_descriptors_update_twice
  (s : equivocator_descriptors)
  (i : index)
  (si si' : MachineDescriptor (IM i))
  : equivocator_descriptors_update (equivocator_descriptors_update s i si) i si'
  = equivocator_descriptors_update s i si'.
Proof.
  apply functional_extensionality_dep_good.
  intro j.
  destruct (decide (j = i)); subst.
  - by rewrite equivocator_descriptors_update_eq, equivocator_descriptors_update_eq.
  - by rewrite !equivocator_descriptors_update_neq.
Qed.

Lemma equivocators_state_project_state_update_eqv
  (eqv_descriptors : equivocator_descriptors)
  (s : state equivocators_free_vlsm)
  (eqv : index)
  (seqv : state (equivocator_IM eqv))
  : let si :=  match eqv_descriptors eqv with
    | NewMachine sn => sn
    | Existing i =>
      match equivocator_state_project seqv i with
      | Some si => si
      | None => equivocator_state_zero seqv
      end
    end in
  equivocators_state_project eqv_descriptors (state_update equivocator_IM s eqv seqv)
  = state_update IM (equivocators_state_project eqv_descriptors s) eqv si.
Proof.
  cbn; extensionality ieqv.
  unfold equivocators_state_project, state_update.
  by case_decide; subst.
Qed.

Lemma equivocators_initial_state_project
  (es : state equivocators_free_vlsm)
  (Hes : initial_state_prop equivocators_free_vlsm es)
  (eqv_descriptors : equivocator_descriptors)
  (Heqv : proper_equivocator_descriptors eqv_descriptors es)
  : initial_state_prop Free (equivocators_state_project eqv_descriptors es).
Proof.
  intro eqv. specialize (Hes eqv).
  unfold equivocator_IM in Hes.
  unfold equivocators_state_project.
  specialize (Heqv eqv).
  destruct (eqv_descriptors eqv) as [sn | i]; [done |].
  destruct Heqv as [es_eqv_i Hes_eqv_i].
  simpl. rewrite Hes_eqv_i. simpl.
  by eapply equivocator_vlsm_initial_state_preservation_rev.
Qed.

Lemma equivocators_initial_message
  (m : message)
  (Hem : initial_message_prop equivocators_free_vlsm m)
  : initial_message_prop Free m.
Proof.
  destruct Hem as [eqv [emi Hem]].
  by exists eqv, emi.
Qed.

End sec_fully_equivocating_composition.

#[export] Hint Rewrite @equivocator_descriptors_update_eq : state_update.
#[export] Hint Rewrite @equivocator_descriptors_update_id using done : state_update.
#[export] Hint Rewrite @equivocator_descriptors_update_neq using done : state_update.
#[export] Hint Rewrite @equivocators_state_project_state_update_eqv using done : state_update.

Section sec_equivocators_sub_projections.

Context
  {message : Type}
  `{EqDecision index}
  (IM : index -> VLSM message)
  `{forall i, HasBeenSentCapability (IM i)}
  (equivocating : list index)
  (sub_equivocator_IM := sub_IM (equivocator_IM IM) equivocating)
  (sub_IM_equivocator := equivocator_IM (sub_IM IM equivocating))
  .

Definition seeded_equivocators_no_equivocation_vlsm
  (seed : message -> Prop)
  : VLSM message :=
  composite_no_equivocation_vlsm_with_pre_loaded
    sub_equivocator_IM (free_constraint sub_equivocator_IM) seed.

Lemma sub_equivocator_IM_initial_state_commute is :
  composite_initial_state_prop sub_equivocator_IM is <->
  composite_initial_state_prop sub_IM_equivocator is.
Proof. done. Qed.

End sec_equivocators_sub_projections.
