From Cdcl Require Import Itauto. Local Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude finite.
From Coq Require Import FinFun Lia Program.
From VLSM Require Import Lib.Preamble Lib.ListExtras Lib.FinExtras Lib.FinFunExtras.
From VLSM Require Import Core.VLSM Core.VLSMProjections Core.Composition Core.ProjectionTraces Core.SubProjectionTraces.
From VLSM Require Import Core.Equivocation Core.Equivocation.NoEquivocation.
From VLSM Require Import Core.Equivocators.Common Core.Equivocators.Projections Core.Equivocators.EquivocatorReplay.
From VLSM Require Import Core.Equivocators.MessageProperties Core.Equivocators.Composition.Common.
From VLSM Require Import Core.Equivocators.Composition.Projections Core.Plans.

(** * VLSM Equivocator Full Replay Traces

In this section we show that given a trace of equivocators, one can "replay"
that at the end of an existing trace, by first equivocating for each initial
state and then performing each transition, but appropriately "shifted".

To make the results more general, we take the trace to be replayed to be
produced by a restricted set of equivocators pre-loaded with messages
satisfying some conditions.
*)

Section all_equivocating.

Context {message : Type}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  `{forall i : index, HasBeenSentCapability (IM i)}
  `{forall i : index, HasBeenReceivedCapability (IM i)}
  (seed : message -> Prop)
  (equivocating : list index)
  (* abbreviations *)
  (equiv_index : Type := sub_index equivocating)
  (equivocator_descriptors := equivocator_descriptors IM)
  (equivocators_state_project := equivocators_state_project IM)
  (equivocator_IM := equivocator_IM IM)
  (sub_equivocator_IM := sub_IM equivocator_IM equivocating)
  (sub_IM := sub_IM IM equivocating)
  (equivocator_descriptors_update := equivocator_descriptors_update IM)
  (proper_equivocator_descriptors := proper_equivocator_descriptors IM)
  (equivocators_trace_project := equivocators_trace_project IM)
  (Free := free_composite_vlsm IM)
  (FreeE := free_composite_vlsm equivocator_IM)
  (PreFreeE := pre_loaded_with_all_messages_vlsm FreeE)
  (FreeSubE := free_composite_vlsm sub_equivocator_IM)
  (PreFreeSubE := pre_loaded_with_all_messages_vlsm FreeSubE)
  (SeededXE : VLSM message := seeded_equivocators_no_equivocation_vlsm IM equivocating seed)
  (equivocators_no_equivocations_vlsm := equivocators_no_equivocations_vlsm IM)
.

Lemma SeededXE_Free_full_projection
  (Hseed : forall m, seed m -> valid_message_prop FreeE m)
  : VLSM_full_projection SeededXE
    (composite_vlsm equivocator_IM (free_constraint equivocator_IM))
    (lift_sub_label equivocator_IM equivocating) (lift_sub_state equivocator_IM equivocating).
Proof.
  apply basic_VLSM_full_projection; intros ? *.
  - split; [|exact I].
    apply lift_sub_valid. apply Hv.
  - intros [_ Ht]. revert Ht. apply lift_sub_transition.
  - intros; apply (lift_sub_state_initial equivocator_IM). assumption.
  - intros; destruct HmX as [Hinit|Hseeded]; [|apply Hseed; assumption].
    apply initial_message_is_valid.
    destruct Hinit as [i Him].
    exists (proj1_sig i). assumption.
Qed.

(**
Given a <<base_s>>tate to replay on, the replay label corresponding to a
given transition label is obtained as the [equivocator_state_append_label].
*)
Definition lift_equivocators_sub_label_to
  (base_s : composite_state equivocator_IM)
  (l : composite_label sub_equivocator_IM)
  : composite_label equivocator_IM
  :=
  let (sub_i, li) := l in
  let i := proj1_sig sub_i in
  existT i (equivocator_state_append_label (IM i) (base_s i) li).

(**
Given a <<base_s>>tate to replay on, the replay state corresponding to a
destination state in a transition by appending its components to the
base state using [equivocator_state_append].
*)
Definition lift_equivocators_sub_state_to
  (base_s : composite_state equivocator_IM)
  (s : composite_state sub_equivocator_IM)
  : composite_state equivocator_IM
  := fun i =>
    match @decide  (sub_index_prop equivocating i) (sub_index_prop_dec equivocating i) with
    | left e =>  equivocator_state_append (base_s i) (s (dexist i e))
    | _ => base_s i
    end.

Lemma lift_equivocators_sub_state_to_sub
  (base_s : composite_state equivocator_IM)
  (s : composite_state sub_equivocator_IM)
  i
  (Hi : sub_index_prop equivocating i)
  : lift_equivocators_sub_state_to base_s s i =  equivocator_state_append (base_s i) (s (dexist i Hi)).
Proof.
  unfold lift_equivocators_sub_state_to.
  case_decide as H_i; [| contradiction].
  rewrite (sub_IM_state_pi s H_i Hi); reflexivity.
Qed.

Lemma lift_equivocators_sub_state_to_size
  (base_s : composite_state equivocator_IM)
  (s : composite_state sub_equivocator_IM)
  : forall i,
    equivocator_state_n (base_s i) <= equivocator_state_n (lift_equivocators_sub_state_to base_s s i).
Proof.
  intro i.
  unfold lift_equivocators_sub_state_to.
  destruct (decide _); [|lia].
  rewrite equivocator_state_append_size. lia.
Qed.

(** The plan item corresponding to an initial state equivocation *)
Definition initial_new_machine_transition_item
  (is : composite_state sub_equivocator_IM)
  (eqv : equiv_index)
  : composite_plan_item equivocator_IM
  :=
  let i := proj1_sig eqv in
  let seqv := is eqv in
  let new_l :=
    (existT i (Spawn (equivocator_state_zero seqv)))
    in
  @Build_plan_item message (composite_type equivocator_IM) new_l None.

(** Command for equivocating all states of an initial composite state. *)
Definition spawn_initial_state
  (is : composite_state sub_equivocator_IM)
  : composite_plan equivocator_IM
  := map (initial_new_machine_transition_item is) (enum (sub_index equivocating)).

Definition replayed_initial_state_from full_replay_state is :=
  fst (composite_apply_plan equivocator_IM full_replay_state (spawn_initial_state is)).

(** The final state obtained after replaying an initial state is precisely
the lifting of that initial state over the given base state.
*)
Lemma replayed_initial_state_from_lift
  (full_replay_state : composite_state equivocator_IM)
  (is : composite_state sub_equivocator_IM)
  (His : composite_initial_state_prop sub_equivocator_IM is)
  : finite_trace_last full_replay_state (replayed_initial_state_from full_replay_state is)
    = lift_equivocators_sub_state_to full_replay_state is.
Proof.
  cut (forall l (Hincl : incl l (enum (sub_index equivocating))) (Hnodup : NoDup l),
    let tr_full_replay_is :=
      composite_apply_plan equivocator_IM full_replay_state
        (map (initial_new_machine_transition_item is)
          l) in
    (∀ i : index,
      tr_full_replay_is.2 i =
      match @decide  (sub_index_prop equivocating i) (sub_index_prop_dec equivocating i) with
      | left e =>
        let eqv := (dexist i e) in
        if (decide (eqv ∈ l)) then equivocator_state_append (full_replay_state i) (is eqv)
        else full_replay_state i
      | _ =>  full_replay_state i
      end
    )).
  {
    intros Hcut; specialize (Hcut _ (incl_refl _) ltac:(apply NoDup_enum)).
    unfold replayed_initial_state_from, composite_apply_plan.
    rewrite _apply_plan_last; extensionality i.
    spec Hcut i; unfold composite_apply_plan in Hcut; unfold spawn_initial_state
    ; simpl in *; rewrite Hcut.
    unfold lift_equivocators_sub_state_to.
    case_decide; [| reflexivity].
    rewrite decide_True; [reflexivity |].
    apply elem_of_enum.
  }
  induction l using rev_ind; intros.
  - case_decide; [|reflexivity].
    rewrite decide_False; [reflexivity|]. intro Hin. inversion Hin.
  - spec IHl; [apply incl_app_inv in Hincl; apply Hincl |].
    spec IHl; [apply NoDup_app in Hnodup; apply Hnodup |].
    subst tr_full_replay_is.
    rewrite map_app, (composite_apply_plan_app equivocator_IM); simpl in *
    ; destruct (composite_apply_plan _ _ _) as (aitems, afinal); simpl in *.
    spec IHl i; destruct_dec_sig x ix Hix Heqx; subst x; simpl in *.
    case_decide as _Hix; cycle 1.
    + rewrite state_update_neq; congruence.
    + destruct (decide (ix = i)).
      * subst ix; rewrite state_update_eq.
        rewrite decide_False in IHl.
        2: {
          intro Heqv.
          apply NoDup_app in Hnodup as (_ & Hnodup & _).
          eapply Hnodup; [eassumption |].
          rewrite elem_of_list_singleton.
          apply dec_sig_eq_iff; cbn; reflexivity.
        }
        rewrite IHl, decide_True.
        -- rewrite (sub_IM_state_pi is _Hix Hix); symmetry.
           apply equivocator_state_append_singleton_is_extend, (His (dexist i Hix)).
        -- rewrite elem_of_app, elem_of_list_singleton; right.
           apply dec_sig_eq_iff; cbn; reflexivity.
      * rewrite state_update_neq by congruence.
        case_decide.
        -- rewrite decide_True; rewrite ?elem_of_app; itauto.
        -- rewrite decide_False; [assumption |].
           intros [Hin | Hx]%elem_of_app; [contradiction Hin | contradict Hx].
           rewrite elem_of_list_singleton, dsig_eq; cbn; congruence.
Qed.

(** For any [equivocator_descriptors] corresponding to the base state
the projection of the replaying of an initial state is empty.
*)
Lemma equivocators_trace_project_replayed_initial_state_from full_replay_state is
  (eqv_descriptors: equivocator_descriptors)
  (Heqv_descriptors: not_equivocating_equivocator_descriptors IM eqv_descriptors full_replay_state)
  : equivocators_trace_project eqv_descriptors
      (replayed_initial_state_from full_replay_state is) =
    Some ([], eqv_descriptors).
Proof.
  unfold replayed_initial_state_from, spawn_initial_state.
  generalize (enum (sub_index equivocating)).
  intro l.
  remember (composite_apply_plan _ _ _) as plan.
  apply proj1 with (forall i, equivocator_state_n (full_replay_state i) <= equivocator_state_n (plan.2 i)).
  subst plan.
  induction l using rev_ind; [split; simpl; [reflexivity|lia]|].
  rewrite map_app, (composite_apply_plan_app equivocator_IM).
  destruct (composite_apply_plan _ _ _) as (litems, lfinal) eqn:Hplanl.
  destruct (composite_apply_plan _ lfinal _) as (aitems, afinal) eqn:Hplana.
  simpl in *.
  inversion_clear Hplana.
  split.
  - apply equivocators_trace_project_app_iff.
    exists [],[],eqv_descriptors.
    repeat split; [|apply IHl].
    specialize (Heqv_descriptors (` x)).
    unfold existing_descriptor in Heqv_descriptors.
    destruct (eqv_descriptors (` x)) eqn:Heqv_x; [contradiction|].
    destruct Heqv_descriptors as [s_x_n Heqv_descriptors].
    apply equivocator_state_project_Some_rev in Heqv_descriptors as Hltn.
    apply proj2 in IHl.
    specialize (IHl (` x)).
    cbn. unfold equivocators_transition_item_project; simpl.
    unfold equivocator_vlsm_transition_item_project. rewrite Heqv_x.
    simpl. rewrite state_update_eq.
    rewrite equivocator_state_extend_project_1 by lia.
    destruct_equivocator_state_project (lfinal (` x)) n lfinal_x_n Hltn'; [|lia].
    rewrite equivocator_state_extend_lst.
    rewrite decide_False by lia.
    f_equal. f_equal. apply equivocator_descriptors_update_id. assumption.
  - intro i. apply proj2 in IHl. specialize (IHl i).
    destruct (decide (` x = i)).
    + subst. rewrite state_update_eq, equivocator_state_extend_size. lia.
    + rewrite state_update_neq by congruence. assumption.
Qed.

Lemma equivocator_state_project_replayed_initial_state_from_left full_replay_state is
  (lst := finite_trace_last full_replay_state (replayed_initial_state_from full_replay_state is))
  : forall i j,
    j < equivocator_state_n (full_replay_state i) ->
    equivocator_state_project (lst i) j =
    equivocator_state_project (full_replay_state i) j.
Proof.
  subst lst.
  unfold replayed_initial_state_from, spawn_initial_state.
  generalize (enum (sub_index equivocating)).
  intro l.
  induction l using rev_ind; simpl; [reflexivity|].
  rewrite map_app, (composite_apply_plan_app equivocator_IM).
  specialize (composite_apply_plan_last equivocator_IM full_replay_state (map (initial_new_machine_transition_item is) l))
    as Hlst.
  destruct (composite_apply_plan _ _ _) as (litems, lfinal) eqn:Hplanl.
  destruct (composite_apply_plan _ lfinal _) as (aitems, afinal) eqn:Hplana.
  inversion_clear Hplana.
  simpl in *.
  rewrite finite_trace_last_is_last. simpl.
  intros i j Hj.
  destruct (decide (` x = i)); subst.
  - rewrite state_update_eq.
    specialize (IHl (` x) j Hj).
    destruct_equivocator_state_project (full_replay_state (` x)) j s_x_j Hltj; [|lia].
    rewrite equivocator_state_extend_project_1; [assumption|].
    apply equivocator_state_project_Some_rev in IHl as Hltj'.
    assumption.
  - rewrite state_update_neq by congruence.
    apply IHl.
    by assumption.
Qed.

Lemma equivocator_state_descriptor_project_replayed_initial_state_from_left full_replay_state is
  (eqv_descriptors: equivocator_descriptors)
  (Heqv_descriptors: not_equivocating_equivocator_descriptors IM eqv_descriptors full_replay_state)
  (lst := finite_trace_last full_replay_state (replayed_initial_state_from full_replay_state is))
  : forall i,
    equivocator_state_descriptor_project (lst i) (eqv_descriptors i) =
    equivocator_state_descriptor_project (full_replay_state i) (eqv_descriptors i).
Proof.
  intro i. spec Heqv_descriptors i.
  unfold equivocator_state_descriptor_project.
  unfold existing_descriptor in Heqv_descriptors.
  destruct (eqv_descriptors i) as [sn|ji]; [contradiction|].
  destruct Heqv_descriptors as [full_i_ji Hpr_ji].
  apply equivocator_state_project_Some_rev in Hpr_ji as Hltji.
  subst lst.
  rewrite equivocator_state_project_replayed_initial_state_from_left by assumption.
  rewrite Hpr_ji.
  reflexivity.
Qed.

Definition replayed_trace_from full_replay_state is tr :=
  replayed_initial_state_from full_replay_state is ++
  pre_VLSM_full_projection_finite_trace_project (type FreeSubE) (type FreeE)
    (lift_equivocators_sub_label_to full_replay_state)
    (lift_equivocators_sub_state_to full_replay_state) tr.

Lemma replayed_trace_from_finite_trace_last full_replay_state is tr
  (His : composite_initial_state_prop _ is)
  : finite_trace_last full_replay_state (replayed_trace_from full_replay_state is tr) =
    (lift_equivocators_sub_state_to full_replay_state (finite_trace_last is tr)).
Proof.
  destruct_list_last tr tr' item Htr; subst.
  - unfold replayed_trace_from. cbn.
    rewrite app_nil_r.
    apply replayed_initial_state_from_lift.
    assumption.
  - unfold replayed_trace_from, pre_VLSM_full_projection_finite_trace_project.
    rewrite map_app, app_assoc. simpl.
    rewrite !finite_trace_last_is_last.
    reflexivity.
Qed.

Lemma equivocator_state_project_replayed_trace_from_left full_replay_state is tr
  (lst := finite_trace_last full_replay_state (replayed_trace_from full_replay_state is tr))
  : forall i j,
    j < equivocator_state_n (full_replay_state i) ->
    equivocator_state_project (lst i) j =
    equivocator_state_project (full_replay_state i) j.
Proof.
  subst lst.
  unfold replayed_trace_from.
  destruct_list_last tr tr' lst Htr.
  - simpl. rewrite app_nil_r.
    apply equivocator_state_project_replayed_initial_state_from_left.
  - unfold pre_VLSM_full_projection_finite_trace_project.
    rewrite map_app, app_assoc. simpl.
    rewrite finite_trace_last_is_last.
    simpl.
    intros i j Hltj.
    unfold lift_equivocators_sub_state_to.
    destruct (decide _); [|reflexivity].
    rewrite equivocator_state_append_project_1 by assumption.
    reflexivity.
Qed.

Lemma equivocator_state_descriptor_project_replayed_trace_from_left full_replay_state is tr
  (eqv_descriptors: equivocator_descriptors)
  (Heqv_descriptors: not_equivocating_equivocator_descriptors IM eqv_descriptors full_replay_state)
  (lst := finite_trace_last full_replay_state (replayed_trace_from full_replay_state is tr))
  : forall i,
    equivocator_state_descriptor_project (lst i) (eqv_descriptors i) =
    equivocator_state_descriptor_project (full_replay_state i) (eqv_descriptors i).
Proof.
  intro i. spec Heqv_descriptors i.
  unfold equivocator_state_descriptor_project.
  unfold existing_descriptor in Heqv_descriptors.
  destruct (eqv_descriptors i) as [sn|ji]; [contradiction|].
  destruct Heqv_descriptors as [full_i_ji Hpr_ji].
  apply equivocator_state_project_Some_rev in Hpr_ji as Hltji.
  subst lst.
  rewrite equivocator_state_project_replayed_trace_from_left by assumption.
  rewrite Hpr_ji.
  reflexivity.
Qed.

Lemma equivocators_total_state_project_replayed_trace_from full_replay_state is tr
  (lst := finite_trace_last full_replay_state (replayed_trace_from full_replay_state is tr))
  : equivocators_total_state_project IM lst = equivocators_total_state_project IM full_replay_state.
Proof.
  apply functional_extensionality_dep.
  intro i.
  apply equivocator_state_descriptor_project_replayed_trace_from_left.
  apply zero_descriptor_not_equivocating.
Qed.

Lemma equivocators_trace_project_replayed_trace_from_left full_replay_state is tr
  (eqv_descriptors: equivocator_descriptors)
  (Heqv_descriptors: not_equivocating_equivocator_descriptors IM eqv_descriptors full_replay_state)
  : equivocators_trace_project eqv_descriptors
      (replayed_trace_from full_replay_state is tr) =
    Some ([], eqv_descriptors).
Proof.
  apply equivocators_trace_project_app_iff.
  exists [],[],eqv_descriptors.
  repeat split; [|apply equivocators_trace_project_replayed_initial_state_from; assumption].
  induction tr using rev_ind; [reflexivity|].
  unfold pre_VLSM_full_projection_finite_trace_project.
  rewrite map_app.
  apply equivocators_trace_project_app_iff.
  exists [],[], eqv_descriptors.
  repeat split; [|assumption].
  clear IHtr.
  destruct x. simpl.
  destruct l as (sub_i,li).
  destruct_dec_sig sub_i i Hi Heqsub_i.
  subst sub_i.
  specialize (Heqv_descriptors i).
  unfold existing_descriptor in Heqv_descriptors.
  destruct (eqv_descriptors _) eqn:Heqv_l; [contradiction|].
  destruct Heqv_descriptors as [s_l_n Hs_l_n].
  apply equivocator_state_project_Some_rev in Hs_l_n as Hltn.
  specialize (lift_equivocators_sub_state_to_size full_replay_state destination i)
    as Hltsize.
  unfold equivocators_transition_item_project. simpl.
  rewrite Heqv_l.
  simpl.
  destruct_equivocator_state_project
    (lift_equivocators_sub_state_to full_replay_state destination i) n
    lift_n Hlt_n; [|lia].
  rewrite (lift_equivocators_sub_state_to_sub) with (Hi := Hi).
  rewrite equivocator_state_append_lst.
  destruct li as [sn_d| id li| id li]; simpl
  ; rewrite !decide_False by lia
  ; f_equal; f_equal; apply equivocator_descriptors_update_id; assumption.
Qed.

Lemma equivocators_total_trace_project_replayed_trace_from full_replay_state is tr
  : equivocators_total_trace_project IM (replayed_trace_from full_replay_state is tr) = [].
Proof.
  unfold equivocators_total_trace_project.
  rewrite equivocators_trace_project_replayed_trace_from_left
  ; [reflexivity|].
  apply zero_descriptor_not_equivocating.
Qed.

Lemma lift_equivocators_sub_valid
  (full_replay_state : composite_state equivocator_IM)
  l s om
  (Hv : composite_valid sub_equivocator_IM l (s, om))
  : composite_valid equivocator_IM (lift_equivocators_sub_label_to full_replay_state  l)
      (lift_equivocators_sub_state_to full_replay_state s, om).
Proof.
  destruct l as (sub_i, li).
  destruct_dec_sig sub_i i Hi Heqsub_i. subst sub_i.
  specialize
    (equivocator_state_append_valid (IM i) li
      (s (dexist i Hi)) om
      (full_replay_state i) Hv
    ) as Hlift.
  cbn.
  rewrite (lift_equivocators_sub_state_to_sub _ _ _ Hi).
  assumption.
Qed.

Lemma lift_equivocators_sub_transition
  (full_replay_state : composite_state equivocator_IM)
  l s om s' om'
  (Hv : composite_valid sub_equivocator_IM l (s, om))
  (Ht: composite_transition sub_equivocator_IM l (s, om) = (s', om'))
  : composite_transition equivocator_IM (lift_equivocators_sub_label_to full_replay_state  l)
      (lift_equivocators_sub_state_to full_replay_state s, om) =
      (lift_equivocators_sub_state_to full_replay_state s', om').
Proof.
  destruct l as (sub_i, li).
  destruct_dec_sig sub_i i Hi Heqsub_i. subst sub_i.
  specialize
    (equivocator_state_append_transition (IM i) li
      (s (dexist i Hi)) om
      (s' (dexist i Hi)) om'
      (full_replay_state i) Hv
    ) as Hlift.
  cbn in Ht.
  destruct (equivocator_transition _ _ _) as (_si', _om').
  inversion Ht. subst s' om'. clear Ht. rewrite state_update_eq in Hlift.
  specialize (Hlift eq_refl).
  cbn.
  rewrite (lift_equivocators_sub_state_to_sub _ _ _ Hi).
  replace (equivocator_transition _ _ _) with
    (equivocator_state_append (full_replay_state i) _si', _om').
  f_equal.
  apply functional_extensionality_dep. intro j.
  destruct (decide (i = j)).
  - subst. rewrite state_update_eq.
    rewrite (lift_equivocators_sub_state_to_sub _ _ _ Hi).
    rewrite state_update_eq. reflexivity.
  - rewrite state_update_neq by congruence.
    unfold lift_equivocators_sub_state_to.
    destruct (decide _); [|reflexivity].
    rewrite state_update_neq; [reflexivity|].
    intro Hcontra. apply dsig_eq in Hcontra. simpl in Hcontra. congruence.
Qed.

Section pre_loaded_constrained_projection.
(**
By replaying a [valid_trace] on top of a [valid_state] we obtain a
[valid_trace]. We derive this as a more general [VLSM_weak_full_projection]
result for a class of VLSM parameterized by a constraint having "good"
properties and pre-loaded with a seed, to allow deriving the
[VLSM_weak_full_projection] result for both the free composition of equivocators
and for the no message equivocation composition of equivocators (free, or with
an additional fixed-set state-equivocation constraint).
*)

Context
  (constraint : composite_label equivocator_IM -> composite_state equivocator_IM * option message -> Prop)
  (seed1 : message -> Prop)
  (SeededCE := pre_loaded_vlsm (composite_vlsm equivocator_IM constraint) seed1)
  (Hconstraint_none : forall i ns s, i ∈ equivocating -> valid_state_prop SeededCE s -> constraint (existT i (Spawn ns)) (s, None))
  (Hseed : forall m, seed m -> valid_message_prop SeededCE m)
  (full_replay_state : composite_state equivocator_IM)
  (Hfull_replay_state : valid_state_prop SeededCE full_replay_state)
  (Hsubsumption : forall l s om, input_valid SeededXE l (s, om) ->
    valid_state_prop SeededCE (lift_equivocators_sub_state_to full_replay_state s) ->
    constraint (lift_equivocators_sub_label_to full_replay_state l)  (lift_equivocators_sub_state_to full_replay_state s, om))
  .

Lemma replayed_initial_state_from_valid
  (is : composite_state sub_equivocator_IM)
  (His : composite_initial_state_prop sub_equivocator_IM is)
  : finite_valid_trace_from SeededCE full_replay_state (replayed_initial_state_from full_replay_state is).
Proof.
  cut (forall l, incl l (enum (sub_index equivocating)) ->
    finite_valid_plan_from SeededCE
      full_replay_state (map (initial_new_machine_transition_item is) l)).
  { intros Hplan. specialize (Hplan _ (incl_refl _)).
    unfold finite_valid_plan_from in Hplan.
    assumption.
  }
  intro l.
  induction l using rev_ind; intros Hincl.
  - constructor. assumption.
  - spec IHl.  {  intros i Hi. apply Hincl. apply in_app_iff. left. assumption. }
    rewrite map_app.
    apply finite_valid_plan_from_app_iff.
    split; [assumption|].
    apply finite_valid_trace_singleton. simpl.
    repeat split.
    + revert IHl. apply apply_plan_last_valid.
    + apply option_valid_message_None.
    + apply His.
    + apply Hconstraint_none.
      * clear -x. destruct_dec_sig x i Hi Hx.
        subst. assumption.
      * apply finite_valid_trace_last_pstate in IHl.
        remember (finite_trace_last _ _) as lst.
        replace ((apply_plan _ _ _).2) with lst
        ; [assumption|].
        subst.
        apply apply_plan_last.
Qed.

Lemma lift_initial_message
  : forall m, vinitial_message_prop SeededXE m -> valid_message_prop SeededCE m.
Proof.
  intros m [Hinit | Hseeded].
  - apply initial_message_is_valid. destruct Hinit as [[i Hi] Hinit].
    left. exists i. assumption.
  - apply Hseed. assumption.
Qed.

Lemma lift_equivocators_sub_weak_projection
  : VLSM_weak_full_projection SeededXE SeededCE (lift_equivocators_sub_label_to full_replay_state) (lift_equivocators_sub_state_to full_replay_state).
Proof.
  apply basic_VLSM_weak_full_projection; intros ? *.
  - split.
    + apply lift_equivocators_sub_valid. apply Hv.
    + apply Hsubsumption; assumption.
  - intros Ht. apply lift_equivocators_sub_transition; apply Ht.
  - intro. rewrite <- replayed_initial_state_from_lift; [|assumption].
    apply finite_valid_trace_last_pstate.
    apply replayed_initial_state_from_valid.
    assumption.
  - intros. apply lift_initial_message. assumption.
Qed.

Lemma sub_preloaded_replayed_trace_from_valid_equivocating
  (is : composite_state sub_equivocator_IM)
  (tr : list (composite_transition_item sub_equivocator_IM))
  (Htr : finite_valid_trace SeededXE is tr)
  : finite_valid_trace_from SeededCE
      full_replay_state (replayed_trace_from full_replay_state is tr).
Proof.
  destruct Htr as [Htr His].
  apply finite_valid_trace_from_app_iff.
  split; [apply replayed_initial_state_from_valid; assumption|].
  rewrite replayed_initial_state_from_lift by assumption.
  revert Htr.
  apply (VLSM_weak_full_projection_finite_valid_trace_from lift_equivocators_sub_weak_projection).
Qed.

End pre_loaded_constrained_projection.

Lemma SeededXE_PreFreeE_weak_full_projection
  (full_replay_state : composite_state equivocator_IM)
  (Hfull_replay_state : valid_state_prop PreFreeE  full_replay_state)
  : VLSM_weak_full_projection SeededXE PreFreeE (lift_equivocators_sub_label_to full_replay_state) (lift_equivocators_sub_state_to full_replay_state).
Proof.
  constructor.
  intros sX trX HtrX.
  specialize (pre_loaded_with_all_messages_vlsm_is_pre_loaded_with_True FreeE) as Heq.
  apply (VLSM_eq_finite_valid_trace_from Heq).
  revert sX trX HtrX.
  apply lift_equivocators_sub_weak_projection.
  - intros; exact I.
  - intros. apply initial_message_is_valid. right. exact I.
  - apply (VLSM_eq_valid_state Heq) in Hfull_replay_state. assumption.
  - intros. exact I.
Qed.

Lemma PreFreeSubE_PreFreeE_weak_full_projection
  (full_replay_state : composite_state equivocator_IM)
  (Hfull_replay_state : valid_state_prop PreFreeE  full_replay_state)
  : VLSM_weak_full_projection PreFreeSubE PreFreeE (lift_equivocators_sub_label_to full_replay_state) (lift_equivocators_sub_state_to full_replay_state).
Proof.
  apply basic_VLSM_weak_full_projection; intros ? *.
  - split; [apply lift_equivocators_sub_valid; apply Hv|exact I].
  - intro Ht. apply lift_equivocators_sub_transition; apply Ht.
  - intros.
    rewrite <- replayed_initial_state_from_lift; [|assumption].
    apply finite_valid_trace_last_pstate.
    specialize (pre_loaded_with_all_messages_vlsm_is_pre_loaded_with_True FreeE) as Heq.
    apply (VLSM_eq_finite_valid_trace_from Heq).
    apply replayed_initial_state_from_valid.
    + intro; intros. exact I.
    + apply (VLSM_eq_valid_state Heq). assumption.
    + assumption.
  - intros. apply any_message_is_valid_in_preloaded.
Qed.

Section seeded_no_equiv.

Context
  (SeededAllXE : VLSM message := composite_no_equivocation_vlsm_with_pre_loaded equivocator_IM (free_constraint _) seed)
  (full_replay_state : composite_state equivocator_IM)
  (Hfull_replay_state : valid_state_prop SeededAllXE full_replay_state)
  .

Local Lemma SeededNoEquiv_subsumption
  : forall l s om, input_valid SeededXE l (s, om) ->
  no_equivocations_additional_constraint_with_pre_loaded equivocator_IM (free_constraint _) seed (lift_equivocators_sub_label_to full_replay_state l)  (lift_equivocators_sub_state_to full_replay_state s, om).
Proof.
  intros l s om (Hs & _ & _ & Hc1 & _).
  split; [|exact I].
  destruct om as [m|]; [|exact I].
  apply (VLSM_incl_valid_state (NoEquivocation.seeded_no_equivocation_incl_preloaded equivocator_IM (free_constraint _) seed)) in Hfull_replay_state.
  specialize (valid_state_project_preloaded_to_preloaded _ equivocator_IM (free_constraint _) full_replay_state)
    as Hfull_replay_state_pr.
  pose (no_equivocations_additional_constraint_with_pre_loaded
          sub_equivocator_IM (free_constraint sub_equivocator_IM) seed)
        as constraint.
  specialize
    (pre_loaded_vlsm_incl_pre_loaded_with_all_messages
      (composite_vlsm sub_equivocator_IM constraint)
      seed) as Hincl.
  apply (VLSM_incl_valid_state Hincl) in Hs.
  specialize (valid_state_project_preloaded_to_preloaded _ sub_equivocator_IM constraint s)
    as Hs_pr.
  simpl in Hc1.
  destruct Hc1 as [Hsub_sent | Hseeded].
  - destruct Hsub_sent as [sub_i Hsent].
    destruct_dec_sig sub_i i Hi Heqsub_i.
    left. exists i.
    simpl. rewrite (lift_equivocators_sub_state_to_sub _ _ _ Hi).
    subst. unfold SubProjectionTraces.sub_IM in Hsent. cbn in Hsent |-*.
    specialize (Hfull_replay_state_pr i Hfull_replay_state).
    specialize (Hs_pr (dexist i Hi) Hs).
    apply equivocator_state_append_sent_right; assumption.
  - right. assumption.
Qed.

Local Lemma sent_are_valid
  : forall m, seed m -> valid_message_prop SeededAllXE m.
Proof.
  intros m Hm.
  apply initial_message_is_valid.
  right. assumption.
Qed.

(** Here we specialize the generic [lift_equivocators_sub_weak_projection]
result for the [equivocators_no_equivocations_constraint].
*)
Lemma SeededXE_SeededNoEquiv_weak_full_projection
  : VLSM_weak_full_projection SeededXE SeededAllXE (lift_equivocators_sub_label_to full_replay_state) (lift_equivocators_sub_state_to full_replay_state).
Proof.
  constructor.
  apply lift_equivocators_sub_weak_projection; intros.
  - split; exact I.
  - apply sent_are_valid. assumption.
  - assumption.
  - apply SeededNoEquiv_subsumption; assumption.
Qed.

Lemma sub_replayed_trace_from_valid_equivocating
  (is : composite_state sub_equivocator_IM)
  (tr : list (composite_transition_item sub_equivocator_IM))
  (Htr : finite_valid_trace SeededXE is tr)
  : finite_valid_trace_from SeededAllXE
      full_replay_state (replayed_trace_from full_replay_state is tr).
Proof.
  unfold composite_no_equivocation_vlsm_with_pre_loaded in SeededAllXE.
  specialize
    (sub_preloaded_replayed_trace_from_valid_equivocating
      (no_equivocations_additional_constraint_with_pre_loaded equivocator_IM (free_constraint _) seed)
      seed)
      as Hvalid.
  spec Hvalid; [split; exact I|].
  spec Hvalid; [apply sent_are_valid|].
  specialize (Hvalid _ Hfull_replay_state).
  apply Hvalid; [|assumption].
  intros.
  apply SeededNoEquiv_subsumption.
  assumption.
Qed.

End seeded_no_equiv.

End all_equivocating.
