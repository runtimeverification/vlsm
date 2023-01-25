From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From Coq Require Import FunctionalExtensionality Lia.
From stdpp Require Import prelude finite.
From VLSM.Lib Require Import Preamble ListExtras StdppListSet StdppExtras StdppListFinSet.
From VLSM.Core Require Import VLSM VLSMProjections ProjectionTraces Composition Validator.
From VLSM.Core Require Import Equivocation EquivocationProjections Equivocation.NoEquivocation.

(** * VLSM Subcomposition *)

Section sec_sub_composition.

Context
  {message : Type}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  (sub_index_list : list index)
  .

Definition sub_index_prop (i : index) : Prop := i ∈ sub_index_list.

#[local] Program Instance sub_index_prop_dec
  (i : index)
  : Decision (sub_index_prop i).
Next Obligation.
Proof.
  intros; apply decide_rel; typeclasses eauto.
Qed.

Definition sub_index : Type := dsig sub_index_prop.

Definition sub_IM
  (ei : sub_index)
  : VLSM message
  := IM (proj1_sig ei).

Lemma sub_IM_state_pi
  {i : index}
  (s : composite_state sub_IM)
  (e1 e2 : sub_index_prop i)
  : s (dexist i e1) = s (dexist i e2).
Proof.
  unfold dexist.
  replace (bool_decide_pack _ e1) with (bool_decide_pack _ e2); [done |].
  by apply proof_irrel.
Qed.

Lemma sub_IM_state_update_eq
  (i : index)
  (s : composite_state sub_IM)
  (si : vstate (IM i))
  (e1 e2 : sub_index_prop i)
  : state_update sub_IM s (dexist i e1) si (dexist i e2) = si.
Proof.
  cut (forall be1 be2, be1 = be2 ->
      state_update sub_IM s (exist _ i be1) si (exist _ i be2) = si).
  - by intro Heq; apply Heq, proof_irrel.
  - by intros; subst; state_update_simpl.
Qed.

Lemma sub_IM_state_update_neq
  (s : composite_state sub_IM)
  (i : index)
  (ei : sub_index_prop i)
  (si : vstate (IM i))
  (j : index)
  (ej : sub_index_prop j)
  : i <> j ->
      state_update sub_IM s (dexist i ei) si (dexist j ej)
        =
      s (dexist j ej).
Proof.
  by intro Hneq; apply state_update_neq; inversion 1.
Qed.

Definition free_sub_vlsm_composition : VLSM message
  := free_composite_vlsm sub_IM.

Definition seeded_free_sub_composition
  (messageSet : message -> Prop)
  := pre_loaded_vlsm free_sub_vlsm_composition
      (fun m => messageSet m \/ composite_initial_message_prop IM m).

Definition composite_state_sub_projection
  (s : composite_state IM)
  : composite_state sub_IM
  := fun (subi : sub_index) => s (proj1_sig subi) : vstate (sub_IM subi).

Lemma composite_initial_state_sub_projection
  (s : composite_state IM)
  (Hs : composite_initial_state_prop IM s)
  : composite_initial_state_prop sub_IM (composite_state_sub_projection s).
Proof.
  by intros [i Hi]; apply Hs.
Qed.

Definition composite_label_sub_projection
  (l : composite_label IM)
  (i := projT1 l)
  (e : sub_index_prop i)
  : composite_label sub_IM
  :=
  existT (dexist i e) (projT2 l).

Definition lift_sub_label
  (l : composite_label sub_IM)
  : composite_label IM
  :=
  existT (proj1_sig (projT1 l)) (projT2 l).

Definition lift_sub_state_to
  (s0 : composite_state IM)
  (s : composite_state sub_IM)
  : composite_state IM
  := fun i =>
    match @decide  (sub_index_prop i) (sub_index_prop_dec i) with
    | left e =>  s (dexist i e)
    | _ => s0 i
    end.

Definition lift_sub_state := lift_sub_state_to (fun (n : index) => proj1_sig (vs0 (IM n))).

Lemma lift_sub_state_to_eq
  (s0 : composite_state IM)
  (s : composite_state sub_IM)
  i
  (Hi : sub_index_prop i)
  : lift_sub_state_to s0 s i = s (dexist i Hi).
Proof.
  unfold lift_sub_state_to.
  by case_decide; [apply sub_IM_state_pi |].
Qed.

Lemma lift_sub_state_to_neq
  (s0 : composite_state IM)
  (s : composite_state sub_IM)
  i
  (Hni : ~ sub_index_prop i)
  : lift_sub_state_to s0 s i = s0 i.
Proof.
  by unfold lift_sub_state_to; case_decide.
Qed.

Lemma composite_state_sub_projection_lift_to
  (s0 : composite_state IM)
  (s : composite_state sub_IM)
  : composite_state_sub_projection (lift_sub_state_to s0 s) = s.
Proof.
  extensionality sub_i.
  destruct_dec_sig sub_i i Hi Heqsub_i.
  subst.
  unfold composite_state_sub_projection.
  simpl.
  by rewrite lift_sub_state_to_eq with (Hi := Hi).
Qed.

Lemma lift_sub_state_to_neq_state_update
  (s0 : composite_state IM)
  (s : composite_state sub_IM)
  i
  (Hni : ~ sub_index_prop i)
  si'
  : state_update IM (lift_sub_state_to s0 s) i si' =
    lift_sub_state_to (state_update IM s0 i si') s.
Proof.
  symmetry.
  extensionality j.
  unfold lift_sub_state_to.
  by destruct (decide (i = j)); subst; state_update_simpl; case_decide.
Qed.

#[local] Hint Rewrite @sub_IM_state_update_eq using done : state_update.
#[local] Hint Rewrite @sub_IM_state_update_neq using done : state_update.
#[local] Hint Rewrite @lift_sub_state_to_eq using done : state_update.
#[local] Hint Rewrite @lift_sub_state_to_neq using done : state_update.
#[local] Hint Rewrite @lift_sub_state_to_neq_state_update using done : state_update.

Section sec_induced_sub_projection.

Context
  (constraint : composite_label IM -> composite_state IM * option message -> Prop)
  (X := composite_vlsm IM constraint)
  .

Definition composite_label_sub_projection_option
  (l : composite_label IM)
  : option (composite_label sub_IM) :=
  match decide (projT1 l ∈ sub_index_list) with
  | left i_in => Some (composite_label_sub_projection l i_in)
  | _ => None
  end.

(**
  By restricting the components of a composition to a subset we obtain a
  [projection_induced_validator].
*)
Definition pre_induced_sub_projection : VLSM message :=
  pre_projection_induced_validator X (composite_type sub_IM)
    composite_label_sub_projection_option
    composite_state_sub_projection
    lift_sub_label lift_sub_state.

Lemma induced_sub_projection_transition_consistency_None
  : weak_projection_transition_consistency_None X (composite_type sub_IM)
      composite_label_sub_projection_option composite_state_sub_projection.
Proof.
  intros lX HlX sX om s'X om' HtX.
  extensionality sub_i.
  destruct_dec_sig sub_i i Hi Heqsub_i.
  subst sub_i.
  unfold composite_state_sub_projection. simpl.
  destruct lX as [x v].
  apply proj2 in HtX. cbn in HtX.
  destruct (vtransition _ _ _) as (si', _om').
  inversion_clear HtX.
  rewrite state_update_neq; [done | intros ->].
  unfold composite_label_sub_projection_option in HlX; simpl in HlX.
  by case_decide.
Qed.

Lemma composite_label_sub_projection_option_lift
  : induced_validator_label_lift_prop composite_label_sub_projection_option lift_sub_label.
Proof.
  intros [sub_i li].
  destruct_dec_sig sub_i i Hi Heqsub_i; subst.
  unfold lift_sub_label, composite_label_sub_projection_option, composite_label_sub_projection; cbn.
  case_decide; [f_equal | done].
  by apply (@dec_sig_sigT_eq _ _ sub_index_prop_dec (fun i => vlabel (IM i))).
Qed.

Lemma composite_state_sub_projection_lift
  : induced_validator_state_lift_prop composite_state_sub_projection lift_sub_state.
Proof. by intro; apply composite_state_sub_projection_lift_to. Qed.

Lemma composite_trace_sub_projection_lift
  (tr : list (composite_transition_item sub_IM))
  : @pre_VLSM_projection_finite_trace_project _ (composite_type IM) _
    composite_label_sub_projection_option composite_state_sub_projection
    (pre_VLSM_embedding_finite_trace_project _ _ lift_sub_label lift_sub_state tr)
    = tr.
Proof.
  apply (induced_validator_trace_lift (free_composite_vlsm IM)).
  - by apply composite_label_sub_projection_option_lift.
  - by apply composite_state_sub_projection_lift.
Qed.

Lemma induced_sub_projection_transition_consistency_Some
  : induced_validator_transition_consistency_Some X (composite_type sub_IM)
      composite_label_sub_projection_option composite_state_sub_projection.
Proof.
  intros lX1 lX2 lY HlX1_pr HlX2_pr sX1 sX2 HsXeq_pr iom sX1' oom1 Ht1 sX2' oom2 Ht2.
  destruct lX1 as (i, lXi).
  unfold composite_label_sub_projection_option in HlX1_pr.
  simpl in HlX1_pr. case_decide as Hi; [| done].
  apply Some_inj in HlX1_pr. subst lY.
  destruct lX2 as (_i, _lXi).
  unfold composite_label_sub_projection_option in HlX2_pr.
  simpl in HlX2_pr. case_decide as H_i; [| done].
  apply Some_inj in HlX2_pr.
  unfold composite_label_sub_projection in HlX2_pr.
  simpl in HlX2_pr.
  inversion HlX2_pr.
  subst _i.
  apply
    (@dec_sig_sigT_eq_rev _ _ _ sub_index_prop_dec (fun i => vlabel (IM i)))
    in HlX2_pr as ->.
  apply f_equal_dep with (x := dexist i Hi) in HsXeq_pr as HsXeq_pri.
  cbv in HsXeq_pri.
  cbn in Ht1, Ht2.
  rewrite <- HsXeq_pri in Ht2.
  destruct (vtransition _ _ _) as (si', om').
  inversion Ht1. subst. clear Ht1.
  inversion Ht2. subst. clear Ht2.
  split; [| done].
  extensionality sub_j.
  apply f_equal_dep with (x := sub_j) in HsXeq_pr.
  destruct_dec_sig sub_j j Hj Heqsub_j.
  subst.
  unfold composite_state_sub_projection in HsXeq_pr |- *.
  simpl in HsXeq_pr |- *.
  by destruct (decide (i = j)); subst; state_update_simpl.
Qed.

(**
  The [pre_induced_sub_projection] is actually a [VLSM_projection] of the
  original composition.
*)
Lemma induced_sub_projection_is_projection
  : VLSM_projection X pre_induced_sub_projection
    composite_label_sub_projection_option
    composite_state_sub_projection.
Proof.
  apply projection_induced_validator_is_projection.
  - by apply composite_label_sub_projection_option_lift.
  - by apply composite_state_sub_projection_lift.
  - by apply induced_sub_projection_transition_consistency_Some.
  - by apply induced_sub_projection_transition_consistency_None.
Qed.

Lemma induced_sub_projection_valid_projection l s om
  (Hv : vvalid pre_induced_sub_projection l (s, om))
  : exists i, i ∈ sub_index_list /\
    exists l s, input_valid (pre_loaded_with_all_messages_vlsm (IM i)) l (s, om).
Proof.
  destruct l as (sub_i, li).
  destruct Hv as (lX & sX & [HlX Heqs (HsX & Hom & Hv)]).
  destruct lX as [i _li].
  unfold composite_label_sub_projection_option in HlX.
  simpl in HlX.
  case_decide; [| by congruence].
  unfold composite_label_sub_projection in HlX.
  simpl in HlX.
  apply Some_inj in HlX.
  simplify_eq.
  exists i.
  split; [done |].
  exists _li, (sX i).
  repeat split; [| by apply any_message_is_valid_in_preloaded | by apply Hv].
  apply (VLSM_projection_valid_state (preloaded_component_projection IM i)).
  apply (VLSM_incl_valid_state (vlsm_incl_pre_loaded_with_all_messages_vlsm
    (free_composite_vlsm IM))).
  by apply (VLSM_incl_valid_state (constraint_free_incl IM constraint)).
Qed.

Lemma induced_sub_projection_transition_is_composite l s om
  : vtransition pre_induced_sub_projection l (s, om) = composite_transition sub_IM l (s, om).
Proof.
  destruct l as (sub_i, li).
  destruct_dec_sig sub_i i Hi Heqsub_i; subst.
  cbn; unfold sub_IM, lift_sub_state;
  rewrite lift_sub_state_to_eq with (Hi := Hi); cbn;
  destruct (vtransition _ _ _) as (si', om').
  f_equal; extensionality sub_k.
  destruct_dec_sig sub_k k Hk Heqsub_k; subst.
  unfold composite_state_sub_projection; cbn.
  destruct (decide (i = k)); subst; state_update_simpl; [done |].
  by apply lift_sub_state_to_eq.
Qed.

End sec_induced_sub_projection.

Section sec_induced_sub_projection_subsumption.

Context
  (constraint1 : composite_label IM -> composite_state IM * option message -> Prop)
  (constraint2 : composite_label IM -> composite_state IM * option message -> Prop)
  .

Lemma induced_sub_projection_constraint_subsumption_incl
  (Hsubsumption : input_valid_constraint_subsumption IM constraint1 constraint2)
  : VLSM_incl (pre_induced_sub_projection constraint1) (pre_induced_sub_projection constraint2).
Proof.
  apply projection_induced_validator_incl.
  - by apply composite_label_sub_projection_option_lift.
  - by apply composite_state_sub_projection_lift.
  - by apply induced_sub_projection_transition_consistency_Some.
  - by apply induced_sub_projection_transition_consistency_Some.
  - by apply constraint_subsumption_incl.
Qed.

End sec_induced_sub_projection_subsumption.

Definition from_sub_projection : composite_transition_item IM -> Prop :=
  @pre_VLSM_projection_in_projection _ (composite_type IM) _ composite_label_sub_projection_option.

Definition finite_trace_sub_projection
  : list (composite_transition_item IM) -> list (composite_transition_item sub_IM) :=
  @pre_VLSM_projection_finite_trace_project _ (composite_type IM) _
    composite_label_sub_projection_option composite_state_sub_projection.

Section sec_sub_projection_with_no_equivocation_constraints.

Context
  (constraint : composite_label IM -> composite_state IM * option message -> Prop)
  `{forall i : index, (HasBeenSentCapability (IM i))}
  (Free := free_composite_vlsm IM)
  (Sub_Free := free_composite_vlsm sub_IM)
  (X := composite_vlsm IM constraint)
  (Pre := pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM))
  .

Program Definition sub_index_list_annotate : list sub_index :=
  list_annotate _ sub_index_list _.
Next Obligation.
Proof.
  by apply Forall_forall.
Qed.

#[export] Instance stdpp_finite_sub_index
  : finite.Finite sub_index.
Proof.
  exists (remove_dups sub_index_list_annotate).
  - by apply NoDup_remove_dups.
  - intro sub_x.
    apply elem_of_remove_dups, elem_of_list_annotate.
    by destruct_dec_sig sub_x x Hx Heqsub_x; subst.
Qed.

Definition finite_trace_sub_projection_app
  (tr1 tr2 : list (composite_transition_item IM)) :
  finite_trace_sub_projection (tr1 ++ tr2) =
  finite_trace_sub_projection tr1 ++ finite_trace_sub_projection tr2
  :=
    @pre_VLSM_projection_finite_trace_project_app _ (composite_type IM) _
      composite_label_sub_projection_option composite_state_sub_projection tr1 tr2.

Lemma X_incl_Pre : VLSM_incl X Pre.
Proof.
  apply VLSM_incl_trans with (machine (free_composite_vlsm IM)).
  - by apply (constraint_free_incl IM constraint).
  - by apply vlsm_incl_pre_loaded_with_all_messages_vlsm.
Qed.

Lemma finite_trace_sub_projection_last_state
  (start : composite_state IM)
  (transitions : list (composite_transition_item IM))
  (Htr : finite_valid_trace_from X start transitions)
  (lstx := finite_trace_last start transitions)
  (lstj := finite_trace_last
    (composite_state_sub_projection start)
    (finite_trace_sub_projection transitions))
  : lstj = composite_state_sub_projection lstx.
Proof.
  by apply (VLSM_projection_finite_trace_last (induced_sub_projection_is_projection constraint))
        in Htr.
Qed.

Lemma transition_sub_projection
  l s om s' om'
  (Ht : composite_transition IM l  (s, om) = (s', om'))
  (Hsub : sub_index_prop (projT1 l))
  : composite_transition sub_IM
    (existT
      (dexist (projT1 l) Hsub)
      (projT2 l))
    (composite_state_sub_projection s, om)
    = (composite_state_sub_projection s', om').
Proof.
  simpl. simpl in Ht.
  destruct l as (i, li).
  unfold vtransition. simpl.
  unfold composite_state_sub_projection at 1. simpl.
  destruct (vtransition (IM i) li (s i, om)) as (si', omi') eqn: Hti.
  inversion Ht. subst omi' s'. clear Ht.
  match goal with
  |- (let (_, _) := ?t in _) = _ =>
    replace t with (si', om')
  end.
  f_equal.
  extensionality sub_j.
  destruct_dec_sig sub_j j Hj Heqj.
  unfold composite_state_sub_projection at 2.
  by destruct (decide (i = j)); subst; state_update_simpl.
Qed.

Lemma valid_sub_projection
  l s om
  (Hv : composite_valid IM l  (s, om))
  (Hsub : sub_index_prop (projT1 l))
  : composite_valid sub_IM
    (existT
      (dexist (projT1 l) Hsub)
      (projT2 l))
    (composite_state_sub_projection s, om).
Proof. by destruct l. Qed.

Context
  (seed : message -> Prop)
  (sub_constraint : composite_label sub_IM -> composite_state sub_IM * option message -> Prop)
  (Xj := composite_no_equivocation_vlsm_with_pre_loaded sub_IM (free_constraint sub_IM) seed)
  .

Lemma Xj_incl_Pre_Sub_Free
  : VLSM_incl Xj (pre_loaded_with_all_messages_vlsm Sub_Free).
Proof.
  subst Xj.
  unfold composite_no_equivocation_vlsm_with_pre_loaded.
  specialize
    (preloaded_constraint_subsumption_incl sub_IM
      (no_equivocations_additional_constraint_with_pre_loaded sub_IM
        (free_constraint sub_IM)
        seed)
      (free_constraint sub_IM))
    as Hincl.
  spec Hincl; [done |].
  match goal with
  |- context [pre_loaded_vlsm ?v _] =>
    apply VLSM_incl_trans with (machine (pre_loaded_with_all_messages_vlsm v))
  end; [| apply Hincl].
  clear Hincl.
  match goal with
  |- context [pre_loaded_with_all_messages_vlsm ?v] =>
    apply VLSM_incl_trans with (machine (pre_loaded_vlsm v (fun m => True)))
  end.
  - match goal with
    |- context [pre_loaded_vlsm ?v _] =>
      apply (pre_loaded_vlsm_incl v seed (fun m => True))
    end.
    itauto.
  - match goal with
    |- context [pre_loaded_with_all_messages_vlsm ?v] =>
      specialize (pre_loaded_with_all_messages_vlsm_is_pre_loaded_with_True v) as Hincl
    end.
    by apply VLSM_eq_incl_iff, proj2 in Hincl.
Qed.

(**
  Property of a composite trace requiring that every message received in an
  transition involving a machine in the chosen subset must either belong to
  the set specified by [seed], or it must [have_been_sent] by some machine
  in the chosen subset (prior to it being received).
*)
Definition trace_sub_item_input_is_seeded_or_sub_previously_sent
  (tr : list (composite_transition_item IM))
  : Prop
  :=
  forall pre item suf m,
    tr = pre ++ [item] ++ suf ->
    input item = Some m ->
    from_sub_projection item ->
      seed m \/
      exists pre_item,
        pre_item ∈ pre /\
        output pre_item = Some m /\
        from_sub_projection pre_item.

Definition state_sub_item_input_is_seeded_or_sub_previously_sent
  (s : composite_state IM)
  : Prop
  := forall is tr,
    finite_valid_trace_init_to Pre is s tr ->
    trace_sub_item_input_is_seeded_or_sub_previously_sent tr.

Lemma finite_valid_trace_sub_projection
  (s : composite_state IM)
  (tr : list (composite_transition_item IM))
  (Hmsg :  trace_sub_item_input_is_seeded_or_sub_previously_sent tr)
  (Htr : finite_valid_trace X s tr)
  : finite_valid_trace Xj (composite_state_sub_projection s) (finite_trace_sub_projection tr).
Proof.
  destruct Htr as [Htr His].
  apply (composite_initial_state_sub_projection s) in His.
  split; [| done].
  apply (initial_state_is_valid Xj) in His as Hisp.
  induction tr using rev_ind; simpl
  ; [by constructor |].
  apply finite_valid_trace_from_app_iff in Htr.
  destruct Htr as [Htr Hx].
  spec IHtr.
  { intros pre item suf m Heq Hin_m Hitem.
    subst tr.
    specialize (Hmsg pre item (suf ++ [x]) m).
    rewrite! app_assoc in Hmsg.
    by destruct (Hmsg eq_refl Hin_m Hitem); [left | right].
  }
  specialize (IHtr Htr).
  rewrite finite_trace_sub_projection_app.
  apply finite_valid_trace_from_app_iff.
  split; [done |].
  match goal with
  |- finite_valid_trace_from _ ?l _ => remember l as lst
  end.
  assert (Hlst : valid_state_prop Xj lst).
  { by apply finite_valid_trace_last_pstate in IHtr; subst. }
  simpl.
  unfold pre_VLSM_projection_transition_item_project, composite_label_sub_projection_option.
  case_decide as Hlx; [| by constructor].
  apply (finite_valid_trace_singleton Xj).
  inversion Hx; subst. simpl in *.
  destruct Ht as [Hv Ht].
  specialize (transition_sub_projection _ _ _ _ _ Ht Hlx)
    as Htj.
  destruct Hv as [_ [_ [Hv Hc]]].
  specialize (valid_sub_projection _ _ _ Hv Hlx)
    as Hvj.
  rewrite <- (finite_trace_sub_projection_last_state s tr Htr) in Htj, Hvj.
  repeat split; [done | | done | | done].
  - destruct iom as [m |]; [| by apply (option_valid_message_None Xj)].
    apply (option_valid_message_Some Xj).
    clear -Hmsg m Hlx IHtr tr.
    remember {| input := Some m |} as x.
    specialize (Hmsg tr x []).
    assert (Hx : from_sub_projection x).
    {
      unfold from_sub_projection at 1, pre_VLSM_projection_in_projection,
        composite_label_sub_projection_option.
      by subst; case_decide.
    }
    rewrite Heqx in Hmsg.
    specialize (Hmsg m eq_refl eq_refl).
    spec Hmsg; [by subst |].
    destruct Hmsg as [Hseed | [item [Hitem [Hout Hsub_item]]]]
    ; [by apply (initial_message_is_valid Xj); right |].
    apply (valid_trace_output_is_valid Xj _ _ IHtr).
    apply Exists_exists.
    specialize
      (@pre_VLSM_projection_transition_item_project_is_Some _ (composite_type IM) _
        composite_label_sub_projection_option composite_state_sub_projection
        item Hsub_item)
      as [itemX HitemX].
    exists itemX.
    split.
    + by apply elem_of_map_option; exists item.
    + unfold pre_VLSM_projection_transition_item_project in HitemX.
      destruct (composite_label_sub_projection_option _); [| by congruence].
      by inversion HitemX.
  - clear -Hmsg Sub_Free Hlst His IHtr.
    destruct iom as [m |]; [| done].
    simpl in *.
    remember {| input := Some m |} as x.
    assert (Hx : from_sub_projection x).
    {
      unfold from_sub_projection at 1, pre_VLSM_projection_in_projection,
        composite_label_sub_projection_option.
      by subst; case_decide.
    }
    specialize (Hmsg tr x []). rewrite Heqx in Hmsg.
    specialize (Hmsg m eq_refl eq_refl).
    spec Hmsg; [by subst |].
    destruct Hmsg as [Hseed | [item [Hitem [Hout Hsub_item]]]]; [by right |].
    left.
    remember (finite_trace_last (composite_state_sub_projection _) _) as lst.
    assert (Hlst_pre : valid_state_prop (pre_loaded_with_all_messages_vlsm Sub_Free) lst)
      by (revert Hlst; apply VLSM_incl_valid_state, Xj_incl_Pre_Sub_Free; done).
    apply composite_proper_sent; [done |].
    apply has_been_sent_consistency; [by typeclasses eauto | done |].
    exists (composite_state_sub_projection s), (finite_trace_sub_projection tr).
    split.
    + split; [| done].
      apply (VLSM_incl_finite_valid_trace_from_to Xj_incl_Pre_Sub_Free).
      by apply valid_trace_add_last; auto.
    + apply Exists_exists.
      assert
        (Hsome : is_Some
          (pre_VLSM_projection_transition_item_project
            (composite_type IM) (composite_type sub_IM)
            composite_label_sub_projection_option composite_state_sub_projection
            item))
        by (apply pre_VLSM_projection_transition_item_project_is_Some; done).
      exists (is_Some_proj Hsome).
      destruct (pre_VLSM_projection_transition_item_project _ _ _ _ _) eqn: Hproj;
      [| contradict Hsome; apply is_Some_None].
      cbn.
      split.
      * by apply elem_of_map_option; exists item.
      * unfold pre_VLSM_projection_transition_item_project in Hproj.
        by destruct (composite_label_sub_projection_option _); [inversion Hproj | congruence].
Qed.

Lemma valid_state_sub_projection
  (s : state)
  (Hs : state_sub_item_input_is_seeded_or_sub_previously_sent s)
  (Hps : valid_state_prop X s)
  : valid_state_prop Xj (composite_state_sub_projection s).
Proof.
  apply valid_state_has_trace in Hps.
  destruct Hps as [is [tr Htr]].
  specialize (Hs _ _ (VLSM_incl_finite_valid_trace_init_to X_incl_Pre _ _ _ Htr)).
  apply valid_trace_get_last in Htr as Hlst.
  apply valid_trace_forget_last in Htr.
  specialize (finite_trace_sub_projection_last_state _ _ (proj1 Htr)) as Hlst'.
  apply (finite_valid_trace_sub_projection _ _ Hs) in Htr as Hptr.
  - destruct Hptr as [Hptr _]. apply finite_valid_trace_last_pstate in Hptr.
    by cbn in *; rewrite Hlst' in Hptr; subst.
Qed.

Lemma finite_valid_trace_from_sub_projection
  (s : composite_state IM)
  (tr : list (composite_transition_item IM))
  (lst := finite_trace_last s tr)
  (Hmsg : state_sub_item_input_is_seeded_or_sub_previously_sent lst)
  (Htr : finite_valid_trace_from X s tr)
  : finite_valid_trace_from Xj (composite_state_sub_projection s) (finite_trace_sub_projection tr).
Proof.
  apply finite_valid_trace_from_complete_left in Htr.
  destruct Htr as [is [pre [Htr Hs]]].
  assert (Hpre := proj1 Htr).
  apply finite_valid_trace_from_app_iff in Hpre.
  destruct Hpre as [Hpre _].
  specialize (finite_trace_sub_projection_last_state _ _ Hpre) as Hpre_lst.
  apply finite_valid_trace_sub_projection in Htr.
  - destruct Htr as [Htr His].
    rewrite finite_trace_sub_projection_app in Htr.
    apply finite_valid_trace_from_app_iff in Htr.
    destruct Htr as [_ Htr].
    subst s. simpl in *.
    by rewrite Hpre_lst in Htr.
  - specialize (Hmsg is (pre ++ tr)).
    apply Hmsg.
    apply (VLSM_incl_finite_valid_trace_init_to X_incl_Pre).
    apply valid_trace_add_last; [done |].
    rewrite finite_trace_last_app.
    by unfold lst; subst.
Qed.

End sec_sub_projection_with_no_equivocation_constraints.

Lemma lift_sub_state_initial
  (s : composite_state sub_IM)
  (Hs : composite_initial_state_prop sub_IM s)
  : composite_initial_state_prop IM (lift_sub_state s).
Proof.
  intros i.
  unfold lift_sub_state, lift_sub_state_to.
  case_decide as Hi.
  - by apply (Hs (dexist i Hi)).
  - by destruct (vs0 _).
Qed.

Lemma lift_sub_state_to_initial
  (s0 : composite_state IM)
  (Hs0 : composite_initial_state_prop IM s0)
  (s : composite_state sub_IM)
  (Hs : composite_initial_state_prop sub_IM s)
  : composite_initial_state_prop IM (lift_sub_state_to s0 s).
Proof.
  intros i.
  unfold lift_sub_state_to.
  case_decide as Hi.
  - by apply (Hs (dexist i Hi)).
  - by apply Hs0.
Qed.

Lemma lift_sub_message_initial
  (m : message)
  (Hm : composite_initial_message_prop sub_IM m)
  : composite_initial_message_prop IM m.
Proof.
  destruct Hm as [[i Hi] Hm].
  unfold sub_IM in Hm. simpl in Hm.
  by exists i.
Qed.

Lemma lift_sub_valid l s om
  (Hv : composite_valid sub_IM l (s, om))
  : composite_valid IM (lift_sub_label l) (lift_sub_state s, om).
Proof.
  revert Hv.
  destruct l as (sub_i, li).
  destruct_dec_sig sub_i i Hi Heqsub_i.
  simpl.
  unfold vvalid. unfold lift_sub_state, lift_sub_state_to.
  simpl.
  subst. simpl.
  unfold sub_IM in li. simpl in li.
  case_decide as _Hi; [| done].
  by rewrite (sub_IM_state_pi s _Hi Hi); auto.
Qed.

Lemma lift_sub_transition l s om s' om'
  (Ht : composite_transition sub_IM l (s, om) = (s', om'))
  : composite_transition IM
    (lift_sub_label l) (lift_sub_state s, om) = (lift_sub_state s', om').
Proof.
  revert Ht.
  destruct l as (sub_i, li).
  destruct_dec_sig sub_i i Hi Heqsub_i.
  simpl.
  unfold vtransition. unfold lift_sub_state at 1. unfold lift_sub_state_to.
  simpl.
  subst. simpl.
  unfold sub_IM in li. simpl in li.
  case_decide as _Hi; [| done].
  rewrite (sub_IM_state_pi s _Hi Hi).
  clear _Hi; destruct (transition _ _) as (si', _om'); inversion_clear 1.
  f_equal; extensionality j.
  unfold lift_sub_state, lift_sub_state_to.
  by destruct (decide (i = j)); subst; state_update_simpl; case_decide; state_update_simpl.
Qed.

End sec_sub_composition.

#[export] Hint Rewrite @sub_IM_state_update_eq using done : state_update.
#[export] Hint Rewrite @sub_IM_state_update_neq using done : state_update.
#[export] Hint Rewrite @lift_sub_state_to_eq using done : state_update.
#[export] Hint Rewrite @lift_sub_state_to_neq using done : state_update.
#[export] Hint Rewrite @lift_sub_state_to_neq_state_update using done : state_update.

Arguments sub_IM_state_pi {_ _ _ _ _ _} _ _ _.

(*
  Make initial arguments of lift_sub_transition not maximally inserted,
  so tactics like rapply lift_sub_transition
  do not try to guess those arguments before looking at the goal,
  and we don't have to always write rapply @lift_sub_transition.
*)
Arguments lift_sub_transition [message index]%type_scope {EqDecision0} IM%function_scope
  sub_index_list%list_scope l s om s' om' Ht.

(** ** Lifting a trace from a sub-composition to the full composition

  In this section we first show that given a valid state for a composition of
  all nodes we can reset some of its state-components to initial states for those
  components without losing the valid state property.

  The set of nodes for which the reset operation will happen is <<equivocators>>.

  We then show that a similar result holds for replacing the equivocator
  components with the components corresponding to any valid state of the
  composition of just the equivocators.

  We proving those results for compositions pre-loaded with all messages
  (Lemmas [reset_equivocating_transitions_preloaded_projection] and
  [PreSubFree_PreFree_weak_embedding]).
*)

Section sec_lift_sub_state_to_preloaded.

Context
  {message : Type}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  (equivocators : list index)
  (Free := free_composite_vlsm IM)
  (PreFree := pre_loaded_with_all_messages_vlsm Free)
  (equivocating_IM := sub_IM IM equivocators)
  (SubFree : VLSM message :=  free_composite_vlsm equivocating_IM)
  (PreSubFree := pre_loaded_with_all_messages_vlsm SubFree)
  (base_s : composite_state IM)
  (Hbase_s : valid_state_prop PreFree base_s)
  .

(** A partial label projection function which only keeps non-equivocating transitions. *)
Definition remove_equivocating_label_project (l : composite_label IM) : option (composite_label IM)
  := if decide (projT1 l ∈ equivocators) then None else Some l.

(** Replaces the state components of the given state with those of <<eqv_is>>. *)
Definition remove_equivocating_state_project eqv_is
  : composite_state IM -> composite_state IM
  := fun s => lift_sub_state_to IM equivocators s eqv_is.

Lemma remove_equivocating_strong_projection_valid_preservation eqv_is :
  strong_projection_valid_preservation Free Free
    remove_equivocating_label_project (remove_equivocating_state_project eqv_is).
Proof.
  intros lX lY Hl s om Hv.
  destruct lX as (i, liX).
  unfold remove_equivocating_label_project in Hl.
  simpl in Hl.
  destruct (decide _); [by congruence |].
  inversion Hl. subst lY. clear Hl.
  split; [| done].
  cbn in Hv |- *.
  unfold remove_equivocating_state_project.
  by rewrite lift_sub_state_to_neq; [apply Hv |].
Qed.

Lemma remove_equivocating_strong_projection_transition_preservation_Some eqv_is :
  strong_projection_transition_preservation_Some Free Free
    remove_equivocating_label_project (remove_equivocating_state_project eqv_is).
Proof.
  intros lX lY Hl s om s' om' Ht.
  destruct lX as (i, liX).
  unfold remove_equivocating_label_project in Hl.
  simpl in Hl.
  destruct (decide _); [by congruence |].
  inversion Hl. subst lY. clear Hl.
  cbn in Ht |- *.
  unfold remove_equivocating_state_project.
  rewrite lift_sub_state_to_neq by done.
  destruct (vtransition _ _ _) as (si', _om').
  inversion_clear Ht.
  f_equal; extensionality j.
  by destruct (decide (i = j)); subst; state_update_simpl.
Qed.

Lemma remove_equivocating_strong_projection_transition_consistency_None eqv_is :
  @strong_projection_transition_consistency_None _ Free _
    remove_equivocating_label_project (remove_equivocating_state_project eqv_is).
Proof.
  intros lX Hl s om s' om' Ht.
  destruct lX as (i, liX).
  unfold remove_equivocating_label_project in Hl.
  simpl in Hl.
  case_decide; [| by congruence]. clear Hl.
  cbn in Ht.
  destruct (vtransition _ _ _) as (si', _om').
  inversion_clear Ht.
  extensionality j.
  unfold remove_equivocating_state_project, lift_sub_state_to.
  case_decide; [done |].
  by destruct (decide (i = j)); subst; state_update_simpl.
Qed.

Lemma remove_equivocating_strong_embedding_initial_state_preservation eqv_is
  (Heqv_is : composite_initial_state_prop (sub_IM IM equivocators) eqv_is) :
  strong_projection_initial_state_preservation Free Free
    (remove_equivocating_state_project eqv_is).
Proof.
  intros s Hs i.
  unfold remove_equivocating_state_project, lift_sub_state_to.
  destruct (decide _); [| done].
  by apply (Heqv_is (dexist i s0)).
Qed.

(**
  Given any valid trace for the composition of all nodes and an initial state
  for the composition of just the equivocators, the trace obtained by resetting
  the components corresponding to the equivocators to those of the given initial
  state and removing the transitions corresponding to the equivocators is
  still a valid trace.
*)
Lemma remove_equivocating_transitions_preloaded_projection eqv_is
  (Heqv_is : composite_initial_state_prop (sub_IM IM equivocators) eqv_is) :
  VLSM_projection PreFree PreFree
    remove_equivocating_label_project (remove_equivocating_state_project eqv_is).
Proof.
  apply basic_VLSM_projection_preloaded.
  - by apply remove_equivocating_strong_projection_valid_preservation.
  - by apply remove_equivocating_strong_projection_transition_preservation_Some.
  - by apply remove_equivocating_strong_projection_transition_consistency_None.
  - by apply remove_equivocating_strong_embedding_initial_state_preservation.
Qed.

Lemma preloaded_lift_sub_state_to_initial_state :
  weak_projection_initial_state_preservation PreSubFree PreFree
    (lift_sub_state_to IM equivocators base_s).
Proof.
  apply valid_state_has_trace in Hbase_s as Htr.
  destruct Htr as [is [tr Htr]].
  intros eqv_is Heqv_is.
  apply (VLSM_projection_finite_valid_trace_init_to
    (remove_equivocating_transitions_preloaded_projection _ Heqv_is)) in Htr.
  by apply valid_trace_last_pstate in Htr.
Qed.

Lemma lift_sub_to_valid l s om
  (Hv : composite_valid (sub_IM IM equivocators) l (s, om)) :
  composite_valid IM (lift_sub_label IM equivocators l)
    (lift_sub_state_to IM equivocators base_s s, om).
Proof.
  revert Hv. destruct l as (i, li).
  destruct_dec_sig i j Hj Heq. subst i.
  simpl. unfold equivocating_IM, sub_IM. simpl.
  by erewrite lift_sub_state_to_eq.
Qed.

Lemma lift_sub_to_transition l s om s' om'
  (Ht : composite_transition (sub_IM IM equivocators) l (s, om) = (s', om'))
  : composite_transition IM
    (lift_sub_label IM equivocators l) (lift_sub_state_to IM equivocators base_s s, om) =
    (lift_sub_state_to IM equivocators base_s s', om').
Proof.
  destruct l as (i, li).
  destruct_dec_sig i j Hj Heq. subst i.
  revert Ht. unfold vtransition. simpl. unfold vtransition. simpl.
  rewrite lift_sub_state_to_eq with (Hi := Hj).
  destruct (transition _ _) as (si', _om').
  inversion_clear 1.
  f_equal; extensionality i.
  destruct (decide (i = j)); subst; state_update_simpl.
  - by rewrite lift_sub_state_to_eq with (Hi := Hj); state_update_simpl.
  - destruct (decide (i ∈ equivocators)).
    + by rewrite !lift_sub_state_to_eq with (Hi := e); state_update_simpl.
    + by state_update_simpl.
Qed.

(**
  Given any valid state for the composition of all nodes and a valid trace
  for the composition of just the equivocators, the trace obtained by completing
  the state-components from the trace with the components from the given
  valid state is a valid trace for the composition of all nodes.
*)
Lemma PreSubFree_PreFree_weak_embedding :
  VLSM_weak_embedding PreSubFree PreFree
    (lift_sub_label IM equivocators) (lift_sub_state_to IM equivocators base_s).
Proof.
  apply basic_VLSM_weak_embedding.
  - split; [| done].
    by apply lift_sub_to_valid, Hv.
  - intros l s om s' om' Hv.
    by apply lift_sub_to_transition, Hv.
  - by apply preloaded_lift_sub_state_to_initial_state.
  - by intro; intros; apply any_message_is_valid_in_preloaded.
Qed.

(**
  If the composition constraint only depends on the projection sub-state,
  then valid traces of the [pre_induced_sub_projection] can be lifted to valid traces
  of the constrained composition.
*)
Lemma induced_sub_projection_lift
  (constraint : composite_label IM -> composite_state IM * option message -> Prop)
  (Hconstraint_consistency :
    forall s1 s2,
      composite_state_sub_projection IM equivocators s1
        =
      composite_state_sub_projection IM equivocators s2 ->
        forall l om, constraint l (s1, om) -> constraint l (s2, om))
   : VLSM_embedding
    (pre_induced_sub_projection IM equivocators constraint)
    (composite_vlsm IM constraint)
    (lift_sub_label IM equivocators)
    (lift_sub_state IM equivocators).
Proof.
  apply basic_VLSM_embedding.
  - intros l s om (_ & _ & (i, li) & sX & [Heql [=] (HsX & Hom & Hv & Hc)]) _ _.
    unfold composite_label_sub_projection_option in Heql; cbn in Heql.
    case_decide as Hi; [| by congruence].
    apply Some_inj in Heql; subst l; cbn.
    unfold constrained_composite_valid, lift_sub_state; cbn;
    rewrite (lift_sub_state_to_eq _ _ _ _ _ Hi); subst.
    split; [done |].
    eapply Hconstraint_consistency; [| done].
    by symmetry; apply composite_state_sub_projection_lift_to.
  - intros l s om s' om' [_ Ht]; revert Ht; cbn
    ; destruct (vtransition _ _ _) as [si' _om']
    ; inversion_clear 1.
    f_equal; extensionality i.
    destruct l as [sub_j lj]
    ; destruct_dec_sig sub_j j Hj Heqsub_j; subst; cbn
    ; destruct (decide (i = j)); subst.
    + unfold lift_sub_state, composite_state_sub_projection; cbn.
      by rewrite state_update_eq, lift_sub_state_to_eq with (Hi := Hj), state_update_eq.
    + state_update_simpl.
      destruct (decide (i ∈ equivocators)).
      * unfold lift_sub_state, composite_state_sub_projection; cbn.
        by rewrite !lift_sub_state_to_eq with (Hi := e), state_update_neq,
          lift_sub_state_to_eq with (Hi := e).
      * by unfold lift_sub_state, lift_sub_state_to; case_decide.
  - intros s Hs.
    apply (lift_sub_state_initial IM).
    destruct Hs as (sX & <- & HsX).
    by intro sub_i; destruct_dec_sig sub_i i Hi Heqsub_i; subst; apply HsX.
  - by intros _ ? m (_ & _ & _ & _ & [_ _ (_ & HmX & _)]).
Qed.

(**
  A specialization of [basic_projection_induces_friendliness] for
  [pre_induced_sub_projection]s.
*)
Lemma induced_sub_projection_friendliness
  (constraint : composite_label IM -> composite_state IM * option message -> Prop)
  (Hlift_proj : VLSM_embedding
    (pre_induced_sub_projection IM equivocators constraint)
    (composite_vlsm IM constraint)
    (lift_sub_label IM equivocators)
    (lift_sub_state IM equivocators))
  : projection_friendly_prop (induced_sub_projection_is_projection IM equivocators constraint).
Proof.
  unshelve eapply basic_projection_induces_friendliness; [| | | | done].
  - by apply composite_label_sub_projection_option_lift.
  - by apply composite_state_sub_projection_lift.
  - by apply induced_sub_projection_transition_consistency_Some.
  - by apply induced_sub_projection_transition_consistency_None.
Qed.

End sec_lift_sub_state_to_preloaded.

Section sec_sub_composition_incl.

Context
  {message : Type}
  `{EqDecision index}
  (IM : index -> VLSM message)
  (indices1 indices2 : list index)
  (Hincl : indices1 ⊆ indices2)
  (sub_IM1 := sub_IM IM indices1)
  (sub_IM2 := sub_IM IM indices2)
  (sub_index1_prop_dec :
    forall i, Decision (sub_index_prop indices1 i) := fun i => sub_index_prop_dec indices1 i)
  (sub_index2_prop_dec :
    forall i, Decision (sub_index_prop indices2 i) := fun i => sub_index_prop_dec indices2 i)
  .

Definition lift_sub_incl_state
  (s : composite_state sub_IM1)
  : composite_state sub_IM2
  := fun sub_i2 =>
    let i := proj1_sig sub_i2 in
    match @decide  (sub_index_prop indices1 i) (sub_index1_prop_dec i) with
    | left e =>  s (dexist i e)
    | _ => proj1_sig (vs0 (IM i))
    end.

Lemma lift_sub_incl_state_initial
  (s : composite_state sub_IM1)
  (Hs : composite_initial_state_prop sub_IM1 s)
  : composite_initial_state_prop sub_IM2 (lift_sub_incl_state s).
Proof.
  intros [i Hi].
  unfold lift_sub_incl_state.
  case_decide.
  - by apply (Hs (dexist i H)).
  - by destruct (vs0 _).
Qed.

Lemma lift_sub_incl_message_initial
  (m : message)
  (Hm : composite_initial_message_prop sub_IM1 m)
  : composite_initial_message_prop sub_IM2 m.
Proof.
  destruct Hm as [[i Hi] Hm].
  unfold sub_IM1, sub_IM in Hm. simpl in Hm.
  apply bool_decide_spec, Hincl in Hi.
  by exists (dexist i Hi).
Qed.

Definition lift_sub_incl_label
  (l : composite_label sub_IM1)
  : composite_label sub_IM2
  :=
  let sub1_i := projT1 l in
  let i := proj1_sig sub1_i in
  let H1i := proj2_dsig sub1_i in
  let H2i := Hincl _ H1i in
  existT (dexist i H2i) (projT2 l).

Lemma lift_sub_incl_valid l s om
  (Hv : composite_valid (sub_IM IM indices1) l (s, om))
  : composite_valid (sub_IM IM indices2) (lift_sub_incl_label l) (lift_sub_incl_state s, om).
Proof.
  revert Hv.
  destruct l as (sub1_i, li); destruct_dec_sig sub1_i i Hi Heqsub1_i; subst; cbn.
  unfold vvalid, lift_sub_incl_state; cbn.
  unfold sub_IM in li; simpl in li.
  destruct (decide (sub_index_prop indices1 i)) as [H_i |]
  ; [| done].
  by rewrite (sub_IM_state_pi s H_i Hi).
Qed.

Lemma lift_sub_incl_transition l s om s' om'
  (Ht : composite_transition (sub_IM IM indices1) l (s, om) = (s', om'))
  : composite_transition (sub_IM IM indices2)
    (lift_sub_incl_label l) (lift_sub_incl_state s, om) = (lift_sub_incl_state s', om').
Proof.
  revert Ht.
  destruct l as (sub1_i, li); destruct_dec_sig sub1_i i Hi Heqsub1_i; subst
  ; cbn; unfold vtransition, lift_sub_incl_state at 1
  ; cbn; unfold sub_IM in li; simpl in li.
  destruct (decide (sub_index_prop indices1 i)) as [H_i |]
  ; [| done].
  rewrite (sub_IM_state_pi s H_i Hi).
  destruct (transition _ _) as (si', _om'); inversion_clear 1; f_equal.
  extensionality sub2_j; destruct_dec_sig sub2_j j Hj Heqsub2_j; subst.
  unfold lift_sub_incl_state.
  by destruct (decide (i = j)); subst; state_update_simpl; cbn; case_decide; state_update_simpl.
Qed.

Lemma lift_sub_incl_embedding :
  VLSM_embedding (free_composite_vlsm sub_IM1) (free_composite_vlsm sub_IM2)
    lift_sub_incl_label lift_sub_incl_state.
Proof.
  apply basic_VLSM_strong_embedding; intro; intros.
  - by split; [apply lift_sub_incl_valid, H |].

  - by apply lift_sub_incl_transition.
  - by apply lift_sub_incl_state_initial.
  - by apply lift_sub_incl_message_initial.
Qed.

Lemma lift_sub_incl_preloaded_embedding
  (P Q : message -> Prop)
  (Hpq : forall m, P m -> Q m)
  : VLSM_embedding
      (pre_loaded_vlsm (free_composite_vlsm sub_IM1) P)
      (pre_loaded_vlsm (free_composite_vlsm sub_IM2) Q)
      lift_sub_incl_label lift_sub_incl_state.
Proof.
  apply basic_VLSM_embedding_preloaded_with; [done | ..]; intro; intros.
  - by split; [apply lift_sub_incl_valid, H |].
  - by apply lift_sub_incl_transition.
  - by apply lift_sub_incl_state_initial.
  - by apply lift_sub_incl_message_initial.
Qed.

End sec_sub_composition_incl.

Section sec_sub_composition_sender.

Context
  {message : Type}
  `{EqDecision index}
  (IM : index -> VLSM message)
  indices
  (sub_IM := sub_IM IM indices)
  (sub_index_prop_dec : forall i, Decision (sub_index_prop indices i) := sub_index_prop_dec indices)
  {validator : Type}
  (A : validator -> index)
  (sender : message -> option validator)
  (Hsender_safety : sender_safety_alt_prop IM A sender)
  .

(**
  If a sub-composition [can_emit] a message then its sender must be one of
  the components of the sub-composition.
*)
Lemma sub_can_emit_sender (P : message -> Prop)
  : forall m v,
    sender m = Some v ->
    can_emit (pre_loaded_vlsm (free_composite_vlsm sub_IM) P)  m ->
    A v ∈ indices.
Proof.
  intros m v Hsender Hemit.
  specialize (Hsender_safety m v Hsender).
  destruct Hemit as [[s om] [[sub_i li] [s' Ht]]].
  destruct_dec_sig sub_i i Hi Heqsub_i; subst.
  unfold sub_IM, SubProjectionTraces.sub_IM in li; cbn in li.
  specialize (PreSubFree_PreFree_weak_embedding IM indices (proj1_sig (composite_s0 IM)))
    as Hproj.
  spec Hproj; [by apply initial_state_is_valid; destruct (composite_s0 IM) |].
  apply (VLSM_incl_input_valid_transition
          (pre_loaded_vlsm_incl_pre_loaded_with_all_messages (free_composite_vlsm sub_IM) P))
     in Ht.
  apply (VLSM_weak_embedding_input_valid_transition Hproj) in Ht; clear Hproj.
  specialize (ProjectionTraces.preloaded_component_projection IM i) as Hproj.
  remember (lift_sub_state_to _ _ _ s) as sX.
  remember (lift_sub_state_to _ _ _ s') as sX'.
  remember (lift_sub_label _ _ _) as lX.
  specialize (VLSM_projection_input_valid_transition Hproj lX li) as Hproj_t.
  subst lX; unfold lift_sub_label in Hproj_t; cbn in Hproj_t.
  spec Hproj_t.
  {
    unfold composite_project_label; cbn.
    by rewrite decide_True_pi with eq_refl.
  }
  by rewrite (Hsender_safety i); [| eexists _; eauto].
Qed.

(** *** Sender and sender-safety specialized for the subcomposition *)

Definition sub_IM_sender (m : message)
  : option (dsig (fun v => A v ∈ indices)) :=
  match sender m with
  | None => None
  | Some v =>
    match (decide (A v ∈ indices)) with
    | left Av_in => Some (@dexist _ (fun v => A v ∈ indices) _ v Av_in)
    | _ => None
    end
  end.

Definition sub_IM_A
  (v : dsig (fun v => A v ∈ indices))
  : sub_index indices :=
  dexist (A (proj1_sig v)) (proj2_dsig v).

Lemma sub_IM_preserves_channel_authentication
  : channel_authentication_prop IM A sender ->
    channel_authentication_prop sub_IM sub_IM_A sub_IM_sender.
Proof.
  intros Hsigned sub_i m Hemit.
  destruct_dec_sig sub_i i Hi Heqsub_i.
  subst.
  apply Hsigned in Hemit.
  unfold channel_authenticated_message in *.
  simpl in Hemit.
  unfold sub_IM_sender.
  destruct (sender m) as [v |]; [| by simpl in Hemit; congruence].
  apply Some_inj in Hemit. subst.
  case_decide; [| done].
  simpl.
  f_equal.
  by apply dsig_eq.
Qed.

Lemma sub_IM_preserves_no_initial_messages
  : no_initial_messages_in_IM_prop IM ->
    no_initial_messages_in_IM_prop sub_IM.
Proof.
  intros Hno_init sub_i m.
  destruct_dec_sig sub_i i Hi Heqsub_i.
  subst.
  by apply Hno_init.
Qed.

Lemma sub_IM_sender_safety
  : sender_safety_alt_prop sub_IM sub_IM_A sub_IM_sender.
Proof.
  intros m sub_v Hsender sub_i Hm.
  destruct_dec_sig sub_v v HAv Heqsub_v.
  destruct_dec_sig sub_i i Hi Heqsub_i.
  subst.
  unfold sub_IM_A.
  apply dsig_eq. simpl.
  apply (Hsender_safety m v); [| done].
  clear -Hsender.
  unfold sub_IM_sender in Hsender.
  destruct (sender m) as [_v |] eqn: Hsender_v; [| by congruence].
  case_decide; [| by congruence].
  by inversion Hsender; itauto.
Qed.

Context
  `{forall sub_i, HasBeenSentCapability (sub_IM sub_i)}
  .

Lemma sub_IM_has_been_sent_iff_by_sender s
  (Hs : valid_state_prop (pre_loaded_with_all_messages_vlsm (free_composite_vlsm sub_IM)) s)
  m v
  (Hsender : sender m = Some v)
  (Hv : A v ∈ indices)
  : composite_has_been_sent sub_IM s m ->
    has_been_sent (sub_IM (dexist (A v) Hv)) (s (dexist (A v) Hv)) m.
Proof.
  apply valid_state_has_trace in Hs as Htr.
  destruct Htr as [is [tr Htr]].
  assert (Hsub_sender : sub_IM_sender m = Some (dexist v Hv)).
  { unfold sub_IM_sender. rewrite Hsender.
    case_decide; [| done].
    f_equal.
    by apply dsig_eq.
  }
  erewrite has_been_sent_iff_by_sender
  ; [| by apply sub_IM_sender_safety | done | done].
  unfold sub_IM_A, sub_IM, SubProjectionTraces.sub_IM; cbn.
  rewrite (sub_IM_state_pi s (proj2_dsig (dexist v Hv)) Hv).
  apply has_been_sent_irrelevance.
  by revert Hs; apply preloaded_valid_state_projection with (j := dexist (A v) Hv).
Qed.

(** ** No-equivocation results for sub-composition

  Constraining (only) a subset of the nodes of a composition to not message-
  equivocate.
*)
Definition sub_IM_not_equivocating_constraint
  (l : composite_label IM)
  (som : composite_state IM * option message)
  : Prop :=
  let (s, om) := som in
  match om with
  | None => True
  | Some m =>
    match option_map A (sender m) with
    | None => True
    | Some i =>
      match decide (i ∈ indices) with
      | left non_byzantine_i =>
        let sub_i := @dexist _ (sub_index_prop indices) _ i non_byzantine_i in
        has_been_sent (sub_IM sub_i) (s i) m
      | _ => True
      end
    end
  end.

Definition non_sub_index_authenticated_message (m : message) : Prop :=
  exists i, i ∉ indices /\ channel_authenticated_message A sender i m.

Context
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  (can_emit_signed : channel_authentication_prop IM A sender)
  .

Lemma induced_sub_projection_valid_preservation constraint l s om
  (Hv : vvalid (pre_induced_sub_projection IM indices constraint) l (s, om))
  : composite_valid sub_IM l (s, om).
Proof.
  destruct Hv as ([i lXi] & sX & [Heql [=] (HsX & Hom & Hv & Hc)]).
  unfold composite_label_sub_projection_option in Heql; cbn in Heql.
  by case_decide; [inversion Heql; subst |].
Qed.

Lemma induced_sub_projection_transition_preservation [constraint]
  : forall l s om s' om',
  vtransition (pre_induced_sub_projection IM indices constraint) l (s, om) = (s', om') <->
  composite_transition sub_IM l (s, om) = (s', om').
Proof.
  intros.
  destruct l as (sub_i, li).
  destruct_dec_sig sub_i i Hi Heqsub_i.
  subst.
  cbn. unfold sub_IM at 6. simpl.
  unfold lift_sub_state at 1. rewrite (lift_sub_state_to_eq _ _ _ _ _ Hi).
  destruct (vtransition _ _ _) as (si', _om').
  by split; inversion 1; subst; clear H; f_equal; extensionality sub_j
  ; destruct_dec_sig sub_j j Hj Heqsub_j
  ; subst sub_j
  ; unfold composite_state_sub_projection
  ; simpl
  ; unfold sub_IM
  ; (destruct (decide (i = j)); subst; state_update_simpl; [done |])
  ; unfold lift_sub_state
  ; rewrite (lift_sub_state_to_eq _ _ _ _ _ Hj)
  ; itauto.
Qed.

Lemma sub_IM_no_equivocation_preservation
  l s om
  (Hv : vvalid (pre_induced_sub_projection IM indices sub_IM_not_equivocating_constraint)
    l (s, om))
  : composite_no_equivocations_except_from sub_IM
      non_sub_index_authenticated_message l (s, om).
Proof.
  destruct om as [m |]; [| done].
  destruct Hv as (lX & sX & [_ [=] (_ & Hm & _ & Hc)]).
  specialize (composite_no_initial_valid_messages_have_sender IM A sender
                can_emit_signed no_initial_messages_in_IM _ _ Hm)
    as Hhas_sender.
  destruct (sender m) as [v |] eqn: Hsender; [clear Hhas_sender | congruence].
  apply (emitted_messages_are_valid_iff (composite_vlsm IM sub_IM_not_equivocating_constraint) m)
    in Hm as [[i [[im Him] Heqm]] | Hemitted].
  - by elim (no_initial_messages_in_IM i im).
  - apply (VLSM_incl_can_emit (constraint_preloaded_free_incl _ _)) in Hemitted.
    specialize (can_emit_projection IM A sender Hsender_safety (A v) m) as Hemit.
    spec Hemit; [by rewrite Hsender; itauto |].
    apply Hemit in Hemitted; clear Hemit.
    cbn in Hc; rewrite Hsender in Hc; cbn in Hc; case_decide.
    + by left; subst; eexists; exact Hc.
    + right. exists (A v).
      unfold channel_authenticated_message.
      by rewrite Hsender; itauto.
Qed.

End sec_sub_composition_sender.

Section sec_sub_composition_all.

(** ** A subcomposition with all the components

  If taking the subset of indices used for the sub-composition to be the entire
  set of indices, the obtained sub-composition is trace-equivalent with the
  original composition.
*)

Context
  {message : Type}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  .

Context
  (sub_IM := sub_IM IM (enum index))
  .

Program Definition free_sub_free_index (i : index) : sub_index (enum index) :=
  dexist i _.
Next Obligation.
Proof.
  by intros; apply elem_of_enum.
Qed.

Definition free_sub_free_label (l : composite_label IM) : composite_label sub_IM :=
  let (i, li) := l in
  existT (free_sub_free_index i) li.

Definition free_sub_free_state (sub_s : composite_state sub_IM) : composite_state IM :=
  fun i => sub_s (free_sub_free_index i).

Definition free_sub_free_constraint
  (constraint : composite_label IM -> composite_state IM * option message -> Prop)
  : composite_label sub_IM -> composite_state sub_IM * option message -> Prop
  := fun l som => let (s, om) := som in
    constraint (lift_sub_label IM (enum index) l) (free_sub_free_state s, om).

Context
  (constraint : composite_label IM -> composite_state IM * option message -> Prop)
  (X := composite_vlsm IM constraint)
  (SubX := composite_vlsm sub_IM (free_sub_free_constraint constraint))
  .

Lemma preloaded_sub_composition_all_embedding (seed : message -> Prop) :
  VLSM_embedding (pre_loaded_vlsm X seed) (pre_loaded_vlsm SubX seed)
    free_sub_free_label  (composite_state_sub_projection IM (enum index)).
Proof.
  apply basic_VLSM_strong_embedding.
  - by intros [i li] *; auto.
  - intros [i li] *; cbn.
    unfold sub_IM, SubProjectionTraces.sub_IM at 2; cbn
    ; unfold composite_state_sub_projection at 1; cbn
    ; destruct (vtransition _ _ _) as (si', _om')
    ; inversion_clear 1; f_equal.
    extensionality sub_j; destruct_dec_sig sub_j j Hj Heqj; subst sub_j
    ; unfold composite_state_sub_projection at 2; cbn.
    unfold free_sub_free_index.
    by destruct (decide (i = j)); subst; state_update_simpl.
  - by intros s Hs; rapply (composite_initial_state_sub_projection IM).
  - intros m [[i Hi] | Hseed]; [left | by right].
    by exists (free_sub_free_index i).
Qed.

Lemma sub_composition_all_embedding :
  VLSM_embedding X SubX free_sub_free_label
    (composite_state_sub_projection IM (enum index)).
Proof.
  apply basic_VLSM_strong_embedding.
  - by intros [i li] *; auto.
  - intros [i li] *
    ; cbn; unfold vtransition
    ; cbn; unfold sub_IM, SubProjectionTraces.sub_IM at 2
    ; cbn; unfold composite_state_sub_projection at 1
    ; cbn; destruct (transition _ _) as (si', _om'); inversion_clear 1.
    f_equal; extensionality sub_j; destruct_dec_sig sub_j j Hj Heqj; subst sub_j
    ; unfold composite_state_sub_projection at 2; cbn.
    unfold free_sub_free_index.
    by destruct (decide (i = j)); subst; state_update_simpl.
  - by intros s Hs; rapply (composite_initial_state_sub_projection IM).
  - by intros m [i Hi]; exists (free_sub_free_index i).
Qed.

Lemma sub_composition_all_embedding_rev
  : VLSM_embedding SubX X (lift_sub_label IM (enum index)) free_sub_free_state.
Proof.
  apply basic_VLSM_strong_embedding.
  - intros [sub_i li] * [Hv Hc]; split; [| done].
    destruct_dec_sig sub_i i Hi Heqi; subst sub_i; cbn in *
    ; unfold sub_IM, SubProjectionTraces.sub_IM in Hc; cbn in Hc
    ; unfold free_sub_free_state, free_sub_free_index.
    by rewrite (sub_IM_state_pi s (free_sub_free_index_obligation_1 i) Hi).
  - intros [sub_i li] *; destruct_dec_sig sub_i i Hi Heqi; subst sub_i.
    unfold vtransition; cbn
    ; unfold sub_IM at 2, SubProjectionTraces.sub_IM, free_sub_free_state at 1,
             free_sub_free_index; cbn
    ; rewrite (sub_IM_state_pi s (free_sub_free_index_obligation_1 i) Hi)
    ; destruct (vtransition _ _ _) as (si', _om'); inversion_clear 1.
    f_equal; extensionality j; unfold free_sub_free_state at 2.
    unfold free_sub_free_index, sub_IM.
    by destruct (decide (i = j)); subst; state_update_simpl.
  - intros s Hi i; rapply Hi.
  - by intros m [[i Hi] Him]; exists i.
Qed.

End sec_sub_composition_all.

Section sec_sub_composition_element.

(** ** Relating a sub-composition with one of its components

  *** A component can be lifted to a free subcomposition
*)

Context
  {message : Type}
  `{FinSet index Ci}
  (IM : index -> VLSM message)
  (indices : Ci)
  (j : index)
  (Hj : j ∈ elements indices)
  .

Definition sub_element_label (l : vlabel (IM j))
  : composite_label (sub_IM IM (elements indices)) :=
  existT (dexist j Hj) l.

Definition sub_element_state (s : vstate (IM j)) sub_i
  : vstate (sub_IM IM (elements indices) sub_i) :=
  match (decide (` sub_i = j)) with
  | left e =>
    eq_rect_r (fun j : index => vstate (IM j)) s e
  | right _ => ` (vs0 (IM (` sub_i)))
  end.

Lemma sub_element_state_eq s H_j
  : sub_element_state s (dexist j H_j) = s.
Proof.
  unfold sub_element_state; cbn.
  by rewrite (decide_True_pi eq_refl).
Qed.

Lemma sub_element_state_neq s i Hi
  : i <> j -> sub_element_state s (dexist i Hi) = ` (vs0 (IM i)).
Proof.
  intros Hij.
  unfold sub_element_state; cbn.
  by case_decide; congruence.
Qed.

#[local] Hint Rewrite @sub_element_state_eq : state_update.
#[local] Hint Rewrite @sub_element_state_neq using done : state_update.

Lemma preloaded_sub_element_embedding
  (P Q : message -> Prop)
  (PimpliesQ : forall m, P m -> Q m)
  (PrePXj := pre_loaded_vlsm (IM j) P)
  (PreQSubFree := pre_loaded_vlsm (free_composite_vlsm (sub_IM IM (elements indices))) Q)
  : VLSM_embedding PrePXj PreQSubFree sub_element_label sub_element_state.
Proof.
  apply basic_VLSM_embedding_preloaded_with; [done | ..].
  - intros l s om Hv.
    split; [cbn | done].
    by rewrite sub_element_state_eq with (H_j := Hj).
  - intros l s om s' om'; cbn.
    rewrite sub_element_state_eq with (H_j := Hj).
    intro Ht; replace (vtransition _ _ _) with (s', om'); f_equal.
    extensionality sub_i.
    destruct_dec_sig sub_i i Hi Heqsub_i; subst.
    by destruct (decide (i = j)); subst; state_update_simpl.
  - intros sj Hsj sub_i.
    destruct_dec_sig sub_i i Hi Heqsub_i; subst.
    destruct (decide (i = j)); subst.
    + by rewrite sub_element_state_eq.
    + by rewrite sub_element_state_neq; destruct (vs0 (IM i)).
  - intros m Hm.
    by exists (dexist j Hj), (exist _ m Hm).
Qed.

Lemma sub_valid_preloaded_lifts_can_be_emitted
  (P Q : message -> Prop)
  (HPvalid : forall dm, P dm ->
    valid_message_prop (pre_loaded_vlsm (free_composite_vlsm (sub_IM IM (elements indices))) Q) dm)
  : forall m, can_emit (pre_loaded_vlsm (IM j) P) m ->
    can_emit (pre_loaded_vlsm (free_composite_vlsm (sub_IM IM (elements indices))) Q) m.
Proof.
  intros m Hm.
  eapply VLSM_incl_can_emit.
  - apply (pre_loaded_vlsm_incl_relaxed _ (fun m => Q m \/ P m)).
    by itauto.
  - eapply VLSM_embedding_can_emit; [| done].
    apply preloaded_sub_element_embedding.
    by itauto.
Qed.

(** *** A subcomposition can be projected to one component

  In the following we define the [projection_induced_validator] to a single component
  of the [pre_induced_sub_projection] of a constrained composition so a subset of its
  components.

  Note that, in general, this is not trace-equivalent with the directly obtained
  [projection_induced_validator] of the constrained composition to the corresponding
  component, as the intermediate induced projection might generate more
  [input_valid_transitions] to be considered as a basis for the next projection.
*)

Definition sub_label_element_project
  (l : composite_label (sub_IM IM (elements indices)))
  : option (vlabel (IM j)) :=
  match decide (j = ` (projT1 l)) with
  | left e => Some (eq_rect_r (fun j => vlabel (IM j)) (projT2 l) e)
  | right _ => None
  end.

Definition sub_state_element_project
  (s : composite_state (sub_IM IM (elements indices)))
  : vstate (IM j) := s (dexist j Hj).

Lemma sub_transition_element_project_None
  : forall lX, sub_label_element_project lX = None ->
    forall s om s' om', composite_transition (sub_IM IM (elements indices)) lX (s, om) = (s', om') ->
    sub_state_element_project s' = sub_state_element_project s.
Proof.
  intros (sub_i, li) HlX s om s' om' HtX.
  destruct_dec_sig sub_i i Hi Heqsub_i; subst.
  unfold sub_label_element_project in HlX; cbn in HlX, HtX.
  case_decide as Hij; [by congruence |].
  destruct (vtransition _ _ _) as (si', _om').
  inversion_clear HtX.
  unfold sub_state_element_project.
  by state_update_simpl.
Qed.

Lemma sub_element_label_project
  : forall lY, sub_label_element_project (sub_element_label lY) = Some lY.
Proof.
  intros lY.
  unfold sub_element_label, sub_label_element_project; cbn.
  by rewrite (decide_True_pi eq_refl).
Qed.

Lemma sub_element_state_project
  : forall sY, sub_state_element_project (sub_element_state sY) = sY.
Proof.
  intros sY.
  unfold sub_element_state, sub_state_element_project; cbn.
  by rewrite (decide_True_pi eq_refl).
Qed.

Lemma sub_transition_element_project_Some :
  forall lX1 lX2 lY,
    sub_label_element_project lX1 = Some lY ->
    sub_label_element_project lX2 = Some lY ->
  forall sX1 sX2,
    sub_state_element_project sX1 = sub_state_element_project sX2 ->
  forall iom sX1' oom1,
    composite_transition (sub_IM IM (elements indices)) lX1 (sX1, iom) = (sX1', oom1) ->
  forall sX2' oom2,
    composite_transition (sub_IM IM (elements indices)) lX2 (sX2, iom) = (sX2', oom2) ->
      sub_state_element_project sX1' = sub_state_element_project sX2' /\ oom1 = oom2.
Proof.
  intros [sub_j1 lj1] [sub_j2 lj2] lj.
  destruct_dec_sig sub_j1 j1 Hj1 Heqsub_j1;
  destruct_dec_sig sub_j2 j2 Hj2 Heqsub_j2; subst.
  unfold sub_label_element_project; cbn.
  do 2 (case_decide; inversion 1); subst; cbn in *; subst.
  unfold sub_state_element_project.
  intros sX1 sX2 Hsjeq iom.
  rewrite (sub_IM_state_pi sX1 Hj1 Hj), (sub_IM_state_pi sX2 Hj2 Hj), <- Hsjeq
  ; unfold sub_IM at 3 13; cbn
  ; destruct (vtransition _ _ _) as (si', om').
  do 2 inversion_clear 1.
  by state_update_simpl.
Qed.

Definition induced_sub_element_projection constraint : VLSM message :=
  projection_induced_validator
    (pre_induced_sub_projection IM (elements indices) constraint) (type (IM j))
    sub_label_element_project sub_state_element_project
    sub_element_label sub_element_state.

Definition pre_induced_sub_element_projection constraint : VLSM message :=
  pre_loaded_with_all_messages_vlsm (induced_sub_element_projection constraint).

Lemma induced_sub_element_projection_is_projection constraint
  : VLSM_projection
    (pre_induced_sub_projection IM (elements indices) constraint)
    (pre_induced_sub_element_projection constraint)
    sub_label_element_project sub_state_element_project.
Proof.
  apply @projection_induced_validator_is_projection.
  - by intro; apply sub_element_label_project.
  - by intro; apply sub_element_state_project.
  - intros ? **; eapply sub_transition_element_project_Some; cycle 2.
    2-3: setoid_rewrite <- (induced_sub_projection_transition_is_composite _ _ constraint).
    all: done.
  - intros lX HlX s om s' om' [_ Ht].
    apply sub_transition_element_project_None with lX om om'; [done |].
    by setoid_rewrite <- (induced_sub_projection_transition_is_composite _ _ constraint).
Qed.

End sec_sub_composition_element.

#[export] Hint Rewrite @sub_element_state_eq : state_update.
#[export] Hint Rewrite @sub_element_state_neq using done : state_update.

Section sec_sub_composition_preloaded_lift.

Context
  {message : Type}
  `{EqDecision index}
  (IM : index -> VLSM message)
  indices
  (Free := free_composite_vlsm IM)
  (PreFree := pre_loaded_with_all_messages_vlsm Free)
  (SubFree := free_composite_vlsm (sub_IM IM indices))
  (PreSubFree := pre_loaded_with_all_messages_vlsm SubFree)
  .

Lemma lift_sub_free_preloaded_with_embedding
  (seed : message -> Prop)
  : VLSM_embedding (pre_loaded_vlsm SubFree seed) (pre_loaded_vlsm Free seed)
    (lift_sub_label IM indices) (lift_sub_state IM indices).
Proof.
  apply (basic_VLSM_embedding_preloaded_with SubFree Free seed seed); intro; intros.
  - done.
  - by split; [apply lift_sub_valid, H |].
  - by rapply lift_sub_transition.
  - by apply (lift_sub_state_initial IM).
  - by apply (lift_sub_message_initial IM indices).
Qed.

Lemma lift_sub_free_embedding
  : VLSM_embedding SubFree Free
    (lift_sub_label IM indices) (lift_sub_state IM indices).
Proof.
  constructor.
  intros sX trX HtrX.
  by apply (VLSM_eq_finite_valid_trace (vlsm_is_pre_loaded_with_False Free)),
    (VLSM_embedding_finite_valid_trace (lift_sub_free_preloaded_with_embedding _)),
    (VLSM_eq_finite_valid_trace (vlsm_is_pre_loaded_with_False SubFree)).
Qed.

Lemma lift_sub_preloaded_free_embedding
  : VLSM_embedding PreSubFree PreFree
    (lift_sub_label IM indices) (lift_sub_state IM indices).
Proof.
  constructor.
  intros sX trX HtrX.
  by apply (VLSM_eq_finite_valid_trace
    (pre_loaded_with_all_messages_vlsm_is_pre_loaded_with_True Free)),
    (VLSM_embedding_finite_valid_trace (lift_sub_free_preloaded_with_embedding _)),
    (VLSM_eq_finite_valid_trace (pre_loaded_with_all_messages_vlsm_is_pre_loaded_with_True SubFree)).
Qed.

(**
  Deriving reachable-validity for the component from the input validity
  w.r.t. a sub_composition preloaded with messages.
*)
Lemma pre_loaded_sub_composite_input_valid_projection constraint Q
  i Hi li sub_s im
  : input_valid
      (pre_loaded_vlsm (composite_vlsm (sub_IM IM indices) constraint) Q)
      (existT (dexist i Hi) li) (sub_s, Some im) ->
    input_valid (pre_loaded_with_all_messages_vlsm (IM i))
      li (lift_sub_state IM indices sub_s i, Some im).
Proof.
  intro Ht_sub.
  eapply (VLSM_projection_input_valid (preloaded_component_projection IM i) (existT i li) li)
  ; [by rewrite composite_project_label_eq |].
  cut (input_valid
        (pre_loaded_with_all_messages_vlsm (free_composite_vlsm (sub_IM IM indices)))
        (existT (dexist i Hi) li) (sub_s, Some im));
    [by apply (VLSM_embedding_input_valid lift_sub_preloaded_free_embedding) |].
  eapply VLSM_incl_input_valid; [| done].
  by apply composite_pre_loaded_vlsm_incl_pre_loaded_with_all_messages.
Qed.

Lemma can_emit_sub_projection
  {validator : Type}
  (A : validator -> index)
  (sender : message -> option validator)
  (Hsender_safety : sender_safety_alt_prop IM A sender)
  (j : index)
  (m : message)
  (Hj : option_map A (sender m) = Some j)
  : can_emit PreSubFree m -> can_emit (pre_loaded_with_all_messages_vlsm (IM j)) m.
Proof.
  intro Hemit.
  apply can_emit_projection with validator A sender; [done | done |].
  by apply (VLSM_embedding_can_emit lift_sub_preloaded_free_embedding).
Qed.

(**
  If a node can emit a message, it can also emit it in a subcomposition with
  other nodes, and starting with more pre-loaded messages.
*)
Lemma can_emit_with_more
  (j : index)
  (m : message)
  (Hj : j ∈ indices)
  (P Q : message -> Prop)
  (PimpliesQ : forall m, P m -> Q m)
  : can_emit (pre_loaded_vlsm (IM j) P) m -> can_emit (pre_loaded_vlsm SubFree Q) m.
Proof.
  intro Hemit.
  specialize
    (lift_to_composite_generalized_preloaded_VLSM_embedding
      (sub_IM IM indices) _ _ PimpliesQ (dexist j Hj))
    as Hproj.
  by apply (VLSM_embedding_can_emit Hproj).
Qed.

End sec_sub_composition_preloaded_lift.

Section sec_empty_sub_composition.

(** ** A subcomposition with no components

  If taking the subset of indices used for the sub-composition to be the empty
  set of indices, the obtained sub-composition is an empty composition.
*)

Context
  {message : Type}
  `{EqDecision index}
  (IM : index -> VLSM message)
  indices
  (sub_IM := sub_IM IM indices)
  (Hno_indices : indices = [])
  .

(**
  If a sub-composition [can_emit] a message then its sender must be one of
  the components of the sub-composition.
*)
Lemma sub_no_indices_no_can_emit (P : message -> Prop)
  : forall m, ~ can_emit (pre_loaded_vlsm (free_composite_vlsm sub_IM) P) m.
Proof.
  apply pre_loaded_empty_composition_no_emit, elem_of_empty_nil.
  by intro sub_i; destruct_dec_sig sub_i i Hi Heqsub_i; subst; inversion Hi.
Qed.

End sec_empty_sub_composition.

Section sec_update_IM.

Context
  {message : Type}
  `{FinSet index Ci}
  `{@finite.Finite index _}
  (IM : index -> VLSM message)
  (selection : Ci)
  .

Definition update_IM
  (replacement_IM : sub_index (elements selection) -> VLSM message)
  (i : index)
  : VLSM message :=
  match decide (i ∈ elements selection) with
  | left i_in => replacement_IM (@dexist _ (sub_index_prop (elements selection)) _ i i_in)
  | _ => IM i
  end.

(*
  TODO(bmmoore): use the definition above to provide an alternate definition
  for fixed-set equivocation model, similar to the one for byzantine traces.
*)

Context
  (replacement_IM : sub_index (elements selection) -> VLSM message)
  (updated_IM := update_IM replacement_IM)
  (selection_complement : Ci := set_diff (list_to_set (enum index)) selection)
  .

#[export] Instance update_IM_complement_Hbs
  `{forall i : index, HasBeenSentCapability (IM i)}
  : forall sub_i : sub_index (elements selection_complement),
    HasBeenSentCapability (sub_IM updated_IM (elements selection_complement) sub_i).
Proof.
  intros sub_i.
  unfold sub_IM, updated_IM, update_IM.
  case_decide as Hi; [| typeclasses eauto].
  contradict Hi.
  destruct_dec_sig sub_i i Hi Heqsub_i; subst sub_i; simpl.
  apply elem_of_elements, set_diff_elim2 in Hi.
  by rewrite elem_of_elements.
Qed.

End sec_update_IM.
