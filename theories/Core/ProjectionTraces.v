From VLSM.Lib Require Import Itauto.
From stdpp Require Import prelude.
From VLSM.Lib Require Import Preamble ListExtras StdppExtras.
From VLSM.Core Require Import VLSM PreloadedVLSM Composition VLSMProjections Validator.

Section sec_projections.

(** * Composite VLSM induced projections

  In this section we define a VLSM representing the induced projection of a
  composite VLSM to a single node ([composite_vlsm_induced_projection]), and we
  study the relation between their traces.

  Let us fix an indexed set of VLSMs <<IM>> and their composition <<X>>
  constrained using the <<constraint>> predicate.
*)

Context
  {message : Type}
  `{EqDecision index}
  (IM : index -> VLSM message)
  (constraint : composite_label IM -> composite_state IM * option message -> Prop)
  (X := composite_vlsm IM constraint)
  .

Definition composite_vlsm_induced_projection j : VLSM message :=
  pre_loaded_vlsm (IM j) (valid_message_prop X).

Lemma composite_vlsm_induced_projection_is_projection :
  forall j,
    VLSM_projection X (composite_vlsm_induced_projection j)
      (composite_project_label IM j) (fun s => s j).
Proof.
  intro j; apply basic_VLSM_projection.
  - intros [i li] lY HlX s om (_ & _ & Hv & _) _ _.
    by unfold composite_project_label in HlX; cbn in HlX;
      case_decide; inversion HlX; subst; clear HlX; cbn in *.
  - intros [i li] lY HlX s om s' om' [_ Ht].
    unfold composite_project_label in HlX; cbn in HlX;
      case_decide; inversion HlX; subst; clear HlX; cbn in *.
    destruct (transition _ _) as (si', _om').
    by inversion Ht; state_update_simpl.
  - intros [i li] HlX s om s' om' [_ Ht].
      unfold composite_project_label in HlX; cbn in HlX;
      case_decide; inversion HlX; cbn in *.
    destruct (transition _ _ _); inversion Ht.
    by state_update_simpl.
  - by intros sX HsX; specialize (HsX j).
  - intros [i li] lY HlX s m (_ & Hm & _ & _) _.
    by apply initial_message_is_valid; right.
Qed.

Lemma composite_vlsm_induced_projection_composition_iff :
  VLSM_eq X (composite_vlsm composite_vlsm_induced_projection constraint).
Proof.
  split.
  - apply basic_VLSM_strong_incl; [| | by intro..].
    + by intros s Hs i; specialize (Hs i).
    + intros ? (i & [im Him] & <-).
      assert (Him' : initial_message_prop (composite_vlsm_induced_projection i) im) by (left; done).
      by exists i, (exist _ _ Him').
  - apply basic_VLSM_incl.
    + by intros s Hs i; specialize (Hs i).
    + intros _ _ m _ _ (i & [im [Him | HX]] & <-); [| done].
      apply initial_message_is_valid.
      by exists i, (exist _ _ Him).
    + by intros ? ? ? (_ & _ & ?).
    + by intros ? ? ? ? ? [_ ?].
Qed.

End sec_projections.

(** ** VLSM Projection Traces *)

Section sec_pre_loaded_projection_traces.

Context
  {message : Type}
  `{EqDecision index}
  (IM : index -> VLSM message)
  (j : index)
  .

(* The projection of a preloaded finite valid trace remains a preloaded valid trace. *)
Lemma preloaded_component_projection :
  VLSM_projection
    (pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM))
    (pre_loaded_with_all_messages_vlsm (IM j))
    (composite_project_label IM j) (fun s => s j).
Proof.
  apply basic_VLSM_projection_preloaded; intro; intros; [.. | done]
  ; destruct lX as [i li]
  ; unfold composite_project_label in H; cbn in H
  ; case_decide; inversion H; subst; clear H; cbn in *.
  - apply H0.
  - destruct (transition _ _ _) as [si' _om']
    ; inversion H0; subst; clear H0.
    by state_update_simpl.
  - destruct (transition _ _ _) as [si' _om']
    ; inversion H0; subst; clear H0.
    by state_update_simpl.
Qed.

Definition composite_transition_item_projection_from_eq
  (item : composite_transition_item IM)
  (i := projT1 (l item))
  j
  (e : j = i)
  : transition_item (IM j)
  :=
  let lj := eq_rect_r _ (projT2 (l item)) e in
  Build_transition_item (IM j) lj (input item) (destination item j) (output item).

Definition composite_transition_item_projection
  (item : composite_transition_item IM)
  (i := projT1 (l item))
  : transition_item (IM i)
  :=
  composite_transition_item_projection_from_eq item i eq_refl.

Lemma composite_transition_item_projection_iff
  (item : composite_transition_item IM)
  (i := projT1 (l item))
  : pre_VLSM_projection_transition_item_project (composite_type IM) _
      (composite_project_label IM i) (fun s => s i)
      item
    = Some (composite_transition_item_projection item).
Proof.
  destruct item. subst i. destruct l as (i, li).
  simpl. unfold pre_VLSM_projection_transition_item_project, composite_project_label.
  simpl.
  destruct (decide _); [| by congruence].
  f_equal. unfold composite_transition_item_projection, composite_transition_item_projection_from_eq.
  simpl.
  f_equal.
  replace e with (eq_refl (A := index) (x := i)); [done |].
  by apply Eqdep_dec.UIP_dec.
Qed.

Lemma composite_transition_item_projection_neq
  (item : composite_transition_item IM)
  (Hneq : j <> projT1 (l item))
  : pre_VLSM_projection_transition_item_project (composite_type IM) _
      (composite_project_label IM j) (fun s => s j)
      item
    = None.
Proof.
  destruct item. destruct l as (i, li).
  unfold pre_VLSM_projection_transition_item_project, composite_project_label.
  simpl in *.
  by destruct (decide _).
Qed.

Definition finite_trace_projection_list (tr : list (composite_transition_item IM))
  : list (transition_item (IM j)) :=
  pre_VLSM_projection_finite_trace_project (composite_type IM) _
    (composite_project_label IM j) (fun s => s j) tr.

Lemma preloaded_valid_state_projection
  (s : state _)
  (Hps : valid_state_prop (pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM)) s)
  : valid_state_prop (pre_loaded_with_all_messages_vlsm (IM j)) (s j).
Proof.
  by apply (VLSM_projection_valid_state preloaded_component_projection).
Qed.

Lemma preloaded_finite_valid_trace_projection
  (s : composite_state IM)
  (trx : list (composite_transition_item IM))
  (Htr : finite_valid_trace_from (pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM)) s trx)
   : finite_valid_trace_from (pre_loaded_with_all_messages_vlsm (IM j)) (s j)
      (VLSM_projection_finite_trace_project preloaded_component_projection trx).
Proof.
  by apply (VLSM_projection_finite_valid_trace_from preloaded_component_projection).
Qed.

Lemma preloaded_finite_valid_trace_from_to_projection
  (s s' : composite_state IM)
  (trx : list (composite_transition_item IM))
  (Htr : finite_valid_trace_from_to
          (pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM)) s s' trx)
   : finite_valid_trace_from_to (pre_loaded_with_all_messages_vlsm (IM j)) (s j) (s' j)
      (VLSM_projection_finite_trace_project preloaded_component_projection trx).
Proof.
  by apply (VLSM_projection_finite_valid_trace_from_to preloaded_component_projection).
Qed.

Lemma preloaded_finite_valid_trace_init_to_projection
  (s s' : composite_state IM)
  (trx : list (composite_transition_item IM))
  (Htr : finite_valid_trace_init_to
          (pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM)) s s' trx)
   : finite_valid_trace_init_to (pre_loaded_with_all_messages_vlsm (IM j)) (s j) (s' j)
      (VLSM_projection_finite_trace_project preloaded_component_projection trx).
Proof.
  by apply (VLSM_projection_finite_valid_trace_init_to preloaded_component_projection).
Qed.

Lemma pre_loaded_with_all_messages_projection_input_valid_transition_eq
  (s1 s2 : composite_state IM)
  (om1 om2 : option message)
  (l : label (pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM)))
  (Ht : input_valid_transition
          (pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM)) l (s1, om1) (s2, om2))
  (Hl : projT1 l = j)
  : input_valid_transition (pre_loaded_with_all_messages_vlsm (IM (projT1 l)))
      (projT2 l) (s1 (projT1 l), om1) (s2 (projT1 l), om2).
Proof.
  specialize
    (VLSM_projection_input_valid_transition preloaded_component_projection l) as Hivt.
  subst j. specialize (Hivt (projT2 l)).
  apply Hivt; [| done].
  unfold composite_project_label. destruct (decide _); [| by elim n].
  replace e with (eq_refl (A := index) (x := projT1 l)); [done |].
  by apply Eqdep_dec.UIP_dec.
Qed.

Lemma pre_loaded_with_all_messages_projection_input_valid_transition_neq
  [s1 s2 : composite_state IM]
  [om1 om2 : option message]
  [l : label (pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM))]
  (Ht : input_valid_transition
          (pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM)) l (s1, om1) (s2, om2))
  [i : index]
  (Hi : i <> projT1 l)
  : s1 i = s2 i.
Proof.
  destruct Ht as [[Hs1 [Hom1 Hv]] Ht]; cbn in Hv, Ht.
  destruct l as [il l].
  destruct (transition _ _ _) as (si', om') eqn: Htj.
  inversion Ht; subst; clear Ht.
  by state_update_simpl.
Qed.

End sec_pre_loaded_projection_traces.

Section sec_projection_traces_membership.

Context
  {message : Type}
  `{EqDecision index}
  (IM : index -> VLSM message)
  (constraint : composite_label IM -> composite_state IM * option message -> Prop)
  (X := composite_vlsm IM constraint)
  .

Lemma finite_trace_projection_list_in
  (tr : list (composite_transition_item IM))
  (itemX : composite_transition_item IM)
  (HitemX : itemX ∈ tr)
  (j := projT1 (l itemX)) :
    Build_transition_item (IM j) (projT2 (l itemX)) (input itemX) (destination itemX j)
      (output itemX)
      ∈
    VLSM_projection_finite_trace_project (preloaded_component_projection IM j) tr.
Proof.
  apply elem_of_map_option.
  exists itemX; split; [done |].
  unfold pre_VLSM_projection_transition_item_project, composite_project_label; subst j.
  case_decide; [| by elim H].
  replace H with (eq_refl (A := index) (x := projT1 (l itemX))); [done |].
  by apply Eqdep_dec.UIP_dec.
Qed.

Lemma finite_trace_projection_list_in_rev
  (tr : list (composite_transition_item IM))
  (j : index)
  (itemj : transition_item (IM j))
  (Hitemj : itemj ∈ VLSM_projection_finite_trace_project (preloaded_component_projection IM j) tr)
  : exists (itemX : composite_transition_item IM), itemX ∈ tr /\
    output itemX = output itemj /\
    input itemX = input itemj /\
    destination itemX j = destination itemj /\
    exists (Hl1 : j = projT1 (l itemX)),
    eq_rect_r _ (projT2 (l itemX)) Hl1 = l itemj.
Proof.
  apply elem_of_map_option in Hitemj as [itemX [HitemX HitemX_pr]].
  exists itemX. split; [done |].
  unfold pre_VLSM_projection_transition_item_project in HitemX_pr.
  destruct (composite_project_label _ _ _) as [lY |] eqn: Hly; [| by congruence].
  inversion HitemX_pr. subst. clear HitemX_pr.
  repeat split.
  unfold composite_project_label in Hly.
  case_decide; [| by congruence].
  exists H.
  by inversion Hly.
Qed.

End sec_projection_traces_membership.

Section sec_binary_free_composition_projections.

(** ** Projections of Free composition of two VLSMs

  This projections are used in defining the [byzantine_trace_prop]erties.
*)
Context
  {message : Type}
  (M1 M2 : VLSM message)
  .

Definition binary_free_composition_fst : VLSM message :=
  pre_composite_vlsm_induced_projection_validator (binary_IM M1 M2)
    (free_constraint (binary_IM M1 M2)) first.

Definition binary_free_composition_snd : VLSM message :=
  pre_composite_vlsm_induced_projection_validator (binary_IM M1 M2)
    (free_constraint (binary_IM M1 M2)) second.

End sec_binary_free_composition_projections.

Section sec_fixed_projection.

Context
  {message : Type}
  `{EqDecision index}
  (IM : index -> VLSM message)
  (constraint : composite_label IM -> composite_state IM * option message -> Prop)
  (X := composite_vlsm IM constraint)
  .

(** ** Projection traces are Byzantine

  Let us fix an index <<j>> and let <<Xj>> be the projection of <<X>> on
  component <<j>>.

  In this section we establish some basic properties for projections, building up
  to Lemma [proj_pre_loaded_with_all_messages_incl], which guarantees that all
  [valid_trace]s of <<Xj>> are also [valid_trace]s for the
  [pre_loaded_with_all_messages_vlsm] associated to the component <<IM j>>.
  In particular this ensures that the byzantine traces of <<IM j>> include all
  [valid_trace]s of <<Xj>> (see Lemma [pre_loaded_with_all_messages_alt_eq]).

*)

Context
  (j : index)
  (Xj := pre_composite_vlsm_induced_projection_validator IM constraint j)
  .

Lemma projection_valid_input_valid
  (l : label Xj)
  (som : state Xj * option message)
  (Hv : valid Xj l som)
  : input_valid Xj l som.
Proof.
  destruct som as (s, om).
  destruct (id Hv) as [sX [Hsi [Hps [Hopm _]]]]; subst.
  repeat split; [| | done].
  - by eapply (VLSM_projection_valid_state (component_projection _ constraint j)).
  - by apply any_message_is_valid_in_preloaded.
Qed.

Lemma projection_valid_implies_composition_valid_message
  (l : label Xj)
  (s : state Xj)
  (om : option message)
  (Hv : valid Xj l (s, om))
  : option_valid_message_prop X om.
Proof.
  by destruct Hv as (sx & Hs & HpsX & HpmX & Hv).
Qed.

Lemma projection_valid_implies_projection_valid_state
  (lj : label Xj)
  (sj : state Xj)
  (om : option message)
  (Hv : valid Xj lj (sj, om))
  : valid_state_prop Xj sj.
Proof.
  by destruct Hv as (s & <- & Hs & _)
  ; eapply (VLSM_projection_valid_state (component_projection _ constraint j)).
Qed.

Lemma projection_valid_implies_projection_valid_state_message_outputs
    (l : label Xj)
    (s : state Xj)
    (om : option message)
    (Hv : valid Xj l (s, om))
    s' om'
    (Ht : transition (IM j) l (s, om) = (s', om'))
    : valid_state_message_prop Xj s' om'.
Proof.
  apply projection_valid_implies_projection_valid_state in Hv as Hs.
  destruct Hs as [? Hs].
  eapply (valid_generated_state_message Xj s x Hs (` (vs0 (IM j)))); [| done..].
  apply valid_initial_state_message.
  - by destruct (vs0 (IM j)); cbn.
  - by destruct om; cbn; [right |].
Qed.

Lemma projection_valid_implies_destination_projection_valid_state
    (l : label Xj)
    (s : state Xj)
    (om : option message)
    (Hv : valid Xj l (s, om))
    s' om'
    (Ht : transition (IM j) l (s, om) = (s', om'))
    : valid_state_prop Xj s'.
Proof.
  by eexists; eapply projection_valid_implies_projection_valid_state_message_outputs.
Qed.

Lemma projection_valid_implies_destination_projection_valid_message
    (l : label Xj)
    (s : state Xj)
    (om : option message)
    (Hv : valid Xj l (s, om))
    s' om'
    (Ht : transition (IM j) l (s, om) = (s', om'))
    : option_valid_message_prop Xj om'.
Proof.
  by eexists; eapply projection_valid_implies_projection_valid_state_message_outputs.
Qed.

(**
  Interestingly enough, <<Xj>> cannot produce any additional messages than
  the initial ones available from <<X>>.
*)
Lemma valid_message_projection_rev :
  forall m, can_emit Xj m -> can_emit X m.
Proof.
  intros m ((sj, om) & lj & sj' & (_ & _ & s & <- & Hv) & Ht).
  eexists _, _, (state_update IM s j sj'); split; [done |].
  by cbn in *; replace (transition _ _ _) with (sj', Some m).
Qed.

(**
  As a stepping stone towards proving trace inclusion between <<Xj>> and
  the [pre_loaded_with_all_messages_vlsm] associated to <<IM j>>, we prove that the
  [valid_state_message_prop]erty is transferred.
*)
Lemma proj_pre_loaded_with_all_messages_valid_state_message_preservation
  (PreLoaded := pre_loaded_with_all_messages_vlsm (IM j))
  (s : state Xj)
  (om : option message)
  (Hps : valid_state_message_prop Xj s om)
  : valid_state_message_prop PreLoaded s om.
Proof.
  induction Hps.
  - by apply (valid_initial_state_message PreLoaded); [| destruct om].
  - apply (valid_generated_state_message PreLoaded) with s _om _s om l; [done.. | | done].
    by cbn; eapply (projection_valid_implies_valid IM), Hv.
Qed.

(** We can now finally prove the main result for this section. *)
Lemma proj_pre_loaded_with_all_messages_incl
  (PreLoaded := pre_loaded_with_all_messages_vlsm (IM j))
  : VLSM_incl Xj PreLoaded.
Proof.
  apply (basic_VLSM_incl Xj PreLoaded); intro; intros.
  - done.
  - by apply initial_message_is_valid.
  - by cbn; eapply (projection_valid_implies_valid IM), Hv.
  - by apply H.
Qed.

Lemma component_projection_to_preloaded :
  VLSM_projection X (pre_loaded_with_all_messages_vlsm (IM j))
    (composite_project_label IM j) (fun s => s j).
Proof.
  eapply VLSM_projection_incl_trans.
  - by apply component_projection.
  - by apply proj_pre_loaded_with_all_messages_incl.
Qed.

(**
  We say that the component <<j>> of X is a validator for received messages if
  if [valid]ity in the component (for reachable states) implies validity in the
  [composite_vlsm_induced_projection_validator].
*)
Definition component_projection_validator_prop :=
  forall (lj : label (IM j)) (sj : state (IM j)) (omi : option message),
    input_valid (pre_loaded_with_all_messages_vlsm (IM j)) lj (sj, omi) ->
    valid Xj lj (sj, omi).

Lemma component_projection_validator_prop_is_induced
  : component_projection_validator_prop <->
    @projection_validator_prop _ X (IM j) (composite_project_label IM j) (fun s => s j).
Proof.
  split; intros Hvalidator li si omi Hvi.
  - apply Hvalidator in Hvi as (sX & <- & Hv).
    by eexists (existT j li), sX; split; [apply composite_project_label_eq | ..].
  - apply Hvalidator in Hvi as ([i _li] & sX & []).
    unfold composite_project_label in tiv_label_project; case_decide; [subst; cbn in * | done].
    apply Some_inj in tiv_label_project; subst _li.
    by eexists.
Qed.

Definition component_message_validator_prop : Prop :=
  @message_validator_prop _ X (IM j).

(**
  Assuming the [component_projection_validator_prop]erty, the component
  [pre_loaded_with_all_messages_vlsm] is [VLSM_eq]ual (trace-equivalent) with
  its corresponding [projection_induced_validator].
*)
Lemma pre_loaded_with_all_messages_validator_component_proj_eq
  (Hvalidator : component_projection_validator_prop)
  : VLSM_eq (pre_loaded_with_all_messages_vlsm (IM j)) Xj.
Proof.
  eapply VLSM_eq_trans;
    [| apply VLSM_eq_sym, pre_composite_vlsm_induced_projection_validator_iff].
  apply pre_loaded_with_all_messages_validator_proj_eq.
  - by apply component_transition_projection_None.
  - by apply component_label_projection_lift.
  - by apply component_state_projection_lift.
  - by intro s; apply (composite_initial_state_prop_lift IM).
  - by apply component_transition_projection_Some.
  - by apply component_projection_to_preloaded.
  - intros li si omi Hiv.
    apply Hvalidator in Hiv as (sX & <- & HivX).
    exists (existT j li), sX; split; [| done..].
    by unfold composite_project_label; cbn; rewrite (decide_True_pi eq_refl).
Qed.

Definition pre_loaded_with_all_messages_validator_component_proj_incl
  (Hvalidator : component_projection_validator_prop)
  : VLSM_incl (pre_loaded_with_all_messages_vlsm (IM j)) Xj :=
  proj1 (pre_loaded_with_all_messages_validator_component_proj_eq Hvalidator).

End sec_fixed_projection.

Section sec_projection_friendliness_sufficient_condition.

Context
  {message : Type}
  `{EqDecision index}
  (IM : index -> VLSM message)
  (constraint : composite_label IM -> composite_state IM * option message -> Prop)
  (X := composite_vlsm IM constraint)
  .

(** ** A sufficient condition for the [projection_friendly_prop]erty *)

Context
  (j : index)
  (Xj := pre_composite_vlsm_induced_projection_validator IM constraint j)
  .

(**
  This condition states that [input_valid]ity in a projection <<Xj>>
  can be lifted to any [valid_state] in <<X>> which projects to the
  corresponding <<Xj>> state.
*)

Definition projection_friendliness_sufficient_condition
  := forall
    (lj : label (IM j))
    (sj : state (IM j))
    (om : option message)
    (Hiv : input_valid Xj lj (sj, om))
    (s : state X)
    (Hs : valid_state_prop X s)
    (Hsi : s j = sj)
    , valid X (existT j lj) (s, om).

Lemma projection_friendliness_sufficient_condition_valid_state
  (Hfr : projection_friendliness_sufficient_condition)
  (s : state Xj)
  (Hp : valid_state_prop Xj s)
  : valid_state_prop X (lift_to_composite_state' IM j s).
Proof.
  induction Hp using valid_state_prop_ind.
  - by apply initial_state_is_valid, (composite_initial_state_prop_lift IM j).
  - destruct Ht as [Hvj Ht].
    specialize (Hfr _ _ _ Hvj _ IHHp).
    spec Hfr; [by apply state_update_eq |].
    exists om'.
    destruct Hvj as [_ [_ Hvj]].
    apply (projection_valid_implies_composition_valid_message IM) in Hvj as Hom.
    destruct IHHp as [_om HsX].
    destruct Hom as [_s Hom].
    specialize (valid_generated_state_message X _ _ HsX _ _ Hom _ Hfr) as Hgen.
    apply Hgen.
    cbn; unfold lift_to_composite_state' at 1.
    state_update_simpl.
    replace (transition (IM j) _ _) with (s', om').
    f_equal.
    by apply state_update_twice.
Qed.

(**
  The result below shows that the [projection_friendliness_sufficient_condition]
  might be too strong, in the sense that it allows any trace from the
  projection to be lifted directly to <<X>>
  (all other machines stay in their initial state).
*)
Lemma projection_friendliness_lift_to_composite_VLSM_embedding
  (Hfr : projection_friendliness_sufficient_condition)
  : VLSM_embedding Xj X (lift_to_composite_label IM j) (lift_to_composite_state' IM j).
Proof.
  apply basic_VLSM_embedding; intro; intros.
  - apply (Hfr _ _ _ Hv); [| apply state_update_eq].
    by apply (projection_friendliness_sufficient_condition_valid_state Hfr), Hv.
  - cbn; unfold lift_to_composite_state' at 1.
    state_update_simpl.
    replace (transition (IM j) _ _) with (s', om')
      by (symmetry; apply H).
    by rewrite state_update_twice.
  - by apply (composite_initial_state_prop_lift IM j).
  - by destruct Hv as [Hs [Homj [sX [Heqs [HsX [Hom Hv]]]]]].
Qed.

End sec_projection_friendliness_sufficient_condition.
