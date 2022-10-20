From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From VLSM.Lib Require Import ListExtras.
From VLSM.Core Require Import VLSM VLSMProjections Validator Composition.

(** * State-annotated VLSMs

  This module describes the VLSM obtained by augmenting the states of an existing
  VLSM with annotations and providing additional validity constraints taking into
  account the annotations, and a function for updating the annotations following a
  transition.
*)

Section sec_annotated_vlsm.

Context
  {message : Type}
  (X : VLSM message)
  (annotation : Type)
  .

Record annotated_state :=
  { original_state : vstate X
  ; state_annotation : annotation
  }.

Definition annotated_type : VLSMType message :=
  {| label := vlabel X;
     state := annotated_state
  |}.

Context
  (initial_annotation_prop : annotation -> Prop)
  `{Inhabited (sig initial_annotation_prop)}
  .

Definition annotated_initial_state_prop (sa : annotated_state) :=
  vinitial_state_prop X (original_state sa) /\ initial_annotation_prop (state_annotation sa).

#[export] Program Instance annotated_initial_state_prop_inhabited
  : Inhabited (sig annotated_initial_state_prop) :=
  populate (exist _ {| original_state := ` (vs0 X); state_annotation := ` inhabitant  |} _).
Next Obligation.
  split; cbn.
  - by destruct (vs0 X).
  - by destruct inhabitant.
Qed.

Context
  (annotated_constraint : @label _ annotated_type -> annotated_state * option message -> Prop)
  (annotated_transition_state : @label _ annotated_type -> annotated_state * option message -> annotation)
  .

Definition annotated_valid
  (l : @label _ annotated_type)
  (som : annotated_state * option message)
  : Prop :=
  vvalid X l (original_state som.1, som.2) /\
  annotated_constraint l som.

Definition annotated_transition
  (l : @label _ annotated_type)
  (som : annotated_state * option message)
  : annotated_state * option message :=
  let (s', om') := vtransition X l (original_state som.1, som.2) in
  ({| original_state := s'; state_annotation := annotated_transition_state l som |}, om').

Definition annotated_vlsm_machine : VLSMMachine annotated_type :=
  {| initial_state_prop := fun s : @state _ annotated_type => annotated_initial_state_prop s
  ; initial_message_prop := λ m : message, vinitial_message_prop X m
  ; valid := annotated_valid
  ; transition := annotated_transition
  |}.

Definition annotated_vlsm : VLSM message := mk_vlsm annotated_vlsm_machine.

Definition annotate_trace_item
  (item : vtransition_item X)
  (k : annotated_state -> list (@transition_item _ annotated_type))
  (sa : annotated_state)
  : list (@transition_item _ annotated_type) :=
    let sa' := {| original_state := destination item; state_annotation := annotated_transition_state (l item) (sa, input item) |} in
    @Build_transition_item _ annotated_type (l item) (input item) sa' (output item) :: k sa'.

Lemma annotate_trace_item_project
  (item : vtransition_item X)
  (k : annotated_state -> list (@transition_item _ annotated_type))
  (sa : annotated_state)
  : pre_VLSM_full_projection_finite_trace_project
      annotated_type (type X) id original_state
      (annotate_trace_item item k sa)
      = item ::
        pre_VLSM_full_projection_finite_trace_project
            annotated_type (type X) id original_state
            (k {| original_state := destination item; state_annotation := annotated_transition_state (l item) (sa, input item) |}).
Proof.
  by destruct item.
Qed.

Definition annotate_trace_from (sa : @state _ annotated_type) (tr : list (vtransition_item X))
  : list (@transition_item _ annotated_type) :=
  fold_right annotate_trace_item (fun sa => []) tr sa.

Lemma annotate_trace_from_unroll sa item tr
  : annotate_trace_from sa (item :: tr) =
    let sa' := {| original_state := destination item; state_annotation := annotated_transition_state (l item) (sa, input item) |} in
    @Build_transition_item _ annotated_type (l item) (input item) sa' (output item) :: annotate_trace_from sa' tr.
Proof.
  by destruct item.
Qed.

Lemma annotate_trace_from_app sa tr1 tr2
  : annotate_trace_from sa (tr1 ++ tr2) =
    annotate_trace_from sa tr1 ++
      annotate_trace_from (finite_trace_last sa ( annotate_trace_from sa tr1)) tr2.
Proof.
  revert sa.
  induction tr1 as [| item tr1]; [done | intro sa].
  by rewrite <- app_comm_cons, !annotate_trace_from_unroll
  ; simpl; rewrite IHtr1, finite_trace_last_cons.
Qed.

Lemma annotate_trace_from_last_original_state sa sa' tr
  : original_state (finite_trace_last sa (annotate_trace_from sa' tr)) =
    finite_trace_last (original_state sa) tr.
Proof.
  destruct_list_last tr tr' item Heqtr; subst; [done |].
  rewrite annotate_trace_from_app.
  cbn; unfold annotate_trace_item.
  by rewrite! finite_trace_last_is_last.
Qed.

Definition annotate_trace (s : vstate X) (tr : list (vtransition_item X))
  : list (@transition_item _ annotated_type) :=
  annotate_trace_from {| original_state := s; state_annotation := ` inhabitant |} tr.

Lemma annotate_trace_last_original_state s s' tr
  : original_state (finite_trace_last s (annotate_trace s' tr)) =
    finite_trace_last (original_state s) tr.
Proof. apply annotate_trace_from_last_original_state. Qed.

Lemma annotate_trace_project is tr
  : pre_VLSM_full_projection_finite_trace_project
      annotated_type (type X) id original_state
      (annotate_trace is tr)
      = tr.
Proof.
  unfold annotate_trace
  ; remember {| original_state := is |} as sa; clear Heqsa; revert sa.
  induction tr as [| item]; [done | intro sa].
  setoid_rewrite annotate_trace_item_project; f_equal.
  apply IHtr.
Qed.

End sec_annotated_vlsm.

Arguments original_state {_ _ _} _ : assert.
Arguments state_annotation {_ _ _} _ : assert.

Section sec_annotated_vlsm_projections.

Context
  {message : Type}
  (X : VLSM message)
  {annotation : Type}
  (initial_annotation_prop : annotation -> Prop)
  `{Inhabited (sig initial_annotation_prop)}
  (annotated_constraint : @label _ (annotated_type X annotation) -> annotated_state X annotation  * option message -> Prop)
  (annotated_transition_state : @label _ (annotated_type X annotation) -> annotated_state X annotation * option message -> annotation)
  (AnnotatedX : VLSM message := annotated_vlsm X annotation initial_annotation_prop annotated_constraint annotated_transition_state)
  .

Definition forget_annotations_projection
  : VLSM_full_projection AnnotatedX X id original_state.
Proof.
  apply basic_VLSM_strong_full_projection.
  1, 3-4: cbv; itauto.
  intros l [s a] om [s' a'] om'.
  cbn; unfold annotated_transition; cbn
  ; destruct (vtransition _ _ _) as (_s', _om').
  by inversion 1.
Qed.

End sec_annotated_vlsm_projections.

Section sec_composite_annotated_vlsm_projections.

(** ** Specializing [projection_validator_prop]erties to annotated compositions. *)

Context
  {message : Type}
  `{EqDecision index}
  (IM : index -> VLSM message)
  (Free := free_composite_vlsm IM)
  {annotation : Type}
  (initial_annotation_prop : annotation -> Prop)
  `{Inhabited (sig initial_annotation_prop)}
  (annotated_constraint : @label _ (annotated_type Free annotation) -> annotated_state Free annotation  * option message -> Prop)
  (annotated_transition_state : @label _ (annotated_type Free annotation) -> annotated_state Free annotation * option message -> annotation)
  (AnnotatedFree : VLSM message := annotated_vlsm Free annotation initial_annotation_prop annotated_constraint annotated_transition_state)
  (i : index)
  .

Definition annotated_composite_label_project : vlabel AnnotatedFree -> option (vlabel (IM i))
  := composite_project_label IM i.

Definition annotated_composite_state_project : vstate AnnotatedFree -> vstate (IM i)
  := fun s => original_state s i.

Definition annotated_projection_validator_prop : Prop :=
  @projection_validator_prop _ AnnotatedFree (IM i)
    annotated_composite_label_project annotated_composite_state_project.

Definition annotated_message_validator_prop : Prop :=
  @message_validator_prop _ AnnotatedFree (IM i).

Definition annotated_composite_label_lift : vlabel (IM i) -> vlabel AnnotatedFree
  := lift_to_composite_label IM i.

Definition annotated_composite_state_lift : vstate (IM i) -> vstate AnnotatedFree
  := fun si =>
     @Build_annotated_state _ (free_composite_vlsm IM) _
      (lift_to_composite_state' IM i si) (` inhabitant).

Definition annotated_projection_validator_prop_alt : Prop :=
  @projection_validator_prop_alt _ AnnotatedFree (IM i)
    annotated_composite_label_project annotated_composite_state_project
    annotated_composite_label_lift annotated_composite_state_lift.

Lemma annotated_composite_preloaded_projection
  : VLSM_projection AnnotatedFree (pre_loaded_with_all_messages_vlsm (IM i))
    annotated_composite_label_project annotated_composite_state_project.
Proof.
  apply basic_VLSM_projection.
  - intros [_i _li] li.
    unfold annotated_composite_label_project, composite_project_label; cbn.
    case_decide; [| congruence].
    subst _i; cbn; inversion_clear 1.
    by intros (s, ann) om (_ & _ & [Hv _] & _) _ _.
  - intros [_i _li] li.
    unfold annotated_composite_label_project, composite_project_label; cbn.
    case_decide; [| congruence].
    subst _i; cbn; inversion_clear 1.
    intros [s ann] iom [s' ann'] oom.
    unfold input_valid_transition; cbn
    ; unfold annotated_transition; cbn
    ; destruct (vtransition _ _ _) as (si', om').
    intros [_ Ht]; inversion Ht.
    by state_update_simpl.
  - intros [j lj].
    unfold annotated_composite_label_project, composite_project_label; cbn.
    case_decide as Hij; [congruence |].
    intros _ [s ann] iom [s' ann'] oom.
    unfold input_valid_transition; cbn
    ; unfold annotated_transition; cbn
    ; destruct (vtransition _ _ _) as (si', om').
    intros [_ Ht]; inversion Ht.
    by state_update_simpl.
  - intros [s ann] [Hs _]; cbn; apply Hs.
  - intro; intros; apply any_message_is_valid_in_preloaded.
Qed.

Definition annotated_composite_induced_validator : VLSM message
  := projection_induced_validator AnnotatedFree (type (IM i))
    annotated_composite_label_project annotated_composite_state_project
    annotated_composite_label_lift annotated_composite_state_lift.

Lemma annotated_composite_induced_validator_transition_None
  : weak_projection_transition_consistency_None _ _ annotated_composite_label_project annotated_composite_state_project.
Proof.
  intros [j lj].
  unfold annotated_composite_label_project, composite_project_label; cbn.
  case_decide as Hij; [congruence |].
  intros _ sX omX s'X om'X [_ Ht]; revert Ht; cbn.
  unfold annotated_transition; cbn
  ; destruct (vtransition _ _ _) as (si', om')
  ; inversion 1; clear Ht; subst om' s'X; cbn.
  by state_update_simpl.
Qed.

Lemma annotated_composite_induced_validator_label_lift
  : induced_validator_label_lift_prop annotated_composite_label_project annotated_composite_label_lift.
Proof. apply component_label_projection_lift. Qed.

Lemma annotated_composite_induced_validator_state_lift
  : induced_validator_state_lift_prop annotated_composite_state_project annotated_composite_state_lift.
Proof. intros si; apply state_update_eq. Qed.

Lemma annotated_composite_induced_validator_initial_lift
  : strong_projection_initial_state_preservation (IM i) AnnotatedFree
    annotated_composite_state_lift.
Proof.
  split; cbn.
  - by apply composite_initial_state_prop_lift.
  - by destruct inhabitant.
Qed.

Lemma annotated_composite_induced_validator_transition_consistency
  : induced_validator_transition_consistency_Some _ _
    annotated_composite_label_project annotated_composite_state_project.
Proof.
  intros [i1 li1] [i2 li2] li.
  unfold annotated_composite_label_project, composite_project_label; cbn.
  case_decide as Hi1; [| congruence].
  subst i1; cbn; inversion_clear 1.
  case_decide as Hi2; [| congruence].
  subst i2; cbn; inversion_clear 1.
  intros [s1 ann1] [s2 ann2]
  ; unfold annotated_transition; cbn
  ; intros <- iom sX1' oom1
  ;destruct (vtransition _ _ _) as (si', om').
  inversion_clear 1; intros sX2' oom2; inversion_clear 1.
  by cbn; state_update_simpl.
Qed.

Definition annotated_composite_induced_validator_is_projection :=
  projection_induced_validator_is_projection _ _ _ _ _ _
    annotated_composite_induced_validator_label_lift
    annotated_composite_induced_validator_state_lift
    annotated_composite_induced_validator_transition_consistency
    annotated_composite_induced_validator_transition_None.

Lemma annotated_projection_validator_prop_alt_iff
  : annotated_projection_validator_prop_alt <-> annotated_projection_validator_prop.
Proof.
  apply projection_validator_prop_alt_iff.
  - apply annotated_composite_induced_validator_transition_None.
  - apply annotated_composite_induced_validator_label_lift.
  - apply annotated_composite_induced_validator_state_lift.
  - apply annotated_composite_induced_validator_initial_lift.
  - apply annotated_composite_induced_validator_transition_consistency.
  - apply annotated_composite_preloaded_projection.
Qed.

End sec_composite_annotated_vlsm_projections.
