From stdpp Require Import prelude.
From VLSM.Lib Require Import ListExtras.
From VLSM.Core Require Import VLSM VLSMProjections.

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

Global Program Instance annotated_initial_state_prop_inhabited
  : Inhabited (sig annotated_initial_state_prop) :=
  populate (exist _ {| original_state := ` (vs0 X); state_annotation := ` inhabitant  |} _).
Next Obligation.
  split; cbn.
  - destruct (vs0 X). assumption.
  - destruct inhabitant. assumption.
Qed.

Instance annotated_sign : VLSMSign annotated_type :=
  { initial_state_prop := annotated_initial_state_prop
  ; initial_message_prop := λ m : message, vinitial_message_prop X m
  }.

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

Instance annotated_vlsm_class : VLSMClass annotated_sign :=
  { valid := annotated_valid
  ; transition := annotated_transition
  }.

Definition annotated_vlsm : VLSM message := mk_vlsm annotated_vlsm_class.

Definition annotate_trace_item
  (item : vtransition_item X)
  (k : annotated_state -> list (@transition_item _ annotated_type))
  (sa : annotated_state)
  : list (@transition_item _ annotated_type) :=
  match item with
  | {| l := l; input := iom; destination := s'; output := oom |} =>
    let sa' := {| original_state := s'; state_annotation := annotated_transition_state l (sa, iom) |} in
    @Build_transition_item _ annotated_type l iom sa' oom :: k sa'
  end.

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
  destruct item. reflexivity.
Qed.

Definition annotate_trace_from (sa : @state _ annotated_type) (tr : list (vtransition_item X))
  : list (@transition_item _ annotated_type) :=
  fold_right annotate_trace_item (fun sa => []) tr sa.

Lemma annotate_trace_from_unroll sa item tr
  : annotate_trace_from sa (item :: tr) =
    let sa' := {| original_state := destination item; state_annotation := annotated_transition_state (l item) (sa, input item) |} in
    @Build_transition_item _ annotated_type (l item) (input item) sa' (output item) :: annotate_trace_from sa' tr.
Proof.
  destruct item; reflexivity.
Qed.

Lemma annotate_trace_from_app sa tr1 tr2
  : annotate_trace_from sa (tr1 ++ tr2) =
    annotate_trace_from sa tr1 ++
      annotate_trace_from (finite_trace_last sa ( annotate_trace_from sa tr1)) tr2.
Proof.
  revert sa.
  induction tr1 as [|item tr1]; [reflexivity|].
  intro sa.
  change ((item :: tr1) ++ tr2) with (item :: (tr1 ++ tr2)).
  rewrite !annotate_trace_from_unroll.
  simpl.
  rewrite IHtr1.
  f_equal.
  f_equal.
  f_equal.
  rewrite finite_trace_last_cons.
  reflexivity.
Qed.

Lemma annotate_trace_from_last_original_state sa tr
  : original_state (finite_trace_last sa (annotate_trace_from sa tr)) =
    finite_trace_last (original_state sa) tr.
Proof.
  destruct_list_last tr tr' item Heqtr; subst; [reflexivity|].
  rewrite annotate_trace_from_app.
  destruct item.
  cbn.
  rewrite! finite_trace_last_is_last.
  reflexivity.
Qed.

Definition annotate_trace (s : vstate X) (tr : list (vtransition_item X))
  : list (@transition_item _ annotated_type) :=
  annotate_trace_from {| original_state := s; state_annotation := ` inhabitant |} tr.

Lemma annotate_trace_project is tr
  : pre_VLSM_full_projection_finite_trace_project
      annotated_type (type X) id original_state
      (annotate_trace is tr)
      = tr.
Proof.
  unfold annotate_trace.
  remember {| original_state := is |} as sa.
  clear Heqsa.
  revert sa.
  induction tr as [| item]; [reflexivity|].
  intro sa.
  cbn.
  rewrite annotate_trace_item_project.
  f_equal.
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
  - cbv; intuition.
  - intros l (s,a) om (s', a') om'.
    cbn.
    unfold annotated_transition.
    cbn.
    destruct (vtransition _ _ _) as (_s', _om').
    inversion 1; reflexivity.
  - cbv; intuition.
  - cbv; intuition.
Qed.

End sec_annotated_vlsm_projections.
