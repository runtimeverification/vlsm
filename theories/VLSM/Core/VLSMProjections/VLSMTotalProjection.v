From VLSM.Lib Require Import Itauto.
From stdpp Require Import prelude.
From VLSM.Lib Require Import Preamble ListExtras StreamExtras StreamFilters StdppExtras.
From VLSM.Core Require Import VLSM VLSMProjections.VLSMPartialProjection.

Section sec_VLSM_projection.

(** * VLSM Total Projections

  A VLSM projection guaranteeing the existence of projection for all states and
  traces. We say that VLSM <<X>> projects to VLSM <<Y>> (sharing the same messages) if
  there exists maps <<state_project>> taking <<X>>-states to <<Y>>-states,
  and <<trace_project>>, taking list of transitions from <<X>> to <<Y>>, such that:

  - state and [trace_project_preserves_valid_trace]s.

  - [trace_project_app]: trace projection commutes with concatenation of traces

  - [final_state_project]: state projection commutes with [finite_trace_last]

  Proper examples of total projections (which are not [VLSM_embedding]s)
  are projections in which some of transitions might be dropped, such as
  the projection of a composition to one of the components ([component_projection])
  or the projection of the compositions of equivocators to the composition of
  regular nodes using the particular [MachineDescriptor] which select the
  first (original) node instance for each equivocator (e.g.,
  [equivocators_no_equivocations_vlsm_X_vlsm_projection]).
*)

Section sec_pre_definitions.

Context
  {message : Type}
  (TX TY : VLSMType message)
  (label_project : label TX -> option (label TY))
  (state_project : state TX -> state TY)
  .

Definition pre_VLSM_projection_in_projection
  (item : @transition_item _ TX)
  : Prop :=
  is_Some (label_project (l item)).

Definition pre_VLSM_projection_transition_item_project
  (item : @transition_item _ TX)
  : option (@transition_item _ TY)
  :=
  match label_project (l item) with
  | None => None
  | Some lY =>
    Some {| l := lY; input := input item; destination := state_project (destination item);
            output := output item |}
  end.

Lemma pre_VLSM_projection_transition_item_project_is_Some
  (item : @transition_item _ TX)
  : pre_VLSM_projection_in_projection item ->
    is_Some (pre_VLSM_projection_transition_item_project item).
Proof.
  intros [lY HlY].
  unfold pre_VLSM_projection_transition_item_project.
  rewrite HlY.
  by eexists.
Qed.

Lemma pre_VLSM_projection_transition_item_project_is_Some_rev
  (item : @transition_item _ TX)
  : is_Some (pre_VLSM_projection_transition_item_project item) ->
    pre_VLSM_projection_in_projection item.
Proof.
  intros [itemY HitemY].
  unfold pre_VLSM_projection_transition_item_project in HitemY.
  destruct (label_project (l item)) as [lY |] eqn: HlY; [| by congruence].
  by exists lY.
Qed.

Lemma pre_VLSM_projection_transition_item_project_infinitely_often
  (s : Streams.Stream (@transition_item _ TX))
  : InfinitelyOften pre_VLSM_projection_in_projection s ->
    InfinitelyOften (is_Some ∘ pre_VLSM_projection_transition_item_project) s.
Proof.
  apply InfinitelyOften_impl.
  intro item.
  by apply pre_VLSM_projection_transition_item_project_is_Some.
Qed.

Lemma pre_VLSM_projection_transition_item_project_finitely_many
  (s : Streams.Stream (@transition_item _ TX))
  : FinitelyManyBound pre_VLSM_projection_in_projection s ->
    FinitelyManyBound (is_Some ∘ pre_VLSM_projection_transition_item_project) s.
Proof.
  apply FinitelyManyBound_impl_rev.
  intro item.
  by apply pre_VLSM_projection_transition_item_project_is_Some_rev.
Qed.

Definition pre_VLSM_projection_finite_trace_project
  : list (@transition_item _ TX) -> list (@transition_item _ TY)
  :=
  map_option pre_VLSM_projection_transition_item_project.

Definition pre_VLSM_projection_infinite_trace_project
  (s : Streams.Stream (@transition_item _ TX))
  (Hs : InfinitelyOften  pre_VLSM_projection_in_projection s)
  : Streams.Stream (@transition_item _ TY) :=
  stream_map_option pre_VLSM_projection_transition_item_project s
    (pre_VLSM_projection_transition_item_project_infinitely_often _ Hs).

Definition pre_VLSM_projection_infinite_finite_trace_project
  (s : Streams.Stream (@transition_item _ TX))
  (Hs : FinitelyManyBound pre_VLSM_projection_in_projection s)
  : list (@transition_item _ TY) :=
  pre_VLSM_projection_finite_trace_project (stream_prefix s (proj1_sig Hs)).

Definition pre_VLSM_projection_finite_trace_project_app
  : forall l1 l2, pre_VLSM_projection_finite_trace_project (l1 ++ l2) =
    pre_VLSM_projection_finite_trace_project l1 ++ pre_VLSM_projection_finite_trace_project l2
  := map_option_app _.

Definition pre_VLSM_projection_finite_trace_project_app_rev
  : forall l l1' l2', pre_VLSM_projection_finite_trace_project l = l1' ++ l2' ->
    exists l1 l2, l = l1 ++ l2 /\
      pre_VLSM_projection_finite_trace_project l1 = l1' /\
      pre_VLSM_projection_finite_trace_project l2 = l2'
  := map_option_app_rev _.

Definition pre_VLSM_projection_finite_trace_project_elem_of_iff
  : forall trX itemY, itemY ∈ pre_VLSM_projection_finite_trace_project trX <->
    exists itemX, itemX ∈ trX /\ pre_VLSM_projection_transition_item_project itemX = Some itemY
  := elem_of_map_option _.

Definition elem_of_pre_VLSM_projection_finite_trace_project
  : forall trX itemY, itemY ∈ pre_VLSM_projection_finite_trace_project trX <->
    exists itemX, itemX ∈ trX /\ pre_VLSM_projection_transition_item_project itemX = Some itemY
  := elem_of_map_option _.

Definition pre_VLSM_projection_finite_trace_project_elem_of
  : forall itemX itemY, pre_VLSM_projection_transition_item_project itemX = Some itemY ->
    forall trX, itemX ∈ trX -> itemY ∈ pre_VLSM_projection_finite_trace_project trX.
Proof.
  by intros; apply elem_of_map_option; exists itemX.
Qed.

End sec_pre_definitions.

Record VLSM_projection_type
  {message : Type}
  (X : VLSM message)
  (TY : VLSMType message)
  (label_project : vlabel X -> option (label TY))
  (state_project : vstate X -> state TY)
  (trace_project := pre_VLSM_projection_finite_trace_project (type X) TY label_project state_project)
  : Prop :=
{
  final_state_project :
    forall sX trX,
      finite_valid_trace_from X sX trX ->
        state_project (finite_trace_last sX trX) =
        finite_trace_last (state_project sX) (trace_project trX);
}.

(** ** Projection definitions and properties *)

Section sec_projection_type_properties.

Definition VLSM_partial_trace_project_from_projection
  {message : Type}
  {X : VLSM message}
  {TY : VLSMType message}
  (label_project : vlabel X -> option (label TY))
  (state_project : vstate X -> state TY)
  (trace_project := pre_VLSM_projection_finite_trace_project _ _ label_project state_project)
  := fun str : vstate X * list (vtransition_item X) =>
      let (s, tr) := str in Some (state_project s, trace_project tr).

Context
  {message : Type}
  {X Y : VLSM message}
  {label_project : vlabel X -> option (vlabel Y)}
  {state_project : vstate X -> vstate Y}
  (trace_project := pre_VLSM_projection_finite_trace_project _ _ label_project state_project)
  (Hsimul : VLSM_projection_type X (type Y) label_project state_project)
  .

(**
  Any [VLSM_projection_type] determines a [VLSM_partial_projection_type], allowing us
  to lift to VLSM projection the generic results proved about VLSM partial projections.
*)
Lemma VLSM_partial_projection_type_from_projection :
  VLSM_partial_projection_type X Y
    (VLSM_partial_trace_project_from_projection label_project state_project).
Proof.
  split; intros; inversion H; subst; clear H.
  exists (state_project s'X), (trace_project preX).  split.
  - by cbn; rewrite pre_VLSM_projection_finite_trace_project_app.
  - symmetry. apply (final_state_project _ _ _ _ Hsimul).
    by apply (finite_valid_trace_from_app_iff  X) in H1; apply H1.
Qed.

End sec_projection_type_properties.

Section sec_projection_transition_consistency_None.

Context
  {message : Type}
  (X : VLSM message)
  (TY : VLSMType message)
  (label_project : vlabel X -> option (label TY))
  (state_project : vstate X -> state TY)
  (trace_project := pre_VLSM_projection_finite_trace_project _ _ label_project state_project)
  .

(**
  When a label cannot be projected, and thus the transition will not be
  preserved by the projection, the state projections of the states between and
  after the transition must coincide.
*)
Definition weak_projection_transition_consistency_None : Prop :=
  forall lX, label_project lX = None ->
  forall s om s' om', input_valid_transition X lX (s, om) (s', om') ->
      state_project s' = state_project s.

Definition strong_projection_transition_consistency_None : Prop :=
  forall lX, label_project lX = None ->
  forall s om s' om', vtransition X lX (s, om) = (s', om') ->
    state_project s' = state_project s.

Lemma strong_projection_transition_consistency_None_weaken
  : strong_projection_transition_consistency_None ->
    weak_projection_transition_consistency_None.
Proof.
  intros Hstrong lX Hl s om s' om' Ht.
  by apply (Hstrong lX Hl _ _ _ _ (proj2 Ht)).
Qed.

End sec_projection_transition_consistency_None.

Section sec_VLSM_projection_definitions.

Context
  {message : Type}
  (X Y : VLSM message)
  (label_project : vlabel X -> option (vlabel Y))
  (state_project : vstate X -> vstate Y)
  (trace_project := pre_VLSM_projection_finite_trace_project _ _ label_project state_project)
  .

(**
  Similarly to the [VLSM_partial_projection] case we distinguish two types of
  projections: [VLSM_weak_projection] and [VLSM_projection], distinguished by the
  fact that the weak projections are not required to preserve initial states.

  Although we don't have proper examples of [VLSM_weak_projection]s, they are a
  support base for [VLSM_weak_embedding]s for which we have proper examples.
*)
Record VLSM_weak_projection : Prop :=
{
  weak_projection_type :> VLSM_projection_type X (type Y) label_project state_project;
  weak_trace_project_preserves_valid_trace :
    forall sX trX,
      finite_valid_trace_from X sX trX ->
      finite_valid_trace_from Y (state_project sX) (trace_project trX);
}.

Record VLSM_projection : Prop :=
{
  projection_type :> VLSM_projection_type X (type Y) label_project state_project;
  trace_project_preserves_valid_trace :
    forall sX trX,
      finite_valid_trace X sX trX -> finite_valid_trace Y (state_project sX) (trace_project trX);
}.

Definition weak_projection_initial_state_preservation : Prop :=
  forall s : vstate X,
    vinitial_state_prop X s -> valid_state_prop Y (state_project s).

Definition strong_projection_initial_state_preservation : Prop :=
  forall s : vstate X,
    vinitial_state_prop X s -> vinitial_state_prop Y (state_project s).

Lemma strong_projection_initial_state_preservation_weaken
  : strong_projection_initial_state_preservation ->
    weak_projection_initial_state_preservation.
Proof.
  intros Hstrong s Hs. apply Hstrong in Hs.
  by apply initial_state_is_valid.
Qed.

Definition weak_projection_valid_preservation : Prop :=
  forall lX lY (HlX : label_project lX = Some lY),
  forall s om
    (Hv : input_valid X lX (s, om))
    (HsY : valid_state_prop Y (state_project s))
    (HomY : option_valid_message_prop Y om),
    vvalid Y lY ((state_project s), om).

Definition strong_projection_valid_preservation : Prop :=
  forall lX lY, label_project lX = Some lY ->
  forall s om,
  vvalid X lX (s, om) -> vvalid Y lY ((state_project s), om).

Lemma strong_projection_valid_preservation_weaken
  : strong_projection_valid_preservation ->
    weak_projection_valid_preservation.
Proof.
  intros Hstrong lX lY Hl s om Hpv Hs Hom.
  by apply (Hstrong lX lY Hl), Hpv.
Qed.

Definition weak_projection_transition_preservation_Some : Prop :=
  forall lX lY, label_project lX = Some lY ->
  forall s om s' om', input_valid_transition X lX (s, om) (s', om') ->
    vtransition Y lY (state_project s, om) = (state_project s', om').

Definition strong_projection_transition_preservation_Some : Prop :=
  forall lX lY, label_project lX = Some lY ->
  forall s om s' om', vtransition X lX (s, om) = (s', om') ->
    vtransition Y lY (state_project s, om) = (state_project s', om').

Lemma strong_projection_transition_preservation_Some_weaken
  : strong_projection_transition_preservation_Some ->
    weak_projection_transition_preservation_Some.
Proof.
  intros Hstrong lX lY Hl s om s' om' Ht.
  by apply (Hstrong lX lY Hl), Ht.
Qed.

Definition weak_projection_valid_message_preservation : Prop :=
  forall lX lY (HlX : label_project lX = Some lY),
  forall s m
    (Hv : input_valid X lX (s, Some m))
    (HsY : valid_state_prop Y (state_project s)),
    valid_message_prop Y m.

Definition strong_projection_valid_message_preservation : Prop :=
  forall m : message,
    valid_message_prop X m -> valid_message_prop Y m.

Lemma strong_projection_valid_message_preservation_weaken
  : strong_projection_valid_message_preservation ->
    weak_projection_valid_message_preservation.
Proof.
  by intros Hstrong lX lY Hl  s m [_ [Hm%Hstrong _]] HsY.
Qed.

End sec_VLSM_projection_definitions.

Section sec_weak_projection_properties.

Definition VLSM_weak_projection_trace_project
  {message : Type}
  {X Y : VLSM message}
  {label_project : vlabel X -> option (vlabel Y)}
  {state_project : vstate X -> vstate Y}
  (Hsimul : VLSM_weak_projection X Y label_project state_project)
  : list (vtransition_item X) -> list (vtransition_item Y)
  := pre_VLSM_projection_finite_trace_project _ _ label_project state_project.

Definition VLSM_weak_projection_in
  {message : Type}
  {X Y : VLSM message}
  {label_project : vlabel X -> option (vlabel Y)}
  {state_project : vstate X -> vstate Y}
  (Hsimul : VLSM_weak_projection X Y label_project state_project)
  := pre_VLSM_projection_in_projection _ _ label_project.

Definition VLSM_weak_projection_infinite_trace_project
  {message : Type}
  {X Y : VLSM message}
  {label_project : vlabel X -> option (vlabel Y)}
  {state_project : vstate X -> vstate Y}
  (Hsimul : VLSM_weak_projection X Y label_project state_project)
  (s : Streams.Stream (vtransition_item X))
  (Hinf : InfinitelyOften (VLSM_weak_projection_in Hsimul) s)
  : Streams.Stream (vtransition_item Y)
  := pre_VLSM_projection_infinite_trace_project _ _ label_project state_project s Hinf.

Definition VLSM_weak_projection_infinite_finite_trace_project
  {message : Type}
  {X Y : VLSM message}
  {label_project : vlabel X -> option (vlabel Y)}
  {state_project : vstate X -> vstate Y}
  (Hsimul : VLSM_weak_projection X Y label_project state_project)
  (s : Streams.Stream (vtransition_item X))
  (Hfin : FinitelyManyBound (VLSM_weak_projection_in Hsimul) s)
  : list (vtransition_item Y)
  := pre_VLSM_projection_infinite_finite_trace_project _ _ label_project state_project s Hfin.

Context
  {message : Type}
  {X Y : VLSM message}
  {label_project : vlabel X -> option (vlabel Y)}
  {state_project : vstate X -> vstate Y}
  (Hsimul : VLSM_weak_projection X Y label_project state_project)
  .

Definition VLSM_weak_projection_trace_project_app
  : forall l1 l2, VLSM_weak_projection_trace_project Hsimul (l1 ++ l2) =
    VLSM_weak_projection_trace_project Hsimul l1 ++ VLSM_weak_projection_trace_project Hsimul l2
  := pre_VLSM_projection_finite_trace_project_app _ _ label_project state_project.

Definition VLSM_weak_projection_trace_project_app_rev
  : forall l l1' l2', VLSM_weak_projection_trace_project Hsimul l = l1' ++ l2' ->
    exists l1 l2, l = l1 ++ l2 /\
      VLSM_weak_projection_trace_project Hsimul l1 = l1' /\
      VLSM_weak_projection_trace_project Hsimul l2 = l2'
  := pre_VLSM_projection_finite_trace_project_app_rev _ _ label_project state_project.

Definition VLSM_weak_projection_finite_trace_last
  : forall sX trX,
    finite_valid_trace_from X sX trX ->
    state_project (finite_trace_last sX trX) =
    finite_trace_last (state_project sX) (VLSM_weak_projection_trace_project Hsimul trX)
  := final_state_project _ _ _ _ Hsimul.

Definition VLSM_weak_projection_finite_valid_trace_from
  : forall sX trX,
    finite_valid_trace_from X sX trX ->
      finite_valid_trace_from Y (state_project sX) (VLSM_weak_projection_trace_project Hsimul trX)
  := weak_trace_project_preserves_valid_trace _ _ _ _ Hsimul.

Lemma VLSM_weak_projection_infinite_valid_trace_from
  : forall sX trX (Hinf : InfinitelyOften (VLSM_weak_projection_in Hsimul) trX),
    infinite_valid_trace_from X sX trX ->
    infinite_valid_trace_from Y (state_project sX)
      (VLSM_weak_projection_infinite_trace_project Hsimul trX Hinf).
Proof.
  intros sX trX Hinf HtrX.
  apply infinite_valid_trace_from_prefix_rev.
  intros n.
  specialize
    (stream_map_option_prefix_ex (pre_VLSM_projection_transition_item_project _ _
      label_project state_project) trX
    (pre_VLSM_projection_transition_item_project_infinitely_often _ _
      label_project state_project trX Hinf)
    n)
    as [m Hrew].
  unfold VLSM_weak_projection_infinite_trace_project, pre_VLSM_projection_infinite_trace_project.
  replace (stream_prefix _ _) with (VLSM_weak_projection_trace_project Hsimul (stream_prefix trX m)).
  by apply VLSM_weak_projection_finite_valid_trace_from, infinite_valid_trace_from_prefix.
Qed.

Lemma VLSM_weak_projection_infinite_finite_valid_trace_from
  : forall sX trX (Hfin : FinitelyManyBound (VLSM_weak_projection_in Hsimul) trX),
    infinite_valid_trace_from X sX trX ->
    finite_valid_trace_from Y (state_project sX)
      (VLSM_weak_projection_infinite_finite_trace_project Hsimul trX Hfin).
Proof.
  intros sX trX Hfin HtrX.
  apply VLSM_weak_projection_finite_valid_trace_from.
  by apply infinite_valid_trace_from_prefix with (n := `Hfin) in HtrX.
Qed.

(**
  Any [VLSM_projection] determines a [VLSM_partial_projection], allowing us
  to lift to VLSM projection the generic results proved about VLSM partial projections.
*)
Lemma VLSM_weak_partial_projection_from_projection :
  VLSM_weak_partial_projection X Y
    (VLSM_partial_trace_project_from_projection label_project state_project).
Proof.
  split.
  - by apply VLSM_partial_projection_type_from_projection, Hsimul.
  - cbn; intros sX trX sY trY [= <- <-].
    by apply VLSM_weak_projection_finite_valid_trace_from.
Qed.

Lemma VLSM_weak_projection_valid_state
  : forall sX,
    valid_state_prop X sX -> valid_state_prop Y (state_project sX).
Proof.
  specialize VLSM_weak_partial_projection_from_projection as Hpart_simul.
  specialize (VLSM_weak_partial_projection_valid_state Hpart_simul) as Hps.
  by intro sX; eapply Hps.
Qed.

Lemma VLSM_weak_projection_input_valid_transition
  : forall lX lY, label_project lX = Some lY ->
    forall s im s' om,
    input_valid_transition X lX (s, im) (s', om) ->
    input_valid_transition Y lY (state_project s, im) (state_project s', om).
Proof.
  specialize VLSM_weak_partial_projection_from_projection as Hpart_simul.
  specialize (VLSM_weak_partial_projection_input_valid_transition Hpart_simul) as Hivt.
  intros.
  apply
    (Hivt s {| l := lX; input := im; destination := s'; output := om |}
      (state_project s) {| l := lY; input := im; destination := state_project s'; output := om |})
  ; [| done].
  by cbn; unfold pre_VLSM_projection_transition_item_project; cbn; rewrite H.
Qed.

Lemma VLSM_weak_projection_input_valid
  : forall lX lY, label_project lX = Some lY ->
    forall s im, input_valid X lX (s, im) -> input_valid Y lY (state_project s, im).
Proof.
  intros lX lY Hpr sX im HvX.
  destruct (vtransition X lX (sX, im)) eqn: HtX.
  by eapply VLSM_weak_projection_input_valid_transition, input_valid_can_transition.
Qed.

Lemma VLSM_weak_projection_finite_valid_trace_from_to :
  forall sX s'X trX,
    finite_valid_trace_from_to X sX s'X trX ->
      finite_valid_trace_from_to Y (state_project sX) (state_project s'X)
        (VLSM_weak_projection_trace_project Hsimul trX).
Proof.
  specialize VLSM_weak_partial_projection_from_projection as Hpart_simul.
  specialize (VLSM_weak_partial_projection_finite_valid_trace_from Hpart_simul) as Htr.
  intros sX s'X trX HtrX.
  apply valid_trace_get_last in HtrX as Hs'X.
  apply valid_trace_forget_last in HtrX. subst.
  rewrite (final_state_project _ _ _ _ Hsimul); [| done].
  by apply valid_trace_add_default_last; eauto.
Qed.

Lemma VLSM_weak_projection_in_futures
  : forall s1 s2,
    in_futures X s1 s2 -> in_futures Y (state_project s1) (state_project s2).
Proof.
  intros s1 s2 [tr Htr].
  exists (VLSM_weak_projection_trace_project Hsimul tr).
  by apply VLSM_weak_projection_finite_valid_trace_from_to.
Qed.

End sec_weak_projection_properties.

Section sec_projection_properties.

Definition VLSM_projection_finite_trace_project
  {message : Type}
  {X Y : VLSM message}
  {label_project : vlabel X -> option (vlabel Y)}
  {state_project : vstate X -> vstate Y}
  (Hsimul : VLSM_projection X Y label_project state_project)
  : list (vtransition_item X) -> list (vtransition_item Y)
  := pre_VLSM_projection_finite_trace_project _ _ label_project state_project.

Definition VLSM_projection_in
  {message : Type}
  {X Y : VLSM message}
  {label_project : vlabel X -> option (vlabel Y)}
  {state_project : vstate X -> vstate Y}
  (Hsimul : VLSM_projection X Y label_project state_project)
  := pre_VLSM_projection_in_projection _ _ label_project.

Definition VLSM_projection_infinite_trace_project
  {message : Type}
  {X Y : VLSM message}
  {label_project : vlabel X -> option (vlabel Y)}
  {state_project : vstate X -> vstate Y}
  (Hsimul : VLSM_projection X Y label_project state_project)
  (s : Streams.Stream (vtransition_item X))
  (Hinf : InfinitelyOften (VLSM_projection_in Hsimul) s)
  : Streams.Stream (vtransition_item Y)
  := pre_VLSM_projection_infinite_trace_project _ _ label_project state_project s Hinf.

Definition VLSM_projection_infinite_finite_trace_project
  {message : Type}
  {X Y : VLSM message}
  {label_project : vlabel X -> option (vlabel Y)}
  {state_project : vstate X -> vstate Y}
  (Hsimul : VLSM_projection X Y label_project state_project)
  (s : Streams.Stream (vtransition_item X))
  (Hfin : FinitelyManyBound (VLSM_projection_in Hsimul) s)
  : list (vtransition_item Y)
  := pre_VLSM_projection_infinite_finite_trace_project _ _ label_project state_project s Hfin.

Context
  {message : Type}
  {X Y : VLSM message}
  {label_project : vlabel X -> option (vlabel Y)}
  {state_project : vstate X -> vstate Y}
  (Hsimul : VLSM_projection X Y label_project state_project)
  .

Definition VLSM_projection_finite_trace_project_app
  : forall l1 l2, VLSM_projection_finite_trace_project Hsimul (l1 ++ l2) =
    VLSM_projection_finite_trace_project Hsimul l1 ++ VLSM_projection_finite_trace_project Hsimul l2
  := pre_VLSM_projection_finite_trace_project_app _ _ label_project state_project.

Definition VLSM_projection_finite_trace_project_app_rev
  : forall l l1' l2', VLSM_projection_finite_trace_project Hsimul l = l1' ++ l2' ->
    exists l1 l2,
      l = l1 ++ l2 /\
      VLSM_projection_finite_trace_project Hsimul l1 = l1' /\
      VLSM_projection_finite_trace_project Hsimul l2 = l2'
  := pre_VLSM_projection_finite_trace_project_app_rev _ _ label_project state_project.

Definition VLSM_projection_finite_trace_project_in
  : forall itemX itemY,
      pre_VLSM_projection_transition_item_project
        _ _ label_project state_project itemX = Some itemY ->
    forall trX,
      itemX ∈ trX -> itemY ∈ VLSM_projection_finite_trace_project Hsimul trX
  := pre_VLSM_projection_finite_trace_project_elem_of _ _ label_project state_project.

Definition VLSM_projection_finite_trace_last
  : forall sX trX,
      finite_valid_trace_from X sX trX ->
      state_project (finite_trace_last sX trX) = finite_trace_last (state_project sX)
        (VLSM_projection_finite_trace_project Hsimul trX)
  := final_state_project _ _ _ _ Hsimul.

Definition VLSM_projection_finite_valid_trace
  : forall sX trX,
      finite_valid_trace X sX trX -> finite_valid_trace Y (state_project sX)
        (VLSM_projection_finite_trace_project Hsimul trX)
  := trace_project_preserves_valid_trace _ _ _ _ Hsimul.

(**
  Any [VLSM_projection] determines a [VLSM_partial_projection], allowing us
  to lift to VLSM projection the generic results proved about VLSM partial projections.
*)
Lemma VLSM_partial_projection_from_projection :
  VLSM_partial_projection X Y
    (VLSM_partial_trace_project_from_projection label_project state_project).
Proof.
  split.
  - by apply VLSM_partial_projection_type_from_projection, Hsimul.
  - cbn; intros sX trX sY trY [= <- <-].
    by apply VLSM_projection_finite_valid_trace.
Qed.

Lemma VLSM_projection_finite_valid_trace_from
  : forall sX trX,
      finite_valid_trace_from X sX trX ->
      finite_valid_trace_from Y (state_project sX) (VLSM_projection_finite_trace_project Hsimul trX).
Proof.
  specialize VLSM_partial_projection_from_projection as Hpart_simul.
  specialize (VLSM_partial_projection_finite_valid_trace_from Hpart_simul) as Hivt.
  by intros sX trX; apply Hivt.
Qed.

Definition VLSM_projection_weaken : VLSM_weak_projection X Y label_project state_project :=
  {| weak_projection_type := projection_type _ _ _ _ Hsimul
  ;  weak_trace_project_preserves_valid_trace := VLSM_projection_finite_valid_trace_from
  |}.

Definition VLSM_projection_valid_state
  : forall sX,
    valid_state_prop X sX -> valid_state_prop Y (state_project sX)
  := VLSM_weak_projection_valid_state VLSM_projection_weaken.

Definition VLSM_projection_input_valid_transition
  : forall lX lY, label_project lX = Some lY ->
    forall s im s' om,
    input_valid_transition X lX (s, im) (s', om) ->
    input_valid_transition Y lY (state_project s, im) (state_project s', om)
  := VLSM_weak_projection_input_valid_transition VLSM_projection_weaken.

Definition VLSM_projection_input_valid
  := VLSM_weak_projection_input_valid VLSM_projection_weaken.

Definition VLSM_projection_finite_valid_trace_from_to
  : forall sX s'X trX,
      finite_valid_trace_from_to X sX s'X trX ->
      finite_valid_trace_from_to Y (state_project sX) (state_project s'X)
        (VLSM_projection_finite_trace_project Hsimul trX)
  := VLSM_weak_projection_finite_valid_trace_from_to VLSM_projection_weaken.

Definition VLSM_projection_in_futures
  : forall s1 s2,
    in_futures X s1 s2 -> in_futures Y (state_project s1) (state_project s2)
  := VLSM_weak_projection_in_futures VLSM_projection_weaken.

Definition VLSM_projection_infinite_valid_trace_from
  : forall sX trX (Hinf : InfinitelyOften (VLSM_projection_in Hsimul) trX),
    infinite_valid_trace_from X sX trX ->
    infinite_valid_trace_from Y (state_project sX)
      (VLSM_projection_infinite_trace_project Hsimul trX Hinf)
    := VLSM_weak_projection_infinite_valid_trace_from VLSM_projection_weaken.

Definition VLSM_projection_infinite_finite_valid_trace_from
  : forall sX trX (Hfin : FinitelyManyBound (VLSM_projection_in Hsimul) trX),
    infinite_valid_trace_from X sX trX ->
    finite_valid_trace_from Y (state_project sX)
      (VLSM_projection_infinite_finite_trace_project Hsimul trX Hfin)
    := VLSM_weak_projection_infinite_finite_valid_trace_from VLSM_projection_weaken.

Lemma VLSM_projection_initial_state
  : forall sX, vinitial_state_prop X sX -> vinitial_state_prop Y (state_project sX).
Proof.
  specialize VLSM_partial_projection_from_projection as Hpart_simul.
  specialize (VLSM_partial_projection_initial_state Hpart_simul) as His.
  by intro sX; eapply His.
Qed.

Lemma VLSM_projection_finite_valid_trace_init_to
  : forall sX s'X trX,
      finite_valid_trace_init_to X sX s'X trX ->
      finite_valid_trace_init_to Y (state_project sX) (state_project s'X)
        (VLSM_projection_finite_trace_project Hsimul trX).
Proof.
  intros. destruct H as [H Hinit]. split.
  - by apply VLSM_projection_finite_valid_trace_from_to.
  - by apply VLSM_projection_initial_state.
Qed.

Lemma VLSM_projection_infinite_valid_trace
  : forall sX trX (Hinf : InfinitelyOften (VLSM_projection_in Hsimul) trX),
    infinite_valid_trace X sX trX ->
    infinite_valid_trace Y (state_project sX)
      (VLSM_projection_infinite_trace_project Hsimul trX Hinf).
Proof.
  intros sX trX Hinf [HtrX HsX].
  split.
  - by apply VLSM_projection_infinite_valid_trace_from.
  - by apply VLSM_projection_initial_state.
Qed.

Lemma VLSM_projection_infinite_finite_valid_trace
  : forall sX trX (Hfin : FinitelyManyBound (VLSM_projection_in Hsimul) trX),
    infinite_valid_trace X sX trX ->
    finite_valid_trace Y (state_project sX)
      (VLSM_projection_infinite_finite_trace_project Hsimul trX Hfin).
Proof.
  intros sX trX Hfin [HtrX HsX].
  split.
  - by apply VLSM_projection_infinite_finite_valid_trace_from.
  - by apply VLSM_projection_initial_state.
Qed.

(** ** Projection friendliness

  A projection is friendly if all the valid traces of the projection are
  projections of the valid traces of the source VLSM.
*)

Section sec_projection_friendliness.

(**
  We axiomatize projection friendliness as the converse of
  [VLSM_projection_finite_valid_trace]
*)
Definition projection_friendly_prop
  := forall
    (sY : vstate Y)
    (trY : list (vtransition_item Y))
    (HtrY : finite_valid_trace Y sY trY),
    exists (sX : vstate X) (trX : list (vtransition_item X)),
      finite_valid_trace X sX trX
      /\ state_project sX = sY
      /\ VLSM_projection_finite_trace_project Hsimul trX = trY.

Lemma projection_friendly_in_futures
  (Hfr : projection_friendly_prop)
  (s1 s2 : vstate Y)
  (Hfuture : in_futures Y s1 s2)
  : exists (sX1 sX2 : vstate X),
    state_project sX1 = s1 /\ state_project sX2 = s2 /\ in_futures X sX1 sX2.
Proof.
  destruct Hfuture as [tr_s2 Hfuture].
  apply finite_valid_trace_from_to_complete_left in Hfuture
    as [is [tr_s1 [Htr Heq_s1]]].
  apply valid_trace_get_last in Htr as Heq_s2.
  apply valid_trace_forget_last in Htr.
  apply Hfr in Htr as [isX [trX [Htr [His Htr_pr]]]].
  apply VLSM_projection_finite_trace_project_app_rev in Htr_pr
    as (trX_s1 & trX_s2 & HeqtrX & Htr_s1_pr & Htr_s2_pr).
  subst.
  destruct Htr as [HtrX HisX].
  apply finite_valid_trace_from_app_iff in HtrX as HtrX12.
  destruct HtrX12 as [HtrX1 HtrX2].
  apply valid_trace_add_default_last in HtrX2.
  exists (finite_trace_last isX trX_s1).
  exists (finite_trace_last isX  (trX_s1 ++ trX_s2)).
  rewrite !VLSM_projection_finite_trace_last,
    VLSM_projection_finite_trace_project_app; [| done | done].
  repeat split.
  by rewrite finite_trace_last_app; eexists.
Qed.

(**
  A consequence of the [projection_friendly_prop]erty is that the valid
  traces of the projection are precisely the projections of all the valid traces
  of the source VLSM.
*)
Lemma projection_friendly_trace_char
  (Hfriendly : projection_friendly_prop)
  : forall sY trY, finite_valid_trace Y sY trY <->
    exists (sX : vstate X) (trX : list (vtransition_item X)),
      finite_valid_trace X sX trX
      /\ state_project sX = sY
      /\ VLSM_projection_finite_trace_project Hsimul trX = trY.
Proof.
  split; [by apply Hfriendly |].
  intros [sX [trX [HtrX [<- <-]]]].
  by apply VLSM_projection_finite_valid_trace.
Qed.

End sec_projection_friendliness.

End sec_projection_properties.

End sec_VLSM_projection.

(**
  For VLSM <<X>> to project to a VLSM <<Y>>, the following set of conditions is sufficient:
  - <<X>>'s [initial_state]s project to <<Y>>'s [initial state]s
  - Every message <<m>> (including the empty one) which can be input to a
    projectable [input_valid] transition in <<X>>, is a [valid_message]
    in <<Y>>
  - <<X>>'s [input_valid] is included in <<Y>>'s [valid].
  - For all projectable [input_valid] inputs (in <<X>>), <<Y>>'s [transition]
    acts like <<X>>'s [transition].
  - All non-projectable transitions preserve the projected state
*)

Section sec_basic_VLSM_projection.

Section sec_basic_VLSM_projection_type.

Context
  {message : Type}
  (X : VLSM message)
  (TY : VLSMType message)
  (label_project : vlabel X -> option (label TY))
  (state_project : vstate X -> state TY)
  (Htransition_None : weak_projection_transition_consistency_None X TY label_project state_project)
  .

Lemma basic_VLSM_projection_type
  : VLSM_projection_type X TY label_project state_project.
Proof.
  constructor.
  intros is tr Htr.
  induction Htr using finite_valid_trace_from_rev_ind
  ; [done |].
  rewrite (pre_VLSM_projection_finite_trace_project_app _ _ label_project state_project).
  rewrite finite_trace_last_is_last.
  rewrite finite_trace_last_app, <- IHHtr.
  clear IHHtr.
  simpl.
  unfold pre_VLSM_projection_transition_item_project.
  destruct (label_project _) as [lY |] eqn: Hl; [done |].
  apply (Htransition_None _ Hl) in Hx.
  by rewrite Hx.
Qed.

End sec_basic_VLSM_projection_type.

Context
  {message : Type}
  (X Y : VLSM message)
  (label_project : vlabel X -> option (vlabel Y))
  (state_project : vstate X -> vstate Y)
  .

Context
  (Hvalid : weak_projection_valid_preservation X Y label_project state_project)
  (Htransition_Some : weak_projection_transition_preservation_Some X Y label_project state_project)
  (Htransition_None : weak_projection_transition_consistency_None _ _ label_project state_project)
  (Htype : VLSM_projection_type X (type Y) label_project state_project :=
    basic_VLSM_projection_type X (type Y) label_project state_project Htransition_None)
  .

Section sec_weak_projection.

Context
  (Hstate : weak_projection_initial_state_preservation X Y state_project)
  (Hmessage : weak_projection_valid_message_preservation X Y label_project state_project)
  .

#[local] Lemma basic_VLSM_projection_finite_valid_trace_init_to
  is s tr
  (Htr : finite_valid_trace_init_to X is s tr)
  : finite_valid_trace_from_to Y (state_project is) (state_project s)
      (pre_VLSM_projection_finite_trace_project _ _ label_project state_project tr).
Proof.
  induction Htr using finite_valid_trace_init_to_rev_strong_ind; [by constructor; apply Hstate |].
  unfold pre_VLSM_projection_finite_trace_project.
  rewrite map_option_app.
  apply finite_valid_trace_from_to_app with (state_project s)
  ; [done |].
  simpl. unfold pre_VLSM_projection_transition_item_project.
  simpl.
  apply valid_trace_last_pstate in IHHtr1.
  destruct (label_project l) as [lY |] eqn: Hl; cycle 1.
  - by apply (Htransition_None _ Hl) in Ht; rewrite Ht; constructor.
  - apply finite_valid_trace_from_to_singleton.
    assert (Hiom : option_valid_message_prop Y iom).
    {
      destruct iom as [im |]; [| by apply option_valid_message_None].
      by apply (Hmessage _ _ Hl _ _ (proj1 Ht)).
    }
    specialize (Hvalid _ _ Hl _ _ (proj1 Ht) IHHtr1 Hiom).
    by apply (Htransition_Some _ _ Hl) in Ht.
Qed.

#[local] Lemma basic_VLSM_projection_finite_valid_trace_from
  (s : vstate X)
  (ls : list transition_item)
  (Hpxt : finite_valid_trace_from X s ls)
  : finite_valid_trace_from Y (state_project s)
      (pre_VLSM_projection_finite_trace_project _ _ label_project state_project ls).
Proof.
  apply valid_trace_add_default_last in Hpxt.
  apply valid_trace_first_pstate in Hpxt as Hs.
  apply valid_state_has_trace in Hs as [is_s [tr_s Hs]].
  specialize (finite_valid_trace_from_to_app X _ _ _ _ _ (proj1 Hs) Hpxt) as Happ.
  specialize (basic_VLSM_projection_finite_valid_trace_init_to _ _ _ (conj Happ (proj2 Hs)))
    as Happ_pr.
  rewrite (pre_VLSM_projection_finite_trace_project_app _ _ label_project state_project) in Happ_pr.
  apply finite_valid_trace_from_to_app_split, proj2 in Happ_pr.
  apply valid_trace_get_last in Hs as Heqs.
  apply valid_trace_forget_last, proj1 in Hs.
  rewrite <- (final_state_project X (type Y) label_project state_project Htype)
    in Happ_pr by done.
  by apply valid_trace_forget_last in Happ_pr; subst.
Qed.

Lemma basic_VLSM_weak_projection
  : VLSM_weak_projection X Y label_project state_project.
Proof.
  constructor; [done |].
  apply basic_VLSM_projection_finite_valid_trace_from.
Qed.

End sec_weak_projection.

Lemma basic_VLSM_weak_projection_strengthen
  (Hweak : VLSM_weak_projection X Y label_project state_project)
  (Hstate : strong_projection_initial_state_preservation X Y state_project)
  : VLSM_projection X Y label_project state_project.
Proof.
  constructor; [by apply Hweak |].
  intros sX trX [HtrX HsX]; split.
  - by apply (VLSM_weak_projection_finite_valid_trace_from Hweak).
  - by apply Hstate.
Qed.

Lemma basic_VLSM_projection
  (Hstate : strong_projection_initial_state_preservation X Y state_project)
  (Hmessage : weak_projection_valid_message_preservation X Y label_project state_project)
  : VLSM_projection X Y label_project state_project.
Proof.
  apply basic_VLSM_weak_projection_strengthen; [| done].
  apply basic_VLSM_weak_projection; [| done].
  by apply strong_projection_initial_state_preservation_weaken.
Qed.

End sec_basic_VLSM_projection.

Lemma basic_VLSM_strong_projection
  {message : Type}
  (X Y : VLSM message)
  (label_project : vlabel X -> option (vlabel Y))
  (state_project : vstate X -> vstate Y)
  (Hvalid : strong_projection_valid_preservation X Y label_project state_project)
  (Htransition_Some : strong_projection_transition_preservation_Some X Y label_project state_project)
  (Htransition_None : strong_projection_transition_consistency_None _ _ label_project state_project)
  (Hstate : strong_projection_initial_state_preservation X Y state_project)
  (Hmessage : strong_projection_valid_message_preservation X Y)
  : VLSM_projection X Y label_project state_project.
Proof.
  apply basic_VLSM_projection.
  - by apply strong_projection_valid_preservation_weaken.
  - by apply strong_projection_transition_preservation_Some_weaken.
  - by apply strong_projection_transition_consistency_None_weaken.
  - done.
  - by apply strong_projection_valid_message_preservation_weaken.
Qed.

Lemma basic_VLSM_projection_type_preloaded
  {message : Type}
  (X Y : VLSM message)
  (label_project : vlabel X -> option (vlabel Y))
  (state_project : vstate X -> vstate Y)
  (Htransition_None : strong_projection_transition_consistency_None _ _ label_project state_project)
  : VLSM_projection_type (pre_loaded_with_all_messages_vlsm X) (type Y) label_project state_project.
Proof.
  constructor.
  intros is tr Htr.
  induction Htr using finite_valid_trace_from_rev_ind
  ; [done |].
  rewrite (@pre_VLSM_projection_finite_trace_project_app _
    (type (pre_loaded_with_all_messages_vlsm X)) (type Y) label_project state_project).
  rewrite finite_trace_last_is_last.
  rewrite finite_trace_last_app, <- IHHtr.
  clear IHHtr.
  simpl.
  unfold pre_VLSM_projection_transition_item_project.
  destruct (label_project _) as [lY |] eqn: Hl; [done |].
  apply proj2, (Htransition_None _ Hl) in Hx.
  by rewrite Hx.
Qed.

Lemma basic_VLSM_projection_preloaded
  {message : Type}
  (X Y : VLSM message)
  (label_project : vlabel X -> option (vlabel Y))
  (state_project : vstate X -> vstate Y)
  (Hvalid : strong_projection_valid_preservation X Y label_project state_project)
  (Htransition_Some : strong_projection_transition_preservation_Some X Y label_project state_project)
  (Htransition_None : strong_projection_transition_consistency_None _ _ label_project state_project)
  (Hstate : strong_projection_initial_state_preservation X Y state_project)
  : VLSM_projection
      (pre_loaded_with_all_messages_vlsm X)
      (pre_loaded_with_all_messages_vlsm Y) label_project state_project.
Proof.
  specialize (basic_VLSM_projection_type_preloaded X Y label_project state_project Htransition_None)
    as Htype.
  constructor; [done |].
  intros sX trX HtrX.
  split; [| by apply Hstate; apply HtrX].
  induction HtrX using finite_valid_trace_rev_ind.
  - by constructor; apply initial_state_is_valid, Hstate.
  - rewrite (@pre_VLSM_projection_finite_trace_project_app _
      (type (pre_loaded_with_all_messages_vlsm X)) (type Y) label_project state_project).
    apply (finite_valid_trace_from_app_iff (pre_loaded_with_all_messages_vlsm Y)).
    split; [done |].
    simpl. unfold pre_VLSM_projection_transition_item_project.
    simpl.
    apply finite_valid_trace_last_pstate in IHHtrX.
    destruct Hx as [[_ [_ Hv]] Ht].
    rewrite <- (final_state_project _ _ _ _ Htype) in IHHtrX |- * by apply HtrX.
    destruct (label_project l) as [lY |] eqn: Hl.
    + apply (finite_valid_trace_singleton (pre_loaded_with_all_messages_vlsm Y)).
      assert (Hiom : option_valid_message_prop (pre_loaded_with_all_messages_vlsm Y) iom).
      {
        destruct iom as [im |]; [| by apply option_valid_message_None].
        by apply (any_message_is_valid_in_preloaded Y).
      }
      apply (Hvalid _ _ Hl) in Hv.
      by apply (Htransition_Some _ _ Hl) in Ht.
    + by apply (finite_valid_trace_from_empty (pre_loaded_with_all_messages_vlsm Y)).
Qed.

Lemma basic_VLSM_projection_type_preloaded_with
  {message : Type}
  (X Y : VLSM message)
  (P Q : message -> Prop)
  (label_project : vlabel X -> option (vlabel Y))
  (state_project : vstate X -> vstate Y)
  (Htransition_None : strong_projection_transition_consistency_None _ _ label_project state_project)
  : VLSM_projection_type (pre_loaded_vlsm X P) (type Y) label_project state_project.
Proof.
  constructor.
  intros is tr Htr.
  induction Htr using finite_valid_trace_from_rev_ind
  ; [done |].
  rewrite (@pre_VLSM_projection_finite_trace_project_app
    _ (type (pre_loaded_vlsm X P)) (type Y) label_project state_project).
  rewrite finite_trace_last_is_last.
  rewrite finite_trace_last_app, <- IHHtr.
  clear IHHtr.
  simpl.
  unfold pre_VLSM_projection_transition_item_project.
  destruct (label_project _) as [lY |] eqn: Hl; [done |].
  apply proj2, (Htransition_None _ Hl) in Hx.
  by rewrite Hx.
Qed.

Lemma basic_VLSM_projection_preloaded_with
  {message : Type}
  (X Y : VLSM message)
  (P Q : message -> Prop)
  (label_project : vlabel X -> option (vlabel Y))
  (state_project : vstate X -> vstate Y)
  (Hvalid : strong_projection_valid_preservation X Y label_project state_project)
  (Htransition_Some : strong_projection_transition_preservation_Some X Y label_project state_project)
  (Htransition_None : strong_projection_transition_consistency_None _ _ label_project state_project)
  (Hstate : strong_projection_initial_state_preservation X Y state_project)
  (Hmessage : weak_projection_valid_message_preservation
                (pre_loaded_vlsm X P) (pre_loaded_vlsm Y Q) label_project state_project)
  : VLSM_projection (pre_loaded_vlsm X P) (pre_loaded_vlsm Y Q) label_project state_project.
Proof.
  specialize (basic_VLSM_projection_type_preloaded_with X Y P Q
    label_project state_project Htransition_None) as Htype.
  constructor; [done |].
  intros sX trX HtrX.
  split; [| by apply Hstate; apply HtrX].
  induction HtrX using finite_valid_trace_rev_ind.
  - by constructor; apply initial_state_is_valid, Hstate.
  - rewrite (@pre_VLSM_projection_finite_trace_project_app _
      (type (pre_loaded_vlsm X P)) (type Y) label_project state_project).
    apply (finite_valid_trace_from_app_iff (pre_loaded_vlsm Y Q)).
    split; [done |].
    simpl. unfold pre_VLSM_projection_transition_item_project.
    simpl.
    apply finite_valid_trace_last_pstate in IHHtrX.
    apply proj1 in Hx as Hpv.
    destruct Hx as [[_ [_ Hv]] Ht].
    rewrite <- (final_state_project _ _ _ _ Htype) in IHHtrX |- * by apply HtrX.
    destruct (label_project l) as [lY |] eqn: Hl.
    + apply (finite_valid_trace_singleton (pre_loaded_vlsm Y Q)).
      assert (Hiom : option_valid_message_prop (pre_loaded_vlsm Y Q) iom).
      { destruct iom as [im |]; [| by apply option_valid_message_None].
        by apply (Hmessage _ _ Hl) in Hpv.
      }
      apply (Hvalid _ _ Hl) in Hv.
      by apply (Htransition_Some _ _ Hl) in Ht.
    + by apply (finite_valid_trace_from_empty (pre_loaded_vlsm Y Q)).
Qed.
