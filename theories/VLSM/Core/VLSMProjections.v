From stdpp Require Import prelude.
From Coq Require Import FunctionalExtensionality.
From VLSM Require Import Core.VLSM.
From VLSM.Lib Require Import Preamble ListExtras StreamExtras StreamFilters.

(** * VLSM (partial) projections and inclusions

This section introduces several types VLSM projections: [VLSM_partial_projection],
[VLSM_projection], [VLSM_full_projection], as well as [VLSM_incl]usion and
[VLSM_eq]uality.
*)

Section VLSM_partial_projection.

(** ** VLSM partial projections

A generic notion of VLSM projection. We say that VLSM X partially projects to
VLSM Y (sharing the same messages) if there exists a partial map <<partial_trace_project>>
from traces over X (pairs of state and list of transitions from that state)
to traces over Y such that:

- [partial_trace_project_preserves_valid_trace]s, if the projection is defined.

- The projection operation is stable to adding valid prefixes (property
[partial_trace_project_extends_left]). More precisely, if the projection of a
trace (sX, tX) yields (sY, tY), then for any trace (s'X, preX) ending in sX
such that (s'X, preX ++ tX) is a valid trace, then there exists a
trace (s'Y, preY) ending in sY such that (s'X, preX ++ tX) projects
to (s'Y, preY ++ tY).

Proper examples of partial projections (which are not [VLSM_projection]s) are
the projections from the compositions of equivocators to the composition
of regular nodes guided by a specific start [MachineDescriptor] (see, e.g.,
[equivocators_no_equivocations_vlsm_X_vlsm_partial_projection]).
*)

Record VLSM_partial_projection_type
  {message : Type}
  (X Y : VLSM message)
  (partial_trace_project : vstate X * list (vtransition_item X) -> option (vstate Y * list (vtransition_item Y)))
  :=
  { partial_trace_project_extends_left :
      forall sX trX sY trY,
      partial_trace_project (sX, trX) = Some (sY, trY) ->
      forall s'X preX,
        finite_trace_last s'X preX = sX ->
        finite_valid_trace_from X s'X (preX ++ trX) ->
        exists s'Y preY,
          partial_trace_project (s'X, preX ++ trX) = Some (s'Y, preY ++ trY) /\
          finite_trace_last s'Y preY = sY
  }.

(** We define two kinds of partial projection: [VLSM_weak_partial_projection]
and [VLSM_partial_projection], the main difference between them being that the
"weak" one is not required to preserve initial states.

Although there are no current examples of proper [VLSM_weak_partial_projection]s,
their definition serves as a support base for [VLSM_weak_projection]s.
*)
Record VLSM_weak_partial_projection
  {message : Type}
  (X Y : VLSM message)
  (partial_trace_project : vstate X * list (vtransition_item X) -> option (vstate Y * list (vtransition_item Y)))
  :=
  { weak_partial_projection_type :> VLSM_partial_projection_type X Y partial_trace_project
  ; weak_partial_trace_project_preserves_valid_trace :
      forall sX trX sY trY,
        partial_trace_project (sX, trX) = Some (sY, trY) ->
        finite_valid_trace_from X sX trX -> finite_valid_trace_from Y sY trY
  }.

Record VLSM_partial_projection
  {message : Type}
  (X Y : VLSM message)
  (partial_trace_project : vstate X * list (vtransition_item X) -> option (vstate Y * list (vtransition_item Y)))
  :=
  { partial_projection_type :> VLSM_partial_projection_type X Y partial_trace_project
  ; partial_trace_project_preserves_valid_trace :
      forall sX trX sY trY,
        partial_trace_project (sX, trX) = Some (sY, trY) ->
        finite_valid_trace X sX trX -> finite_valid_trace Y sY trY
  }.

Section weak_partial_projection_properties.

Context
  {message : Type}
  {X Y : VLSM message}
  {trace_project : vstate X * list (vtransition_item X) -> option (vstate Y * list (vtransition_item Y))}
  (Hsimul : VLSM_weak_partial_projection X Y trace_project)
  .

Definition VLSM_weak_partial_projection_finite_valid_trace_from
  : forall sX trX sY trY,
    trace_project (sX, trX) = Some (sY, trY) ->
    finite_valid_trace_from X sX trX -> finite_valid_trace_from Y sY trY
  := weak_partial_trace_project_preserves_valid_trace _ _ _ Hsimul.

Lemma VLSM_weak_partial_projection_valid_state
  : forall sX sY trY,
    trace_project (sX, []) = Some (sY, trY) ->
    valid_state_prop X sX -> valid_state_prop Y sY.
Proof.
  intros sX sY trY Hpr HsX.
  apply valid_state_has_trace in HsX.
  destruct HsX as [isX [trX HtrX]].
  apply finite_valid_trace_init_to_last in HtrX as HsX.
  apply finite_valid_trace_init_to_forget_last, proj1 in HtrX.
  specialize (partial_trace_project_extends_left _ _ _ Hsimul _ _ _ _ Hpr _ _ HsX)
    as Hpr_extends_left.
  spec Hpr_extends_left.
  { rewrite app_nil_r. assumption. }
  destruct Hpr_extends_left as [isY [preY [Hpr_tr HsY]]].
  rewrite !app_nil_r in Hpr_tr.
  specialize (VLSM_weak_partial_projection_finite_valid_trace_from _ _ _ _ Hpr_tr HtrX)
    as Hinit_to.
  apply finite_valid_trace_from_app_iff, proj1, finite_valid_trace_last_pstate in Hinit_to.
  subst sY. assumption.
Qed.

Lemma VLSM_weak_partial_projection_input_valid_transition
  : forall sX itemX sY itemY,
    trace_project (sX, [itemX]) = Some (sY, [itemY]) ->
    input_valid_transition X (l itemX) (sX, input itemX) (destination itemX, output itemX) ->
    input_valid_transition Y (l itemY) (sY, input itemY) (destination itemY, output itemY).
Proof.
  intros sX itemX sY itemY Hpr HtX.
  apply finite_valid_trace_singleton in HtX.
  apply VLSM_weak_partial_projection_finite_valid_trace_from with (sY := sY) (trY := [itemY]) in HtX
  ; [|destruct itemX; assumption].
  inversion HtX. subst. assumption.
Qed.

Lemma VLSM_weak_partial_projection_input_valid
  : forall lX sX inX, input_valid X lX (sX, inX) ->
    forall sX' outX, vtransition X lX (sX, inX) = (sX', outX) ->
    forall sY itemY,
    trace_project (sX, [{| l := lX;  input := inX; destination := sX'; output := outX |}])
      = Some (sY, [itemY]) ->
    input_valid Y (l itemY) (sY, input itemY).
Proof.
  intros lX sX inX HvX sX' outX HtX sY itemY Hpr.
  eapply proj1, VLSM_weak_partial_projection_input_valid_transition
  ; [eassumption|].
  split; assumption.
Qed.

End weak_partial_projection_properties.

Section partial_projection_properties.

Context
  {message : Type}
  {X Y : VLSM message}
  {trace_project : vstate X * list (vtransition_item X) -> option (vstate Y * list (vtransition_item Y))}
  (Hsimul : VLSM_partial_projection X Y trace_project)
  .

Definition VLSM_partial_projection_finite_valid_trace
  : forall sX trX sY trY,
    trace_project (sX, trX) = Some (sY, trY) ->
    finite_valid_trace X sX trX -> finite_valid_trace Y sY trY
  := partial_trace_project_preserves_valid_trace _ _ _ Hsimul.

Lemma VLSM_partial_projection_finite_valid_trace_from
  : forall sX trX sY trY,
    trace_project (sX, trX) = Some (sY, trY) ->
    finite_valid_trace_from X sX trX -> finite_valid_trace_from Y sY trY.
Proof.
  intros sX trX sY trY Hpr_tr HtrX.
  apply (finite_valid_trace_from_complete_left X) in HtrX
    as [isX [preX [Htr'X HsX]]].
  specialize (partial_trace_project_extends_left _ _ _ Hsimul _ _ _ _ Hpr_tr _ _ HsX)
    as Hpr_extends_left.
  spec Hpr_extends_left.
  { apply proj1 in Htr'X. assumption. }
  destruct Hpr_extends_left as [isY [preY [Hpr_tr' HsY]]].
  specialize (VLSM_partial_projection_finite_valid_trace _ _ _ _ Hpr_tr' Htr'X)
    as Hinit_to.
  apply proj1, finite_valid_trace_from_app_iff, proj2 in Hinit_to.
  subst sY. assumption.
Qed.

Lemma VLSM_partial_projection_initial_state
  : forall sX sY trY,
    trace_project (sX, []) = Some (sY, trY) ->
    vinitial_state_prop X sX -> vinitial_state_prop Y sY.
Proof.
  intros sX sY trY Hpr HsX.
  assert (HtrX : finite_valid_trace X sX []).
  { split; [|assumption].  constructor. apply initial_state_is_valid. assumption. }
  apply (VLSM_partial_projection_finite_valid_trace _ _ _ _ Hpr HtrX).
Qed.

Definition VLSM_partial_projection_weaken : VLSM_weak_partial_projection X Y trace_project :=
  {| weak_partial_projection_type := partial_projection_type _ _ _ Hsimul
  ;  weak_partial_trace_project_preserves_valid_trace := VLSM_partial_projection_finite_valid_trace_from
  |}.

Definition VLSM_partial_projection_valid_state
  : forall sX sY trY,
    trace_project (sX, []) = Some (sY, trY) ->
    valid_state_prop X sX -> valid_state_prop Y sY
  := VLSM_weak_partial_projection_valid_state VLSM_partial_projection_weaken.

Definition VLSM_partial_projection_input_valid_transition
  : forall sX itemX sY itemY,
    trace_project (sX, [itemX]) = Some (sY, [itemY]) ->
    input_valid_transition X (l itemX) (sX, input itemX) (destination itemX, output itemX) ->
    input_valid_transition Y (l itemY) (sY, input itemY) (destination itemY, output itemY)
  := VLSM_weak_partial_projection_input_valid_transition VLSM_partial_projection_weaken.

Definition VLSM_partial_projection_input_valid
  : forall lX sX inX, input_valid X lX (sX, inX) ->
    forall sX' outX, vtransition X lX (sX, inX) = (sX', outX) ->
    forall sY itemY,
    trace_project (sX, [{| l := lX;  input := inX; destination := sX'; output := outX |}])
      = Some (sY, [itemY]) ->
    input_valid Y (l itemY) (sY, input itemY)
  := VLSM_weak_partial_projection_input_valid VLSM_partial_projection_weaken.

End partial_projection_properties.

End VLSM_partial_projection.

Section VLSM_projection.

(** ** VLSM (total) projections

A VLSM projection guaranteeing the existence of projection for all states and
traces. We say that VLSM X projects to VLSM Y (sharing the same messages) if
there exists maps <<state_project>> taking X-states to Y-states,
and <<trace_project>>, taking list of transitions from X to Y, such that:

- state and [trace_project_preserves_valid_trace]s.

- [trace_project_app]: trace projection commutes with concatenation of traces

- [final_state_project]: state projection commutes with [finite_trace_last]

Proper examples of total projections (which are not [VLSM_full_projection]s)
are projections in which some of transitions might be dropped, such as
the projection of a composition to one of the components ([component_projection])
or the projection of the compositions of equivocators to the composition of
regular nodes using the particular [MachineDescriptor] which select the
first (original) node instance for each equivocator (e.g.,
[equivocators_no_equivocations_vlsm_X_vlsm_projection]).
*)

Section pre_definitions.

Context
  {message : Type}
  (TX TY : VLSMType message)
  (label_project : @label _ TX -> option (@label _ TY))
  (state_project : @state _ TX -> @state _ TY)
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
    Some {| l := lY; input := input item; destination := state_project (destination item); output := output item |}
  end.

Lemma pre_VLSM_projection_transition_item_project_is_Some
  (item : @transition_item _ TX)
  : pre_VLSM_projection_in_projection item ->
    is_Some (pre_VLSM_projection_transition_item_project item).
Proof.
  intros [lY HlY].
  unfold pre_VLSM_projection_transition_item_project.
  rewrite HlY.
  eexists; reflexivity.
Qed.

Lemma pre_VLSM_projection_transition_item_project_is_Some_rev
  (item : @transition_item _ TX)
  : is_Some (pre_VLSM_projection_transition_item_project item) ->
    pre_VLSM_projection_in_projection item.
Proof.
  intros [itemY HitemY].
  unfold pre_VLSM_projection_transition_item_project in HitemY.
  destruct (label_project (l item)) as [lY|] eqn:HlY; [|congruence].
  exists lY. assumption.
Qed.

Lemma pre_VLSM_projection_transition_item_project_infinitely_often
  (s : Streams.Stream (@transition_item _ TX))
  : InfinitelyOften pre_VLSM_projection_in_projection s ->
    InfinitelyOften (is_Some ∘ pre_VLSM_projection_transition_item_project) s.
Proof.
  apply InfinitelyOften_impl.
  intro item.
  apply pre_VLSM_projection_transition_item_project_is_Some.
Qed.

Lemma pre_VLSM_projection_transition_item_project_finitely_many
  (s : Streams.Stream (@transition_item _ TX))
  : FinitelyManyBound pre_VLSM_projection_in_projection s ->
    FinitelyManyBound (is_Some ∘ pre_VLSM_projection_transition_item_project ) s.
Proof.
  apply FinitelyManyBound_impl_rev.
  intro item.
  apply pre_VLSM_projection_transition_item_project_is_Some_rev.
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

Definition pre_VLSM_projection_finite_trace_project_in_iff
  : forall trX itemY, In itemY (pre_VLSM_projection_finite_trace_project trX) <->
    exists itemX, In itemX trX /\ pre_VLSM_projection_transition_item_project itemX = Some itemY
  := in_map_option _.

Definition pre_VLSM_projection_finite_trace_project_in
  : forall itemX itemY, pre_VLSM_projection_transition_item_project itemX = Some itemY ->
    forall trX, In itemX trX -> In itemY (pre_VLSM_projection_finite_trace_project trX)
  := in_map_option_rev _.

End pre_definitions.

Record VLSM_projection_type
  {message : Type}
  (X : VLSM message)
  (TY : VLSMType message)
  (label_project : vlabel X -> option (@label _ TY))
  (state_project : vstate X -> @state _ TY)
  (trace_project := pre_VLSM_projection_finite_trace_project (type X) TY label_project state_project)
  :=
  { final_state_project :
      forall sX trX,
        finite_valid_trace_from X sX trX ->
        state_project (finite_trace_last sX trX) = finite_trace_last (state_project sX) (trace_project trX)
  }.

Section projection_type_properties.

Definition VLSM_partial_trace_project_from_projection
  {message : Type}
  {X : VLSM message}
  {TY : VLSMType message}
  (label_project : vlabel X -> option (@label _ TY))
  (state_project : vstate X -> @state _ TY)
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

(** Any [VLSM_projection_type] determines a [VLSM_partial_projection_type], allowing us
to lift to VLSM projection the generic results proved about VLSM partial projections.
*)
Lemma VLSM_partial_projection_type_from_projection
  : VLSM_partial_projection_type X Y (VLSM_partial_trace_project_from_projection label_project state_project).
Proof.
  split; intros; inversion H; subst; clear H.
  exists (state_project s'X), (trace_project preX).  split.
  + simpl. f_equal. f_equal. apply pre_VLSM_projection_finite_trace_project_app.
  + symmetry. apply (final_state_project _ _ _ _ Hsimul).
    apply (finite_valid_trace_from_app_iff  X) in H1.
    apply H1.
Qed.

End projection_type_properties.

Section projection_transition_consistency_None.

Context
  {message : Type}
  (X : VLSM message)
  (TY : VLSMType message)
  (label_project : vlabel X -> option (@label _ TY))
  (state_project : vstate X -> @state _ TY)
  (trace_project := pre_VLSM_projection_finite_trace_project _ _ label_project state_project)
  .

(** When a label cannot be projected, and thus the transition will not be
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
  apply (Hstrong lX Hl _ _ _ _ (proj2 Ht)).
Qed.

End projection_transition_consistency_None.


Section VLSM_projection_definitions.

Context
  {message : Type}
  (X Y : VLSM message)
  (label_project : vlabel X -> option (vlabel Y))
  (state_project : vstate X -> vstate Y)
  (trace_project := pre_VLSM_projection_finite_trace_project _ _ label_project state_project)
  .

(** Similarly to the [VLSM_partial_projection] case we distinguish two types of
projections: [VLSM_weak_projection] and [VLSM_projection], distinguished by the
fact that the weak projections are not required to preserve initial states.

Although we don't have proper examples of [VLSM_weak_projection]s, they are a
support base for [VLSM_weak_full_projection]s for which we have proper examples.
*)
Record VLSM_weak_projection :=
  { weak_projection_type :> VLSM_projection_type X (type Y) label_project state_project
  ; weak_trace_project_preserves_valid_trace :
      forall sX trX,
        finite_valid_trace_from X sX trX -> finite_valid_trace_from Y (state_project sX) (trace_project trX)
  }.

Record VLSM_projection :=
  { projection_type :> VLSM_projection_type X (type Y) label_project state_project
  ; trace_project_preserves_valid_trace :
      forall sX trX,
        finite_valid_trace X sX trX -> finite_valid_trace Y (state_project sX) (trace_project trX)
  }.

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
  apply (Hstrong lX lY Hl). apply Hpv.
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
  apply (Hstrong lX lY Hl). apply Ht.
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
  intros Hstrong lX lY Hl  s m [_ [Hm _]] HsY. apply Hstrong in Hm.
  assumption.
Qed.

End VLSM_projection_definitions.

Section weak_projection_properties.

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
    state_project (finite_trace_last sX trX) = finite_trace_last (state_project sX) (VLSM_weak_projection_trace_project Hsimul trX)
  := final_state_project _ _ _ _ Hsimul.

Definition VLSM_weak_projection_finite_valid_trace_from
  : forall sX trX,
    finite_valid_trace_from X sX trX -> finite_valid_trace_from Y (state_project sX) (VLSM_weak_projection_trace_project Hsimul trX)
  := weak_trace_project_preserves_valid_trace _ _ _ _ Hsimul.

Lemma VLSM_weak_projection_infinite_valid_trace_from
  : forall sX trX (Hinf : InfinitelyOften (VLSM_weak_projection_in Hsimul) trX),
    infinite_valid_trace_from X sX trX ->
    infinite_valid_trace_from Y (state_project sX) (VLSM_weak_projection_infinite_trace_project Hsimul trX Hinf).
Proof.
  intros sX trX Hinf HtrX.
  apply infinite_valid_trace_from_prefix_rev.
  intros n.

  specialize
    (stream_map_option_prefix_ex (pre_VLSM_projection_transition_item_project _ _ label_project state_project) trX
    (pre_VLSM_projection_transition_item_project_infinitely_often _ _ label_project state_project trX Hinf)
    n)
    as [m Hrew].
  unfold VLSM_weak_projection_infinite_trace_project, pre_VLSM_projection_infinite_trace_project.
  replace (stream_prefix _ _) with (VLSM_weak_projection_trace_project Hsimul (stream_prefix trX m)).
  apply VLSM_weak_projection_finite_valid_trace_from.

  apply infinite_valid_trace_from_prefix with (n0 := m) in HtrX.
  assumption.
Qed.

Lemma VLSM_weak_projection_infinite_finite_valid_trace_from
  : forall sX trX (Hfin : FinitelyManyBound (VLSM_weak_projection_in Hsimul) trX),
    infinite_valid_trace_from X sX trX ->
    finite_valid_trace_from Y (state_project sX) (VLSM_weak_projection_infinite_finite_trace_project Hsimul trX Hfin).
Proof.
  intros sX trX Hfin HtrX.
  apply VLSM_weak_projection_finite_valid_trace_from.
  apply infinite_valid_trace_from_prefix with (n := `Hfin) in HtrX.
  assumption.
Qed.

(** Any [VLSM_projection] determines a [VLSM_partial_projection], allowing us
to lift to VLSM projection the generic results proved about VLSM partial projections.
*)
Lemma VLSM_weak_partial_projection_from_projection
  : VLSM_weak_partial_projection X Y (VLSM_partial_trace_project_from_projection label_project state_project).
Proof.
  split.
  - apply VLSM_partial_projection_type_from_projection. apply Hsimul.
  - simpl. intros sX trX sY trY Heq.
    inversion Heq.
    apply VLSM_weak_projection_finite_valid_trace_from.
Qed.

Lemma VLSM_weak_projection_valid_state
  : forall sX,
    valid_state_prop X sX -> valid_state_prop Y (state_project sX).
Proof.
  specialize VLSM_weak_partial_projection_from_projection as Hpart_simul.
  specialize (VLSM_weak_partial_projection_valid_state Hpart_simul) as Hps.
  intro sX. eapply Hps; reflexivity.
Qed.

Lemma VLSM_weak_projection_input_valid_transition
  : forall lX lY, label_project lX = Some lY ->
    forall s im s' om,
    input_valid_transition X lX (s, im) (s', om ) ->
    input_valid_transition Y lY (state_project s, im) (state_project s', om).
Proof.
  specialize VLSM_weak_partial_projection_from_projection as Hpart_simul.
  specialize (VLSM_weak_partial_projection_input_valid_transition Hpart_simul) as Hivt.
  intros.
  apply
    (Hivt s {| l := lX; input := im; destination := s'; output := om|}
      (state_project s) {| l := lY; input := im; destination := state_project s'; output := om|})
  ; [|assumption].
  simpl. unfold pre_VLSM_projection_transition_item_project.
  simpl. rewrite H. reflexivity.
Qed.

Lemma VLSM_weak_projection_input_valid
  : forall lX lY, label_project lX = Some lY ->
    forall s im, input_valid X lX (s, im) -> input_valid Y lY (state_project s, im).
Proof.
  intros lX lY HlX_pr s im Hv.
  destruct (vtransition X lX (s, im)) as (s', om') eqn:Ht.
  eapply input_valid_transition_valid.
  eapply VLSM_weak_projection_input_valid_transition; [eassumption|].
  split; eassumption.
Qed.

Lemma VLSM_weak_projection_finite_valid_trace_from_to
  : forall sX s'X trX,
    finite_valid_trace_from_to X sX s'X trX -> finite_valid_trace_from_to Y (state_project sX) (state_project s'X) (VLSM_weak_projection_trace_project Hsimul trX).
Proof.
  specialize VLSM_weak_partial_projection_from_projection as Hpart_simul.
  specialize (VLSM_weak_partial_projection_finite_valid_trace_from Hpart_simul) as Htr.
  intros sX s'X trX HtrX.
  apply valid_trace_get_last in HtrX as Hs'X.
  apply valid_trace_forget_last in HtrX. subst.
  rewrite (final_state_project _ _ _ _ Hsimul).
  - apply valid_trace_add_default_last. revert HtrX.
    apply Htr. reflexivity.
  - assumption.
Qed.

Lemma VLSM_weak_projection_in_futures
  : forall s1 s2,
    in_futures X s1 s2 -> in_futures Y (state_project s1) (state_project s2).
Proof.
  intros s1 s2 [tr Htr].
  exists (VLSM_weak_projection_trace_project Hsimul tr).
  revert Htr.
  apply VLSM_weak_projection_finite_valid_trace_from_to.
Qed.

End weak_projection_properties.

Section projection_properties.

Definition VLSM_projection_trace_project
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

Definition VLSM_projection_trace_project_app
  : forall l1 l2, VLSM_projection_trace_project Hsimul (l1 ++ l2) =
    VLSM_projection_trace_project Hsimul l1 ++ VLSM_projection_trace_project Hsimul l2
  := pre_VLSM_projection_finite_trace_project_app _ _ label_project state_project.

Definition VLSM_projection_trace_project_app_rev
  : forall l l1' l2', VLSM_projection_trace_project Hsimul l = l1' ++ l2' ->
    exists l1 l2, l = l1 ++ l2 /\
      VLSM_projection_trace_project Hsimul l1 = l1' /\
      VLSM_projection_trace_project Hsimul l2 = l2'
  := pre_VLSM_projection_finite_trace_project_app_rev _ _ label_project state_project.

Definition VLSM_projection_trace_project_in
  : forall itemX itemY, pre_VLSM_projection_transition_item_project _ _ label_project state_project itemX = Some itemY ->
    forall trX, In itemX trX -> In itemY (VLSM_projection_trace_project Hsimul trX)
  := pre_VLSM_projection_finite_trace_project_in _ _ label_project state_project.

Definition VLSM_projection_finite_trace_last
  : forall sX trX,
    finite_valid_trace_from X sX trX ->
    state_project (finite_trace_last sX trX) = finite_trace_last (state_project sX) (VLSM_projection_trace_project Hsimul trX)
  := final_state_project _ _ _ _ Hsimul.

Definition VLSM_projection_finite_valid_trace
  : forall sX trX,
    finite_valid_trace X sX trX -> finite_valid_trace Y (state_project sX) (VLSM_projection_trace_project Hsimul trX)
  := trace_project_preserves_valid_trace _ _ _ _ Hsimul.

(** Any [VLSM_projection] determines a [VLSM_partial_projection], allowing us
to lift to VLSM projection the generic results proved about VLSM partial projections.
*)
Lemma VLSM_partial_projection_from_projection
  : VLSM_partial_projection X Y (VLSM_partial_trace_project_from_projection label_project state_project).
Proof.
  split.
  - apply VLSM_partial_projection_type_from_projection. apply Hsimul.
  - simpl. intros sX trX sY trY Heq.
    inversion Heq.
    apply VLSM_projection_finite_valid_trace.
Qed.

Lemma VLSM_projection_finite_valid_trace_from
  : forall sX trX,
    finite_valid_trace_from X sX trX -> finite_valid_trace_from Y (state_project sX) (VLSM_projection_trace_project Hsimul trX).
Proof.
  specialize VLSM_partial_projection_from_projection as Hpart_simul.
  specialize (VLSM_partial_projection_finite_valid_trace_from Hpart_simul) as Hivt.
  intros sX trX.
  apply Hivt. simpl. reflexivity.
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
    input_valid_transition X lX (s, im) (s', om ) ->
    input_valid_transition Y lY (state_project s, im) (state_project s', om)
  := VLSM_weak_projection_input_valid_transition VLSM_projection_weaken.

Definition VLSM_projection_input_valid
  : forall lX lY, label_project lX = Some lY ->
    forall s im,
    input_valid X lX (s, im) -> input_valid Y lY (state_project s, im)
  := VLSM_weak_projection_input_valid VLSM_projection_weaken.

Definition VLSM_projection_finite_valid_trace_from_to
  : forall sX s'X trX,
    finite_valid_trace_from_to X sX s'X trX -> finite_valid_trace_from_to Y (state_project sX) (state_project s'X) (VLSM_projection_trace_project Hsimul trX)
  := VLSM_weak_projection_finite_valid_trace_from_to VLSM_projection_weaken.

Definition VLSM_projection_in_futures
  : forall s1 s2,
    in_futures X s1 s2 -> in_futures Y (state_project s1) (state_project s2)
  := VLSM_weak_projection_in_futures VLSM_projection_weaken.

Definition VLSM_projection_infinite_valid_trace_from
  : forall sX trX (Hinf : InfinitelyOften (VLSM_projection_in Hsimul) trX),
    infinite_valid_trace_from X sX trX ->
    infinite_valid_trace_from Y (state_project sX) (VLSM_projection_infinite_trace_project Hsimul trX Hinf)
    := VLSM_weak_projection_infinite_valid_trace_from VLSM_projection_weaken.

Definition VLSM_projection_infinite_finite_valid_trace_from
  : forall sX trX (Hfin : FinitelyManyBound (VLSM_projection_in Hsimul) trX),
    infinite_valid_trace_from X sX trX ->
    finite_valid_trace_from Y (state_project sX) (VLSM_projection_infinite_finite_trace_project Hsimul trX Hfin)
    := VLSM_weak_projection_infinite_finite_valid_trace_from VLSM_projection_weaken.

Lemma VLSM_projection_initial_state
  : forall sX, vinitial_state_prop X sX -> vinitial_state_prop Y (state_project sX).
Proof.
  specialize VLSM_partial_projection_from_projection as Hpart_simul.
  specialize (VLSM_partial_projection_initial_state Hpart_simul) as His.
  intro sX. eapply His; reflexivity.
Qed.

Lemma VLSM_projection_finite_valid_trace_init_to
  : forall sX s'X trX,
    finite_valid_trace_init_to X sX s'X trX -> finite_valid_trace_init_to Y (state_project sX) (state_project s'X) (VLSM_projection_trace_project Hsimul trX).
Proof.
  intros. destruct H as [H Hinit]. split.
  - revert H. apply VLSM_projection_finite_valid_trace_from_to.
  - revert Hinit. apply VLSM_projection_initial_state.
Qed.

Lemma VLSM_projection_infinite_valid_trace
  : forall sX trX (Hinf : InfinitelyOften (VLSM_projection_in Hsimul) trX),
    infinite_valid_trace X sX trX ->
    infinite_valid_trace Y (state_project sX) (VLSM_projection_infinite_trace_project Hsimul trX Hinf).
Proof.
  intros sX trX Hinf [HtrX HsX].
  split.
  - apply VLSM_projection_infinite_valid_trace_from. assumption.
  - apply VLSM_projection_initial_state. assumption.
Qed.

Lemma VLSM_projection_infinite_finite_valid_trace
  : forall sX trX (Hfin : FinitelyManyBound (VLSM_projection_in Hsimul) trX),
    infinite_valid_trace X sX trX ->
    finite_valid_trace Y (state_project sX) (VLSM_projection_infinite_finite_trace_project Hsimul trX Hfin).
Proof.
  intros sX trX Hfin [HtrX HsX].
  split.
  - apply VLSM_projection_infinite_finite_valid_trace_from. assumption.
  - apply VLSM_projection_initial_state. assumption.
Qed.

(** ** Projection Friendliness

A projection is friendly if all the valid traces of the projection are
projections of the valid traces of the source VLSM.
*)

Section projection_friendliness.

(** We axiomatize projection friendliness as the converse of
[VLSM_projection_finite_valid_trace] *)
Definition projection_friendly_prop
  := forall
    (sY : vstate Y)
    (trY : list (vtransition_item Y))
    (HtrY : finite_valid_trace Y sY trY),
    exists (sX : vstate X) (trX : list (vtransition_item X)),
      finite_valid_trace X sX trX
      /\ state_project sX = sY
      /\ VLSM_projection_trace_project Hsimul trX = trY.

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
  apply VLSM_projection_trace_project_app_rev in Htr_pr
    as [trX_s1 [trX_s2 [HeqtrX [Htr_s1_pr Htr_s2_pr]]]].
  subst.
  destruct Htr as [HtrX HisX].
  apply finite_valid_trace_from_app_iff in HtrX as HtrX12.
  destruct HtrX12 as [HtrX1 HtrX2].
  apply valid_trace_add_default_last in HtrX2.
  exists (finite_trace_last isX trX_s1).
  exists (finite_trace_last isX  (trX_s1 ++ trX_s2)).
  rewrite !VLSM_projection_finite_trace_last,
    VLSM_projection_trace_project_app.
  - repeat split.
    rewrite finite_trace_last_app.
    eexists; exact HtrX2.
  - assumption.
  - assumption.
Qed.

(** A consequence of the [projection_friendly_prop]erty is that the valid
traces of the projection are precisely the projections of all the valid traces
of the source VLSM.
*)
Lemma projection_friendly_trace_char
  (Hfriendly : projection_friendly_prop)
  : forall sY trY, finite_valid_trace Y sY trY <->
    exists (sX : vstate X) (trX : list (vtransition_item X)),
      finite_valid_trace X sX trX
      /\ state_project sX = sY
      /\ VLSM_projection_trace_project Hsimul trX = trY.
Proof.
  split; [apply Hfriendly|].
  intros [sX [trX [HtrX [<- <-]]]].
  apply VLSM_projection_finite_valid_trace.
  assumption.
Qed.

End projection_friendliness.

End projection_properties.

End VLSM_projection.

Section VLSM_full_projection.

(** ** VLSM full projections

A VLSM projection guaranteeing the existence of projection for all labels and
states, and the full correspondence between [transition_item]s.
We say that VLSM X fully projects to VLSM Y (sharing the same messages)
if there exists maps <<label_project>> taking X-labels to Y-labels
and <<state_project>> taking X-states to Y-states, such that the
[finite_valid_trace_prop]erty is preserved bu the trace
transformation induced by the label and state projection functions,
in which each X-[transition_item] is projected to an Y-[transition_item]
preserving the messages and transforming labels and states accordingly.

Besides [VLSM_incl]usions, which are a prototypical example of VLSM full
projections, we can also prove "lifting" relations between components and the
composition that they are part of as being full projections (see, e.g.,
[lift_to_composite_vlsm_full_projection] or [projection_friendliness_lift_to_composite_vlsm_full_projection]).
*)

Section pre_definitions.

Context
  {message : Type}
  (TX TY : VLSMType message)
  (label_project : @label _ TX -> @label _ TY)
  (state_project : @state _ TX -> @state _ TY)
  .

Definition pre_VLSM_full_projection_transition_item_project
  : @transition_item _ TX -> @transition_item _ TY
  :=
  fun item =>
  {| l := label_project (l item)
   ; input := input item
   ; destination := state_project (destination item)
   ; output := output item
  |}.

Definition pre_VLSM_full_projection_finite_trace_project
  : list (@transition_item _ TX) -> list (@transition_item _ TY)
  := map pre_VLSM_full_projection_transition_item_project.

Definition pre_VLSM_full_projection_infinite_trace_project
  : Streams.Stream (@transition_item _ TX) -> Streams.Stream (@transition_item _ TY)
  := Streams.map pre_VLSM_full_projection_transition_item_project.

Lemma pre_VLSM_full_projection_infinite_trace_project_infinitely_often
  : forall s, InfinitelyOften (is_Some ∘ (Some ∘ label_project ∘ l)) s.
Proof.
  cofix H. intros (a, s). constructor; simpl; [|apply H].
  apply Streams.Here. eexists; reflexivity.
Qed.

Lemma pre_VLSM_full_projection_infinite_trace_project_EqSt
  : forall s (Hinf := pre_VLSM_full_projection_infinite_trace_project_infinitely_often s),
  Streams.EqSt (pre_VLSM_full_projection_infinite_trace_project s) (pre_VLSM_projection_infinite_trace_project _ _ (Some ∘ label_project) state_project s Hinf).
Proof.
  intros.
  apply stream_map_option_EqSt.
Qed.

Lemma pre_VLSM_full_projection_finite_trace_last
  : forall sX trX,
    state_project (finite_trace_last sX trX) = finite_trace_last (state_project sX) (pre_VLSM_full_projection_finite_trace_project trX).
Proof.
  intros.
  destruct_list_last trX trX' lst HtrX
  ; [reflexivity|].
  setoid_rewrite map_app. simpl. rewrite !finite_trace_last_is_last.
  reflexivity.
Qed.

Lemma pre_VLSM_full_projection_finite_trace_last_output
  : forall trX,
    finite_trace_last_output trX = finite_trace_last_output (pre_VLSM_full_projection_finite_trace_project trX).
Proof.
  intros.
  destruct_list_last trX trX' lst HtrX
  ; [reflexivity|].
  setoid_rewrite map_app. simpl. rewrite !finite_trace_last_output_is_last.
  reflexivity.
Qed.

End pre_definitions.

Section pre_definitions_projection_relation.

Context
  {message : Type}
  (TX TY : VLSMType message)
  (label_project : @label _ TX -> @label _ TY)
  (state_project : @state _ TX -> @state _ TY)
  .

Section pre_definitions_projection_relation_right.

Context
  (TZ : VLSMType message)
  (label_projectYZ : @label _ TY -> option (@label _ TZ))
  (state_projectYZ : @state _ TY -> @state _ TZ)
  .

Lemma pre_definitions_projection_relation_right_item
  : pre_VLSM_projection_transition_item_project TX TZ (label_projectYZ ∘ label_project) (state_projectYZ ∘ state_project) =
  pre_VLSM_projection_transition_item_project TY TZ label_projectYZ state_projectYZ ∘
  pre_VLSM_full_projection_transition_item_project TX TY label_project state_project.
Proof.
  extensionality item.
  reflexivity.
Qed.

Lemma pre_definitions_projection_relation_right_trace
  : pre_VLSM_projection_finite_trace_project TX TZ (label_projectYZ ∘ label_project) (state_projectYZ ∘ state_project) =
  pre_VLSM_projection_finite_trace_project TY TZ label_projectYZ state_projectYZ ∘
  pre_VLSM_full_projection_finite_trace_project TX TY label_project state_project.
Proof.
  unfold pre_VLSM_projection_finite_trace_project at 1.
  rewrite pre_definitions_projection_relation_right_item.
  apply map_option_comp_r.
Qed.

End pre_definitions_projection_relation_right.

Section pre_definitions_projection_relation_left.

Context
  (TW : VLSMType message)
  (label_projectWX : @label _ TW -> option (@label _ TX))
  (state_projectWX : @state _ TW -> @state _ TX)
  .

Lemma pre_definitions_projection_relation_left_item
  : pre_VLSM_projection_transition_item_project TW TY (option_map label_project ∘ label_projectWX) (state_project ∘ state_projectWX) =
  option_map (pre_VLSM_full_projection_transition_item_project TX TY label_project state_project) ∘
  pre_VLSM_projection_transition_item_project TW TX label_projectWX state_projectWX.
Proof.
  extensionality item.
  destruct item.
  unfold pre_VLSM_projection_transition_item_project; cbn.
  destruct (label_projectWX l) as [lX|]; cbn; reflexivity.
Qed.

Lemma pre_definitions_projection_relation_left_trace
  : pre_VLSM_projection_finite_trace_project TW TY (option_map label_project ∘ label_projectWX) (state_project ∘ state_projectWX) =
  pre_VLSM_full_projection_finite_trace_project TX TY label_project state_project ∘
  pre_VLSM_projection_finite_trace_project TW TX label_projectWX state_projectWX.
Proof.
  unfold pre_VLSM_projection_finite_trace_project at 1.
  rewrite pre_definitions_projection_relation_left_item.
  apply map_option_comp_l.
Qed.

End pre_definitions_projection_relation_left.

End pre_definitions_projection_relation.

Section basic_definitions.

Context
  {message : Type}
  (X Y : VLSM message)
  (label_project : vlabel X -> vlabel Y)
  (state_project : vstate X -> vstate Y)
  .

(** Similarly to [VLSM_partial_projection]s and [VLSM_projection]s, we
distinguish two types of projections: [VLSM_weak_full_projection] and
[VLSM_full_projection], distinguished by the fact that the weak projections
are not required to preserve initial states.

Proper examples of [VLSM_weak_full_projection] are presented in Lemmas
[PreSubFree_PreFree_weak_full_projection] and
[EquivPreloadedBase_Fixed_weak_full_projection], which show that a trace over
a subset of nodes can be replayed on top of a valid state for the full
composition. Note that in this case, the initial state of the trace not
translated to an initial state but rather to a regular valid state.
*)
Record VLSM_weak_full_projection
  :=
  { weak_full_trace_project_preserves_valid_trace :
      forall sX trX,
        finite_valid_trace_from X sX trX -> finite_valid_trace_from Y (state_project sX) (pre_VLSM_full_projection_finite_trace_project _ _ label_project state_project trX)
  }.

Record VLSM_full_projection
  :=
  { full_trace_project_preserves_valid_trace :
      forall sX trX,
        finite_valid_trace X sX trX -> finite_valid_trace Y (state_project sX) (pre_VLSM_full_projection_finite_trace_project _ _ label_project state_project trX)
  }.

Definition weak_full_projection_valid_preservation : Prop :=
  forall (l : label) (s : state) (om : option message)
    (Hv : input_valid X l (s, om))
    (HsY : valid_state_prop Y (state_project s))
    (HomY : option_valid_message_prop Y om),
    vvalid Y (label_project l) ((state_project s), om).

Lemma weak_projection_valid_preservation_from_full
  : weak_full_projection_valid_preservation ->
    weak_projection_valid_preservation X Y (fun l => Some (label_project l)) state_project.
Proof.
  intros Hvalid lX lY Hl.
  inversion_clear Hl. apply Hvalid.
Qed.

Definition strong_full_projection_valid_preservation : Prop :=
  forall (l : label) (s : state) (om : option message),
    vvalid X l (s, om) -> vvalid Y (label_project l) ((state_project s), om).

Lemma strong_projection_valid_preservation_from_full
  : strong_full_projection_valid_preservation ->
    strong_projection_valid_preservation X Y (fun l => Some (label_project l)) state_project.
Proof.
  intros Hvalid lX lY Hl.
  inversion_clear Hl. apply Hvalid.
Qed.

Lemma strong_full_projection_valid_preservation_weaken
  : strong_full_projection_valid_preservation ->
    weak_full_projection_valid_preservation.
Proof.
  intros Hstrong l s om Hpv Hs Hom.
  apply Hstrong. apply Hpv.
Qed.

Definition weak_full_projection_transition_preservation : Prop :=
  forall l s om s' om',
    input_valid_transition X l (s, om) (s', om') ->
    vtransition Y (label_project l) (state_project s, om) = (state_project s', om').

Lemma weak_projection_transition_preservation_Some_from_full
  : weak_full_projection_transition_preservation ->
    weak_projection_transition_preservation_Some X Y (fun l => Some (label_project l)) state_project.
Proof.
  intros Htransition lX lY Hl.
  inversion_clear Hl. apply Htransition.
Qed.

Lemma weak_projection_transition_consistency_None_from_full
  : weak_projection_transition_consistency_None _ _ (fun l => Some (label_project l)) state_project.
Proof.
  congruence.
Qed.

Definition strong_full_projection_transition_preservation : Prop :=
  forall l s om s' om',
      vtransition X l (s, om) = (s', om') ->
      vtransition Y (label_project l) (state_project s, om) = (state_project s', om').

Lemma strong_projection_transition_preservation_Some_from_full
  : strong_full_projection_transition_preservation ->
    strong_projection_transition_preservation_Some X Y (fun l => Some (label_project l)) state_project.
Proof.
  intros Htransition lX lY Hl.
  inversion_clear Hl. apply Htransition.
Qed.

Lemma strong_projection_transition_consistency_None_from_full
  : strong_projection_transition_consistency_None _ _ (fun l => Some (label_project l)) state_project.
Proof.
  congruence.
Qed.

Lemma strong_full_projection_transition_preservation_weaken
  : strong_full_projection_transition_preservation ->
    weak_full_projection_transition_preservation.
Proof.
  intros Hstrong l s om s' om' Ht.
  apply Hstrong. apply Ht.
Qed.

Definition weak_full_projection_initial_state_preservation : Prop :=
  forall s : state,
    vinitial_state_prop X s -> valid_state_prop Y (state_project s).

Definition strong_full_projection_initial_state_preservation : Prop :=
  forall s : state,
    vinitial_state_prop X s -> vinitial_state_prop Y (state_project s).

Lemma strong_full_projection_initial_state_preservation_weaken
  : strong_full_projection_initial_state_preservation ->
    weak_full_projection_initial_state_preservation.
Proof.
  intros Hstrong s Hs. apply Hstrong in Hs.
  apply initial_state_is_valid. assumption.
Qed.

Definition weak_full_projection_initial_message_preservation : Prop :=
  forall (l : label) (s : state) (m : message)
    (Hv : input_valid X l (s, Some m))
    (HsY : valid_state_prop Y (state_project s))
    (HmX : vinitial_message_prop X m),
    valid_message_prop Y m.

Definition strong_full_projection_initial_message_preservation : Prop :=
  forall m : message,
    vinitial_message_prop X m -> vinitial_message_prop Y m.

Lemma strong_full_projection_initial_message_preservation_weaken
  : strong_full_projection_initial_message_preservation ->
    weak_full_projection_initial_message_preservation.
Proof.
  intros Hstrong l s m Hv HsY Him. apply Hstrong in Him.
  apply initial_message_is_valid. assumption.
Qed.

End basic_definitions.

Definition VLSM_full_projection_transition_item_project
  {message : Type}
  {X Y : VLSM message}
  {label_project : vlabel X -> vlabel Y}
  {state_project : vstate X -> vstate Y}
  (Hsimul : VLSM_full_projection X Y label_project state_project)
  := pre_VLSM_full_projection_transition_item_project _ _  label_project state_project
  .

Definition VLSM_full_projection_finite_trace_project
  {message : Type}
  {X Y : VLSM message}
  {label_project : vlabel X -> vlabel Y}
  {state_project : vstate X -> vstate Y}
  (Hsimul : VLSM_full_projection X Y label_project state_project)
  := pre_VLSM_full_projection_finite_trace_project _ _  label_project state_project.

Definition VLSM_full_projection_infinite_trace_project
  {message : Type}
  {X Y : VLSM message}
  {label_project : vlabel X -> vlabel Y}
  {state_project : vstate X -> vstate Y}
  (Hsimul : VLSM_full_projection X Y label_project state_project)
  := pre_VLSM_full_projection_infinite_trace_project _ _  label_project state_project.

Definition VLSM_weak_full_projection_finite_trace_project
  {message : Type}
  {X Y : VLSM message}
  {label_project : vlabel X -> vlabel Y}
  {state_project : vstate X -> vstate Y}
  (Hsimul : VLSM_weak_full_projection X Y label_project state_project)
  := pre_VLSM_full_projection_finite_trace_project _ _ label_project state_project.

Definition VLSM_weak_full_projection_infinite_trace_project
  {message : Type}
  {X Y : VLSM message}
  {label_project : vlabel X -> vlabel Y}
  {state_project : vstate X -> vstate Y}
  (Hsimul : VLSM_weak_full_projection X Y label_project state_project)
  := pre_VLSM_full_projection_infinite_trace_project _ _  label_project state_project.

Lemma VLSM_full_projection_projection_type
  {message : Type}
  (X Y : VLSM message)
  (label_project : vlabel X -> vlabel Y)
  (state_project : vstate X -> vstate Y)
  : VLSM_projection_type X (type Y) (fun l => Some (label_project l)) state_project.
Proof.
  split; intros.
  - destruct_list_last trX trX' lstX Heq; [reflexivity|].
    apply (pre_VLSM_full_projection_finite_trace_last _).
Qed.

Section weak_projection_properties.

Context
  {message : Type}
  {X Y : VLSM message}
  {label_project : vlabel X -> vlabel Y}
  {state_project : vstate X -> vstate Y}
  (Hsimul : VLSM_weak_full_projection X Y label_project state_project)
  .

Definition VLSM_weak_full_projection_finite_trace_last
  : forall sX trX,
    state_project (finite_trace_last sX trX) = finite_trace_last (state_project sX) (VLSM_weak_full_projection_finite_trace_project Hsimul trX)
  := pre_VLSM_full_projection_finite_trace_last _ _ label_project state_project.

Definition VLSM_weak_full_projection_finite_valid_trace_from
  : forall s tr,
    finite_valid_trace_from X s tr ->
    finite_valid_trace_from Y (state_project s) (VLSM_weak_full_projection_finite_trace_project Hsimul tr)
  :=
  (weak_full_trace_project_preserves_valid_trace _ _ _ _ Hsimul).

(** Any [VLSM_full_projection] determines a [VLSM_projection], allowing us
to lift to VLSM full projections the generic results proved about VLSM projections.
*)
Lemma VLSM_weak_full_projection_is_projection
  : VLSM_weak_projection X Y (fun l => Some (label_project l)) state_project.
Proof.
  split.
  - apply VLSM_full_projection_projection_type.
  - apply VLSM_weak_full_projection_finite_valid_trace_from.
Qed.

Definition VLSM_weak_full_projection_valid_state
  : forall (s : vstate X) (Hs : valid_state_prop X s),  valid_state_prop Y (state_project s)
  := VLSM_weak_projection_valid_state VLSM_weak_full_projection_is_projection.

Definition VLSM_weak_full_projection_finite_valid_trace_from_to
  : forall
    (s f : vstate X)
    (tr : list (vtransition_item X))
    (Htr : finite_valid_trace_from_to X s f tr),
    finite_valid_trace_from_to Y (state_project s) (state_project f) (VLSM_weak_full_projection_finite_trace_project Hsimul tr)
  := VLSM_weak_projection_finite_valid_trace_from_to VLSM_weak_full_projection_is_projection.

Definition VLSM_weak_full_projection_in_futures
  : forall (s1 s2 : vstate X),
    in_futures X s1 s2 -> in_futures Y (state_project s1) (state_project s2)
  := VLSM_weak_projection_in_futures VLSM_weak_full_projection_is_projection.

Lemma VLSM_weak_full_projection_input_valid_transition
  : forall l s im s' om,
  input_valid_transition X l (s,im) (s',om) ->
  input_valid_transition Y (label_project l) (state_project s,im) (state_project s',om).
Proof.
  intros.
  apply (VLSM_weak_projection_input_valid_transition VLSM_weak_full_projection_is_projection)
    with (lY := label_project l) in H
  ; [assumption|reflexivity].
Qed.

Lemma VLSM_weak_full_projection_input_valid l s im
  : input_valid X l (s,im) -> input_valid Y (label_project l) (state_project s,im).
Proof.
  intros.
  eapply (VLSM_weak_projection_input_valid VLSM_weak_full_projection_is_projection)
  ; [reflexivity|assumption].
Qed.

Lemma VLSM_weak_full_projection_infinite_valid_trace_from
  : forall sX trX,
    infinite_valid_trace_from X sX trX ->
    infinite_valid_trace_from Y (state_project sX) (VLSM_weak_full_projection_infinite_trace_project Hsimul trX).
Proof.
  intros.
  specialize (pre_VLSM_full_projection_infinite_trace_project_EqSt _ _ label_project state_project trX)
    as Heq.
  apply Streams.sym_EqSt in Heq.
  apply (infinite_valid_trace_from_EqSt Y _ _ _ Heq).
  apply (VLSM_weak_projection_infinite_valid_trace_from VLSM_weak_full_projection_is_projection sX trX).
  assumption.
Qed.

Lemma VLSM_weak_full_projection_can_produce
  (s : state)
  (om : option message)
  : option_can_produce X s om -> option_can_produce Y (state_project s) om.
Proof.
  intros [(s0, im) [l Ht]].
  apply VLSM_weak_full_projection_input_valid_transition in Ht.
  eexists. eexists. exact Ht.
Qed.

Lemma VLSM_weak_full_projection_can_emit
  (m : message)
  : can_emit X m -> can_emit Y m.
Proof.
  repeat rewrite can_emit_iff.
  intros [s Hsm]. exists (state_project s). revert Hsm.
  apply VLSM_weak_full_projection_can_produce.
Qed.

Lemma VLSM_weak_full_projection_valid_message
  (Hinitial_valid_message : strong_full_projection_initial_message_preservation X Y)
  (m : message)
  : valid_message_prop X m -> valid_message_prop Y m.
Proof.
  intros Hm.
  apply emitted_messages_are_valid_iff in Hm as [Hinit | Hemit].
  - apply Hinitial_valid_message in Hinit. apply initial_message_is_valid. assumption.
  - apply emitted_messages_are_valid. revert Hemit. apply VLSM_weak_full_projection_can_emit.
Qed.

End weak_projection_properties.

Section full_projection_properties.

Context
  {message : Type}
  {X Y : VLSM message}
  {label_project : vlabel X -> vlabel Y}
  {state_project : vstate X -> vstate Y}
  (Hsimul : VLSM_full_projection X Y label_project state_project)
  .

Definition VLSM_full_projection_finite_trace_last
  : forall sX trX,
    state_project (finite_trace_last sX trX) = finite_trace_last (state_project sX) (VLSM_full_projection_finite_trace_project Hsimul trX)
  := pre_VLSM_full_projection_finite_trace_last _ _ label_project state_project.

Definition VLSM_full_projection_finite_valid_trace
  : forall s tr,
    finite_valid_trace X s tr ->
    finite_valid_trace Y (state_project s) (VLSM_full_projection_finite_trace_project Hsimul tr)
  := full_trace_project_preserves_valid_trace _ _ _ _ Hsimul.

(** Any [VLSM_full_projection] determines a [VLSM_projection], allowing us
to lift to VLSM full projections the generic results proved about VLSM projections.
*)
Lemma VLSM_full_projection_is_projection
  : VLSM_projection X Y (fun l => Some (label_project l)) state_project.
Proof.
  split.
  - apply VLSM_full_projection_projection_type.
  - apply VLSM_full_projection_finite_valid_trace.
Qed.

Definition VLSM_full_projection_finite_valid_trace_from
  : forall
    (s : vstate X)
    (tr : list (vtransition_item X))
    (Htr : finite_valid_trace_from X s tr),
    finite_valid_trace_from Y (state_project s) (VLSM_full_projection_finite_trace_project Hsimul tr)
  := VLSM_projection_finite_valid_trace_from VLSM_full_projection_is_projection.

Definition VLSM_full_projection_finite_valid_trace_init_to
  : forall
    (s f : vstate X)
    (tr : list (vtransition_item X))
    (Htr : finite_valid_trace_init_to X s f tr),
    finite_valid_trace_init_to Y (state_project s) (state_project f) (VLSM_full_projection_finite_trace_project Hsimul tr)
  := VLSM_projection_finite_valid_trace_init_to VLSM_full_projection_is_projection.

Definition VLSM_full_projection_initial_state
  : forall (is : vstate X),
    vinitial_state_prop X is -> vinitial_state_prop Y (state_project is)
  := VLSM_projection_initial_state VLSM_full_projection_is_projection.

Lemma VLSM_full_projection_weaken
  : VLSM_weak_full_projection X Y label_project state_project.
Proof.
  constructor. apply VLSM_full_projection_finite_valid_trace_from.
Qed.

Definition VLSM_full_projection_valid_state
  : forall (s : vstate X) (Hs : valid_state_prop X s),  valid_state_prop Y (state_project s)
  := VLSM_weak_full_projection_valid_state VLSM_full_projection_weaken.

Definition VLSM_full_projection_finite_valid_trace_from_to
  : forall
    (s f : vstate X)
    (tr : list (vtransition_item X))
    (Htr : finite_valid_trace_from_to X s f tr),
    finite_valid_trace_from_to Y (state_project s) (state_project f) (VLSM_full_projection_finite_trace_project Hsimul tr)
  := VLSM_weak_full_projection_finite_valid_trace_from_to VLSM_full_projection_weaken.

Definition VLSM_full_projection_in_futures
  : forall (s1 s2 : vstate X),
    in_futures X s1 s2 -> in_futures Y (state_project s1) (state_project s2)
  := VLSM_weak_full_projection_in_futures VLSM_full_projection_weaken.

Definition VLSM_full_projection_input_valid_transition
  : forall l s im s' om,
  input_valid_transition X l (s,im) (s',om) ->
  input_valid_transition Y (label_project l) (state_project s,im) (state_project s',om)
  := VLSM_weak_full_projection_input_valid_transition VLSM_full_projection_weaken.

Definition VLSM_full_projection_input_valid
  : forall l s im,
  input_valid X l (s,im) ->
  input_valid Y (label_project l) (state_project s,im)
  := VLSM_weak_full_projection_input_valid VLSM_full_projection_weaken.

Definition VLSM_full_projection_can_produce
  : forall
    (s : state)
    (om : option message),
    option_can_produce X s om -> option_can_produce Y (state_project s) om
  := VLSM_weak_full_projection_can_produce VLSM_full_projection_weaken.

Definition VLSM_full_projection_can_emit
  : forall (m : message), can_emit X m -> can_emit Y m
  := VLSM_weak_full_projection_can_emit VLSM_full_projection_weaken.

Definition VLSM_full_projection_valid_message
  (Hinitial_valid_message : strong_full_projection_initial_message_preservation X Y)
  : forall (m : message),
    valid_message_prop X m -> valid_message_prop Y m
  := VLSM_weak_full_projection_valid_message VLSM_full_projection_weaken Hinitial_valid_message.

Definition VLSM_full_projection_trace_project (t : vTrace X) : vTrace Y :=
  match t with
  | Finite s tr => Finite (state_project s) (VLSM_full_projection_finite_trace_project Hsimul tr)
  | Infinite s tr => Infinite (state_project s) (VLSM_full_projection_infinite_trace_project Hsimul tr)
  end.

Definition VLSM_full_projection_infinite_valid_trace_from
  s ls
  : infinite_valid_trace_from X s ls ->
    infinite_valid_trace_from Y (state_project s) (VLSM_full_projection_infinite_trace_project Hsimul ls)
  := VLSM_weak_full_projection_infinite_valid_trace_from VLSM_full_projection_weaken s ls.

Lemma VLSM_full_projection_infinite_valid_trace
  s ls
  : infinite_valid_trace X s ls ->
    infinite_valid_trace Y (state_project s) (VLSM_full_projection_infinite_trace_project Hsimul ls).
Proof.
  intros [Htr His]. split.
  - revert Htr. apply VLSM_full_projection_infinite_valid_trace_from.
  - revert His. apply VLSM_full_projection_initial_state.
Qed.

Lemma VLSM_full_projection_valid_trace
  : forall t,
    valid_trace_prop X t ->
    valid_trace_prop Y (VLSM_full_projection_trace_project t).
Proof.
  intros [s tr | s tr]; simpl.
  - apply VLSM_full_projection_finite_valid_trace.
  - apply VLSM_full_projection_infinite_valid_trace.
Qed.

(**
  [VLSM_full_projection] almost implies inclusion of the [valid_state_message_prop] sets.
  Some additional hypotheses are required because [VLSM_full_projection] only
  refers to traces, and [valid_initial_state_message] means that
  [valid_state_message_prop] includes some pairs that do not appear in any
  transition.
 *)
Lemma VLSM_full_projection_valid_state_message
  (Hmessage : strong_full_projection_initial_message_preservation X Y)
  : forall s om, valid_state_message_prop X s om -> valid_state_message_prop Y (state_project s) om.
Proof.
  intros s om Hsom.
  apply option_can_produce_valid_iff.
  apply option_can_produce_valid_iff in Hsom as [Hgen | [His Him]].
  - left. revert Hgen. apply VLSM_full_projection_can_produce.
  - right. split.
    + revert His. apply VLSM_full_projection_initial_state.
    + destruct om as [m|]; [|exact I].
      apply Hmessage. assumption.
Qed.

End full_projection_properties.

End VLSM_full_projection.

(** ** VLSM Inclusion and Equality

We can also define VLSM _inclusion_  and _equality_ in terms of traces.
When both VLSMs have the same state and label types they also share the
same [Trace] type, and sets of traces can be compared without conversion.
- VLSM X is _included_ in VLSM Y if every [valid_trace] available to X
is also available to Y.
- VLSM X and VLSM Y are _equal_ if their [valid_trace]s are exactly the same.
*)

Section VLSM_equality.
  Context
    {message : Type}
    {vtype : VLSMType message}
    .

Definition VLSM_eq_part
  {SigX SigY: VLSMSign vtype}
  (MX : VLSMClass SigX) (MY : VLSMClass SigY)
  (X := mk_vlsm MX) (Y := mk_vlsm MY)
  :=
  forall t : Trace,
    valid_trace_prop X t <-> valid_trace_prop Y t .
Local Notation VLSM_eq X Y := (VLSM_eq_part (machine X) (machine Y)).

Definition VLSM_incl_part
  {SigX SigY: VLSMSign vtype}
  (MX : VLSMClass SigX) (MY : VLSMClass SigY)
  (X := mk_vlsm MX) (Y := mk_vlsm MY)
  :=
  forall t : Trace,
    valid_trace_prop X t -> valid_trace_prop Y t.
Local Notation VLSM_incl X Y := (VLSM_incl_part (machine X) (machine Y)).

Lemma VLSM_incl_refl
  {SigX : VLSMSign vtype}
  (MX : VLSMClass SigX)
  (X := mk_vlsm MX)
  : VLSM_incl X X.
Proof.
  firstorder.
Qed.

Lemma VLSM_incl_trans
  {SigX SigY SigZ: VLSMSign vtype}
  (MX : VLSMClass SigX) (MY : VLSMClass SigY) (MZ : VLSMClass SigZ)
  (X := mk_vlsm MX) (Y := mk_vlsm MY) (Z := mk_vlsm MZ)
  : VLSM_incl X Y -> VLSM_incl Y Z -> VLSM_incl X Z.
Proof.
  firstorder.
Qed.

(* begin hide *)

Lemma VLSM_eq_incl_l
  {SigX SigY: VLSMSign vtype}
  (MX : VLSMClass SigX) (MY : VLSMClass SigY)
  (X := mk_vlsm MX) (Y := mk_vlsm MY)
  : VLSM_eq X Y -> VLSM_incl X Y.
Proof.
  intro Heq.
  intros t Hxt.
  apply Heq.
  assumption.
Qed.

Lemma VLSM_eq_incl_r
  {SigX SigY: VLSMSign vtype}
  (MX : VLSMClass SigX) (MY : VLSMClass SigY)
  (X := mk_vlsm MX) (Y := mk_vlsm MY)
  : VLSM_eq X Y -> VLSM_incl Y X.
Proof.
  intro Heq.
  intros t Hyt.
  apply Heq.
  assumption.
Qed.

Lemma VLSM_eq_incl_iff
  {SigX SigY: VLSMSign vtype}
  (MX : VLSMClass SigX) (MY : VLSMClass SigY)
  (X := mk_vlsm MX) (Y := mk_vlsm MY)
  : VLSM_eq X Y <-> VLSM_incl X Y /\ VLSM_incl Y X.
Proof.
  split.
  - intro Heq.
    split.
    + apply VLSM_eq_incl_l; assumption.
    + apply VLSM_eq_incl_r; assumption.
  - intros [Hxy Hyx].
    intro t.
    split.
    + apply Hxy.
    + apply Hyx.
Qed.

Lemma VLSM_incl_finite_traces_characterization
  {SigX SigY: VLSMSign vtype}
  (MX : VLSMClass SigX) (MY : VLSMClass SigY)
  (X := mk_vlsm MX) (Y := mk_vlsm MY)
  : VLSM_incl X Y <->
    forall (s : vstate X)
    (tr : list (vtransition_item X)),
    finite_valid_trace X s tr -> finite_valid_trace Y s tr.
Proof.
  split; intros Hincl.
  - intros. specialize (Hincl (Finite s tr)). apply Hincl. assumption.
  - intros tr Htr.
    destruct tr as [is tr | is tr]; simpl in *.
    + revert Htr. apply Hincl.
    + destruct Htr as [HtrX HisX].
      assert (His_tr: finite_valid_trace X is []).
      { split; [|assumption]. constructor.
        apply initial_state_is_valid. assumption.
      }
      apply Hincl in His_tr.
      destruct His_tr as [_ HisY].
      split; [|assumption].
      apply infinite_valid_trace_from_prefix_rev.
      intros.
      apply infinite_valid_trace_from_prefix with (n0 := n) in HtrX.
      apply (Hincl _ _ (conj HtrX HisX)).
Qed.

(** A [VLSM_incl]usion is equivalent to a [VLSM_full_projection] in which both the
label and state projection functions are identities.
*)
Lemma VLSM_incl_full_projection_iff
  {SigX SigY: VLSMSign vtype}
  (MX : VLSMClass SigX) (MY : VLSMClass SigY)
  (X := mk_vlsm MX) (Y := mk_vlsm MY)
  : VLSM_incl X Y <-> VLSM_full_projection X Y id id.
Proof.
  assert (Hid : forall tr, tr = pre_VLSM_full_projection_finite_trace_project _ _ id id tr).
  { induction tr; [reflexivity|]. destruct a. simpl. f_equal. assumption. }
  split.
  - constructor; intros.
    apply (proj1 (VLSM_incl_finite_traces_characterization (machine X) (machine Y)) H) in H0.
    replace (pre_VLSM_full_projection_finite_trace_project _ _ _ _ trX) with trX; [assumption|].
    apply Hid.
  - intro Hproject. apply VLSM_incl_finite_traces_characterization.
    intros. apply (VLSM_full_projection_finite_valid_trace Hproject) in H.
    replace (VLSM_full_projection_finite_trace_project Hproject _) with tr in H; [assumption|].
    apply Hid.
Qed.

Definition VLSM_incl_is_full_projection
  {SigX SigY: VLSMSign vtype}
  {MX : VLSMClass SigX} {MY : VLSMClass SigY}
  (X := mk_vlsm MX) (Y := mk_vlsm MY)
  (Hincl : VLSM_incl X Y)
  : VLSM_full_projection X Y id id
  := proj1 (VLSM_incl_full_projection_iff MX MY) Hincl.

Lemma VLSM_incl_is_full_projection_finite_trace_project
  {SigX SigY: VLSMSign vtype}
  {MX : VLSMClass SigX} {MY : VLSMClass SigY}
  (X := mk_vlsm MX) (Y := mk_vlsm MY)
  (Hincl : VLSM_incl X Y)
  : forall tr,
    VLSM_full_projection_finite_trace_project (VLSM_incl_is_full_projection Hincl) tr = tr.
Proof.
  induction tr; [reflexivity|].
  simpl. f_equal; [|assumption].
  destruct a; reflexivity.
Qed.

End VLSM_equality.

Notation VLSM_eq X Y := (VLSM_eq_part (machine X) (machine Y)).
Notation VLSM_incl X Y := (VLSM_incl_part (machine X) (machine Y)).

Lemma VLSM_eq_refl
  {message : Type}
  {vtype : VLSMType message}
  {SigX : VLSMSign vtype}
  (MX : VLSMClass SigX)
  (X := mk_vlsm MX)
  : VLSM_eq X X.
Proof.
  firstorder.
Qed.

Lemma VLSM_eq_sym
  {message : Type}
  {vtype : VLSMType message}
  {SigX SigY: VLSMSign vtype}
  (MX : VLSMClass SigX) (MY : VLSMClass SigY)
  (X := mk_vlsm MX) (Y := mk_vlsm MY)
  : VLSM_eq X Y -> VLSM_eq Y X.
Proof.
  firstorder.
Qed.

Lemma VLSM_eq_trans
  {message : Type}
  {vtype : VLSMType message}
  {SigX SigY SigZ: VLSMSign vtype}
  (MX : VLSMClass SigX) (MY : VLSMClass SigY) (MZ : VLSMClass SigZ)
  (X := mk_vlsm MX) (Y := mk_vlsm MY) (Z := mk_vlsm MZ)
  : VLSM_eq X Y -> VLSM_eq Y Z -> VLSM_eq X Z.
Proof.
  firstorder.
Qed.

Section VLSM_incl_preservation.

Context
  {message : Type}
  {T : VLSMType message}
  {SX SY : VLSMSign T}
  (MX : VLSMClass SX)
  (MY : VLSMClass SY)
  (X := mk_vlsm MX)
  (Y := mk_vlsm MY)
  .

Definition weak_incl_valid_preservation : Prop :=
  weak_full_projection_valid_preservation X Y id id.

Definition strong_incl_valid_preservation : Prop :=
  strong_full_projection_valid_preservation X Y id id.

Definition weak_incl_transition_preservation : Prop :=
  weak_full_projection_transition_preservation X Y id id.

Definition strong_incl_transition_preservation : Prop :=
  strong_full_projection_transition_preservation X Y id id.

Definition strong_incl_initial_state_preservation : Prop :=
  strong_full_projection_initial_state_preservation X Y id.

Definition weak_incl_initial_message_preservation : Prop :=
  weak_full_projection_initial_message_preservation X Y id.

Definition strong_incl_initial_message_preservation : Prop :=
  strong_full_projection_initial_message_preservation X Y.

End VLSM_incl_preservation.

Section VLSM_incl_properties.

Context
  {message : Type} [vtype : VLSMType message] [SigX SigY : VLSMSign vtype]
  [MX : VLSMClass SigX] [MY : VLSMClass SigY]
  (Hincl : VLSM_incl_part MX MY)
  (X := mk_vlsm MX)
  (Y := mk_vlsm MY)
  .

(** VLSM inclusion specialized to finite trace. *)

Lemma VLSM_incl_finite_valid_trace
  (s : vstate X)
  (tr : list (vtransition_item X))
  (Htr : finite_valid_trace X s tr)
  : finite_valid_trace Y s tr.
Proof.
  apply (VLSM_full_projection_finite_valid_trace (VLSM_incl_is_full_projection Hincl))
    in Htr.
  rewrite (VLSM_incl_is_full_projection_finite_trace_project Hincl) in Htr.
  assumption.
Qed.

Lemma VLSM_incl_finite_valid_trace_init_to
  (s f : vstate X)
  (tr : list (vtransition_item X))
  (Htr : finite_valid_trace_init_to X s f tr)
  : finite_valid_trace_init_to Y s f tr.
Proof.
  apply (VLSM_full_projection_finite_valid_trace_init_to (VLSM_incl_is_full_projection Hincl))
    in Htr.
  rewrite (VLSM_incl_is_full_projection_finite_trace_project Hincl) in Htr.
  assumption.
Qed.

Lemma VLSM_incl_valid_state
  (s : vstate X)
  (Hs : valid_state_prop X s)
  : valid_state_prop Y s.
Proof.
  revert Hs. apply (VLSM_full_projection_valid_state (VLSM_incl_is_full_projection Hincl)).
Qed.

Lemma VLSM_incl_initial_state
  (is : vstate X)
  : vinitial_state_prop X is -> vinitial_state_prop Y is.
Proof.
  apply (VLSM_full_projection_initial_state (VLSM_incl_is_full_projection Hincl)).
Qed.

Lemma VLSM_incl_finite_valid_trace_from
  (s : vstate X)
  (tr : list (vtransition_item X))
  (Htr : finite_valid_trace_from X s tr)
  : finite_valid_trace_from Y s tr.
Proof.
  apply (VLSM_full_projection_finite_valid_trace_from (VLSM_incl_is_full_projection Hincl))
    in Htr.
  rewrite (VLSM_incl_is_full_projection_finite_trace_project Hincl) in Htr.
  assumption.
Qed.

Lemma VLSM_incl_finite_valid_trace_from_to
  (s f : vstate X)
  (tr : list (vtransition_item X))
  (Htr : finite_valid_trace_from_to X s f tr)
  : finite_valid_trace_from_to Y s f tr.
Proof.
  apply (VLSM_full_projection_finite_valid_trace_from_to (VLSM_incl_is_full_projection Hincl))
    in Htr.
  rewrite (VLSM_incl_is_full_projection_finite_trace_project Hincl) in Htr.
  assumption.
Qed.

Lemma VLSM_incl_in_futures
  (s1 s2 : vstate X)
  : in_futures X s1 s2 -> in_futures Y s1 s2.
Proof.
  apply (VLSM_full_projection_in_futures (VLSM_incl_is_full_projection Hincl)).
Qed.

Lemma VLSM_incl_input_valid_transition
  : forall l s im s' om,
  input_valid_transition X l (s,im) (s',om) ->
  input_valid_transition Y l (s,im) (s',om).
Proof.
  apply
    (VLSM_full_projection_input_valid_transition (VLSM_incl_is_full_projection Hincl)).
Qed.

Lemma VLSM_incl_input_valid
  : forall l s im,
  input_valid X l (s,im) ->
  input_valid Y l (s,im).
Proof.
  apply
    (VLSM_full_projection_input_valid (VLSM_incl_is_full_projection Hincl)).
Qed.

(**
  [VLSM_incl] almost implies inclusion of the [valid_state_message_prop] sets.
  Some additional hypotheses are required because [VLSM_incl] only
  refers to traces, and [valid_initial_state_message] means that
  [valid_state_message_prop] includes some pairs that do not appear in any
  transition.
 *)
Lemma VLSM_incl_valid_state_message
  (Hmessage : strong_incl_initial_message_preservation MX MY)
  : forall s om, valid_state_message_prop X s om -> valid_state_message_prop Y s om.
Proof.
  intros s om.
  apply (VLSM_full_projection_valid_state_message (VLSM_incl_is_full_projection Hincl)).
  assumption.
Qed.

Lemma VLSM_incl_can_produce
  (s : state)
  (om : option message)
  : option_can_produce X s om -> option_can_produce Y s om.
Proof.
  apply (VLSM_full_projection_can_produce (VLSM_incl_is_full_projection Hincl)).
Qed.

Lemma VLSM_incl_can_emit
  (m : message)
  : can_emit X m -> can_emit Y m.
Proof.
  apply (VLSM_full_projection_can_emit (VLSM_incl_is_full_projection Hincl)).
Qed.

Definition VLSM_incl_valid_message
  (Hinitial_valid_message : strong_incl_initial_message_preservation MX MY)
  : forall (m : message),
    valid_message_prop X m -> valid_message_prop Y m.
Proof.
  intros m [s Hm].
  exists s. revert Hm. apply VLSM_incl_valid_state_message.
  assumption.
Qed.

Lemma VLSM_incl_infinite_valid_trace_from
  s ls
  : infinite_valid_trace_from X s ls ->
    infinite_valid_trace_from Y s ls.
Proof.
  intros Hls.
  apply (VLSM_full_projection_infinite_valid_trace_from (VLSM_incl_is_full_projection Hincl)) in Hls.
  revert Hls.
  apply infinite_valid_trace_from_EqSt.
  apply Streams.ntheq_eqst.
  unfold VLSM_full_projection_infinite_trace_project, pre_VLSM_full_projection_infinite_trace_project.
  intro n. rewrite Streams.Str_nth_map.
  destruct (Streams.Str_nth _ _). reflexivity.
Qed.

Lemma VLSM_incl_infinite_valid_trace
  s ls
  : infinite_valid_trace X s ls -> infinite_valid_trace Y s ls.
Proof.
  intros [Htr His]. split.
  - revert Htr. apply VLSM_incl_infinite_valid_trace_from.
  - revert His. apply VLSM_incl_initial_state.
Qed.

Lemma VLSM_incl_valid_trace
  : forall t, valid_trace_prop X t -> valid_trace_prop Y t.
Proof.
  intros [s tr | s tr]; simpl.
  - apply VLSM_incl_finite_valid_trace.
  - apply VLSM_incl_infinite_valid_trace.
Qed.

End VLSM_incl_properties.

Lemma vlsm_incl_pre_loaded_with_all_messages_vlsm
  {message : Type}
  (X : VLSM message)
  : VLSM_incl X (pre_loaded_with_all_messages_vlsm X).
Proof.
  apply VLSM_incl_finite_traces_characterization.
  intros. split; [|apply H].
  apply preloaded_weaken_valid_trace_from. destruct X as (T, (S, M)). apply H.
Qed.

Section VLSM_eq_properties.

Context
  {message : Type} [vtype : VLSMType message] [SigX SigY : VLSMSign vtype]
  [MX : VLSMClass SigX] [MY : VLSMClass SigY]
  (Hincl : VLSM_eq_part MX MY)
  (X := mk_vlsm MX)
  (Y := mk_vlsm MY)
  .

(** VLSM equality specialized to finite trace. *)

Lemma VLSM_eq_proj1 : VLSM_incl X Y.
Proof.
  apply VLSM_eq_incl_iff in Hincl.
  apply Hincl.
Qed.

Lemma VLSM_eq_proj2 : VLSM_incl Y X.
Proof.
  apply VLSM_eq_incl_iff in Hincl.
  apply Hincl.
Qed.

Lemma VLSM_eq_finite_valid_trace
  (s : vstate X)
  (tr : list (vtransition_item X))
  : finite_valid_trace X s tr <-> finite_valid_trace Y s tr.
Proof.
  split.
  - apply (VLSM_incl_finite_valid_trace VLSM_eq_proj1).
  - apply (VLSM_incl_finite_valid_trace VLSM_eq_proj2).
Qed.

Lemma VLSM_eq_finite_valid_trace_init_to
  (s f : vstate X)
  (tr : list (vtransition_item X))
  : finite_valid_trace_init_to X s f tr <->
    finite_valid_trace_init_to Y s f tr.
Proof.
  split.
  - apply (VLSM_incl_finite_valid_trace_init_to VLSM_eq_proj1).
  - apply (VLSM_incl_finite_valid_trace_init_to VLSM_eq_proj2).
Qed.

Lemma VLSM_eq_valid_state
  (s : vstate X)
  : valid_state_prop X s <-> valid_state_prop Y s.
Proof.
  split.
  - apply (VLSM_incl_valid_state VLSM_eq_proj1).
  - apply (VLSM_incl_valid_state VLSM_eq_proj2).
Qed.

Lemma VLSM_eq_initial_state
  (is : vstate X)
  : vinitial_state_prop X is <-> vinitial_state_prop Y is.
Proof.
  split.
  - apply (VLSM_incl_initial_state VLSM_eq_proj1).
  - apply (VLSM_incl_initial_state VLSM_eq_proj2).
Qed.

Lemma VLSM_eq_finite_valid_trace_from
  (s : vstate X)
  (tr : list (vtransition_item X))
  : finite_valid_trace_from X s tr <->
    finite_valid_trace_from Y s tr.
Proof.
  split.
  - apply (VLSM_incl_finite_valid_trace_from VLSM_eq_proj1).
  - apply (VLSM_incl_finite_valid_trace_from VLSM_eq_proj2).
Qed.

Lemma VLSM_eq_finite_valid_trace_from_to
  (s f : vstate X)
  (tr : list (vtransition_item X))
  : finite_valid_trace_from_to X s f tr <-> finite_valid_trace_from_to Y s f tr.
Proof.
  split.
  - apply (VLSM_incl_finite_valid_trace_from_to VLSM_eq_proj1).
  - apply (VLSM_incl_finite_valid_trace_from_to VLSM_eq_proj2).
Qed.

Lemma VLSM_eq_in_futures
  (s1 s2 : vstate X)
  : in_futures X s1 s2 <-> in_futures Y s1 s2.
Proof.
  split.
  - apply (VLSM_incl_in_futures VLSM_eq_proj1).
  - apply (VLSM_incl_in_futures VLSM_eq_proj2).
Qed.

Lemma VLSM_eq_input_valid_transition
  : forall l s im s' om,
  input_valid_transition X l (s,im) (s',om) <->
  input_valid_transition Y l (s,im) (s',om).
Proof.
  split.
  - apply (VLSM_incl_input_valid_transition VLSM_eq_proj1).
  - apply (VLSM_incl_input_valid_transition VLSM_eq_proj2).
Qed.

Lemma VLSM_eq_input_valid
  : forall l s im,
  input_valid X l (s,im) <-> input_valid Y l (s,im).
Proof.
  split.
  - apply (VLSM_incl_input_valid VLSM_eq_proj1).
  - apply (VLSM_incl_input_valid VLSM_eq_proj2).
Qed.

Lemma VLSM_eq_can_produce
  (s : state)
  (om : option message)
  : option_can_produce X s om <-> option_can_produce Y s om.
Proof.
  split.
  - apply (VLSM_incl_can_produce VLSM_eq_proj1).
  - apply (VLSM_incl_can_produce VLSM_eq_proj2).
Qed.

Lemma VLSM_eq_can_emit
  (m : message)
  : can_emit X m <-> can_emit Y m.
Proof.
  split.
  - apply (VLSM_incl_can_emit VLSM_eq_proj1).
  - apply (VLSM_incl_can_emit VLSM_eq_proj2).
Qed.

Lemma VLSM_eq_infinite_valid_trace_from
  s ls
  : infinite_valid_trace_from X s ls <->
    infinite_valid_trace_from Y s ls.
Proof.
  split.
  - apply (VLSM_incl_infinite_valid_trace_from VLSM_eq_proj1).
  - apply (VLSM_incl_infinite_valid_trace_from VLSM_eq_proj2).
Qed.

Lemma VLSM_eq_infinite_valid_trace
  s ls
  : infinite_valid_trace X s ls <-> infinite_valid_trace Y s ls.
Proof.
  split.
  - apply (VLSM_incl_infinite_valid_trace VLSM_eq_proj1).
  - apply (VLSM_incl_infinite_valid_trace VLSM_eq_proj2).
Qed.

Lemma VLSM_eq_valid_trace
  : forall t, valid_trace_prop X t <-> valid_trace_prop Y t.
Proof.
  split.
  - apply (VLSM_incl_valid_trace VLSM_eq_proj1).
  - apply (VLSM_incl_valid_trace VLSM_eq_proj2).
Qed.

End VLSM_eq_properties.

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

Section basic_VLSM_projection.

Section basic_VLSM_projection_type.

Context
  {message : Type}
  (X : VLSM message)
  (TY : VLSMType message)
  (label_project : vlabel X -> option (@label _ TY))
  (state_project : vstate X -> @state _ TY)
  (Htransition_None : weak_projection_transition_consistency_None X TY label_project state_project)
  .

Lemma basic_VLSM_projection_type
  : VLSM_projection_type X TY label_project state_project.
Proof.
  constructor.
  intros is tr Htr.
  induction Htr using finite_valid_trace_from_rev_ind
  ; [reflexivity|].
  rewrite (pre_VLSM_projection_finite_trace_project_app _ _ label_project state_project).
  rewrite finite_trace_last_is_last.
  rewrite finite_trace_last_app, <- IHHtr.
  clear IHHtr.
  simpl.
  unfold pre_VLSM_projection_transition_item_project.
  destruct (label_project _) as [lY|] eqn:Hl; [reflexivity|].
  apply (Htransition_None _ Hl) in Hx.
  rewrite Hx.
  reflexivity.
Qed.

End basic_VLSM_projection_type.

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

Section weak_projection.

Context
  (Hstate : weak_full_projection_initial_state_preservation X Y state_project)
  (Hmessage : weak_projection_valid_message_preservation X Y label_project state_project)
  .

Local Lemma basic_VLSM_projection_finite_valid_trace_init_to
  is s tr
  (Htr : finite_valid_trace_init_to X is s tr)
  : finite_valid_trace_from_to Y (state_project is) (state_project s) (pre_VLSM_projection_finite_trace_project _ _ label_project state_project tr).
Proof.
  induction Htr using finite_valid_trace_init_to_rev_strong_ind.
  - constructor. apply Hstate. assumption.
  - unfold pre_VLSM_projection_finite_trace_project.
    rewrite map_option_app.
    apply finite_valid_trace_from_to_app with (state_project s)
    ; [assumption|].
    simpl. unfold pre_VLSM_projection_transition_item_project.
    simpl.
    apply valid_trace_last_pstate in IHHtr1.
    destruct (label_project l) as [lY|] eqn:Hl.
    + apply finite_valid_trace_from_to_singleton.
      assert (Hiom : option_valid_message_prop Y iom).
      { destruct iom as [im|]; [|apply option_valid_message_None].
        apply (Hmessage _ _ Hl _ _ (proj1 Ht)).
        assumption.
      }
      specialize (Hvalid _ _ Hl _ _ (proj1 Ht) IHHtr1 Hiom).
      apply (Htransition_Some _ _ Hl) in Ht.
      repeat split; assumption.
    + apply (Htransition_None _ Hl) in Ht.
      rewrite Ht. constructor. assumption.
Qed.

Local Lemma basic_VLSM_projection_finite_valid_trace_from
  (s : state)
  (ls : list transition_item)
  (Hpxt : finite_valid_trace_from X s ls)
  : finite_valid_trace_from Y (state_project s) (pre_VLSM_projection_finite_trace_project _ _ label_project state_project ls).
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
    in Happ_pr by assumption.
  apply valid_trace_forget_last in Happ_pr.
  subst. assumption.
Qed.

(* end hide *)

Lemma basic_VLSM_weak_projection
  : VLSM_weak_projection X Y label_project state_project.
Proof.
  constructor.
  - assumption.
  - apply basic_VLSM_projection_finite_valid_trace_from.
Qed.

End weak_projection.

Lemma basic_VLSM_weak_projection_strengthen
  (Hweak : VLSM_weak_projection X Y label_project state_project)
  (Hstate : strong_full_projection_initial_state_preservation X Y state_project)
  : VLSM_projection X Y label_project state_project.
Proof.
  constructor; [apply Hweak|]. intros sX trX [HtrX HsX].
  split.
  - revert HtrX. apply (VLSM_weak_projection_finite_valid_trace_from Hweak).
  - revert HsX. apply Hstate.
Qed.

Lemma basic_VLSM_projection
  (Hstate : strong_full_projection_initial_state_preservation X Y state_project)
  (Hmessage : weak_projection_valid_message_preservation X Y label_project state_project)
  : VLSM_projection X Y label_project state_project.
Proof.
  apply basic_VLSM_weak_projection_strengthen; [|assumption].
  apply basic_VLSM_weak_projection; [|assumption].
  apply strong_full_projection_initial_state_preservation_weaken.
  assumption.
Qed.

End basic_VLSM_projection.

Lemma basic_VLSM_strong_projection
  {message : Type}
  (X Y : VLSM message)
  (label_project : vlabel X -> option (vlabel Y))
  (state_project : vstate X -> vstate Y)
  (Hvalid : strong_projection_valid_preservation X Y label_project state_project)
  (Htransition_Some : strong_projection_transition_preservation_Some X Y label_project state_project)
  (Htransition_None : strong_projection_transition_consistency_None _ _ label_project state_project)
  (Hstate : strong_full_projection_initial_state_preservation X Y state_project)
  (Hmessage : strong_projection_valid_message_preservation X Y)
  : VLSM_projection X Y label_project state_project.
Proof.
  apply basic_VLSM_projection.
  - apply strong_projection_valid_preservation_weaken. assumption.
  - apply strong_projection_transition_preservation_Some_weaken. assumption.
  - apply strong_projection_transition_consistency_None_weaken. assumption.
  - assumption.
  - apply strong_projection_valid_message_preservation_weaken. assumption.
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
  ; [reflexivity|].
  rewrite (@pre_VLSM_projection_finite_trace_project_app _ (type (pre_loaded_with_all_messages_vlsm X)) (type Y) label_project state_project).
  rewrite finite_trace_last_is_last.
  rewrite finite_trace_last_app, <- IHHtr.
  clear IHHtr.
  simpl.
  unfold pre_VLSM_projection_transition_item_project.
  destruct (label_project _) as [lY|] eqn:Hl; [reflexivity|].
  apply proj2, (Htransition_None _ Hl) in Hx.
  rewrite Hx.
  reflexivity.
Qed.

Lemma basic_VLSM_projection_preloaded
  {message : Type}
  (X Y : VLSM message)
  (label_project : vlabel X -> option (vlabel Y))
  (state_project : vstate X -> vstate Y)
  (Hvalid : strong_projection_valid_preservation X Y label_project state_project)
  (Htransition_Some : strong_projection_transition_preservation_Some X Y label_project state_project)
  (Htransition_None : strong_projection_transition_consistency_None _ _ label_project state_project)
  (Hstate : strong_full_projection_initial_state_preservation X Y state_project)
  : VLSM_projection (pre_loaded_with_all_messages_vlsm X) (pre_loaded_with_all_messages_vlsm Y) label_project state_project.
Proof.
  specialize (basic_VLSM_projection_type_preloaded X Y label_project state_project Htransition_None) as Htype.
  constructor; [assumption|].
  intros sX trX HtrX.
  split; [|apply Hstate; apply HtrX].
  induction HtrX using finite_valid_trace_rev_ind.
  - constructor. apply initial_state_is_valid.
    apply Hstate; assumption.
  - rewrite (@pre_VLSM_projection_finite_trace_project_app _ (type (pre_loaded_with_all_messages_vlsm X)) (type Y) label_project state_project).
    apply (finite_valid_trace_from_app_iff (pre_loaded_with_all_messages_vlsm Y)).
    split; [assumption|].
    simpl. unfold pre_VLSM_projection_transition_item_project.
    simpl.
    apply finite_valid_trace_last_pstate in IHHtrX.
    destruct Hx as [[_ [_ Hv]] Ht].
    rewrite <- (final_state_project _ _ _ _ Htype) in IHHtrX |- * by apply HtrX.
    destruct (label_project l) as [lY|] eqn:Hl.
    + apply (finite_valid_trace_singleton (pre_loaded_with_all_messages_vlsm Y)).
      assert (Hiom : option_valid_message_prop (pre_loaded_with_all_messages_vlsm Y) iom).
      { destruct iom as [im|]; [|apply option_valid_message_None].
        apply (any_message_is_valid_in_preloaded Y).
      }
      apply (Hvalid _ _ Hl) in Hv.
      apply (Htransition_Some _ _ Hl) in Ht.
      repeat split; assumption.
    + apply (finite_valid_trace_from_empty (pre_loaded_with_all_messages_vlsm Y)). assumption.
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
  ; [reflexivity|].
  rewrite (@pre_VLSM_projection_finite_trace_project_app _ (type (pre_loaded_vlsm X P)) (type Y) label_project state_project).
  rewrite finite_trace_last_is_last.
  rewrite finite_trace_last_app, <- IHHtr.
  clear IHHtr.
  simpl.
  unfold pre_VLSM_projection_transition_item_project.
  destruct (label_project _) as [lY|] eqn:Hl; [reflexivity|].
  apply proj2, (Htransition_None _ Hl) in Hx.
  rewrite Hx.
  reflexivity.
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
  (Hstate : strong_full_projection_initial_state_preservation X Y state_project)
  (Hmessage : weak_projection_valid_message_preservation (pre_loaded_vlsm X P) (pre_loaded_vlsm Y Q) label_project state_project)
  : VLSM_projection (pre_loaded_vlsm X P) (pre_loaded_vlsm Y Q) label_project state_project.
Proof.
  specialize (basic_VLSM_projection_type_preloaded_with X Y P Q label_project state_project Htransition_None) as Htype.
  constructor; [assumption|].
  intros sX trX HtrX.
  split; [|apply Hstate; apply HtrX].
  induction HtrX using finite_valid_trace_rev_ind.
  - constructor. apply initial_state_is_valid.
    apply Hstate; assumption.
  - rewrite (@pre_VLSM_projection_finite_trace_project_app _ (type (pre_loaded_vlsm X P)) (type Y) label_project state_project).
    apply (finite_valid_trace_from_app_iff (pre_loaded_vlsm Y Q)).
    split; [assumption|].
    simpl. unfold pre_VLSM_projection_transition_item_project.
    simpl.
    apply finite_valid_trace_last_pstate in IHHtrX.
    apply proj1 in Hx as Hpv.
    destruct Hx as [[_ [_ Hv]] Ht].
    rewrite <- (final_state_project _ _ _ _ Htype) in IHHtrX |- * by apply HtrX.
    destruct (label_project l) as [lY|] eqn:Hl.
    + apply (finite_valid_trace_singleton (pre_loaded_vlsm Y Q)).
      assert (Hiom : option_valid_message_prop (pre_loaded_vlsm Y Q) iom).
      { destruct iom as [im|]; [|apply option_valid_message_None].
        apply (Hmessage _ _ Hl) in Hpv; assumption.
      }
      apply (Hvalid _ _ Hl) in Hv.
      apply (Htransition_Some _ _ Hl) in Ht.
      repeat split; assumption.
    + apply (finite_valid_trace_from_empty (pre_loaded_vlsm Y Q)). assumption.
Qed.


(** It is natural to look for sufficient conditions for VLSM projections
which are easy to verify in a practical setting. One such result is the following.

For VLSM <<X>> to fully-project to a VLSM <<Y>>, the following set of conditions is sufficient:
- <<X>>'s [initial_state]s project to <<Y>>'s [initial state]s
- Every message <<m>> (including the empty one) which can be input to
  an [input_valid] transition in <<X>>, is a [valid_message] in <<Y>>
- <<X>>'s [input_valid] is included in <<Y>>'s [valid].
- For all [input_valid] inputs (in <<X>>), <<Y>>'s [transition] acts
like <<X>>'s [transition].
*)

Section basic_VLSM_full_projection.

Context
  {message : Type}
  (X Y : VLSM message)
  (label_project : vlabel X -> vlabel Y)
  (state_project : vstate X -> vstate Y)
  .

Context
  (Hvalid : weak_full_projection_valid_preservation X Y label_project state_project)
  (Htransition : weak_full_projection_transition_preservation X Y label_project state_project)
  .

Section weak_full_projection.

Context
  (Hstate : weak_full_projection_initial_state_preservation X Y state_project)
  (Hmessage : weak_full_projection_initial_message_preservation X Y state_project)
  .

Lemma weak_projection_valid_message_preservation_from_full
  : weak_projection_valid_message_preservation X Y (Some ∘ label_project) state_project.
Proof.
  intros lX lY Hl s m Hv HsY.
  apply proj2 in Hv as Hom.
  apply proj1 in Hom.
  apply emitted_messages_are_valid_iff in Hom.
  destruct Hom as [Him | Hemit].
  - apply (Hmessage _ _ _ Hv); assumption.
  - apply can_emit_has_trace in Hemit as [is [tr [item [Htr Hm]]]].
    destruct item. simpl in *. subst.
    apply valid_trace_add_default_last in Htr.
    rewrite finite_trace_last_is_last in Htr. simpl in Htr.
    remember (tr ++ _) as tr'.
    cut (option_valid_message_prop Y (Some m)); [exact id|].
    exists (state_project destination).
    clear Hv Hl lX lY.
    revert tr l input Heqtr'.
    generalize (Some m) as om.
    induction Htr using finite_valid_trace_init_to_rev_strong_ind
    ; intros; [destruct tr; simpl in *; congruence|].
    apply app_inj_tail in Heqtr' as [Heqtr Heqitem].
    subst tr0.
    inversion Heqitem. subst l0 input oom. clear Heqitem.
    assert (Hs : valid_state_prop Y (state_project s0)).
    { destruct_list_last tr s_tr' s_item Heqtr.
      - subst tr. destruct Htr1 as [Hs His].
        inversion Hs. subst.
        apply Hstate. assumption.
      - subst.
        apply valid_trace_get_last in Htr1 as Hs0.
        rewrite finite_trace_last_is_last in Hs0.
        destruct s_item. simpl in Hs0. subst destination.
        specialize (IHHtr1 _ _ _ _ eq_refl).
        eexists; exact IHHtr1.
    }
    destruct Hs as [_om Hs].
    assert (Hom : option_valid_message_prop Y iom).
    { destruct iom as [im|]; [|apply option_valid_message_None].
      unfold empty_initial_message_or_final_output in Heqiom.
      destruct_list_last iom_tr iom_tr' iom_item Heqiom_tr.
      - apply (Hmessage _ _ _ (proj1 Ht)); [|assumption].
        eexists; exact Hs.
      - subst.
        apply valid_trace_get_last in Htr2 as Hs0.
        rewrite finite_trace_last_is_last in Hs0.
        destruct iom_item. simpl in *. subst.
        specialize (IHHtr2 _ _ _ _ eq_refl).
        eexists; exact IHHtr2.
    }
    destruct Hom as [_s Hom].
    apply
      (valid_generated_state_message Y _ _ Hs _ _ Hom (label_project l)).
    + apply Hvalid; [apply Ht|exists _om|exists _s]; assumption.
    + apply Htransition. assumption.
Qed.

Lemma basic_VLSM_weak_full_projection : VLSM_weak_full_projection X Y label_project state_project.
Proof.
  specialize (basic_VLSM_weak_projection X Y (fun l => Some (label_project l)) state_project) as Hproj.
  spec Hproj; [apply weak_projection_valid_preservation_from_full; assumption|].
  spec Hproj; [apply weak_projection_transition_preservation_Some_from_full; assumption|].
  spec Hproj; [apply weak_projection_transition_consistency_None_from_full|].
  spec Hproj; [assumption|].
  spec Hproj; [apply weak_projection_valid_message_preservation_from_full|].
  constructor. intro; intros.
  apply (VLSM_weak_projection_finite_valid_trace_from Hproj) in H.
  assumption.
Qed.

End weak_full_projection.

Lemma basic_VLSM_weak_full_projection_strengthen
  (Hweak : VLSM_weak_full_projection X Y label_project state_project)
  (Hstate : strong_full_projection_initial_state_preservation X Y state_project)
  : VLSM_full_projection X Y label_project state_project.
Proof.
  constructor. intros sX trX [HtrX HsX].
  split.
  - revert HtrX. apply (VLSM_weak_full_projection_finite_valid_trace_from Hweak).
  - revert HsX. apply Hstate.
Qed.

Lemma basic_VLSM_full_projection
  (Hstate : strong_full_projection_initial_state_preservation X Y state_project)
  (Hmessage : weak_full_projection_initial_message_preservation X Y state_project)
  : VLSM_full_projection X Y label_project state_project.
Proof.
  apply basic_VLSM_weak_full_projection_strengthen; [|assumption].
  apply basic_VLSM_weak_full_projection; [|assumption].
  apply strong_full_projection_initial_state_preservation_weaken.
  assumption.
Qed.

End basic_VLSM_full_projection.

Lemma basic_VLSM_strong_full_projection
  {message : Type}
  (X Y : VLSM message)
  (label_project : vlabel X -> vlabel Y)
  (state_project : vstate X -> vstate Y)
  (Hvalid : strong_full_projection_valid_preservation X Y label_project state_project)
  (Htransition : strong_full_projection_transition_preservation X Y label_project state_project)
  (Hstate : strong_full_projection_initial_state_preservation X Y state_project)
  (Hmessage : strong_full_projection_initial_message_preservation X Y)
  : VLSM_full_projection X Y label_project state_project.
Proof.
  apply basic_VLSM_full_projection.
  - apply strong_full_projection_valid_preservation_weaken. assumption.
  - apply strong_full_projection_transition_preservation_weaken. assumption.
  - assumption.
  - apply strong_full_projection_initial_message_preservation_weaken. assumption.
Qed.

Lemma basic_VLSM_full_projection_preloaded
  {message : Type}
  (X Y : VLSM message)
  (label_project : vlabel X -> vlabel Y)
  (state_project : vstate X -> vstate Y)
  (Hvalid : strong_full_projection_valid_preservation X Y label_project state_project)
  (Htransition : strong_full_projection_transition_preservation  X Y label_project state_project)
  (Hstate : strong_full_projection_initial_state_preservation X Y state_project)
  : VLSM_full_projection (pre_loaded_with_all_messages_vlsm X) (pre_loaded_with_all_messages_vlsm Y) label_project state_project.
Proof.
  constructor.
  intros sX trX HtrX.
  split; [|apply Hstate; apply HtrX].
  induction HtrX using finite_valid_trace_rev_ind.
  - constructor. apply initial_state_is_valid.
    apply Hstate; assumption.
  - setoid_rewrite map_app. apply finite_valid_trace_from_app_iff.
    split; [assumption|].
    simpl. apply (finite_valid_trace_singleton (pre_loaded_with_all_messages_vlsm Y)).
    destruct Hx as [[_ [_ Hv]] Ht].
    apply Hvalid in Hv.
    apply Htransition in Ht.
    rewrite (pre_VLSM_full_projection_finite_trace_last _ _ label_project state_project) in Hv, Ht.
    repeat split; [..|assumption|assumption].
    + apply finite_valid_trace_last_pstate in IHHtrX. assumption.
    + apply any_message_is_valid_in_preloaded.
Qed.

Lemma basic_VLSM_full_projection_preloaded_with
  {message : Type}
  (X Y : VLSM message)
  (P Q : message -> Prop)
  (PimpliesQ : forall m : message, P m -> Q m)
  (label_project : vlabel X -> vlabel Y)
  (state_project : vstate X -> vstate Y)
  (Hvalid : strong_full_projection_valid_preservation X Y label_project state_project)
  (Htransition : strong_full_projection_transition_preservation  X Y label_project state_project)
  (Hstate : strong_full_projection_initial_state_preservation X Y state_project)
  (Hmessage : strong_full_projection_initial_message_preservation X Y)
  : VLSM_full_projection (pre_loaded_vlsm X P) (pre_loaded_vlsm Y Q) label_project state_project.
Proof.
  constructor.
  intros sX trX HtrX.
  apply valid_trace_add_default_last in HtrX.
  split; [|apply Hstate; apply HtrX].
  induction HtrX using finite_valid_trace_init_to_rev_strong_ind.
  - constructor. apply initial_state_is_valid.
    apply Hstate; assumption.
  - setoid_rewrite map_app. apply finite_valid_trace_from_app_iff.
    split; [assumption|].
    simpl. apply (finite_valid_trace_singleton (pre_loaded_vlsm Y Q)).
    destruct Ht as [[_ [_ Hv]] Ht].
    apply Hvalid in Hv.
    apply Htransition in Ht.
    apply valid_trace_get_last in HtrX1. subst s.
    rewrite (pre_VLSM_full_projection_finite_trace_last _ _ label_project state_project) in Hv, Ht.
    simpl.
    repeat split; [..|assumption|assumption].
    + apply finite_valid_trace_last_pstate in IHHtrX1. assumption.
    + destruct iom as [m|]; [|apply option_valid_message_None].
      unfold empty_initial_message_or_final_output in Heqiom.
      destruct_list_last iom_tr iom_tr' iom_lst Heqiom_tr
      ; [apply option_initial_message_is_valid; destruct Heqiom as [Him | Hp]|].
      * left. revert Him. apply Hmessage.
      * right. apply PimpliesQ. assumption.
      * apply
          (valid_trace_output_is_valid (pre_loaded_vlsm Y Q) _ _ IHHtrX2 m).
        setoid_rewrite map_app. apply Exists_app. right.
        left. assumption.
Qed.

(** We instantiate the above for VLSM inclusions
*)

Section basic_VLSM_incl.

Context
  {message : Type}
  {T : VLSMType message}
  {SX SY : VLSMSign T}
  (MX : VLSMClass SX)
  (MY : VLSMClass SY)
  (X := mk_vlsm MX)
  (Y := mk_vlsm MY)
  .

Lemma basic_VLSM_incl
  (Hinitial_state : strong_incl_initial_state_preservation MX MY)
  (Hinitial_valid_message : weak_incl_initial_message_preservation MX MY)
  (Hvalid : weak_incl_valid_preservation MX MY)
  (Htransition : weak_incl_transition_preservation MX MY)
  : VLSM_incl X Y.
Proof.
  apply VLSM_incl_full_projection_iff.
  apply basic_VLSM_full_projection; assumption.
Qed.

Lemma basic_VLSM_strong_incl
  (Hinitial_state : strong_incl_initial_state_preservation MX MY)
  (Hinitial_valid_message : strong_incl_initial_message_preservation MX MY)
  (Hvalid : strong_incl_valid_preservation MX MY)
  (Htransition : strong_incl_transition_preservation MX MY)
  : VLSM_incl X Y.
Proof.
  apply VLSM_incl_full_projection_iff.
  apply basic_VLSM_strong_full_projection; assumption.
Qed.

Lemma basic_VLSM_incl_preloaded
  (Hinitial_state : strong_incl_initial_state_preservation MX MY)
  (Hvalid : strong_incl_valid_preservation MX MY)
  (Htransition : strong_incl_transition_preservation MX MY)
  : VLSM_incl (pre_loaded_with_all_messages_vlsm X) (pre_loaded_with_all_messages_vlsm Y).
Proof.
  apply VLSM_incl_full_projection_iff.
  apply (basic_VLSM_full_projection_preloaded X Y id id); assumption.
Qed.

Lemma basic_VLSM_incl_preloaded_with
  (P Q : message -> Prop)
  (PimpliesQ : forall m : message, P m -> Q m)
  (Hvalid : strong_incl_valid_preservation MX MY)
  (Htransition : strong_incl_transition_preservation  MX MY)
  (Hstate : strong_incl_initial_state_preservation MX MY)
  (Hmessage : strong_incl_initial_message_preservation MX MY)
  : VLSM_incl (pre_loaded_vlsm X P) (pre_loaded_vlsm Y Q).
Proof.
  apply VLSM_incl_full_projection_iff.
  apply (basic_VLSM_full_projection_preloaded_with X Y _ _ PimpliesQ id id); assumption.
Qed.

End basic_VLSM_incl.

Section VLSM_incl_preloaded_properties.

Context
  {message : Type}
  (X : VLSM message)
  .

Lemma pre_loaded_vlsm_incl_relaxed
  (P Q : message -> Prop)
  (PimpliesQorValid : forall m : message, P m -> Q m \/ valid_message_prop (pre_loaded_vlsm X Q) m)
  : VLSM_incl (pre_loaded_vlsm X P) (pre_loaded_vlsm X Q).
Proof.
  apply basic_VLSM_incl.
  - cbv; intuition.
  - intros _ _ m _ _ [Him | Hp].
    + apply initial_message_is_valid. left. assumption.
    + apply PimpliesQorValid in Hp as [Hq | Hvalid]; [|assumption].
      apply initial_message_is_valid. right. assumption.
  - cbv; intuition.
  - cbv; intuition.
Qed.

Lemma pre_loaded_vlsm_incl
  (P Q : message -> Prop)
  (PimpliesQ : forall m : message, P m -> Q m)
  : VLSM_incl (pre_loaded_vlsm X P) (pre_loaded_vlsm X Q).
Proof.
  apply pre_loaded_vlsm_incl_relaxed. intuition.
Qed.

Lemma pre_loaded_vlsm_with_valid_eq
  (P Q : message -> Prop)
  (QimpliesValid : forall m, Q m -> valid_message_prop (pre_loaded_vlsm X P) m)
  : VLSM_eq (pre_loaded_vlsm X (fun m => P m \/ Q m)) (pre_loaded_vlsm X P).
Proof.
  apply VLSM_eq_incl_iff; split.
  - apply pre_loaded_vlsm_incl_relaxed. intuition.
  - cbv; apply pre_loaded_vlsm_incl. intuition.
Qed.

Lemma pre_loaded_vlsm_idem_l
  (P : message -> Prop)
  : VLSM_incl (pre_loaded_vlsm (pre_loaded_vlsm X P) P) (pre_loaded_vlsm X P).
Proof.
  apply basic_VLSM_strong_incl; cbv; intuition.
Qed.

Lemma pre_loaded_vlsm_idem_r
  (P : message -> Prop)
  : VLSM_incl (pre_loaded_vlsm X P) (pre_loaded_vlsm (pre_loaded_vlsm X P) P).
Proof.
  apply basic_VLSM_incl_preloaded_with; cbv; intuition.
Qed.

Lemma pre_loaded_vlsm_idem
  (P : message -> Prop)
  : VLSM_eq (pre_loaded_vlsm (pre_loaded_vlsm X P) P) (pre_loaded_vlsm X P).
Proof.
  apply VLSM_eq_incl_iff.
  split.
  - apply pre_loaded_vlsm_idem_l.
  - apply pre_loaded_vlsm_idem_r.
Qed.

Lemma pre_loaded_with_all_messages_vlsm_is_pre_loaded_with_True_l
  : VLSM_incl (pre_loaded_with_all_messages_vlsm X) (pre_loaded_vlsm X (fun m => True)).
Proof.
  apply basic_VLSM_strong_incl; cbv; intuition.
Qed.

Lemma pre_loaded_with_all_messages_vlsm_is_pre_loaded_with_True_r
  : VLSM_incl (pre_loaded_vlsm X (fun m => True)) (pre_loaded_with_all_messages_vlsm X).
Proof.
  apply basic_VLSM_strong_incl; cbv; intuition.
Qed.

Lemma pre_loaded_with_all_messages_vlsm_is_pre_loaded_with_True
  : VLSM_eq (pre_loaded_with_all_messages_vlsm X) (pre_loaded_vlsm X (fun m => True)).
Proof.
  apply VLSM_eq_incl_iff.
  split.
  - apply pre_loaded_with_all_messages_vlsm_is_pre_loaded_with_True_l.
  - apply pre_loaded_with_all_messages_vlsm_is_pre_loaded_with_True_r.
Qed.

Lemma pre_loaded_vlsm_incl_pre_loaded_with_all_messages
  (P : message -> Prop)
  : VLSM_incl (pre_loaded_vlsm X P) (pre_loaded_with_all_messages_vlsm X).
Proof.
  apply basic_VLSM_strong_incl; cbv; intuition.
Qed.

Lemma vlsm_is_pre_loaded_with_False
  : VLSM_eq X (pre_loaded_vlsm X (fun m => False)).
Proof.
  destruct X as (T, (S, M)). intro Hpp.
  apply VLSM_eq_incl_iff. simpl.
  split; apply basic_VLSM_strong_incl; cbv; intuition.
Qed.

Lemma vlsm_is_pre_loaded_with_False_initial_message
  : strong_full_projection_initial_message_preservation X (pre_loaded_vlsm X (fun m => False)).
Proof.
  intros m Hm. left. assumption.
Qed.

Lemma vlsm_is_pre_loaded_with_False_initial_message_rev
  : strong_full_projection_initial_message_preservation (pre_loaded_vlsm X (fun m => False)) X.
Proof.
  intros m [Hm | Hfalse]; [assumption|contradiction].
Qed.

Lemma pre_loaded_with_all_messages_vlsm_idem_l
  : VLSM_incl (pre_loaded_with_all_messages_vlsm (pre_loaded_with_all_messages_vlsm X)) (pre_loaded_with_all_messages_vlsm X).
Proof.
  apply basic_VLSM_strong_incl; cbv; intuition.
Qed.

Lemma pre_loaded_with_all_messages_vlsm_idem_r
  : VLSM_incl (pre_loaded_with_all_messages_vlsm X) (pre_loaded_with_all_messages_vlsm (pre_loaded_with_all_messages_vlsm X)).
Proof.
  apply basic_VLSM_incl_preloaded; cbv; intuition.
Qed.

Lemma pre_loaded_with_all_messages_vlsm_idem
  : VLSM_eq (pre_loaded_with_all_messages_vlsm (pre_loaded_with_all_messages_vlsm X)) (pre_loaded_with_all_messages_vlsm X).
Proof.
  apply VLSM_eq_incl_iff.
  split.
  - apply pre_loaded_with_all_messages_vlsm_idem_l.
  - apply pre_loaded_with_all_messages_vlsm_idem_r.
Qed.

Lemma vlsm_is_pre_loaded_with_False_valid_state_message s om
  : valid_state_message_prop X s om <-> valid_state_message_prop (pre_loaded_vlsm X (fun m => False)) s om.
Proof.
  pose proof vlsm_is_pre_loaded_with_False as Heq.
  apply VLSM_eq_incl_iff in Heq.
  destruct X as (T, (S, M)); simpl in *.
  split; (apply VLSM_incl_valid_state_message; [|cbv;tauto]); apply Heq.
Qed.

Lemma pre_loaded_with_all_messages_can_emit
  (m : message)
  (Hm : can_emit X m)
  : can_emit (pre_loaded_with_all_messages_vlsm X) m.
Proof.
  apply (VLSM_incl_can_emit (vlsm_incl_pre_loaded_with_all_messages_vlsm X)).
  rewrite mk_vlsm_machine;assumption.
Qed.

End VLSM_incl_preloaded_properties.

Lemma preloaded_weaken_finite_valid_trace_from
      {message : Type} (X : VLSM message) (from : state) (tr : list transition_item) :
  finite_valid_trace_from X from tr ->
  finite_valid_trace_from (pre_loaded_with_all_messages_vlsm X) from tr.
Proof.
  destruct X as (T, (S, M)).
  apply VLSM_incl_finite_valid_trace_from.
  apply vlsm_incl_pre_loaded_with_all_messages_vlsm.
Qed.

Lemma preloaded_weaken_finite_valid_trace_from_to
      {message : Type} (X : VLSM message) (from to : state) (tr : list transition_item) :
  finite_valid_trace_from_to X from to tr ->
  finite_valid_trace_from_to (pre_loaded_with_all_messages_vlsm X) from to tr.
Proof.
  destruct X as (T, (S, M)).
  apply VLSM_incl_finite_valid_trace_from_to.
  apply vlsm_incl_pre_loaded_with_all_messages_vlsm.
Qed.

(** ** Induced [VLSM_projection]s

Given an existing [VLSM], a target [VLSM_type], a <<state_project>>ion map, and
a partial <<label_project>>ion map, and some corresponding reverse maps
<<state_lift>> and <<label_lift>> we can build a new VLSM over the target type,
induced by the source VLSM, its missing components being defined based on the
source components.

If additionally some consistency ([weak_projection_transition_consistency_None]
and [weak_projection_transition_consistency_Some]) properties are satisfied,
then the induced VLSM is a [VLSM_projection] of the source one.
*)
Section projection_induced_vlsm.

Context
  {message : Type}
  (X : VLSM message)
  (TY : VLSMType message)
  (label_project : vlabel X -> option (@label _ TY))
  (state_project : vstate X -> @state _ TY)
  (trace_project := pre_VLSM_projection_finite_trace_project _ _ label_project state_project)
  (label_lift : @label _ TY -> vlabel X)
  (state_lift : @state _ TY -> vstate X)
  .

Definition projection_induced_initial_state_prop (sY : @state _ TY) : Prop :=
  exists sX, state_project sX = sY /\ vinitial_state_prop X sX.

Program Instance projection_induced_initial_state_inh : Inhabited (sig projection_induced_initial_state_prop)
  := populate (exist _ (state_project (proj1_sig (@inhabitant _ (@s0 _ _ (sign X))))) _).
Next Obligation.
  eexists. split.
  - reflexivity.
  - destruct (@inhabitant _ (@s0 _ _ (sign X))). assumption.
Qed.

Definition projection_induced_initial_message_prop : message -> Prop :=
  valid_message_prop X.

Definition projection_induced_vlsm_sig : VLSMSign TY :=
  {| initial_message_prop := projection_induced_initial_message_prop
   ; initial_state_prop := projection_induced_initial_state_prop
  |}.

Definition projection_induced_transition
  (lY : @label _ TY)
  (somY : @state _ TY * option message)
  : @state _ TY * option message :=
  let (sY, om) := somY in
  let (s'X, om') := vtransition X (label_lift lY) (state_lift sY, om) in
  (state_project s'X, om').

Definition projection_induced_valid
  (lY : @label _ TY)
  (somY : @state _ TY * option message)
  : Prop :=
  let (sY, om) := somY in
  exists lX sX, label_project lX = Some lY /\ state_project sX = sY /\
  input_valid X lX (sX, om).

Definition projection_induced_vlsm_class : VLSMClass projection_induced_vlsm_sig :=
  {| transition := projection_induced_transition
   ;  valid := projection_induced_valid
  |}.

Definition projection_induced_vlsm : VLSM message :=
  mk_vlsm projection_induced_vlsm_class.

(** <<label_project>> is a left-inverse of <<label_lift>> *)
Definition induced_projection_label_lift_prop : Prop :=
  forall lY, label_project (label_lift lY) = Some lY.

(** <<state_project>> is a left-inverse of <<state_lift>> *)
Definition induced_projection_state_lift_prop : Prop :=
  forall sY, state_project (state_lift sY) = sY.

(** Transitions through states and labels with the same projections using the
same message should lead to the same output message and states with the same
projections.
*)
Definition induced_projection_transition_consistency_Some : Prop :=
  forall lX1 lX2 lY, label_project lX1 = Some lY -> label_project lX2 = Some lY ->
  forall sX1 sX2, state_project sX1 = state_project sX2 ->
  forall iom sX1' oom1, vtransition X lX1 (sX1, iom) = (sX1', oom1) ->
  forall sX2' oom2, vtransition X lX2 (sX2, iom) = (sX2', oom2) ->
  state_project sX1' = state_project sX2' /\ oom1 = oom2.

(** A weaker version of [induced_projection_transition_consistency_Some] *)
Definition weak_projection_transition_consistency_Some
  : Prop :=
  forall lX lY, label_project lX = Some lY ->
  forall s1 om s1' om1', input_valid_transition X lX (s1, om) (s1', om1') ->
  forall s2' om2', vtransition X (label_lift lY) (state_lift (state_project s1), om) = (s2', om2') ->
  state_project s1' = state_project s2' /\ om1' = om2'.
(* TODO(traiansf): remove the definition above and assume the properties
deriving it in the next lemma instead. *)

Lemma basic_weak_projection_transition_consistency_Some
  : induced_projection_label_lift_prop -> induced_projection_state_lift_prop ->
    induced_projection_transition_consistency_Some ->
    weak_projection_transition_consistency_Some.
Proof.
  intros Hlabel Hstate Htransition lX lY HlX_pr sX1 iom sX1' oom1 Ht1
    sX2' oom2 Ht2.
  apply proj2 in Ht1.
  eapply Htransition; [eassumption| apply Hlabel| |exact Ht1|exact Ht2].
  symmetry.
  apply Hstate.
Qed.

(** Under transition-consistency assumptions, valid messages of the
[projection_induced_vlsm] coincide with those of the source [VLSM].
*)
Lemma projection_induced_valid_message_char
  (Htransition_Some : weak_projection_transition_consistency_Some)
  : forall om, option_valid_message_prop projection_induced_vlsm om <->
    option_valid_message_prop X om.
Proof.
  split; cycle 1.
  - intros Hm.
    destruct om as [m |].
    + apply initial_message_is_valid. assumption.
    + apply option_valid_message_None.
  - intros [s Hsom].
    induction Hsom.
    + destruct om as [m |].
      * assumption.
      * apply option_valid_message_None.
    + destruct Hv as [lX [sX [HlX_pr [HsX_pr [HsX [HomX Hv]]]]]].
      cbn in Ht.
      destruct (vtransition _ _ _) as (_s'X, __om') eqn: H_tX.
      inversion Ht; subst; clear Ht.
      destruct (vtransition X lX (sX, om)) as (s'X, _om') eqn: HtX.
      assert (HivtX : input_valid_transition X lX (sX, om) (s'X, _om'))
        by (repeat split; assumption).
      replace om' with _om'.
        * eapply input_valid_transition_out. eassumption.
        * eapply Htransition_Some; eassumption.
Qed.

Context
  (Htransition_None : weak_projection_transition_consistency_None _ _ label_project state_project)
  (Htype : VLSM_projection_type X TY label_project state_project :=
    basic_VLSM_projection_type X TY label_project state_project Htransition_None)
  .

Lemma projection_induced_vlsm_is_projection
  (Htransition_Some : weak_projection_transition_consistency_Some)
  : VLSM_projection X projection_induced_vlsm label_project state_project.
Proof.
  apply basic_VLSM_projection; intro; intros.
  - exists lX, s.
    split; [assumption|].
    split; [reflexivity|assumption].
  - specialize (Htransition_Some _ _ H _ _ _ _ H0).
    cbn.
    destruct (vtransition _ _ _) as (s2', om2').
    specialize (Htransition_Some _ _ eq_refl) as [Heqs Heqom].
    subst. rewrite Heqs. reflexivity.
  - apply (Htransition_None _ H _ _ _ _ H0).
  - exists s. split; [reflexivity|assumption].
  - destruct Hv as [_ [Hm _]].
    apply initial_message_is_valid.
    assumption.
Qed.

(** When we have a [VLSM_projection] to the [projection_induced_vlsm],
[valid]ity is [input_valid]ity.
*)
Lemma induced_projection_valid_is_input_valid
  (Hproj : VLSM_projection X projection_induced_vlsm label_project state_project)
  l s om
  : vvalid projection_induced_vlsm l (s, om) -> input_valid projection_induced_vlsm l (s,om).
Proof.
  intro Hv.
  destruct (id Hv) as [lX [sX [HlX [<- [Hps [Hopm _]]]]]].
  repeat split.
  - apply (VLSM_projection_valid_state Hproj). assumption.
  - destruct om as [m|]; [|apply option_valid_message_None].
    apply option_initial_message_is_valid.
    assumption.
  - assumption.
Qed.

Section projection_induced_friendliness.

Context
  (Hlabel_lift : induced_projection_label_lift_prop)
  (Hstate_lift : induced_projection_state_lift_prop)
  (Htransition_consistency : induced_projection_transition_consistency_Some)
  (Htransition_Some  : weak_projection_transition_consistency_Some
    := basic_weak_projection_transition_consistency_Some Hlabel_lift Hstate_lift Htransition_consistency)
  (Hproj := projection_induced_vlsm_is_projection Htransition_Some)
  .

Lemma induced_projection_transition_item_lift
  (item : @transition_item _ TY)
  : @pre_VLSM_projection_transition_item_project _ (type X) _
    label_project state_project
    (pre_VLSM_full_projection_transition_item_project _ _ label_lift state_lift item)
    = Some item.
Proof.
  destruct item.
  unfold pre_VLSM_full_projection_transition_item_project,
    pre_VLSM_projection_transition_item_project.
  simpl.
  rewrite Hlabel_lift.
  f_equal. f_equal.
  apply Hstate_lift.
Qed.

Lemma induced_projection_trace_lift
  (tr : list (@transition_item _ TY))
  : @pre_VLSM_projection_finite_trace_project _ (type X) _
    label_project state_project
    (pre_VLSM_full_projection_finite_trace_project _ _ label_lift state_lift tr)
    = tr.
Proof.
  induction tr; [reflexivity|].
  simpl.
  rewrite induced_projection_transition_item_lift.
  f_equal.
  assumption.
Qed.

(** If there is a way to "lift" valid traces of the [projection_induced_vlsm]
to the original [VLSM], then the induced [VLSM_projection] is friendly.
*)
Lemma basic_projection_induces_friendliness
  : VLSM_full_projection projection_induced_vlsm X label_lift state_lift ->
    projection_friendly_prop Hproj.
Proof.
  intros Hfull_proj isY trY HtrY.
  exists (state_lift isY).
  exists (VLSM_full_projection_finite_trace_project Hfull_proj trY).
  intuition.
  + apply (VLSM_full_projection_finite_valid_trace Hfull_proj).
    assumption.
  + apply induced_projection_trace_lift.
Qed.

End projection_induced_friendliness.

End projection_induced_vlsm.

(** Under [weak_projection_transition_consistency_Some] assumptions,
[VLSM_incl]usion between source [VLSM]s implies [VLSM_incl]usion between
their projections induced by the same maps.
*)
Lemma projection_induced_vlsm_incl
  {message : Type}
  {TX : VLSMType message}
  {SigX1 SigX2: VLSMSign TX}
  (MX1 : VLSMClass SigX1) (MX2 : VLSMClass SigX2)
  (X1 := mk_vlsm MX1) (X2 := mk_vlsm MX2)
  (TY : VLSMType message)
  (label_project : @label _ TX -> option (@label _ TY))
  (state_project : @state _ TX -> @state _ TY)
  (trace_project := pre_VLSM_projection_finite_trace_project _ _ label_project state_project)
  (label_lift : @label _ TY -> @label _ TX)
  (state_lift : @state _ TY -> @state _ TX)
  (XY1 : VLSM message := projection_induced_vlsm X1 TY label_project state_project label_lift state_lift)
  (XY2 : VLSM message := projection_induced_vlsm X2 TY label_project state_project label_lift state_lift)
  (Htransition_Some1 : weak_projection_transition_consistency_Some X1 TY label_project state_project label_lift state_lift)
  (Htransition_Some2 : weak_projection_transition_consistency_Some X2 TY label_project state_project label_lift state_lift)
  : VLSM_incl X1 X2 -> VLSM_incl XY1 XY2.
Proof.
  intros Hincl.
  apply VLSM_incl_finite_traces_characterization.
  assert (His : forall s, vinitial_state_prop XY1 s -> vinitial_state_prop XY2 s).
  {
    intros is [s1 [Hs1_pr Hs1]].
    exists s1.
    split; [assumption|].
    apply VLSM_incl_initial_state; assumption.
  }
  intros is tr Htr.
  split; [|apply His, Htr].
  induction Htr using finite_valid_trace_rev_ind
  ; [apply (finite_valid_trace_from_empty XY2), initial_state_is_valid, His; assumption|].
  apply (finite_valid_trace_from_app_iff XY2).
  split; [apply IHHtr|].
  apply (finite_valid_trace_singleton XY2).
  destruct Hx as [[_ [_ [lX [sX [HlX_pr [HsX_pr HpvX1]]]]]] Ht].
  cbn in Ht.
  destruct (vtransition _ _ _) as (_s'X, _oom) eqn:H_tX1.
  inversion Ht. subst. clear Ht.
  destruct (vtransition X1 lX (sX, iom)) as (s'X, _oom) eqn:HtX1.
  assert (HivtX1 : input_valid_transition X1 lX (sX, iom) (s'X, _oom))
    by (split; assumption).
  simpl in HsX_pr, H_tX1. rewrite <- HsX_pr in H_tX1.
  apply (Htransition_Some1 _ _ HlX_pr _ _ _ _ HivtX1) in H_tX1
    as [Heq_s'X_pr Heq_oom].
  subst.
  apply (VLSM_incl_input_valid_transition Hincl) in HivtX1.
  repeat split.
  - eapply finite_valid_trace_last_pstate; eassumption.
  - apply projection_induced_valid_message_char; [assumption| apply HivtX1].
  - exists lX, sX. intuition. apply HivtX1.
  - cbn in *. rewrite <- HsX_pr.
    destruct (vtransition X2 _ _) as (_s'X2, _oom) eqn:H_tX2.
    apply (Htransition_Some2 _ _ HlX_pr _ _ _ _ HivtX1) in H_tX2
      as [Heq_s'X_pr' Heq_oom].
    congruence.
Qed.

(** Under [weak_projection_transition_consistency_Some] assumptions,
[VLSM_eq]uality between source [VLSM]s implies [VLSM_eq]uality between
their projections induced by the same maps.
*)
Lemma projection_induced_vlsm_eq
  {message : Type}
  {TX : VLSMType message}
  {SigX1 SigX2: VLSMSign TX}
  (MX1 : VLSMClass SigX1) (MX2 : VLSMClass SigX2)
  (X1 := mk_vlsm MX1) (X2 := mk_vlsm MX2)
  (TY : VLSMType message)
  (label_project : @label _ TX -> option (@label _ TY))
  (state_project : @state _ TX -> @state _ TY)
  (trace_project := pre_VLSM_projection_finite_trace_project _ _ label_project state_project)
  (label_lift : @label _ TY -> @label _ TX)
  (state_lift : @state _ TY -> @state _ TX)
  (XY1 : VLSM message := projection_induced_vlsm X1 TY label_project state_project label_lift state_lift)
  (XY2 : VLSM message := projection_induced_vlsm X2 TY label_project state_project label_lift state_lift)
  (Htransition_Some1 : weak_projection_transition_consistency_Some X1 TY label_project state_project label_lift state_lift)
  (Htransition_Some2 : weak_projection_transition_consistency_Some X2 TY label_project state_project label_lift state_lift)
  : VLSM_eq X1 X2 -> VLSM_eq XY1 XY2.
Proof.
  intro Heq.
  apply VLSM_eq_incl_iff.
  split.
  - apply
    (projection_induced_vlsm_incl MX1 MX2 TY
      label_project state_project label_lift state_lift
      Htransition_Some1 Htransition_Some2 (VLSM_eq_proj1 Heq)).
  - apply
    (projection_induced_vlsm_incl MX2 MX1 TY
      label_project state_project label_lift state_lift
      Htransition_Some2 Htransition_Some1 (VLSM_eq_proj2 Heq)).
Qed.

Section same_VLSM_full_projection.

Context
  {message : Type}
  (X1 X2 : VLSM message)
  (Heq : X1 = X2)
  .

Lemma same_VLSM_full_projection
  : VLSM_full_projection X1 X2 (same_VLSM_label_rew Heq) (same_VLSM_state_rew Heq).
Proof.
  apply basic_VLSM_strong_full_projection; intro.
  - apply same_VLSM_valid_preservation.
  - apply same_VLSM_transition_preservation.
  - apply same_VLSM_initial_state_preservation.
  - apply same_VLSM_initial_message_preservation.
    assumption.
Qed.

End same_VLSM_full_projection.
