From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From VLSM.Lib Require Import Preamble ListExtras StreamExtras StreamFilters StdppExtras.
From VLSM.Core Require Import VLSM VLSMProjections.VLSMPartialProjection.

(** * VLSM Stuttering Embeddings

  Stuttering embeddings are VLSM projections guaranteeing the existence of
  translations for all states and traces, in which a transition in the source
  VLSM translates to a (possibly empty) sequence of transitions in the target VLSM.

  A stuttering embedding is established from VLSM <<X>> to VLSM <<Y>>
  (sharing the same messages) if there exists maps <<state_project>>
  taking <<X>>-states to <<Y>>-states, and <<transition_item_project>>, taking
  a transition from <<X>> to a list of transitions in <<Y>>, such that:

  - [transition_item_project_consistency]: the state-translation of the destination
    of a transition is the final state of the translation of the transition.
  - [stuttering_embedding_preserves_valid_trace]s: traces obtained by
    concatenating the translations of transition of a valid trace are valid.

  An example of proper stuttering embedding is given by a VLSM summarizing the
  transitions of another VLSM.
*)

Section sec_pre_definitions.

Context
  {message : Type}
  {TX TY : VLSMType message}
  (state_project : @state _ TX -> @state _ TY)
  (transition_item_project : @transition_item _ TX -> list (@transition_item _ TY))
  .

Definition pre_VLSM_stuttering_embedding_finite_trace_project :
  list (@transition_item _ TX) -> list (@transition_item _ TY) :=
    mbind transition_item_project.

Definition pre_VLSM_stuttering_embedding_infinite_trace_project
  (s : Streams.Stream (@transition_item _ TX))
  (Hs : InfinitelyOften (fun item => transition_item_project item <> []) s)
  : Streams.Stream (@transition_item _ TY) :=
  stream_concat_map transition_item_project s Hs.

Definition pre_VLSM_stuttering_embedding_infinite_finite_trace_project
  (s : Streams.Stream (@transition_item _ TX))
  (Hs : FinitelyManyBound (fun item => transition_item_project item <> []) s)
  : list (@transition_item _ TY) :=
  bounded_stream_concat_map transition_item_project s Hs.

Definition pre_VLSM_stuttering_embedding_finite_trace_project_app :
  forall (l1 l2 : list (@transition_item _ TX)),
    pre_VLSM_stuttering_embedding_finite_trace_project (l1 ++ l2)
      =
    pre_VLSM_stuttering_embedding_finite_trace_project l1
      ++ pre_VLSM_stuttering_embedding_finite_trace_project l2
  := mbind_app _.

Lemma elem_of_pre_VLSM_stuttering_embedding_finite_trace_project :
  forall (trX : list (@transition_item _ TX)) (itemY : @transition_item _ TY),
    itemY ∈ pre_VLSM_stuttering_embedding_finite_trace_project trX
      <->
    exists (itemX : @transition_item _ TX), itemY ∈ transition_item_project itemX /\ itemX ∈ trX.
Proof. by intros; apply elem_of_list_bind. Qed.

End sec_pre_definitions.

Record VLSM_stuttering_embedding_type
  {message : Type}
  (X : VLSM message)
  (TY : VLSMType message)
  (state_project : vstate X -> @state _ TY)
  (transition_item_project : vtransition_item X -> list (@transition_item _ TY))
  : Prop :=
{
  transition_item_project_consistency :
    forall sX itemX,
      input_valid_transition_item X sX itemX ->
        finite_trace_last (state_project sX) (transition_item_project itemX)
          =
        state_project (destination itemX);
}.

(** ** Stuttering embedding definitions and properties *)

Section sec_stuttering_embedding_type_properties.

Definition strong_transition_item_project_consistency
  {message : Type}
  [X : VLSM message]
  [TY : VLSMType message]
  (state_project : vstate X -> @state _ TY)
  (transition_item_project : vtransition_item X -> list (@transition_item _ TY))
  : Prop :=
  forall sX lX inputX destinationX outputX,
    vtransition X lX (sX, inputX) = (destinationX, outputX) ->
    finite_trace_last (state_project sX)
      (transition_item_project
        {| l := lX; input := inputX; destination := destinationX; output := outputX |})
      =
    state_project destinationX.

Section sec_pre_properties.

Context
  {message : Type}
  (X : VLSM message)
  (TY : VLSMType message)
  (state_project : vstate X -> @state _ TY)
  (transition_item_project : vtransition_item X -> list (@transition_item _ TY))
  (Hsimul : VLSM_stuttering_embedding_type X TY state_project transition_item_project)
  .

Definition pre_VLSM_stuttering_embedding_finite_trace_last :
  forall (s : vstate X) (tr : list (vtransition_item X)),
    finite_valid_trace_from X s tr ->
    finite_trace_last (state_project s)
      (pre_VLSM_stuttering_embedding_finite_trace_project transition_item_project tr)
      =
    state_project (finite_trace_last s tr).
Proof.
  induction 1 using finite_valid_trace_from_rev_ind; [done |].
  erewrite finite_trace_last_is_last,
    pre_VLSM_stuttering_embedding_finite_trace_project_app,
    finite_trace_last_app, IHfinite_valid_trace_from,
    <- transition_item_project_consistency; [| done..].
  by cbn; rewrite app_nil_r.
Qed.

End sec_pre_properties.

Definition VLSM_partial_trace_project_from_stuttering_embedding
  {message : Type}
  {X : VLSM message}
  {TY : VLSMType message}
  (state_project : vstate X -> @state _ TY)
  (transition_item_project : vtransition_item X -> list (@transition_item _ TY))
  (trace_project := pre_VLSM_stuttering_embedding_finite_trace_project transition_item_project)
  (str : vstate X * list (vtransition_item X))
  : option (@state _ TY * list (@transition_item _ TY)) :=
    let (s, tr) := str in Some (state_project s, trace_project tr).

Context
  {message : Type}
  {X Y : VLSM message}
  (state_project : vstate X -> vstate Y)
  (transition_item_project : vtransition_item X -> list (vtransition_item Y))
  (Hsimul : VLSM_stuttering_embedding_type X (type Y) state_project transition_item_project)
  .

(**
  Any [VLSM_stuttering_embedding_type] determines a [VLSM_partial_projection_type],
  allowing us to lift to VLSM stuttering embeddings the generic results proved
  about VLSM partial projections.
*)
Lemma VLSM_partial_projection_type_from_stuttering_embedding :
  VLSM_partial_projection_type X Y
    (VLSM_partial_trace_project_from_stuttering_embedding state_project transition_item_project).
Proof.
  constructor; intros * Hpr * Hlst Htr.
  apply Some_inj, pair_equal_spec in Hpr as [<- <-]; cbn.
  rewrite pre_VLSM_stuttering_embedding_finite_trace_project_app.
  eexists (state_project s'X), _.
  split; [done |].
  apply finite_valid_trace_from_app_iff in Htr as [].
  by erewrite pre_VLSM_stuttering_embedding_finite_trace_last, Hlst.
Qed.

End sec_stuttering_embedding_type_properties.

Section sec_VLSM_stuttering_embedding_definitions.

Context
  {message : Type}
  (X Y : VLSM message)
  (state_project : vstate X -> vstate Y)
  (transition_item_project : vtransition_item X -> list (vtransition_item Y))
  (trace_project := pre_VLSM_stuttering_embedding_finite_trace_project transition_item_project)
  .

Definition stuttering_embedding_input_valid_transition_item_validity : Prop :=
  forall s item,
    input_valid_transition_item X s item ->
    finite_valid_trace_from_to Y (state_project s) (state_project (destination item))
      (transition_item_project item).

(**
  Similarly to the [VLSM_partial_projection] case we distinguish two types of
  stuttering embeddings: [VLSM_weak_stuttering_embedding] and
  [VLSM_stuttering_embedding], distinguished by the fact that the weak
  embeddings are not required to preserve initial states.
*)
Record VLSM_weak_stuttering_embedding : Prop :=
{
  weak_stuttering_embedding_type :>
    VLSM_stuttering_embedding_type X (type Y) state_project transition_item_project;
  weak_stuttering_embedding_preserves_valid_trace :
    forall sX trX,
      finite_valid_trace_from X sX trX ->
      finite_valid_trace_from Y (state_project sX) (trace_project trX);
}.

Record VLSM_stuttering_embedding : Prop :=
{
  stuttering_embedding_type :>
    VLSM_stuttering_embedding_type X (type Y) state_project transition_item_project;
  stuttering_embedding_preserves_valid_trace :
    forall sX trX,
      finite_valid_trace X sX trX -> finite_valid_trace Y (state_project sX) (trace_project trX);
}.

Definition weak_stuttering_embedding_initial_state_preservation : Prop :=
  forall s : state,
    vinitial_state_prop X s -> valid_state_prop Y (state_project s).

Definition strong_stuttering_embedding_initial_state_preservation : Prop :=
  forall s : state,
    vinitial_state_prop X s -> vinitial_state_prop Y (state_project s).

Lemma strong_stuttering_embedding_initial_state_preservation_weaken :
  strong_stuttering_embedding_initial_state_preservation ->
    weak_stuttering_embedding_initial_state_preservation.
Proof.
  intros Hstrong s Hs.
  apply initial_state_is_valid.
  by apply Hstrong.
Qed.

End sec_VLSM_stuttering_embedding_definitions.

Section sec_weak_stuttering_embedding_properties.

Context
  {message : Type}
  {X Y : VLSM message}
  {state_project : vstate X -> vstate Y}
  {transition_item_project : vtransition_item X -> list (vtransition_item Y)}
  .

Section sec_weak_stuttering_embedding_trace_projection_redefinitions.

(**
  Here we restate the <<pre_>> definitions above to depend on [VLSM_weak_stuttering_embedding]
  and have their state and transition item projection functions implicit.
*)

Definition VLSM_weak_stuttering_embedding_finite_trace_project
  (Hsimul : VLSM_weak_stuttering_embedding X Y state_project transition_item_project)
  : list (vtransition_item X) -> list (vtransition_item Y)
  := pre_VLSM_stuttering_embedding_finite_trace_project transition_item_project.

Definition elem_of_VLSM_weak_stuttering_embedding
  (Hsimul : VLSM_weak_stuttering_embedding X Y state_project transition_item_project)
  := elem_of_pre_VLSM_stuttering_embedding_finite_trace_project transition_item_project.

Definition VLSM_weak_stuttering_embedding_infinite_trace_project
  (Hsimul : VLSM_weak_stuttering_embedding X Y state_project transition_item_project)
  (s : Streams.Stream (vtransition_item X))
  (Hinf : InfinitelyOften (fun item => transition_item_project item <> []) s)
  : Streams.Stream (vtransition_item Y)
  := pre_VLSM_stuttering_embedding_infinite_trace_project transition_item_project s Hinf.

Definition VLSM_weak_stuttering_embedding_infinite_finite_trace_project
  (Hsimul : VLSM_weak_stuttering_embedding X Y state_project transition_item_project)
  (s : Streams.Stream (vtransition_item X))
  (Hfin : FinitelyManyBound (fun item => transition_item_project item <> []) s)
  : list (vtransition_item Y)
  := pre_VLSM_stuttering_embedding_infinite_finite_trace_project transition_item_project s Hfin.

End sec_weak_stuttering_embedding_trace_projection_redefinitions.

(**
  While for the above section, the [VLSM_weak_stuttering_embedding] was necessary
  to be mentioned explicitly, in the following we make it part of the context.
*)

Context
  (Hsimul : VLSM_weak_stuttering_embedding X Y state_project transition_item_project).

Definition VLSM_weak_stuttering_embedding_finite_trace_project_app :
  forall l1 l2,
    VLSM_weak_stuttering_embedding_finite_trace_project Hsimul (l1 ++ l2)
      =
    VLSM_weak_stuttering_embedding_finite_trace_project Hsimul l1
      ++ VLSM_weak_stuttering_embedding_finite_trace_project Hsimul l2
  := pre_VLSM_stuttering_embedding_finite_trace_project_app transition_item_project.

Definition VLSM_weak_stuttering_embedding_finite_trace_last :
  forall sX trX,
    finite_valid_trace_from X sX trX ->
    finite_trace_last (state_project sX)
      (VLSM_weak_stuttering_embedding_finite_trace_project Hsimul trX)
      =
    state_project (finite_trace_last sX trX)
  := pre_VLSM_stuttering_embedding_finite_trace_last _ _ _ _ Hsimul.

Definition VLSM_weak_stuttering_embedding_finite_valid_trace_from :
  forall sX trX,
    finite_valid_trace_from X sX trX ->
    finite_valid_trace_from Y (state_project sX)
      (VLSM_weak_stuttering_embedding_finite_trace_project Hsimul trX)
  := weak_stuttering_embedding_preserves_valid_trace _ _ _ _ Hsimul.

Lemma VLSM_weak_stuttering_embedding_infinite_valid_trace_from :
  forall sX trX (Hinf : InfinitelyOften (fun item => transition_item_project item <> []) trX),
    infinite_valid_trace_from X sX trX ->
    infinite_valid_trace_from Y (state_project sX)
      (VLSM_weak_stuttering_embedding_infinite_trace_project Hsimul trX Hinf).
Proof.
  intros sX trX Hinf HtrX.
  apply infinite_valid_trace_from_prefix_rev.
  intros n.
  destruct (stream_concat_map_ex_prefix transition_item_project trX Hinf n)
    as (m & suf & Hrew).
  apply finite_valid_trace_from_app_iff with (ls' := suf).
  setoid_rewrite <- Hrew.
  by apply VLSM_weak_stuttering_embedding_finite_valid_trace_from,
    infinite_valid_trace_from_prefix.
Qed.

Lemma VLSM_weak_stuttering_embedding_infinite_finite_valid_trace_from :
  forall sX trX (Hfin : FinitelyManyBound (fun item => transition_item_project item <> []) trX),
    infinite_valid_trace_from X sX trX ->
    finite_valid_trace_from Y (state_project sX)
      (VLSM_weak_stuttering_embedding_infinite_finite_trace_project Hsimul trX Hfin).
Proof.
  intros sX trX Hfin HtrX.
  apply VLSM_weak_stuttering_embedding_finite_valid_trace_from.
  by apply infinite_valid_trace_from_prefix with (n := `Hfin) in HtrX.
Qed.

(**
  Any [VLSM_weak_stuttering_embedding] determines a [VLSM_weak_partial_projection],
  allowing us to lift to weak stuttering embeddings the generic results proved
  about weak partial projections.
*)
Lemma VLSM_weak_partial_projection_from_stuttering_embedding :
  VLSM_weak_partial_projection X Y
    (VLSM_partial_trace_project_from_stuttering_embedding state_project transition_item_project).
Proof.
  split.
  - by apply VLSM_partial_projection_type_from_stuttering_embedding, Hsimul.
  - cbn; intros sX trX sY trY [= <- <-].
    by apply VLSM_weak_stuttering_embedding_finite_valid_trace_from.
Qed.

Lemma VLSM_weak_stuttering_embedding_valid_state :
  forall sX,
    valid_state_prop X sX -> valid_state_prop Y (state_project sX).
Proof.
  by intro sX; eapply VLSM_weak_partial_projection_valid_state;
    [apply VLSM_weak_partial_projection_from_stuttering_embedding |].
Qed.

Lemma VLSM_weak_stuttering_embedding_finite_valid_trace_from_to :
  forall sX s'X trX,
    finite_valid_trace_from_to X sX s'X trX ->
      finite_valid_trace_from_to Y (state_project sX) (state_project s'X)
        (VLSM_weak_stuttering_embedding_finite_trace_project Hsimul trX).
Proof.
  intros sX s'X trX HtrX.
  apply valid_trace_add_last.
  - eapply VLSM_weak_partial_projection_finite_valid_trace_from.
    + by apply VLSM_weak_partial_projection_from_stuttering_embedding.
    + done.
    + by eapply valid_trace_forget_last.
  - rewrite VLSM_weak_stuttering_embedding_finite_trace_last
      by (eapply valid_trace_forget_last; done).
    by erewrite finite_valid_trace_from_to_last.
Qed.

Lemma VLSM_weak_stuttering_embedding_in_futures :
  forall s1 s2,
    in_futures X s1 s2 -> in_futures Y (state_project s1) (state_project s2).
Proof.
  intros s1 s2 [tr Htr].
  exists (VLSM_weak_stuttering_embedding_finite_trace_project Hsimul tr).
  by revert Htr; apply VLSM_weak_stuttering_embedding_finite_valid_trace_from_to.
Qed.

Lemma VLSM_weak_stuttering_embedding_input_valid_transition_item :
  forall s item,
    input_valid_transition_item X s item ->
    finite_valid_trace_from_to Y (state_project s)
      (state_project (destination item)) (transition_item_project item).
Proof.
  intros.
  replace (transition_item_project item)
    with (VLSM_weak_stuttering_embedding_finite_trace_project Hsimul [item])
    by apply app_nil_r.
  apply VLSM_weak_stuttering_embedding_finite_valid_trace_from_to.
  by destruct item; apply finite_valid_trace_from_to_singleton.
Qed.

End sec_weak_stuttering_embedding_properties.

Section sec_stuttering_embedding_properties.

Context
  {message : Type}
  {X Y : VLSM message}
  {state_project : vstate X -> vstate Y}
  {transition_item_project : vtransition_item X -> list (vtransition_item Y)}
  .

Section sec_stuttering_embedding_trace_projection_redefinitions.

(**
  Here we restate the <<pre_>> definitions above to depend on [VLSM_stuttering_embedding]
  and have their state and transition item projection functions implicit.
*)

Definition VLSM_stuttering_embedding_finite_trace_project
  (Hsimul : VLSM_stuttering_embedding X Y state_project transition_item_project)
  : list (vtransition_item X) -> list (vtransition_item Y)
  := pre_VLSM_stuttering_embedding_finite_trace_project transition_item_project.

Definition elem_of_VLSM_stuttering_embedding
  (Hsimul : VLSM_stuttering_embedding X Y state_project transition_item_project)
  := elem_of_pre_VLSM_stuttering_embedding_finite_trace_project transition_item_project.

Definition VLSM_stuttering_embedding_infinite_trace_project
  (Hsimul : VLSM_stuttering_embedding X Y state_project transition_item_project)
  (s : Streams.Stream (vtransition_item X))
  (Hinf : InfinitelyOften (fun item => transition_item_project item <> []) s)
  : Streams.Stream (vtransition_item Y)
  := pre_VLSM_stuttering_embedding_infinite_trace_project transition_item_project s Hinf.

Definition VLSM_stuttering_embedding_infinite_finite_trace_project
  (Hsimul : VLSM_stuttering_embedding X Y state_project transition_item_project)
  (s : Streams.Stream (vtransition_item X))
  (Hfin : FinitelyManyBound (fun item => transition_item_project item <> []) s)
  : list (vtransition_item Y)
  := pre_VLSM_stuttering_embedding_infinite_finite_trace_project transition_item_project s Hfin.

End sec_stuttering_embedding_trace_projection_redefinitions.

(**
  While for the above section, the [VLSM_stuttering_embedding] was necessary
  to be mentioned explicitly, in the following we make it part of the context.
*)

Context
  (Hsimul : VLSM_stuttering_embedding X Y state_project transition_item_project).

Definition VLSM_stuttering_embedding_finite_trace_project_app :
  forall l1 l2,
    VLSM_stuttering_embedding_finite_trace_project Hsimul (l1 ++ l2)
      =
    VLSM_stuttering_embedding_finite_trace_project Hsimul l1
      ++ VLSM_stuttering_embedding_finite_trace_project Hsimul l2
  := pre_VLSM_stuttering_embedding_finite_trace_project_app transition_item_project.

Definition VLSM_stuttering_embedding_finite_trace_last :
  forall sX trX,
    finite_valid_trace_from X sX trX ->
    finite_trace_last (state_project sX) (VLSM_stuttering_embedding_finite_trace_project Hsimul trX)
      =
    state_project (finite_trace_last sX trX)
  := pre_VLSM_stuttering_embedding_finite_trace_last _ _ _ _ Hsimul.

Definition VLSM_stuttering_embedding_finite_valid_trace :
  forall sX trX,
    finite_valid_trace X sX trX -> finite_valid_trace Y (state_project sX)
      (VLSM_stuttering_embedding_finite_trace_project Hsimul trX)
  := stuttering_embedding_preserves_valid_trace _ _ _ _ Hsimul.

(**
  Any [VLSM_stuttering_embedding] determines a [VLSM_partial_projection], allowing us
  to lift to stuttering embeddings the generic results proved about partial projections.
*)
Lemma VLSM_partial_projection_from_stuttering_embedding :
  VLSM_partial_projection X Y
    (VLSM_partial_trace_project_from_stuttering_embedding state_project transition_item_project).
Proof.
  split.
  - by apply VLSM_partial_projection_type_from_stuttering_embedding, Hsimul.
  - intros sX trX sY trY [= <- <-].
    by apply VLSM_stuttering_embedding_finite_valid_trace.
Qed.

Lemma VLSM_stuttering_embedding_finite_valid_trace_from :
  forall sX trX,
    finite_valid_trace_from X sX trX ->
    finite_valid_trace_from Y (state_project sX)
      (VLSM_stuttering_embedding_finite_trace_project Hsimul trX).
Proof.
  by intros; eapply VLSM_partial_projection_finite_valid_trace_from;
    [apply VLSM_partial_projection_from_stuttering_embedding | ..].
Qed.

Definition VLSM_stuttering_embedding_weaken :
  VLSM_weak_stuttering_embedding X Y state_project transition_item_project :=
{|
  weak_stuttering_embedding_type := stuttering_embedding_type _ _ _ _ Hsimul;
  weak_stuttering_embedding_preserves_valid_trace :=
    VLSM_stuttering_embedding_finite_valid_trace_from;
|}.

Definition VLSM_stuttering_embedding_valid_state :
  forall sX,
    valid_state_prop X sX -> valid_state_prop Y (state_project sX)
  := VLSM_weak_stuttering_embedding_valid_state VLSM_stuttering_embedding_weaken.

Definition VLSM_stuttering_embedding_input_valid_transition_item :
  forall s item,
    input_valid_transition_item X s item ->
    finite_valid_trace_from_to Y (state_project s) (state_project (destination item))
      (transition_item_project item)
  := VLSM_weak_stuttering_embedding_input_valid_transition_item VLSM_stuttering_embedding_weaken.

Definition VLSM_stuttering_embedding_finite_valid_trace_from_to :
  forall sX s'X trX,
    finite_valid_trace_from_to X sX s'X trX ->
    finite_valid_trace_from_to Y (state_project sX) (state_project s'X)
      (VLSM_stuttering_embedding_finite_trace_project Hsimul trX)
  := VLSM_weak_stuttering_embedding_finite_valid_trace_from_to VLSM_stuttering_embedding_weaken.

Definition VLSM_stuttering_embedding_in_futures :
  forall s1 s2,
    in_futures X s1 s2 -> in_futures Y (state_project s1) (state_project s2)
  := VLSM_weak_stuttering_embedding_in_futures VLSM_stuttering_embedding_weaken.

Definition VLSM_stuttering_embedding_infinite_valid_trace_from :
  forall sX trX (Hinf : InfinitelyOften _ trX),
    infinite_valid_trace_from X sX trX ->
    infinite_valid_trace_from Y (state_project sX)
      (VLSM_stuttering_embedding_infinite_trace_project Hsimul trX Hinf)
  := VLSM_weak_stuttering_embedding_infinite_valid_trace_from VLSM_stuttering_embedding_weaken.

Definition VLSM_stuttering_embedding_infinite_finite_valid_trace_from :
  forall sX trX (Hfin : FinitelyManyBound _ trX),
    infinite_valid_trace_from X sX trX ->
    finite_valid_trace_from Y (state_project sX)
      (VLSM_stuttering_embedding_infinite_finite_trace_project Hsimul trX Hfin)
  := VLSM_weak_stuttering_embedding_infinite_finite_valid_trace_from VLSM_stuttering_embedding_weaken.

Lemma VLSM_stuttering_embedding_initial_state :
  forall sX, vinitial_state_prop X sX -> vinitial_state_prop Y (state_project sX).
Proof.
  by intros; eapply VLSM_partial_projection_initial_state;
    [apply VLSM_partial_projection_from_stuttering_embedding | ..].
Qed.

Lemma VLSM_stuttering_embedding_finite_valid_trace_init_to :
  forall sX s'X trX,
    finite_valid_trace_init_to X sX s'X trX ->
    finite_valid_trace_init_to Y (state_project sX) (state_project s'X)
      (VLSM_stuttering_embedding_finite_trace_project Hsimul trX).
Proof.
  intros * []; split.
  - by apply VLSM_stuttering_embedding_finite_valid_trace_from_to.
  - by apply VLSM_stuttering_embedding_initial_state.
Qed.

Lemma VLSM_stuttering_embedding_infinite_valid_trace :
  forall sX trX (Hinf : InfinitelyOften _ trX),
    infinite_valid_trace X sX trX ->
    infinite_valid_trace Y (state_project sX)
      (VLSM_stuttering_embedding_infinite_trace_project Hsimul trX Hinf).
Proof.
  intros sX trX Hinf [HtrX HsX].
  split.
  - by apply VLSM_stuttering_embedding_infinite_valid_trace_from.
  - by apply VLSM_stuttering_embedding_initial_state.
Qed.

Lemma VLSM_stuttering_embedding_infinite_finite_valid_trace :
  forall sX trX (Hfin : FinitelyManyBound _ trX),
    infinite_valid_trace X sX trX ->
    finite_valid_trace Y (state_project sX)
      (VLSM_stuttering_embedding_infinite_finite_trace_project Hsimul trX Hfin).
Proof.
  intros sX trX Hfin [HtrX HsX].
  split.
  - by apply VLSM_stuttering_embedding_infinite_finite_valid_trace_from.
  - by apply VLSM_stuttering_embedding_initial_state.
Qed.

(** ** Stuttering embedding friendliness

  A stuttering embedding is friendly if all the valid traces of the destination VLSM
  are prefixes of translations of the valid traces of the source VLSM.
*)

Section sec_stuttering_embedding_friendliness.

(**
  We axiomatize stuttering embedding friendliness as the converse of
  [VLSM_stuttering_embedding_finite_valid_trace]. However, since a transition
  in the source corresponds to possibly multiple transitions in the destination,
  we'll ask that any valid trace in the destination is the prefix of a
  translation of a valid trace from the source.
*)
Definition stuttering_embedding_friendly_prop : Prop :=
  forall
    (sY : vstate Y)
    (trY : list (vtransition_item Y))
    (HtrY : finite_valid_trace Y sY trY),
  exists (sX : vstate X) (trX : list (vtransition_item X)),
    finite_valid_trace X sX trX
    /\ state_project sX = sY
    /\ trY `prefix_of` VLSM_stuttering_embedding_finite_trace_project Hsimul trX.

Lemma stuttering_embedding_friendly_finite_valid_trace_from_to
  (Hfr : stuttering_embedding_friendly_prop)
  (sY1 sY2 : vstate Y) (trY : list (vtransition_item Y))
  (HtrY : finite_valid_trace_from_to Y sY1 sY2 trY)
  : exists (sX1 sX2 : vstate X) (trX : list (vtransition_item X))
      (preY sufY : list (vtransition_item Y)),
      finite_valid_trace_from_to X sX1 sX2 trX /\
      VLSM_stuttering_embedding_finite_trace_project Hsimul trX = preY ++ trY ++ sufY.
Proof.
  apply finite_valid_trace_from_to_complete_left in HtrY
    as (is & tr_s1 & Htr & _).
  apply valid_trace_forget_last, Hfr in Htr as [isX [trX [[Htr _] [His [suf Htr_pr]]]]].
  exists isX, (finite_trace_last isX trX), trX, tr_s1, suf.
  split.
  - by apply valid_trace_add_default_last.
  - by rewrite app_assoc.
Qed.

(**
  A consequence of the [stuttering_embedding_friendly_prop]erty is that the valid
  traces of the target VLSM are precisely prefixes of translations of all
  the valid traces of the source VLSM.
*)
Lemma stuttering_embedding_friendly_trace_char
  (Hfriendly : stuttering_embedding_friendly_prop)
  : forall sY trY, finite_valid_trace Y sY trY <->
    exists (sX : vstate X) (trX : list (vtransition_item X)),
    finite_valid_trace X sX trX
    /\ state_project sX = sY
    /\ trY `prefix_of` VLSM_stuttering_embedding_finite_trace_project Hsimul trX.
Proof.
  split; [by apply Hfriendly |].
  intros (sX & trX & HtrX & <- & sufY & HtrY).
  apply VLSM_stuttering_embedding_finite_valid_trace in HtrX as [HtrX].
  split; [| done].
  eapply finite_valid_trace_from_app_iff.
  by rewrite <- HtrY.
Qed.

End sec_stuttering_embedding_friendliness.

End sec_stuttering_embedding_properties.

(**
  To establish a stuttering embedding from VLSM <<X>> to VLSM <<Y>>,
  the following set of conditions is sufficient:
  - <<X>>'s [initial_state]s project to <<Y>>'s [initial state]s
  - Every input-valid transition translates to a valid trace from the translation
    of the source of the transition to the translation of the destination
    of the transition
*)

Section sec_basic_VLSM_stuttering_embedding.

Section sec_strong_VLSM_stuttering_embedding_type.

Context
  {message : Type}
  (X : VLSM message)
  (TY : VLSMType message)
  (state_project : vstate X -> @state _ TY)
  (transition_item_project : vtransition_item X -> list (@transition_item _ TY))
  .

Lemma strong_VLSM_stuttering_embedding_type
  (Htransition : strong_transition_item_project_consistency state_project transition_item_project)
  : VLSM_stuttering_embedding_type X TY state_project transition_item_project.
Proof. by constructor; intros ? [] []; apply Htransition. Qed.

End sec_strong_VLSM_stuttering_embedding_type.

Context
  {message : Type}
  (X Y : VLSM message)
  (state_project : vstate X -> vstate Y)
  (transition_item_project : vtransition_item X -> list (vtransition_item Y))
  (Htransition : stuttering_embedding_input_valid_transition_item_validity
    X Y state_project transition_item_project)
  .

Lemma basic_VLSM_stuttering_embedding_type :
  VLSM_stuttering_embedding_type X (type Y) state_project transition_item_project.
Proof.
  constructor; intros.
  by eapply finite_valid_trace_from_to_last, Htransition.
Qed.

Section sec_weak_stuttering_embedding.

Context
  (Hstate : weak_stuttering_embedding_initial_state_preservation X Y state_project)
  .

#[local] Lemma basic_VLSM_stuttering_embedding_finite_valid_trace_init_to
  is s tr
  (Htr : finite_valid_trace_init_to X is s tr)
  : finite_valid_trace_from_to Y (state_project is) (state_project s)
      (pre_VLSM_stuttering_embedding_finite_trace_project transition_item_project tr).
Proof.
  induction Htr using finite_valid_trace_init_to_rev_ind; [by constructor; apply Hstate |].
  rewrite pre_VLSM_stuttering_embedding_finite_trace_project_app.
  apply finite_valid_trace_from_to_app with (state_project s); [done |].
  cbn; rewrite app_nil_r.
  remember {| l := _ |} as itemX; replace sf with (destination itemX) by (subst; done).
  by apply Htransition; subst.
Qed.

#[local] Lemma basic_VLSM_stuttering_embedding_finite_valid_trace_from
  (s : state)
  (ls : list transition_item)
  (Hpxt : finite_valid_trace_from X s ls)
  : finite_valid_trace_from Y (state_project s)
      (pre_VLSM_stuttering_embedding_finite_trace_project transition_item_project ls).
Proof.
  apply valid_trace_add_default_last,
    finite_valid_trace_from_to_complete_left
    in Hpxt as (is_s & tr_s & Htr & Heqs).
  replace (state_project s) with
    (finite_trace_last (state_project is_s)
      (pre_VLSM_stuttering_embedding_finite_trace_project transition_item_project tr_s)).
  - eapply valid_trace_forget_last, finite_valid_trace_from_to_app_split.
    rewrite <- pre_VLSM_stuttering_embedding_finite_trace_project_app.
    by apply basic_VLSM_stuttering_embedding_finite_valid_trace_init_to.
  - subst s; apply pre_VLSM_stuttering_embedding_finite_trace_last.
    + by apply basic_VLSM_stuttering_embedding_type.
    + by eapply valid_trace_forget_last, finite_valid_trace_from_to_app_split, Htr.
Qed.

Lemma basic_VLSM_weak_stuttering_embedding :
  VLSM_weak_stuttering_embedding X Y state_project transition_item_project.
Proof.
  constructor.
  - by apply basic_VLSM_stuttering_embedding_type.
  - by apply basic_VLSM_stuttering_embedding_finite_valid_trace_from.
Qed.

End sec_weak_stuttering_embedding.

Lemma basic_VLSM_weak_stuttering_embedding_strengthen
  (Hweak : VLSM_weak_stuttering_embedding X Y state_project transition_item_project)
  (Hstate : strong_stuttering_embedding_initial_state_preservation X Y state_project)
  : VLSM_stuttering_embedding X Y state_project transition_item_project.
Proof.
  constructor; [by apply Hweak |].
  intros sX trX [HtrX HsX].
  split.
  - by apply (VLSM_weak_stuttering_embedding_finite_valid_trace_from Hweak).
  - by apply Hstate.
Qed.

Lemma basic_VLSM_stuttering_embedding
  (Hstate : strong_stuttering_embedding_initial_state_preservation X Y state_project)
  : VLSM_stuttering_embedding X Y state_project transition_item_project.
Proof.
  apply basic_VLSM_weak_stuttering_embedding_strengthen; [| done].
  apply basic_VLSM_weak_stuttering_embedding.
  by apply strong_stuttering_embedding_initial_state_preservation_weaken.
Qed.

End sec_basic_VLSM_stuttering_embedding.
