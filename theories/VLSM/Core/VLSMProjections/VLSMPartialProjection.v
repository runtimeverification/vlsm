From Cdcl Require Import Itauto.
From stdpp Require Import prelude.
From VLSM.Lib Require Import Preamble.
From VLSM.Core Require Import VLSM.

Section sec_VLSM_partial_projection.

(** * VLSM Partial Projections

  A generic notion of VLSM projection. We say that VLSM <<X>> partially projects to
  VLSM <<Y>> (sharing the same messages) if there exists a partial map <<partial_trace_project>>
  from traces over <<X>> (pairs of state and list of transitions from that state)
  to traces over <<Y>> such that:

  - [partial_trace_project_preserves_valid_trace]s, if the projection is defined.

  - The projection operation is stable to adding valid prefixes (property
  [partial_trace_project_extends_left]). More precisely, if the projection of a
  trace <<(sX, tX)>> yields <<(sY, tY)>>, then for any trace <<(s'X, preX)>> ending in <<sX>>
  such that <<(s'X, preX ++ tX)>> is a valid trace, then there exists a
  trace <<(s'Y, preY)>> ending in <<sY>> such that <<(s'X, preX ++ tX)>> projects
  to <<(s'Y, preY ++ tY)>>.

  Proper examples of partial projections (which are not [VLSM_projection]s) are
  the projections from the compositions of equivocators to the composition
  of regular nodes guided by a specific start [MachineDescriptor] (see, e.g.,
  [equivocators_no_equivocations_vlsm_X_vlsm_partial_projection]).
*)

Record VLSM_partial_projection_type
  {message : Type}
  (X Y : VLSM message)
  (partial_trace_project :
    vstate X * list (vtransition_item X) -> option (vstate Y * list (vtransition_item Y)))
  : Prop :=
{
  partial_trace_project_extends_left :
    forall sX trX sY trY,
    partial_trace_project (sX, trX) = Some (sY, trY) ->
    forall s'X preX,
      finite_trace_last s'X preX = sX ->
      finite_valid_trace_from X s'X (preX ++ trX) ->
      exists s'Y preY,
        partial_trace_project (s'X, preX ++ trX) = Some (s'Y, preY ++ trY) /\
        finite_trace_last s'Y preY = sY;
}.

(**
  We define two kinds of partial projection: [VLSM_weak_partial_projection]
  and [VLSM_partial_projection], the main difference between them being that the
  "weak" one is not required to preserve initial states.

  Although there are no current examples of proper [VLSM_weak_partial_projection]s,
  their definition serves as a support base for [VLSM_weak_projection]s.
*)
Record VLSM_weak_partial_projection
  {message : Type}
  (X Y : VLSM message)
  (partial_trace_project :
    vstate X * list (vtransition_item X) -> option (vstate Y * list (vtransition_item Y)))
  : Prop :=
{
  weak_partial_projection_type :> VLSM_partial_projection_type X Y partial_trace_project;
  weak_partial_trace_project_preserves_valid_trace :
    forall sX trX sY trY,
      partial_trace_project (sX, trX) = Some (sY, trY) ->
      finite_valid_trace_from X sX trX -> finite_valid_trace_from Y sY trY;
}.

Record VLSM_partial_projection
  {message : Type}
  (X Y : VLSM message)
  (partial_trace_project :
    vstate X * list (vtransition_item X) -> option (vstate Y * list (vtransition_item Y)))
  : Prop :=
{
  partial_projection_type :> VLSM_partial_projection_type X Y partial_trace_project;
  partial_trace_project_preserves_valid_trace :
    forall sX trX sY trY,
      partial_trace_project (sX, trX) = Some (sY, trY) ->
      finite_valid_trace X sX trX -> finite_valid_trace Y sY trY;
}.

Section sec_weak_partial_projection_properties.

(** ** Weak partial projection properties *)

Context
  {message : Type}
  {X Y : VLSM message}
  {trace_project :
    vstate X * list (vtransition_item X) -> option (vstate Y * list (vtransition_item Y))}
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
  spec Hpr_extends_left; [by rewrite app_nil_r |].
  destruct Hpr_extends_left as [isY [preY [Hpr_tr HsY]]].
  rewrite !app_nil_r in Hpr_tr.
  specialize (VLSM_weak_partial_projection_finite_valid_trace_from _ _ _ _ Hpr_tr HtrX)
    as Hinit_to.
  by apply finite_valid_trace_from_app_iff, proj1, finite_valid_trace_last_pstate in Hinit_to; subst.
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
  ; [| by destruct itemX].
  by inversion_clear HtX.
Qed.

Lemma VLSM_weak_partial_projection_input_valid
  : forall sX itemX, input_valid_transition_item X sX itemX ->
    forall sY itemY, trace_project (sX, [itemX]) = Some (sY, [itemY]) ->
    input_valid Y (l itemY) (sY, input itemY).
Proof.
  intros sX itemX HitemX sY itemY Hpr.
  by eapply VLSM_weak_partial_projection_input_valid_transition.
Qed.

End sec_weak_partial_projection_properties.

Section sec_partial_projection_properties.

(** ** Partial projection properties *)

Context
  {message : Type}
  {X Y : VLSM message}
  {trace_project :
    vstate X * list (vtransition_item X) -> option (vstate Y * list (vtransition_item Y))}
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
  spec Hpr_extends_left; [by apply proj1 in Htr'X |].
  destruct Hpr_extends_left as [isY [preY [Hpr_tr' HsY]]].
  specialize (VLSM_partial_projection_finite_valid_trace _ _ _ _ Hpr_tr' Htr'X)
    as Hinit_to.
  by apply proj1, finite_valid_trace_from_app_iff, proj2 in Hinit_to; subst.
Qed.

Lemma VLSM_partial_projection_initial_state
  : forall sX sY trY,
    trace_project (sX, []) = Some (sY, trY) ->
    vinitial_state_prop X sX -> vinitial_state_prop Y sY.
Proof.
  intros sX sY trY Hpr HsX.
  eapply VLSM_partial_projection_finite_valid_trace; [done |].
  split; [| done].
  by constructor; apply initial_state_is_valid.
Qed.

Definition VLSM_partial_projection_weaken : VLSM_weak_partial_projection X Y trace_project :=
  {| weak_partial_projection_type := partial_projection_type _ _ _ Hsimul
  ;  weak_partial_trace_project_preserves_valid_trace :=
       VLSM_partial_projection_finite_valid_trace_from
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
  := VLSM_weak_partial_projection_input_valid VLSM_partial_projection_weaken.

End sec_partial_projection_properties.

End sec_VLSM_partial_projection.
