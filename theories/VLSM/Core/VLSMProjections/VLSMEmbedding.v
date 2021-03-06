From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From Coq Require Import FunctionalExtensionality.
From VLSM.Lib Require Import Preamble ListExtras StreamExtras StreamFilters.
From VLSM.Core Require Import VLSM VLSMProjections.VLSMTotalProjection.

Section VLSM_full_projection.

(** * VLSM Full Projection (Embedding)

A VLSM projection guaranteeing the existence of projection for all labels and
states, and the full correspondence between [transition_item]s.
We say that VLSM <<X>> fully projects (embeds) into VLSM <<Y>> (sharing the same messages)
if there exist maps <<label_project>> taking <<X>>-labels to <<Y>>-labels
and <<state_project>> taking <<X>>-states to <<Y>>-states, such that the
[finite_valid_trace_prop]erty is preserved by the trace
transformation induced by the label and state projection functions,
in which each <<X>>-[transition_item] is projected to an <<Y>>-[transition_item]
preserving the messages and transforming labels and states accordingly.

Besides [VLSM_incl]usions, which are a prototypical example of VLSM embeddings,
we can also prove "lifting" relations between components and the composition
that they are part of as being full projections (see, e.g.,
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
  : forall s, InfinitelyOften (is_Some ??? (Some ??? label_project ??? l)) s.
Proof.
  cofix H. intros (a, s). constructor; simpl; [|apply H].
  apply Streams.Here. by eexists.
Qed.

Lemma pre_VLSM_full_projection_infinite_trace_project_EqSt
  : forall s (Hinf := pre_VLSM_full_projection_infinite_trace_project_infinitely_often s),
  Streams.EqSt (pre_VLSM_full_projection_infinite_trace_project s) (pre_VLSM_projection_infinite_trace_project _ _ (Some ??? label_project) state_project s Hinf).
Proof.
  intros.
  apply stream_map_option_EqSt.
Qed.

Lemma pre_VLSM_full_projection_finite_trace_last
  : forall sX trX,
    state_project (finite_trace_last sX trX) = finite_trace_last (state_project sX) (pre_VLSM_full_projection_finite_trace_project trX).
Proof.
  intros.
  destruct_list_last trX trX' lst HtrX; [done |].
  by setoid_rewrite map_app; cbn; rewrite !finite_trace_last_is_last.
Qed.

Lemma pre_VLSM_full_projection_finite_trace_last_output :
  forall trX,
    finite_trace_last_output trX
      =
    finite_trace_last_output (pre_VLSM_full_projection_finite_trace_project trX).
Proof.
  intros trX.
  destruct_list_last trX trX' lst HtrX; [done |].
  by setoid_rewrite map_app; simpl; rewrite !finite_trace_last_output_is_last.
Qed.

End pre_definitions.

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
    weak_projection_valid_preservation X Y (Some ??? label_project) state_project.
Proof.
  intros Hvalid lX lY Hl.
  inversion_clear Hl. apply Hvalid.
Qed.

Definition strong_full_projection_valid_preservation : Prop :=
  forall (l : label) (s : state) (om : option message),
    vvalid X l (s, om) -> vvalid Y (label_project l) ((state_project s), om).

Lemma strong_projection_valid_preservation_from_full
  : strong_full_projection_valid_preservation ->
    strong_projection_valid_preservation X Y (Some ??? label_project) state_project.
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
    weak_projection_transition_preservation_Some X Y (Some ??? label_project) state_project.
Proof.
  intros Htransition lX lY Hl.
  inversion_clear Hl. apply Htransition.
Qed.

Lemma weak_projection_transition_consistency_None_from_full
  : weak_projection_transition_consistency_None _ _ (Some ??? label_project) state_project.
Proof. inversion 1. Qed.

Definition strong_full_projection_transition_preservation : Prop :=
  forall l s om s' om',
      vtransition X l (s, om) = (s', om') ->
      vtransition Y (label_project l) (state_project s, om) = (state_project s', om').

Lemma strong_projection_transition_preservation_Some_from_full
  : strong_full_projection_transition_preservation ->
    strong_projection_transition_preservation_Some X Y (Some ??? label_project) state_project.
Proof.
  intros Htransition lX lY Hl.
  inversion_clear Hl. apply Htransition.
Qed.

Lemma strong_projection_transition_consistency_None_from_full
  : strong_projection_transition_consistency_None _ _ (Some ??? label_project) state_project.
Proof. inversion 1. Qed.

Lemma strong_full_projection_transition_preservation_weaken
  : strong_full_projection_transition_preservation ->
    weak_full_projection_transition_preservation.
Proof.
  intros Hstrong l s om s' om' Ht.
  apply Hstrong. apply Ht.
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
  by apply initial_message_is_valid.
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
  : VLSM_projection_type X (type Y) (Some ??? label_project) state_project.
Proof.
  split; intros.
  - destruct_list_last trX trX' lstX Heq; [done |].
    apply (pre_VLSM_full_projection_finite_trace_last _).
Qed.

Section weak_projection_properties.

(** ** Weak projection properties *)

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
  : VLSM_weak_projection X Y (Some ??? label_project) state_project.
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
  by apply (VLSM_weak_projection_input_valid_transition VLSM_weak_full_projection_is_projection)
      with (lY := label_project l) in H.
Qed.

Lemma VLSM_weak_full_projection_input_valid l s im
  : input_valid X l (s,im) -> input_valid Y (label_project l) (state_project s,im).
Proof.
  by intros; eapply (VLSM_weak_projection_input_valid VLSM_weak_full_projection_is_projection).
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
  by apply (VLSM_weak_projection_infinite_valid_trace_from VLSM_weak_full_projection_is_projection sX trX).
Qed.

Lemma VLSM_weak_full_projection_can_produce
  (s : state)
  (om : option message)
  : option_can_produce X s om -> option_can_produce Y (state_project s) om.
Proof.
  intros [(s0, im) [l Ht]].
  apply VLSM_weak_full_projection_input_valid_transition in Ht.
  by do 2 eexists.
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
  - apply Hinitial_valid_message in Hinit. by apply initial_message_is_valid.
  - apply emitted_messages_are_valid. revert Hemit. apply VLSM_weak_full_projection_can_emit.
Qed.

End weak_projection_properties.

Section full_projection_properties.

(** ** Full projection properties *)

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
  : VLSM_projection X Y (Some ??? label_project) state_project.
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
    + destruct om as [m|]; [| done]. by apply Hmessage.
Qed.

End full_projection_properties.

End VLSM_full_projection.



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

(** ** Basic full VLSM projection *)

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

(** ** Weak full VLSM projection *)

Context
  (Hstate : weak_projection_initial_state_preservation X Y state_project)
  (Hmessage : weak_full_projection_initial_message_preservation X Y state_project)
  .

Lemma weak_projection_valid_message_preservation_from_full
  : weak_projection_valid_message_preservation X Y (Some ??? label_project) state_project.
Proof.
  intros lX lY Hl s m Hv HsY.
  apply proj2 in Hv as Hom.
  apply proj1 in Hom.
  apply emitted_messages_are_valid_iff in Hom.
  destruct Hom as [Him | Hemit].
  - by apply (Hmessage _ _ _ Hv).
  - apply can_emit_has_trace in Hemit as [is [tr [item [Htr Hm]]]].
    destruct item. simpl in *. subst.
    apply valid_trace_add_default_last in Htr.
    rewrite finite_trace_last_is_last in Htr. simpl in Htr.
    remember (tr ++ _) as tr'.
    cut (option_valid_message_prop Y (Some m)); [done |].
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
        by apply Hstate.
      - subst.
        apply valid_trace_get_last in Htr1 as Hs0.
        rewrite finite_trace_last_is_last in Hs0.
        destruct s_item. simpl in Hs0. subst destination.
        specialize (IHHtr1 _ _ _ _ eq_refl).
        by eexists.
    }
    destruct Hs as [_om Hs].
    assert (Hom : option_valid_message_prop Y iom).
    { destruct iom as [im|]; [|apply option_valid_message_None].
      unfold empty_initial_message_or_final_output in Heqiom.
      destruct_list_last iom_tr iom_tr' iom_item Heqiom_tr.
      - by apply (Hmessage _ _ _ (proj1 Ht)); [eexists |].
      - subst.
        apply valid_trace_get_last in Htr2 as Hs0.
        rewrite finite_trace_last_is_last in Hs0.
        destruct iom_item. simpl in *. subst.
        specialize (IHHtr2 _ _ _ _ eq_refl).
        by eexists.
    }
    destruct Hom as [_s Hom].
    apply
      (valid_generated_state_message Y _ _ Hs _ _ Hom (label_project l)).
    + by apply Hvalid; [apply Ht | exists _om | exists _s].
    + by apply Htransition.
Qed.

Lemma basic_VLSM_weak_full_projection : VLSM_weak_full_projection X Y label_project state_project.
Proof.
  specialize (basic_VLSM_weak_projection X Y (Some ??? label_project) state_project) as Hproj.
  spec Hproj; [by apply weak_projection_valid_preservation_from_full|].
  spec Hproj; [by apply weak_projection_transition_preservation_Some_from_full|].
  spec Hproj; [apply weak_projection_transition_consistency_None_from_full|].
  spec Hproj; [done |].
  spec Hproj; [apply weak_projection_valid_message_preservation_from_full|].
  constructor. intro; intros.
  by apply (VLSM_weak_projection_finite_valid_trace_from Hproj) in H.
Qed.

End weak_full_projection.

Lemma basic_VLSM_weak_full_projection_strengthen
  (Hweak : VLSM_weak_full_projection X Y label_project state_project)
  (Hstate : strong_projection_initial_state_preservation X Y state_project)
  : VLSM_full_projection X Y label_project state_project.
Proof.
  constructor. intros sX trX [HtrX HsX].
  split.
  - revert HtrX. apply (VLSM_weak_full_projection_finite_valid_trace_from Hweak).
  - revert HsX. apply Hstate.
Qed.

Lemma basic_VLSM_full_projection
  (Hstate : strong_projection_initial_state_preservation X Y state_project)
  (Hmessage : weak_full_projection_initial_message_preservation X Y state_project)
  : VLSM_full_projection X Y label_project state_project.
Proof.
  apply basic_VLSM_weak_full_projection_strengthen; [| done].
  apply basic_VLSM_weak_full_projection; [| done].
  by apply strong_projection_initial_state_preservation_weaken.
Qed.

End basic_VLSM_full_projection.

Lemma basic_VLSM_strong_full_projection
  {message : Type}
  (X Y : VLSM message)
  (label_project : vlabel X -> vlabel Y)
  (state_project : vstate X -> vstate Y)
  (Hvalid : strong_full_projection_valid_preservation X Y label_project state_project)
  (Htransition : strong_full_projection_transition_preservation X Y label_project state_project)
  (Hstate : strong_projection_initial_state_preservation X Y state_project)
  (Hmessage : strong_full_projection_initial_message_preservation X Y)
  : VLSM_full_projection X Y label_project state_project.
Proof.
  apply basic_VLSM_full_projection.
  - by apply strong_full_projection_valid_preservation_weaken.
  - by apply strong_full_projection_transition_preservation_weaken.
  - done.
  - by apply strong_full_projection_initial_message_preservation_weaken.
Qed.

Lemma basic_VLSM_full_projection_preloaded
  {message : Type}
  (X Y : VLSM message)
  (label_project : vlabel X -> vlabel Y)
  (state_project : vstate X -> vstate Y)
  (Hvalid : strong_full_projection_valid_preservation X Y label_project state_project)
  (Htransition : strong_full_projection_transition_preservation  X Y label_project state_project)
  (Hstate : strong_projection_initial_state_preservation X Y state_project)
  : VLSM_full_projection (pre_loaded_with_all_messages_vlsm X) (pre_loaded_with_all_messages_vlsm Y) label_project state_project.
Proof.
  constructor.
  intros sX trX HtrX.
  split; [|apply Hstate; apply HtrX].
  induction HtrX using finite_valid_trace_rev_ind.
  - constructor. by apply initial_state_is_valid, Hstate.
  - setoid_rewrite map_app. apply finite_valid_trace_from_app_iff.
    split; [done |].
    simpl. apply (finite_valid_trace_singleton (pre_loaded_with_all_messages_vlsm Y)).
    destruct Hx as [[_ [_ Hv]] Ht].
    apply Hvalid in Hv.
    apply Htransition in Ht.
    rewrite (pre_VLSM_full_projection_finite_trace_last _ _ label_project state_project) in Hv, Ht.
    repeat split; [.. | done | done].
    + by apply finite_valid_trace_last_pstate in IHHtrX.
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
  (Hstate : strong_projection_initial_state_preservation X Y state_project)
  (Hmessage : strong_full_projection_initial_message_preservation X Y)
  : VLSM_full_projection (pre_loaded_vlsm X P) (pre_loaded_vlsm Y Q) label_project state_project.
Proof.
  constructor.
  intros sX trX HtrX.
  apply valid_trace_add_default_last in HtrX.
  split; [|apply Hstate; apply HtrX].
  induction HtrX using finite_valid_trace_init_to_rev_strong_ind.
  - constructor. by apply initial_state_is_valid, Hstate.
  - setoid_rewrite map_app. apply finite_valid_trace_from_app_iff.
    split; [done |].
    simpl. apply (finite_valid_trace_singleton (pre_loaded_vlsm Y Q)).
    destruct Ht as [[_ [_ Hv]] Ht].
    apply Hvalid in Hv.
    apply Htransition in Ht.
    apply valid_trace_get_last in HtrX1. subst s.
    rewrite (pre_VLSM_full_projection_finite_trace_last _ _ label_project state_project) in Hv, Ht.
    simpl.
    repeat split; [.. | done | done].
    + by apply finite_valid_trace_last_pstate in IHHtrX1.
    + destruct iom as [m|]; [|apply option_valid_message_None].
      unfold empty_initial_message_or_final_output in Heqiom.
      destruct_list_last iom_tr iom_tr' iom_lst Heqiom_tr
      ; [apply option_initial_message_is_valid; destruct Heqiom as [Him | Hp]|].
      * by left; revert Him; apply Hmessage.
      * by right; auto.
      * apply
          (valid_trace_output_is_valid (pre_loaded_vlsm Y Q) _ _ IHHtrX2 m).
        setoid_rewrite map_app. apply Exists_app. by right; left.
Qed.
