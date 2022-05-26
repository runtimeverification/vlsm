From Cdcl Require Import Itauto. Local Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From Coq Require Import FinFun.
From VLSM.Lib Require Import Preamble ListExtras.
From VLSM.Core Require Import VLSM VLSMProjections Composition ProjectionTraces Equivocation MessageDependencies.

(** * VLSM Projection Validators

In the sequel we fix VLSMs <<X>> and <<Y>> and a [VLSM_projection]
of <<X>> into <<PreY>>, the [pre_loaded_with_all_messages_vlsm] of <<Y>>.
*)

Section projection_validator.

Context
  {message : Type}
  {X Y : VLSM message}
  {label_project : vlabel X -> option (vlabel Y)}
  {state_project : vstate X -> vstate Y}
  (PreY := pre_loaded_with_all_messages_vlsm Y)
  (Hproj : VLSM_projection X PreY label_project state_project)
  .

(**
We say that <<Y>> is a validator for received messages if
[valid]ity in the component (for reachable states) implies
[projection_induced_valid]ity.
*)

Definition projection_validator_prop :=
  forall li si omi,
    input_valid PreY li (si,omi) ->
    projection_induced_valid X (type Y) label_project state_project li (si,omi).

(**
We say that <<Y>> is a [transition_validator] if any [valid]
transition (from a reachable state) in <<Y>> can be "lifted" to
an [input_valid_transition] in <<X>>.
*)
Definition transition_validator :=
  forall lY sY omi, input_valid PreY lY (sY, omi) ->
  exists lX sX sX' om',
   input_valid_transition X lX (sX, omi) (sX', om') /\
   label_project lX = Some lY /\
   state_project sX = sY.

(** A message validator can check within a component whether the message
is valid for the composition.
*)
Definition message_validator_prop :=
  forall li si im,
    input_valid PreY li (si, Some im) ->
    valid_message_prop X im.

(** The [projection_validator_prop]erty is stronger. *)
Lemma projection_validator_is_message_validator
  : projection_validator_prop -> message_validator_prop.
Proof.
  intros Hvalidator li si im Hvi.
  by apply Hvalidator in Hvi as (_ & _ & _ & _ & _ & Him & _).
Qed.

Lemma projection_validator_messages_transitions
  : projection_validator_prop -> transition_validator.
Proof.
  intros Hvalidator li si omi Hpvi.
  specialize (Hvalidator _ _ _ Hpvi)
    as (l & s & Hli & Hsi & Hps & Hopm & Hvalid).
  exists l, s.
  unfold input_valid_transition.
  destruct (transition _ _ ) as (s', om').
  by exists s', om'.
Qed.

Lemma transition_validator_messages
  : transition_validator -> projection_validator_prop.
Proof.
  intros Hvalidator li si omi Hpvi.
  specialize (Hvalidator _ _ _ Hpvi)
    as (l & s & s' & om' & [Hvalid Htransition] & Hli & Hsi).
  exists l, s.
  itauto.
Qed.

(** ** Projection validators and Byzantine behavior

In the sequel we assume that the [projection_induced_vlsm_is_projection] and
that initial states of <<Y>> can be lifted to <<X>>.
*)

Section induced_projection_validators.

Context
  (Htransition_None : weak_projection_transition_consistency_None _ _ label_project state_project)
  (label_lift : vlabel Y -> vlabel X)
  (state_lift : vstate Y -> vstate X)
  (Xi := projection_induced_vlsm X (type Y) label_project state_project label_lift state_lift)
  (Hlabel_lift : induced_projection_label_lift_prop _ _ label_project label_lift)
  (Hstate_lift : induced_projection_state_lift_prop _ _ state_project state_lift)
  (Hinitial_lift : strong_full_projection_initial_state_preservation Y X state_lift)
  (Htransition_consistency : induced_projection_transition_consistency_Some _ _ label_project state_project)
  (Htransition_Some  : weak_projection_transition_consistency_Some _ _ label_project state_project label_lift state_lift
    := basic_weak_projection_transition_consistency_Some _ _ _ _ _ _ Hlabel_lift Hstate_lift Htransition_consistency)
  (Hproji := projection_induced_vlsm_is_projection _ _ _ _ _ _ Htransition_None Htransition_Some)
  .

(** If there is a [VLSM_projection] from <<X>> to <<PreY>> and the
[projection_induced_vlsm_is_projection], then a [transition] [valid] for the
[projection_induced_vlsm] has the same output as the transition on <<Y>>.
*)
Lemma projection_induced_valid_transition_eq
  : forall l s om, vvalid Xi l (s, om) ->
    vtransition Xi l (s, om) = vtransition Y l (s, om).
Proof.
  intros l s im (lX & sX & Hlx & <- & Hv).
  replace (vtransition Y _ _) with
    (state_project (vtransition X lX (sX, im)).1, (vtransition X lX (sX, im)).2).
  - eapply (VLSM_projection_input_valid_transition Hproji); [done |].
    by erewrite injective_projections.
  - symmetry.
    eapply (VLSM_projection_input_valid_transition Hproj); [done |].
    by erewrite injective_projections.
Qed.

Lemma induced_projection_incl_preloaded_with_all_messages
  : VLSM_incl Xi PreY.
Proof.
  apply basic_VLSM_incl.
  - intros is (s & <- & Hs).
    by apply (VLSM_projection_initial_state Hproj).
  - intros l s m Hv HsY HmX. apply any_message_is_valid_in_preloaded.
  - intros l s om (_ & _ & lX & sX & Hlx & <- & Hv) _ _.
    simpl.
    by eapply (VLSM_projection_input_valid Hproj).
  - intros l s im s' om [[_ [_ HvXi]] HtXi].
    setoid_rewrite <- HtXi.
    symmetry.
    by apply projection_induced_valid_transition_eq.
Qed.

(** An alternative formulation of the [projection_validator_prop]erty with a
seemingly stronger hypothesis, states that <<Y>> is a validator for <<X>> if
for any <<li>>, <<si>>, <<iom>> such that <<li valid (si, iom)>> in <<Y>>
and <<si>> is a valid state in the induced projection <<Xi>>,
implies that <<li valid (si, om)>> in the induced projection <<Xi>>
(i.e., [projection_induced_valid]ity).
*)
Definition projection_validator_prop_alt :=
  forall li si iom,
    vvalid Y li (si, iom) ->
    valid_state_prop Xi si ->
    vvalid Xi li (si, iom).

(** Under validator assumptions, all reachable states for component <<Y>> are
valid states in the induced projection <<Xi>>.
*)
Lemma validator_alt_free_states_are_projection_states
  : projection_validator_prop_alt ->
    forall s, valid_state_prop PreY s -> valid_state_prop Xi s.
Proof.
  intros Hvalidator sY Hs.
  induction Hs using valid_state_prop_ind.
  - apply initial_state_is_valid.
    exists (state_lift s). auto.
  - destruct Ht as [[_ [_ Hvalid]] Htrans].
    specialize (Hvalidator _ _ _ Hvalid IHHs)
      as (lX & sX & HlX & HsX & HvX).
    replace s' with (state_project (vtransition X lX (sX, om)).1).
    + eapply input_valid_transition_destination,
        (VLSM_projection_input_valid_transition Hproji)
      ; [|split]; [done | done |].
      by apply injective_projections.
    + assert (HivtX : input_valid_transition X lX (sX, om) (vtransition X lX (sX, om)))
        by firstorder.
      destruct (vtransition _ _ _) as (sX', _om').
      eapply (VLSM_projection_input_valid_transition Hproj) in HivtX as [_ Hs']; [| done].
      rewrite HsX in Hs'.
      destruct Y as (TY & MY); cbv in Htrans, Hs'.
      by rewrite Htrans in Hs'; inversion Hs'.
Qed.

(** Below we show that the two definitions above are actually equivalent. *)
Lemma projection_validator_prop_alt_iff
  : projection_validator_prop_alt <-> projection_validator_prop.
Proof.
  split; intros Hvalidator l si om Hvalid.
  - apply Hvalidator; [apply Hvalid|].
    apply validator_alt_free_states_are_projection_states
    ; [done | apply Hvalid].
  - intro HXisi.
    apply Hvalidator.
    repeat split; [| apply any_message_is_valid_in_preloaded | done].
    revert HXisi.
    apply VLSM_incl_valid_state.
    apply induced_projection_incl_preloaded_with_all_messages.
Qed.

Lemma validator_free_states_are_projection_states
  : projection_validator_prop ->
    forall s, valid_state_prop PreY s -> valid_state_prop Xi s.
Proof.
  rewrite <- projection_validator_prop_alt_iff by done.
  apply validator_alt_free_states_are_projection_states.
Qed.

Section pre_loaded_with_all_messages_validator_proj.
  Context
    (Hvalidator : projection_validator_prop)
    .

(**
We can show that <<PreY>> is included in <<Xi>> by applying the meta-lemma
[VLSM_incl_finite_traces_characterization], and by induction on the length
of a trace. The [projection_validator_prop]erty is used to translate
[input_valid]ity for the PreY machine into the [projection_valid]ity.
*)
Lemma pre_loaded_with_all_messages_validator_proj_incl
  : VLSM_incl PreY Xi.
Proof.
  (* reduce inclusion to inclusion of finite traces. *)
  apply VLSM_incl_finite_traces_characterization.
  intros sY trY HtrY.
  split; cycle 1.
  - exists (state_lift sY).
    split; [apply Hstate_lift|].
    apply Hinitial_lift, HtrY.
  - induction HtrY using finite_valid_trace_rev_ind.
    + apply (finite_valid_trace_from_empty Xi), initial_state_is_valid.
      exists (state_lift si).
      auto.
    + apply (extend_right_finite_trace_from Xi); [done |].
      split.
      * apply induced_projection_valid_is_input_valid; [done |].
        apply Hvalidator, Hx.
      * replace (sf, _) with (vtransition Y l (finite_trace_last si tr, iom))
          by apply Hx.
        apply projection_induced_valid_transition_eq, Hvalidator, Hx.
Qed.

(**
Given that any projection is included in the [pre_loaded_with_all_messages_vlsm]
of its component (Lemma [proj_pre_loaded_with_all_messages_incl]), we conclude
that <<PreY>> and <<Xi>> are trace-equal.  This means that all the
byzantine behavior of a component which is a validator
is exhibited by its corresponding projection.
*)
Lemma pre_loaded_with_all_messages_validator_proj_eq
  : VLSM_eq PreY Xi.
Proof.
  apply VLSM_eq_incl_iff.
  split.
  - apply pre_loaded_with_all_messages_validator_proj_incl.
  - apply induced_projection_incl_preloaded_with_all_messages.
Qed.

End pre_loaded_with_all_messages_validator_proj.

End induced_projection_validators.

End projection_validator.

(** ** Validator properties for the [component_projection].

In this section we specialize the validator-related results to the
components of a composition.
*)

Section component_projection_validator.

Context
  {message : Type}
  `{EqDecision index}
  (IM : index -> VLSM message)
  (constraint : composite_label IM -> composite_state IM * option message -> Prop)
  (X := composite_vlsm IM constraint)
  (i : index)
  (Xi := composite_vlsm_constrained_projection IM constraint i)
  (PreXi := pre_loaded_with_all_messages_vlsm (IM i))
  .

(**
We say that the component <<i>> of X is a validator for received messages if
if [valid]ity in the component (for reachable states) implies [projection_valid]ity.
*)
Definition component_projection_validator_prop :=
  forall (li : vlabel (IM i)) (si : vstate (IM i)) (omi : option message),
    input_valid (pre_loaded_with_all_messages_vlsm (IM i)) li (si, omi) ->
    vvalid Xi li (si, omi).

Lemma component_projection_to_preloaded
  : VLSM_projection X PreXi (composite_project_label IM i) (fun s => s i).
Proof.
  constructor.
  - apply component_projection.
  - intros sX trX HtrX.
    apply (VLSM_projection_finite_valid_trace (preloaded_component_projection IM i)).
    revert HtrX.
    apply VLSM_incl_finite_valid_trace.
    apply (constraint_preloaded_free_incl _ constraint).
Qed.

Lemma component_projection_validator_prop_is_induced
  : component_projection_validator_prop <->
    @projection_validator_prop _ X (IM i) (composite_project_label IM i) (fun s => s i).
Proof.
  split; intros Hvalidator li si omi Hvi.
  - apply (VLSM_eq_input_valid (composite_vlsm_constrained_projection_is_induced IM constraint i)),
          (projection_valid_input_valid IM), Hvalidator, Hvi.
  - apply (VLSM_eq_input_valid (composite_vlsm_constrained_projection_is_induced IM constraint i)).
    revert Hvi; apply VLSM_incl_input_valid, pre_loaded_with_all_messages_validator_proj_incl.
    + apply component_projection_to_preloaded.
    + apply component_transition_projection_None.
    + apply component_label_projection_lift.
    + apply component_state_projection_lift.
    + intros isi; apply (composite_initial_state_prop_lift IM).
    + apply component_transition_projection_Some.
    + done.
Qed.

Definition component_message_validator_prop : Prop :=
  @message_validator_prop _ X (IM i).

(** Assuming the [component_projection_validator_prop]erty, the component
[pre_loaded_with_all_messages_vlsm] is [VLSM_eq]ual (trace-equivalent) with
its corresponding [projection_induced_vlsm].
*)
Lemma pre_loaded_with_all_messages_validator_component_proj_eq
  (Hvalidator : component_projection_validator_prop)
  : VLSM_eq PreXi Xi.
Proof.
  apply VLSM_eq_trans with
    (machine (projection_induced_vlsm X (type (IM i))
      (composite_project_label IM i) (fun s => s i)
      (lift_to_composite_label IM i) (lift_to_composite_state' IM i)))
  ; simpl; [|apply VLSM_eq_sym, composite_vlsm_constrained_projection_is_induced].
  apply pre_loaded_with_all_messages_validator_proj_eq.
  - apply component_projection_to_preloaded.
  - apply component_transition_projection_None.
  - apply component_label_projection_lift.
  - apply component_state_projection_lift.
  - intro s. apply (composite_initial_state_prop_lift IM).
  - apply component_transition_projection_Some.
  - intros li si omi Hiv.
    apply Hvalidator in Hiv as (sX & <- & HivX).
    exists (existT i li), sX.
    unfold composite_project_label; cbn.
    by rewrite (decide_True_pi eq_refl).
Qed.

Definition pre_loaded_with_all_messages_validator_component_proj_incl
  (Hvalidator : component_projection_validator_prop)
  : VLSM_incl PreXi Xi :=
  VLSM_eq_proj1 (pre_loaded_with_all_messages_validator_component_proj_eq Hvalidator).

End component_projection_validator.

(** ** Basic validation condition for free composition

In this section we show (Lemma [valid_free_validating_is_message_validating])
that, under [FullMessageDependencies] assumptions, if the validity predicate
ensures that message itself and all of its dependencies can be emitted using
only its dependencies, then the input message is valid for the free composition,
thus the node itself is a validator for the free composition.
*)

Section free_composition_validators.

Context
  {message : Type}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  `{forall i, HasBeenSentCapability (IM i)}
  `{forall i, HasBeenReceivedCapability (IM i)}
  `{FullMessageDependencies message message_dependencies full_message_dependencies}
  {validator : Type}
  (A : validator -> index)
  (sender : message -> option validator)
  .

(**
The property of a message of having a sender and being emittable by the
component corresponding to its sender pre-loaded with the dependencies of the
message.
*)
Inductive Emittable_from_dependencies_prop (m : message) : Prop :=
  | efdp : forall (v : validator) (Hsender : sender m = Some v),
             can_emit (pre_loaded_vlsm (IM (A v)) (fun dm => dm ∈ message_dependencies m)) m ->
               Emittable_from_dependencies_prop m.

Definition emittable_from_dependencies_prop (m : message) : Prop :=
  match sender m with
  | None => False
  | Some v => can_emit (pre_loaded_vlsm (IM (A v)) (fun dm => dm ∈ message_dependencies m)) m
  end.

Lemma emittable_from_dependencies_prop_iff m
  : Emittable_from_dependencies_prop m <-> emittable_from_dependencies_prop m.
Proof.
  unfold emittable_from_dependencies_prop; split.
  - by inversion 1; rewrite Hsender.
  - destruct (sender m) eqn: Hsender; [by split with v | inversion 1].
Qed.

(**
The property of a message that both itself and all of its dependencies are
emittable from their dependencies.
*)
Definition all_dependencies_emittable_from_dependencies_prop (m : message) : Prop :=
  forall dm, dm ∈ m :: full_message_dependencies m -> Emittable_from_dependencies_prop dm.

(**
The property of requiring that the validity predicate subsumes the
[all_dependencies_emittable_from_dependencies_prop]erty.
*)
Definition valid_all_dependencies_emittable_from_dependencies_prop
  (i : index) : Prop :=
    forall l s m, input_valid (pre_loaded_with_all_messages_vlsm (IM i)) l (s, Some m) ->
      all_dependencies_emittable_from_dependencies_prop m.

(**
If a message can be emitted by a node preloaded with the message's direct
dependencies, and if all the dependencies of the message are valid for the
free composition, then the message itself is valid for the free composition.
*)
Lemma free_valid_from_valid_dependencies
  m i
  (Hm : can_emit (pre_loaded_vlsm (IM i) (fun dm => dm ∈ message_dependencies m)) m)
  (Hdeps :
    forall dm, dm ∈ full_message_dependencies m ->
      valid_message_prop (free_composite_vlsm IM) dm)
  : valid_message_prop (free_composite_vlsm IM) m.
Proof.
  eapply emitted_messages_are_valid, free_valid_preloaded_lifts_can_be_emitted;
    [| done].
  by intros; apply Hdeps, full_message_dependencies_happens_before, msg_dep_happens_before_iff_one;
  left.
Qed.

(**
Any message with the [all_dependencies_emittable_from_dependencies_prop]erty
is valid for the free composition.
*)
Lemma free_valid_from_all_dependencies_emitable_from_dependencies :
  forall m,
    all_dependencies_emittable_from_dependencies_prop m ->
      valid_message_prop (free_composite_vlsm IM) m.
Proof.
  intros m Hm.
  specialize (Hm m) as Hemit; spec Hemit; [left |].
  inversion Hemit as [v _ Hemit']; clear Hemit.
  apply free_valid_from_valid_dependencies with (A v); [done | clear v Hemit'].
  eapply FullMessageDependencies_ind; [done |].
  intros dm Hdm Hdeps.
  specialize (Hm dm); spec Hm; [by right |].
  inversion Hm as [v _ ?]; clear Hm.
  by apply free_valid_from_valid_dependencies with (A v).
Qed.

(**
If a node in a composition satisfies the
[valid_all_dependencies_emittable_from_dependencies_prop]erty, then it also has
the [component_message_validator_prop]erty, that is, it is a validator for the
free composition.
*)
Lemma valid_free_validating_is_message_validating
  : forall i, valid_all_dependencies_emittable_from_dependencies_prop i ->
    component_message_validator_prop IM (free_constraint IM) i.
Proof.
  intros i Hvalidating l s im Hv.
  by eapply free_valid_from_all_dependencies_emitable_from_dependencies, Hvalidating.
Qed.

(**
Under several additional (but regularly used) assumptions, including the
[MessageDependencies] assumptions, the [channel_authentication_prop]erty and the
[no_initial_messages_in_IM_prop]erty, we can show that the
[component_message_validator_prop]erty is fully equivalent to the
[valid_all_dependencies_emittable_from_dependencies_prop]erty.
*)
Lemma valid_free_validating_equiv_message_validating
  `{forall i, MessageDependencies message_dependencies (IM i)}
  (Hchannel : channel_authentication_prop  IM A sender)
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  : forall i, component_message_validator_prop IM (free_constraint IM) i <->
  valid_all_dependencies_emittable_from_dependencies_prop i.
Proof.
  intros; split; [|apply valid_free_validating_is_message_validating].
  intros Hvalidator l s m Hv dm Hdm.
  specialize (Hvalidator l s m Hv).
  inversion Hdm as [|? ? ? Hin]; subst.
  - eapply composite_no_initial_valid_messages_emitted_by_sender in Hvalidator
      as [v [Hsender Hemit]]; [| done | done].
    exists v; [done |].
    eapply message_dependencies_are_sufficient; [typeclasses eauto | done].
  - apply full_message_dependencies_happens_before in Hin.
    eapply msg_dep_happens_before_composite_no_initial_valid_messages_emitted_by_sender
      in Hin as [v [Hsender Hemit]]. 2-6: done.
    exists v; [done |].
    by eapply message_dependencies_are_sufficient.
Qed.

End free_composition_validators.

(** ** VLSM self-validation *)

Section self_validator_vlsm.

Context
  {message : Type}
  (X : VLSM message)
  .

(**
Let us fix a (regular) VLSM <<X>>. <<X>> is a self-validator if for any
arguments satisfying [valid] where the state is reachable in the
[pre_loaded_with_all_messages_vlsm], the arguments are also
a [valid_state] and [valid_message] for the original VLSM.
*)

Definition self_validator_vlsm_prop :=
  forall (l : label) (s : state) (om : option message),
    input_valid (pre_loaded_with_all_messages_vlsm X) l (s, om) ->
    input_valid X l (s, om).

(**
In the sequel we will show that a VLSM with the [self_validator_vlsm_prop]erty
is trace-equal to its associated [pre_loaded_with_all_messages_vlsm], basically
meaning (due to Lemma [byzantine_pre_loaded_with_all_messages]) that all traces
with the [byzantine_trace_prop]erty associated to self-validator VLSMs are also
[valid_trace]s for that VLSM, meaning that the VLSM cannot exhibit
byzantine behavior.
*)

Context
  (Hvalidator : self_validator_vlsm_prop)
  (PreX := pre_loaded_with_all_messages_vlsm X)
  .

(**
Let <<PreX>> be the [pre_loaded_with_all_messages_vlsm] associated to X.
From Lemma [vlsm_incl_pre_loaded_with_all_messages_vlsm] we know that <<X>> is
included in <<PreX>>.

To prove the converse we use the [self_validator_vlsm_prop]erty to
verify the conditions of meta-lemma [VLSM_incl_finite_traces_characterization].
*)

Lemma pre_loaded_with_all_messages_self_validator_vlsm_incl
  : VLSM_incl PreX X.
Proof.
  unfold self_validator_vlsm_prop  in Hvalidator.
  destruct X as (T & M). simpl in *.
  (* redcuction to inclusion of finite traces. *)
  apply VLSM_incl_finite_traces_characterization.
  intros s tr [Htr Hs].
  split; [| done].
  (* reverse induction on the length of a trace. *)
  induction tr using rev_ind.
  - by constructor; apply initial_state_is_valid.
  - apply finite_valid_trace_from_app_iff in Htr as [Htr Hx].
    apply (finite_valid_trace_from_app_iff (mk_vlsm M)).
    split; [by apply IHtr |].
    apply (first_transition_valid (mk_vlsm M)).
    apply first_transition_valid in Hx as [Hvx Htx].
    split; [| done].
    (* using the [self_validator_vlsm_prop]erty. *)
    revert Hvx; apply Hvalidator.
Qed.

(**
We conclude that <<X>> and <<PreX>> are trace-equal.
*)

Lemma pre_loaded_with_all_messages_self_validator_vlsm_eq
  : VLSM_eq PreX X.
Proof.
  split.
  - apply pre_loaded_with_all_messages_self_validator_vlsm_incl.
  - pose (vlsm_incl_pre_loaded_with_all_messages_vlsm X) as Hincl.
    destruct X as (T, M).
    apply Hincl.
Qed.

End self_validator_vlsm.
