From stdpp Require Import prelude.
From Coq Require Import FinFun.
From VLSM.Lib Require Import Preamble ListExtras.
From VLSM.Core Require Import VLSM VLSMProjections Composition ProjectionTraces.

(** * VLSM Projection Validators

In the sequel we fix a VLSMs <<X>> and <<Y>> and a [VLSM_projection]
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
non-[projection_induced_valid]itiy implied non-component-[valid]ity
(or non-reachability).
*)

Definition projection_validator_received_messages_prop :=
  forall (li : vlabel Y) (si : vstate Y) (mi : message),
    ~ projection_induced_valid X (type Y) label_project state_project li (si, Some mi)
    -> ~ input_valid PreY li (si, Some mi).

(**
We can slightly generalize the definition above to also include empty messages
and state it in a positive manner as the [projection_validator_prop]erty below,
requiring that [valid]ity in the component (for reachable states) implies
[projection_induced_valid]ity.
*)

Definition projection_validator_prop :=
  forall li si omi,
    input_valid PreY li (si,omi) ->
    projection_induced_valid X (type Y) label_project state_project li (si,omi).

(**
It is easy to see that the [projection_validator_prop]erty includes the
[projection_validator_received_messages_prop]erty.
*)
Lemma projection_validator_messages_received
  : projection_validator_prop -> projection_validator_received_messages_prop.
Proof.
  unfold projection_validator_prop, projection_validator_received_messages_prop.
  intuition.
Qed.

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

(**
Next two results show that the (simpler) [projection_validator_prop]erty
is equivalent with the [transition_validator] property.
*)

Lemma projection_validator_messages_transitions
  : projection_validator_prop -> transition_validator.
Proof.
  intros Hvalidator li si omi Hpvi.
  specialize (Hvalidator _ _ _ Hpvi)
    as [l [s [Hli [Hsi [Hps [Hopm Hvalid]]]]]].
  exists l, s.
  unfold input_valid_transition.
  destruct (transition _ _ ) as (s', om').
  exists s', om'.
  repeat split; assumption.
Qed.

Lemma transition_validator_messages
  : transition_validator -> projection_validator_prop.
Proof.
  intros Hvalidator li si omi Hpvi.
  specialize (Hvalidator _ _ _ Hpvi)
    as [l [s [s' [om' [[Hvalid Htransition] [Hli Hsi]]]]]].
  exists l, s.
  intuition.
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
  intros l s im [lX [sX [Hlx [<- Hv]]]].
  replace (vtransition Y _ _) with
    (state_project (vtransition X lX (sX, im)).1, (vtransition X lX (sX, im)).2).
  - eapply proj2, (VLSM_projection_input_valid_transition Hproji) with (lY := l)
    ; [eassumption|].
    split; [assumption|].
    apply injective_projections; reflexivity.
  - symmetry.
    eapply proj2, (VLSM_projection_input_valid_transition Hproj) with (lY := l)
    ; [eassumption|].
    split; [assumption|].
    apply injective_projections; reflexivity.
Qed.

Lemma induced_projection_incl_preloaded_with_all_messages
  : VLSM_incl Xi PreY.
Proof.
  apply basic_VLSM_incl.
  - intros is [s [<- Hs]].
    apply (VLSM_projection_initial_state Hproj).
    assumption.
  - intro; intros. apply any_message_is_valid_in_preloaded.
  - intros l s om [_ [_ [lX [sX [Hlx [<- Hv]]]]]] _ _.
    simpl.
    eapply proj2, proj2, (VLSM_projection_input_valid Hproj); eassumption.
  - intros l s im s' om [[_ [_ HvXi]] HtXi].
    setoid_rewrite <- HtXi.
    symmetry.
    apply projection_induced_valid_transition_eq.
    assumption.
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
    exists (state_lift s).
    split; [apply Hstate_lift|].
    apply Hinitial_lift.
    assumption.
  - destruct Ht as [[_ [_ Hvalid]] Htrans].
    specialize (Hvalidator _ _ _ Hvalid IHHs)
      as [lX [sX [HlX [HsX HvX]]]].
    replace s' with (state_project (vtransition X lX (sX, om)).1).
    + eapply input_valid_transition_destination,
        (VLSM_projection_input_valid_transition Hproji);
      [exact HlX|].
      split; [exact HvX|].
      apply injective_projections; reflexivity.
    + assert (HivtX : input_valid_transition X lX (sX, om) (vtransition X lX (sX, om)))
        by (split; [assumption|reflexivity]).
      destruct (vtransition _ _ _) as (sX', _om').
      apply (VLSM_projection_input_valid_transition Hproj) with (lY := l)
        in HivtX as [_ Hs']
      ; [|assumption].
      rewrite HsX in Hs'.
      destruct Y as (TY, (SY, MY)).
      cbv in Htrans, Hs'.
      rewrite Htrans in Hs'.
      inversion Hs'.
      reflexivity.
Qed.

(** Below we show that the two definitions above are actually equivalent. *)
Lemma projection_validator_prop_alt_iff
  : projection_validator_prop_alt <-> projection_validator_prop.
Proof.
  split.
  - intros Hvalidator l si om Hvalid.
    apply Hvalidator; [apply Hvalid|].
    apply validator_alt_free_states_are_projection_states; [assumption..|].
    apply Hvalid.
  - intros Hvalidator l si om Hvalid HXisi.
    apply Hvalidator.
    repeat split; [| apply any_message_is_valid_in_preloaded | assumption].
    revert HXisi.
    apply VLSM_incl_valid_state.
    apply induced_projection_incl_preloaded_with_all_messages.
Qed.

Lemma validator_free_states_are_projection_states
  : projection_validator_prop ->
    forall s, valid_state_prop PreY s -> valid_state_prop Xi s.
Proof.
  rewrite <- projection_validator_prop_alt_iff by assumption.
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
    apply Hinitial_lift.
    apply HtrY.
  - induction HtrY using finite_valid_trace_rev_ind.
    + apply (finite_valid_trace_from_empty Xi).
      apply initial_state_is_valid.
      exists (state_lift si).
      split; [apply Hstate_lift|].
      apply Hinitial_lift.
      assumption.
    + apply (extend_right_finite_trace_from Xi);[assumption|].
      split.
      * apply induced_projection_valid_is_input_valid; [assumption|].
        apply Hvalidator.
        apply Hx.
      * replace (sf, _) with (vtransition Y l (finite_trace_last si tr, iom))
          by apply Hx.
        apply projection_induced_valid_transition_eq.
        apply Hvalidator.
        apply Hx.
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
  {index : Type}
  {IndEqDec : EqDecision index}
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
  forall (li : vlabel (IM i)) (siomi : vstate (IM i) * option message),
    input_valid (pre_loaded_with_all_messages_vlsm (IM i)) li siomi ->
    vvalid Xi li siomi.

Lemma component_projection_to_preloaded
  : VLSM_projection X PreXi (composite_project_label IM i) (fun s => s i).
Proof.
  constructor.
  - apply component_projection.
  - intros sX trX HtrX.
    apply (VLSM_projection_finite_valid_trace (preloaded_component_projection IM i)).
    revert HtrX.
    apply VLSM_incl_finite_valid_trace.
    apply constraint_preloaded_free_incl with (constraint0 := constraint).
Qed.

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
      (lift_to_composite_label IM i) (lift_to_composite_state IM i)))
  ; [|apply VLSM_eq_sym; apply composite_vlsm_constrained_projection_is_induced].
  apply pre_loaded_with_all_messages_validator_proj_eq.
  - apply component_projection_to_preloaded.
  - apply component_transition_projection_None.
  - apply component_label_projection_lift.
  - apply component_state_projection_lift.
  - intro s. apply (lift_to_composite_state_initial IM).
  - apply component_transition_projection_Some.
  - intros li si omi Hiv.
    apply Hvalidator in Hiv as [sX [<- HivX]].
    exists (existT i li), sX.
    intuition.
    unfold composite_project_label.
    simpl.
    case_decide as Hi; [|contradiction].
    replace Hi with (@eq_refl index i) by (apply Eqdep_dec.UIP_dec; assumption).
    reflexivity.
Qed.

Definition pre_loaded_with_all_messages_validator_component_proj_incl
  (Hvalidator : component_projection_validator_prop)
  : VLSM_incl PreXi Xi :=
  VLSM_eq_proj1 (pre_loaded_with_all_messages_validator_component_proj_eq Hvalidator).

End component_projection_validator.

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
  destruct X as [T [S M]]. simpl in *.
  (* redcuction to inclusion of finite traces. *)
  apply VLSM_incl_finite_traces_characterization.
  intros.
  split; [|apply H].
  destruct H as [Htr Hs].
  (* reverse induction on the length of a trace. *)
  induction tr using rev_ind.
  - constructor. apply initial_state_is_valid. assumption.
  - apply finite_valid_trace_from_app_iff in Htr.
    destruct Htr as [Htr Hx].
    specialize (IHtr Htr).
    apply (finite_valid_trace_from_app_iff (mk_vlsm M)).
    split; [assumption|].
    apply (first_transition_valid (mk_vlsm M)).
    apply first_transition_valid in Hx.
    destruct Hx as [Hvx Htx].
    split; [|assumption].
    (* using the [self_validator_vlsm_prop]erty. *)
    revert Hvx.
    apply Hvalidator.
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
    destruct X as (T, (S, M)).
    apply Hincl.
Qed.

End self_validator_vlsm.
