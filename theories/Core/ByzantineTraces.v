From stdpp Require Import prelude.
From VLSM.Lib Require Import Preamble.
From VLSM.Core Require Import VLSM VLSMProjections Composition ProjectionTraces Validator.
From VLSM.Core Require Import PreloadedVLSM.

(** * VLSM Byzantine Traces

  In this section, we introduce two definitions of Byzantine traces,
  prove that they are equivalent (lemma [byzantine_alt_byzantine_iff]),
  and then prove that both definitions are equivalent with the definition
  of a valid trace in the corresponding preloaded VLSM
  (lemmas [byzantine_pre_loaded_with_all_messages] and
  [pre_loaded_with_all_messages_alt_eq]).

  Note that, contrary to what one might think, the byzantine trace property
  does not only capture traces exhibiting byzantine behavior, but also all
  valid traces (consequence of lemma [vlsm_incl_pre_loaded_with_all_messages_vlsm]).
  Therefore to avoid confusion we will call _proper byzantine traces_,
  or _traces exhibiting byzantine behavior_ the collection of traces with
  the byzantine trace property but without the valid trace property.

  In the remainder of this section, we fix a VLSM <<M>>.
*)

(** ** Definition and basic properties *)

Section sec_byzantine_traces.

Context
  {message : Type}
  (M : VLSM message)
  .

(**
  The first definition says that a trace has the byzantine trace property
  if it is the projection of a trace which can be obtained by freely composing
  <<M>> with an arbitrary VLSM <<M'>> (over the same set of messages).

  Below, [binary_free_composition_fst] represents the projection of
  the free composition of <<M>> and <<M'>> to the component corresponding
  to <<M>>.
*)
Definition byzantine_trace_prop (tr : Trace M) : Prop :=
  exists (M' : VLSM message),
    valid_trace_prop (binary_free_composition_fst M M') tr.

(**
  The first result says that all traces with the byzantine trace property
  for a VLSM <<M>> are traces of the [pre_loaded_with_all_messages_vlsm]
  associated to <<M>>.
*)
Lemma byzantine_pre_loaded_with_all_messages :
  forall (tr : Trace M),
    byzantine_trace_prop tr ->
    valid_trace_prop (pre_loaded_with_all_messages_vlsm M) tr.
Proof.
  intros tr [M' Htr]; cbn in Htr.
  by apply proj_pre_loaded_with_all_messages_incl in Htr.
Qed.

(** ** An alternative definition

  The alternative definition of byzantine trace property relies on the
  composition of the VLSM with a special VLSM which can produce all messages.

  We will define its type ([emit_any_message_vlsm_type]) and the VLSM itself
  ([emit_any_message_vlsm]) below.

  The labels of [emit_any_message_vlsm] are its messages and there is a single
  state.
*)

Definition emit_any_message_vlsm_type : VLSMType message :=
{|
  label := message;
  state := unit;
|}.

(**
  The single state is the initial state and no messages are initial.
*)

Program Definition emit_any_message_vlsm_s0 : {_ : state emit_any_message_vlsm_type | True} :=
  exist _ tt _.
Next Obligation.
Proof. done. Defined.

#[export] Instance emit_any_message_vlsm_state_inh :
  Inhabited {_ : state emit_any_message_vlsm_type | True} :=
    populate emit_any_message_vlsm_s0.

(**
  The [transition] function of the [emit_any_message_vlsm] generates the
  message given as a label.
*)
Definition emit_any_message_vlsm_transition
  (l : label emit_any_message_vlsm_type)
  (som : state emit_any_message_vlsm_type * option message)
  : state emit_any_message_vlsm_type * option message :=
    (tt, Some l).

(** The [valid]ity predicate specifies that all transitions are valid. *)
Definition emit_any_message_vlsm_valid
  (l : label emit_any_message_vlsm_type)
  (som : state emit_any_message_vlsm_type * option message) : Prop :=
    True.

Definition emit_any_message_vlsm_machine : VLSMMachine emit_any_message_vlsm_type :=
{|
  initial_state_prop := fun _ => True;
  initial_message_prop := fun _ => False;
  transition := emit_any_message_vlsm_transition;
  valid := emit_any_message_vlsm_valid;
|}.

Definition emit_any_message_vlsm : VLSM message :=
  mk_vlsm emit_any_message_vlsm_machine.

(**
  Using the VLSM defined above, we can define the alternative byzantine
  trace property of a trace <<tr>> for the VLSM <<M>> as being a trace
  in the projection of the free composition between <<M>> and the
  [emit_any_message_vlsm], to the component corresponding to <<M>>.
*)
Definition alternate_byzantine_trace_prop (tr : Trace M) : Prop :=
  valid_trace_prop (binary_free_composition_fst M emit_any_message_vlsm) tr.

(**
  Since the byzantine trace property was referring to the free composition
  with any other VLSM, we can instantiate that definition to the
  [emit_any_message_vlsm] to derive that a trace with the
  alternative byzantine trace property also has the byzantine trace property.
*)
Lemma byzantine_alt_byzantine :
  forall (tr : Trace M),
    alternate_byzantine_trace_prop tr ->
    byzantine_trace_prop tr.
Proof.
  by exists emit_any_message_vlsm.
Qed.

(** ** Equivalence between the two Byzantine trace definitions

  In this section we prove that the [alternate_byzantine_trace_prop] is
  equivalent to [byzantine_trace_prop].

  Since we have already proven that [alternate_byzantine_trace_prop]
  implies [byzantine_trace_prop] (lemma [byzantine_alt_byzantine]),
  and since we know that the traces satisfying [byzantine_trace_prop]
  are valid traces for the [pre_loaded_with_all_messages_vlsm], to
  prove the equivalence it is enough to close the circle by proving the
  VLSM inclusion between the [pre_loaded_with_all_messages_vlsm] and the
  projection VLSM used to define [alternate_byzantine_trace_prop].
*)

Section sec_pre_loaded_with_all_messages_byzantine_alt.

(**
  Let <<PreLoaded>> denote the [pre_loaded_with_all_messages_vlsm] of <<M>>,
  let <<Alt>> denote the free composition of <<M>> with the [emit_any_message_vlsm],
  and let <<Alt1>> denote the projection of <<Alt>> to the component of <<M>>.
*)

Context
  (PreLoaded := pre_loaded_with_all_messages_vlsm M)
  (Alt1 := binary_free_composition_fst M emit_any_message_vlsm)
  (Alt := binary_free_composition M emit_any_message_vlsm)
  .

(**
  First, note that using the results above it is easy to prove the inclusion
  of <<Alt1>> into <<Preloaded>>.
*)
Lemma alt_pre_loaded_with_all_messages_incl :
  VLSM_incl Alt1 PreLoaded.
Proof.
  by intros t Hvt; apply byzantine_pre_loaded_with_all_messages, byzantine_alt_byzantine.
Qed.

(**
  To prove the reverse inclusion (between <<PreLoaded>> and <<Alt1>>) we will use the
  [basic_VLSM_incl] meta-result about proving inclusions between
  VLSMs which states that:

  - if all valid messages in the first are valid messages in the second, and
  - if all valid states in the first are also valid states in the second, and
  - if all [input_valid_transition]s in the first are also
    [input_valid_transition]s in the second, then
  - the first VLSM is included in the second.

  First note that _all_ messages are valid for <<Alt>>, as
  [emit_any_message_vlsm] can generate any message without changing state.
*)

Lemma alt_option_valid_message :
  forall (om : option message),
    option_valid_message_prop Alt om.
Proof.
  intros [m |]; [| by apply option_valid_message_None].
  pose (s := ``(vs0 Alt)).
  exists s.
  eapply (valid_generated_state_message Alt)
    with s None s None (existT second _);
    [by apply valid_initial_state, proj2_sig.. | by split |].
  by cbn; state_update_simpl.
Qed.

(** In the projection, all messages are valid. *)
Lemma alt_proj_option_valid_message :
  forall (m : option message),
    option_valid_message_prop Alt1 m.
Proof. by apply any_message_is_valid_in_preloaded. Qed.

(**
  Next we define the "lifting" of a state <<s>> from <<M>> to <<Alt>>,
  by simply setting to <<s>> the  corresponding component of the initial
  (composite) state <<s0>> of <<Alt>>.
*)
Definition lifted_alt_state (s : state M) : state Alt :=
  lift_to_composite_state' (binary_IM M emit_any_message_vlsm) first s.

(** Lifting a valid state of <<PreLoaded>> we obtain a valid state of <<Alt>>. *)
Lemma preloaded_alt_valid_state :
  forall (sj : state PreLoaded) (om : option message),
    valid_state_message_prop PreLoaded sj om ->
    valid_state_prop Alt (lifted_alt_state sj).
Proof.
  intros sj om Hp.
  assert (Hsj : valid_state_prop PreLoaded sj)
    by (exists om; done); clear Hp.
  induction Hsj using valid_state_prop_ind;
    [by apply initial_state_is_valid; intros [] |].
  exists om'.
  eapply (@input_valid_transition_outputs_valid_state_message _ Alt (existT first l)
    (lifted_alt_state s) (lifted_alt_state s') om0).
  repeat split; cbn; [by apply IHHsj | by apply alt_option_valid_message | by apply Ht |].
  unfold lifted_alt_state, lift_to_composite_state', lift_to_composite_state.
  state_update_simpl; cbn in *.
  destruct Ht as [_ Ht]; cbn in Ht; rewrite Ht.
  by rewrite state_update_twice.
Qed.

(**
  Finally, we can use [basic_VLSM_incl] together with the
  results above to show that <<Preloaded>> is included in <<Alt1>>.
*)
Lemma pre_loaded_with_all_messages_alt_incl :
  VLSM_incl PreLoaded Alt1.
Proof.
  apply (basic_VLSM_incl PreLoaded Alt1); intro; intros;
    [done | by apply alt_proj_option_valid_message | | by apply H].
  exists (lifted_alt_state s).
  split; [done |].
  destruct Hv as [[_om Hps] [Hpm Hv]].
  split_and!; [| | done].
  - by apply preloaded_alt_valid_state in Hps.
  - by apply alt_option_valid_message.
Qed.

(** Hence, <<Preloaded>> and <<Alt1>> are actually trace-equivalent. *)
Lemma pre_loaded_with_all_messages_alt_eq :
  VLSM_eq PreLoaded Alt1.
Proof.
  split.
  - by apply pre_loaded_with_all_messages_alt_incl.
  - by apply alt_pre_loaded_with_all_messages_incl.
Qed.

End sec_pre_loaded_with_all_messages_byzantine_alt.

(**
  Finally, we can conclude that the two definitions for byzantine traces are
  equivalent.
*)
Lemma byzantine_alt_byzantine_iff :
  forall (tr : Trace M),
    alternate_byzantine_trace_prop tr <-> byzantine_trace_prop tr.
Proof.
  split; intros.
  - by apply byzantine_alt_byzantine.
  - by apply pre_loaded_with_all_messages_alt_incl, byzantine_pre_loaded_with_all_messages.
Qed.

End sec_byzantine_traces.

(** ** Byzantine fault tolerance for a single validator

  Given that projections of composition of validator VLSMs
  are equivalent to their corresponding VLSM preloaded with all
  messages ([pre_loaded_with_all_messages_validating_proj_eq]),
  we can derive that for validators, all their byzantine traces are
  included in the valid traces of their projection from the composition.
*)

Section sec_single_validator_byzantine_traces.

Context
  {message : Type}
  `{EqDecision index}
  (IM : index -> VLSM message)
  (constraint : composite_label IM -> composite_state IM  * option message -> Prop)
  (i : index)
  (Hvalidator : component_projection_validator_prop IM constraint i)
  .

Lemma validator_component_byzantine_fault_tolerance :
  forall (tr : Trace),
    byzantine_trace_prop (IM i) tr ->
    valid_trace_prop (pre_composite_vlsm_induced_projection_validator IM constraint i) tr.
Proof.
  intros tr Htr.
  eapply VLSM_incl_valid_trace.
  - by apply pre_loaded_with_all_messages_validator_component_proj_incl.
  - by apply byzantine_pre_loaded_with_all_messages in Htr.
Qed.

End sec_single_validator_byzantine_traces.

(** ** Byzantine fault tolerance for a composition of validators

  In this section we show that if all components of a composite VLSM <<X>>
  satisfy [projection_validator_prop], then its byzantine traces (that is,
  traces obtained upon placing this composition in any, possibly adversarial,
  context) are valid traces of <<X>>.
*)

Section sec_composite_validator_byzantine_traces.

(**
  Let us fix an indexed set of VLSMs <<IM>> and their
  constrained composition <<X>>, and let <<PreloadedX>> be
  the [pre_loaded_with_all_messages_vlsm] associated to <<X>>.
*)

Context
  {message : Type}
  `{EqDecision index}
  (IM : index -> VLSM message)
  (constraint : composite_label IM -> composite_state IM  * option message -> Prop)
  (X := composite_vlsm IM constraint)
  (PreLoadedX := pre_loaded_with_all_messages_vlsm X)
  (Hvalidator : forall i : index, component_message_validator_prop IM constraint i)
  .

(**
  Since we know that <<PreloadedX>> contains precisely the byzantine traces
  of <<X>>, we just need to show that <<PreLoadedX>> is included in <<X>> to
  prove our main result.
*)
Lemma validator_pre_loaded_with_all_messages_incl :
  VLSM_incl PreLoadedX X.
Proof.
  apply VLSM_incl_finite_traces_characterization.
  intros s tr Htr.
  split; [| by apply Htr].
  destruct Htr as [Htr Hs].
  induction Htr using finite_valid_trace_from_rev_ind;
    [by apply (finite_valid_trace_from_empty X), initial_state_is_valid |].
  apply (extend_right_finite_trace_from X); [by apply IHHtr |].
  destruct Hx as [Hvx Htx].
  split; [| done].
  apply finite_valid_trace_last_pstate in IHHtr; [| done].
  repeat split; [done | | by apply Hvx..].
  destruct Hvx as (Hlst & _ & Hv & _).
  destruct l as [i li].
  destruct iom as [im |]; [| by apply option_valid_message_None].
  eapply Hvalidator.
  split_and!; [| | by cbn; apply Hv].
  - by eapply valid_state_project_preloaded_to_preloaded in Hlst.
  - eexists _.
    by apply pre_loaded_with_all_messages_message_valid_initial_state_message.
Qed.

(**
  Finally, we can conclude that a composition of validator components can
  resist any kind of external influence.
*)
Lemma composite_validator_byzantine_traces_are_not_byzantine :
  forall (tr : Trace X),
    byzantine_trace_prop X tr ->
    valid_trace_prop X tr.
Proof.
  intros tr Hbyz.
  apply validator_pre_loaded_with_all_messages_incl.
  by apply byzantine_alt_byzantine_iff, alt_pre_loaded_with_all_messages_incl in Hbyz.
Qed.

End sec_composite_validator_byzantine_traces.
