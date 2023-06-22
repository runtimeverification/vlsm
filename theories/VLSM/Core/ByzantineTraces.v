From stdpp Require Import prelude.
From VLSM.Lib Require Import Preamble.
From VLSM.Core Require Import VLSM VLSMProjections Composition ProjectionTraces Validator.
From VLSM.Core Require Import PreloadedVLSM.

(** * VLSM Byzantine Traces

  In this section, we introduce two definitions of Byzantine traces,
  then show them equivalent (Lemma [byzantine_alt_byzantine_iff]),
  and equivalent with traces on the corresponding pre-loaded VLSM
  (Lemmas [byzantine_pre_loaded_with_all_messages] and [pre_loaded_with_all_messages_alt_eq]).

  Note that, contrary to what one might think, the [byzantine_trace_prop]erty
  does not only capture traces exhibiting byzantine behavior, but also all
  [valid_trace]s (consequence of Lemma [vlsm_incl_pre_loaded_with_all_messages_vlsm]).
  Therefore to avoid confusion we will call _proper byzantine traces_,
  or _traces exhibiting byzantine behavior_ the collection of traces with
  the [byzantine_trace_prop]erty but without the [valid_trace_prop]erty.

  In the remainder of this section, we fix a (regular) VLSM <<M>> with
  signature <<S>> and of type <<T>>.
*)

(** ** Definition and basic properties *)

Section sec_byzantine_traces.

Context
  {message : Type}
  (M : VLSM message)
  .

(**
  The first definition says that a trace has the [byzantine_trace_prop]erty
  if it is the projection of
  a trace which can be obtained by freely composing <<M>> with an arbitrary
  VLSM <<M'>> (of a signature <<S'>> and type <<T'>> over the same set of <<message>>s).

  Below, [binary_free_composition_fst] represents the projection of
  the free composition between <<M>> and <<M'>> to the component corresponding
  to <<M>>.
*)
Definition byzantine_trace_prop
    (tr : Trace M) :=
    exists (M' : VLSM message)
        (Proj := binary_free_composition_fst M M'),
        valid_trace_prop Proj tr.

(**
  The first result says that all traces with the [byzantine_trace_prop]erty
  for a VLSM <<M>> are traces of the [pre_loaded_with_all_messages_vlsm] associated to <<M>>.
*)
Lemma byzantine_pre_loaded_with_all_messages
    (PreLoaded := pre_loaded_with_all_messages_vlsm M)
    (tr : Trace M)
    (Hbyz : byzantine_trace_prop tr)
    : valid_trace_prop PreLoaded tr.
Proof.
  destruct Hbyz as [M' Htr]; simpl in Htr.
  by apply (proj_pre_loaded_with_all_messages_incl _ _ _ _ Htr).
Qed.

(** ** An alternative definition

  The [alternate_byzantine_trace_prop]erty relies on the composition
  of the VLSM with a special VLSM which can produce all messages.

  We will define its type ([all_messages_type]),
  signature ([all_messages_sig]) and the VLSM itself ([emit_any_message_vlsm]) below.

  The type of the [emit_any_message_vlsm] sets the [label] set to consist of all
  <<message>>s and the [state] to consist of a single state (here [tt]).
*)

Definition all_messages_type : VLSMType message :=
    {| label := message
     ; state := unit
    |}.

(**
  The [emit_any_message_vlsm] signature further says that the (single) state is
  initial and no messages are initial. It takes as parameter a <<message>> to
  ensure that the sets of labels and messages are both non-empty.
*)

Program Definition all_messages_s0 : {_ : state all_messages_type | True} :=
  exist _ tt _.
Next Obligation.
Proof. done. Defined.

#[export] Instance all_messages_state_inh : Inhabited {_ : state all_messages_type | True} :=
  populate all_messages_s0.

(**
  The [transition] function of the [emit_any_message_vlsm] generates the
  message given as a label.
*)
Definition all_messages_transition
    (l : label all_messages_type)
    (som : state all_messages_type * option message)
    : state all_messages_type * option message
    := (tt, Some l).

(** The [valid]ity predicate specifies that all transitions are valid. *)
Definition all_messages_valid
    (l : label all_messages_type)
    (som : state all_messages_type * option message)
    : Prop
    := True.

Definition emit_any_message_vlsm_machine
    : VLSMMachine all_messages_type
    :=
    {| initial_state_prop := fun s => True
     ; initial_message_prop := fun m => False
     ; transition := all_messages_transition
     ; valid := all_messages_valid
    |}.

Definition emit_any_message_vlsm
    := mk_vlsm emit_any_message_vlsm_machine.

(**
  Using the VLSM defined above, we can define the [alternate_byzantine_trace_prop]erty
  of a trace <<tr>> for the VLSM <<M>> as being a trace in the projection
  of the free composition between <<M>> and the [emit_any_message_vlsm],
  to the component corresponding to <<M>>.
*)
Definition alternate_byzantine_trace_prop
    (tr : Trace M)
    (Proj := binary_free_composition_fst M emit_any_message_vlsm)
    :=
    valid_trace_prop Proj tr.

(**
  Since the [byzantine_trace_prop]erty was referring to the free composition
  to any other VLSM, we can instantiate that definition to the
  [emit_any_message_vlsm] to derive that a trace with the
  [alternate_byzantine_trace_prop]erty also has the [byzantine_trace_prop]erty.
*)
Lemma byzantine_alt_byzantine
    (tr : Trace M)
    (Halt : alternate_byzantine_trace_prop tr)
    : byzantine_trace_prop tr.
Proof.
  by exists emit_any_message_vlsm.
Qed.

(** ** Equivalence between the two Byzantine trace definitions

  In this section we prove that the [alternate_byzantine_trace_prop]erty is
  equivalent to the [byzantine_trace_prop]erty.

  Since we have already proven that the [alternate_byzantine_trace_prop]erty
  implies the [byzantine_trace_prop]erty (Lemma [byzantine_alt_byzantine]),
  and since we know that the traces with the [byzantine_trace_prop]erty
  are [valid_trace]s for the [pre_loaded_with_all_messages_vlsm], to prove the
  equivalence it is enough to close the circle by proving the
  [VLSM_incl]usion between the [pre_loaded_with_all_messages_vlsm] and the projection VLSM used
  in the definition of the [alternate_byzantine_trace_prop]erty.
*)

Section sec_pre_loaded_with_all_messages_byzantine_alt.

Context
    (PreLoaded := pre_loaded_with_all_messages_vlsm M)
    (Alt1 := binary_free_composition_fst M emit_any_message_vlsm)
    (Alt := binary_free_composition M emit_any_message_vlsm)
    .

(**
  Let <<PreLoaded>> denote the [pre_loaded_with_all_messages_vlsm] of <<M>>, <<Alt>> denote
  the free composition of <<M>> with the [emit_any_message_vlsm],
  and <<Alt1>> denote the projection of <<Alt>> to the component of <<M>>.

  First, note that using the results above it is easy to prove the inclusion
  of <<Alt1>> into <<Preloaded>>.
*)
Lemma alt_pre_loaded_with_all_messages_incl
    : VLSM_incl Alt1 PreLoaded.
Proof.
  by intros t Hvt; apply byzantine_pre_loaded_with_all_messages, byzantine_alt_byzantine.
Qed.

(**
  To prove the reverse inclusion (between <<PreLoaded>> and <<Alt1>>) we will use the
  [basic_VLSM_incl] meta-result about proving inclusions between
  VLSMs which states that:

  - if all [valid] messages in the first are [valid_message]s in the second, and
  - if all [valid_state]s in the first are also [valid_state]s in the second, and
  - if all [input_valid_transition]s in the first are also
    [input_valid_transition]s in the second, then
  - the first VLSM is included in the second.

  We will tackle each of these properties in the sequel.

  First note that _all_ messages are [valid_message]s for <<Alt>>, as
  [emit_any_message_vlsm] can generate any message without changing state.
*)

Lemma alt_option_valid_message
    (om : option message)
    : option_valid_message_prop Alt om.
Proof.
  destruct om as [m |]; [| apply option_valid_message_None].
  pose (s := ``(vs0 Alt) : state Alt).
  exists s.
  assert (valid_state_message_prop Alt s None) as Hs
      by (apply valid_initial_state, proj2_sig).
  by eapply (valid_generated_state_message Alt) with s None s None (existT second _)
  ; cbn; state_update_simpl.
Qed.

(** Using the above, it is straight-forward to show that: *)
Lemma alt_proj_option_valid_message
    (m : option message)
    : option_valid_message_prop Alt1 m.
Proof. by apply any_message_is_valid_in_preloaded. Qed.

(**
  Next we define the "lifting" of a [state] <<s>> from <<M>> to <<Alt>>,
  by simply setting to <<s>> the  corresponding component of the initial
  (composed) state [s0] of <<Alt>>.
*)
Definition lifted_alt_state
    (s : state M)
    : state Alt
    := lift_to_composite_state'
         (binary_IM M emit_any_message_vlsm) first s.

(**
  Lifting a [valid_state] of <<PreLoaded>> we obtain
  a [valid_state] of <<Alt>>.
*)
Lemma preloaded_alt_valid_state
    (sj : state PreLoaded)
    (om : option message)
    (Hp : valid_state_message_prop PreLoaded sj om)
    : valid_state_prop Alt (lifted_alt_state sj).
Proof.
  assert (valid_state_prop PreLoaded sj) as Hsj
      by (exists om; done); clear Hp.
  induction Hsj using valid_state_prop_ind.
  - by apply initial_state_is_valid; intros [].
  - exists om'.
    assert (option_valid_message_prop Alt om0) as Hom0
      by apply alt_option_valid_message.
    cut (input_valid_transition Alt (existT first l) (lifted_alt_state s, om0) (lifted_alt_state s', om'))
      ; [by apply input_valid_transition_outputs_valid_state_message |].
    split.
    + by repeat split; [.. | apply Ht].
    + cbn.
      replace (lifted_alt_state s first) with s
        by (unfold lifted_alt_state, lift_to_composite_state'; state_update_simpl; done).
      apply proj2 in Ht.
      replace (transition l _) with (s', om').
      f_equal.
      by apply state_update_twice.
Qed.

(**
  Finally, we can use [basic_VLSM_incl] together with the
  results above to show that <<Preloaded>> is included in <<Alt1>>.
*)
Lemma pre_loaded_with_all_messages_alt_incl
    : VLSM_incl PreLoaded Alt1.
Proof.
  apply (basic_VLSM_incl PreLoaded Alt1)
  ; intro; intros; [done | | | apply H].
  - by apply alt_proj_option_valid_message.
  - exists (lifted_alt_state s).
    split; [done |].
    destruct Hv as [[_om Hps] [Hpm Hv]].
    repeat split; [| | done].
    + by apply preloaded_alt_valid_state with _om.
    + by apply alt_option_valid_message.
Qed.

(** Hence, <<Preloaded>> and <<Alt1>> are actually trace-equal. *)
Lemma pre_loaded_with_all_messages_alt_eq
    : VLSM_eq PreLoaded Alt1
    .
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
Lemma byzantine_alt_byzantine_iff
    (tr : Trace M)
    : alternate_byzantine_trace_prop tr <-> byzantine_trace_prop tr.
Proof.
  split; intros.
  - by apply byzantine_alt_byzantine.
  - by apply pre_loaded_with_all_messages_alt_incl, byzantine_pre_loaded_with_all_messages.
Qed.

End sec_byzantine_traces.

(** ** Byzantine fault tolerance for a single validator

  Given that projections of composition of validator VLSMs are equal to their corresponding
  pre-loaded with all messages VLSM ([pre_loaded_with_all_messages_validating_proj_eq]),
  we can derive that for validators, all their byzantine traces are
  included in the [valid_trace]s of their projection from the composition.
*)
Lemma validator_component_byzantine_fault_tolerance
    message `{EqDecision index}
    (IM : index -> VLSM message)
    (constraint : composite_label IM -> composite_state IM  * option message -> Prop)
    (i : index)
    (Hvalidator : component_projection_validator_prop IM constraint i)
    : forall tr, byzantine_trace_prop (IM i) tr ->
        valid_trace_prop (pre_composite_vlsm_induced_projection_validator IM constraint i) tr.
Proof.
  intros tr Htr.
  apply
      (VLSM_incl_valid_trace
          (pre_loaded_with_all_messages_validator_component_proj_incl _ _ _ Hvalidator)).
  revert Htr.
  by simpl; apply byzantine_pre_loaded_with_all_messages.
Qed.

(** ** Byzantine fault tolerance for a composition of validators

  In this section we show that if all components of a composite VLSM <<X>> have
  the [projection_validator_prop]erty, then its byzantine traces (that is,
  traces obtained upon placing this composition in any, possibly adversarial,
  context) are [valid_trace]s of <<X>>.
*)
Section sec_composite_validator_byzantine_traces.

Context
  {message : Type}
  `{EqDecision index}
  (IM : index -> VLSM message)
  (constraint : composite_label IM -> composite_state IM  * option message -> Prop)
  (X := composite_vlsm IM constraint)
  (PreLoadedX := pre_loaded_with_all_messages_vlsm X)
  (FreeX := free_composite_vlsm IM)
  (Hvalidator : forall i : index, component_message_validator_prop IM constraint i)
  .

(**
  Let us fix an indexed set of VLSMs <<IM>> and their composition <<X>>
  using <<constraint>>, and let <<PreloadedX>> be the
  [pre_loaded_with_all_messages_vlsm] associated to <<X>>.

  Since we know that <<PreloadedX>> contains precisely the byzantine traces
  of <<X>>, we just need to show that <<PreLoadedX>> is
  included in <<X>> to prove our main result.
*)
Lemma validator_pre_loaded_with_all_messages_incl
    : VLSM_incl PreLoadedX X.
Proof.
  apply VLSM_incl_finite_traces_characterization.
  intros.
  split; [| by apply H].
  destruct H as [Htr Hs].
  induction Htr using finite_valid_trace_from_rev_ind.
  - by apply (finite_valid_trace_from_empty X), initial_state_is_valid.
  - specialize (IHHtr Hs) as IHtr; clear IHHtr.
    apply (extend_right_finite_trace_from X); [done |].
    destruct Hx as [Hvx Htx].
    split; [| done].
    apply finite_valid_trace_last_pstate in IHtr.
    simpl in *.
    match type of IHtr with
    | valid_state_prop _ ?s => remember s as lst
    end.
    split; [done |].
    repeat split; [| by apply Hvx | by apply Hvx].
    destruct Hvx as [Hlst [_ [Hv _]]].
    destruct l as (i, li). simpl in *.
    specialize (valid_state_project_preloaded_to_preloaded _ IM constraint lst i Hlst)
      as Hlsti.
    destruct iom as [im |]; [| apply option_valid_message_None].
    eapply Hvalidator; split; [done |]; split; [| done].
    eexists _.
    by apply (pre_loaded_with_all_messages_message_valid_initial_state_message (IM i)).
Qed.

(**
  Finally, we can conclude that a composition of validator components can
  resist any kind of external influence.
*)
Lemma composite_validator_byzantine_traces_are_not_byzantine
    (tr : Trace X)
    (Hbyz : byzantine_trace_prop X tr)
    : valid_trace_prop X tr.
Proof.
  apply validator_pre_loaded_with_all_messages_incl.
  by apply byzantine_alt_byzantine_iff, alt_pre_loaded_with_all_messages_incl in Hbyz.
Qed.

End sec_composite_validator_byzantine_traces.
