From stdpp Require Import prelude.
From Coq Require Import FinFun.
From VLSM Require Import Lib.Preamble Core.VLSM Core.VLSMProjections Core.Composition Core.ProjectionTraces.

(** * VLSM Projection Validators

In the sequel we fix a composite VLSM <<X>> obtained from an indexed family
of VLSMs <<IM>> and a <<constraint>>, and an index <<i>>, corresponding to
component <<IM i>>.
*)

Section projection_validator.

Context
    {message : Type}
    {index : Type}
    {IndEqDec : EqDecision index}
    (IM : index -> VLSM message)
    (constraint : composite_label IM -> composite_state IM * option message -> Prop)
    (X := composite_vlsm IM constraint)
    (i : index)
    (Xi := composite_vlsm_constrained_projection IM constraint i)
    .

(**
We say that the component <<i>> of X is a validator for received messages if
non-[projection_valid]itiy implied non-component-[valid]ity (or non-reachability).
*)

Definition projection_validator_received_messages_prop
    :=
    forall (li : vlabel (IM i)) (si : vstate (IM i)) (mi : message),
        ~ vvalid Xi li (si, Some mi)
        -> ~ input_valid (pre_loaded_with_all_messages_vlsm (IM i)) li (si, Some mi).

(**
We can slightly generalize the definition above to also include empty messages
and state it in a positive manner as the [projection_validator_prop]erty below,
requiring that [valid]ity in the component (for reachable states) implies
[projection_valid]ity.
*)

Definition projection_validator_prop :=
    forall (li : vlabel (IM i)) (siomi : vstate (IM i) * option message),
        input_valid (pre_loaded_with_all_messages_vlsm (IM i)) li siomi ->
        vvalid Xi li siomi.

(** An alternative formulation of the above property with a seemingly
stronger hypothesis, states that component (IM i) is a validator for the composition constraint
if for any <<si>> a valid state in the projection <<Xi>>, <<li valid (IM i) (si, om)>>
implies  that there exists a state <<s>> whose ith  component is <<si>>,
and <<s>> and <<om>> are valid in <<X>>, and <<(i,li) valid (s,om)>> in <<X>>, that is,
we have that <<li valid (si, om)>> in the projection <<Xi>>.
*)
Definition projection_validator_prop_alt :=
    forall (li : vlabel (IM i)) (siom : vstate (IM i) * option message),
        let (si, om) := siom in
        vvalid (IM i) li siom ->
        valid_state_prop Xi si ->
        vvalid Xi li siom.

(** Under validator assumptions, all reachable states for component <<IM i>> are
valid states in the projection <<Xi>>.
*)
Lemma validator_alt_free_states_are_projection_states
    : projection_validator_prop_alt ->
    forall s,
        valid_state_prop (pre_loaded_with_all_messages_vlsm (IM i)) s ->
        valid_state_prop Xi s.
Proof.
    intros Hvalidator s Hs.
    induction Hs using valid_state_prop_ind;
    [apply initial_state_is_valid;assumption|].
    change s' with (fst (s',om')).
    destruct Ht as [[_ [_ Hvalid]] Htrans].
    apply (projection_valid_implies_destination_projection_valid_state IM constraint i) with l s om om'
    ; [|assumption].
    apply (Hvalidator l (s,om));assumption.
Qed.

(** Below we show that the two definitions above are actually equivalent.
*)
Lemma projection_validator_prop_alt_iff
    : projection_validator_prop_alt <-> projection_validator_prop.
Proof.
    split.
    - intros Hvalidator l (si, om) Hvalid.
      destruct Hvalid as [Hsi [_ Hvalid]].
      apply validator_alt_free_states_are_projection_states in Hsi
      ; [|assumption].
      exact (Hvalidator l (si,om) Hvalid Hsi).
    - intros Hvalidator l (si, om) Hvalid HXisi.
      specialize (Hvalidator l (si, om)).
      apply Hvalidator.
      repeat split; [| apply any_message_is_valid_in_preloaded | assumption].
      revert HXisi.
      apply VLSM_incl_valid_state.
      apply proj_pre_loaded_with_all_messages_incl.
Qed.

Lemma validator_free_states_are_projection_states
    : projection_validator_prop ->
    forall s,
        valid_state_prop (pre_loaded_with_all_messages_vlsm (IM i)) s ->
        valid_state_prop Xi s.
Proof.
    rewrite <- projection_validator_prop_alt_iff.
    apply validator_alt_free_states_are_projection_states.
Qed.

(**
It is easy to see that the [projection_validator_prop]erty includes the
[projection_validator_received_messages_prop]erty.
*)
Lemma projection_validator_messages_received
    : projection_validator_prop -> projection_validator_received_messages_prop.
Proof.
    unfold projection_validator_prop. unfold projection_validator_received_messages_prop. intros.
    intro Hvalid. elim H0. clear H0.
    specialize (H li (si, Some mi) Hvalid). assumption.
Qed.

(**
We say that component <<i>> is a [transition_validator] if any [valid]
transition (from a reachable state) in component <<i>> can be "lifted" to
an [input_valid_transition] in <<X>>.

*)

Definition transition_validator :=
    forall
        (si : vstate (IM i))
        (omi : option message)
        (li : vlabel (IM i))
        ,
        input_valid (pre_loaded_with_all_messages_vlsm (IM i)) li (si, omi)
        ->
        (exists
            (s s' : vstate X)
            (om' : option message),
            si = s i
            /\
            input_valid_transition X (existT i li) (s, omi) (s', om')
        ).

(**
Next two results show that the (simpler) [projection_validator_prop]erty
is equivalent with the [transition_validator] property.
*)

Lemma projection_validator_messages_transitions
    : projection_validator_prop -> transition_validator.
Proof.
    intros Hvalidator si omi li Hpvi.
    specialize (Hvalidator li (si, omi) Hpvi). clear Hpvi.
    destruct Hvalidator as [s [Hsi [Hps [Hopm [Hvalid Hctr]]]]].
    destruct (vtransition X (existT i li) (s, omi)) as (s', om') eqn:Heqt.
    exists s. exists s'. exists om'.
    subst si.
    repeat split; assumption.
Qed.

Lemma transition_validator_messages
    : transition_validator -> projection_validator_prop.
Proof.
    intros Hvalidator li (si,omi) Hpvi.
    specialize (Hvalidator si omi li Hpvi). clear Hpvi.
    destruct Hvalidator as [s [s' [om' [Hsi [Hvalid Htransition]]]]].
    symmetry in Hsi.
    exists s. split; assumption.
Qed.

(** ** Projection validators and Byzantine behavior

In the sequel we assume that <<X>> has the [projection_validator_prop]erty for
component <<i>>.  Let <<Xi>> be the projection of <<X>> to component <<i>>
and <<Preloaded>> be the [pre_loaded_with_all_messages_vlsm] associated to component <<i>>.
*)

Section pre_loaded_with_all_messages_validator_proj.
    Context
        (Hvalidator : projection_validator_prop)
        (PreLoaded := pre_loaded_with_all_messages_vlsm (IM i))
        .

(**
We can show that <<Preloaded>> is included in <<Xi>> by applying the meta-lemma
[VLSM_incl_finite_traces_characterization], and by induction on the length
of a trace. The [projection_validator_prop]erty is used to translate
[input_valid]ity for the preloaded machine into the [projection_valid]ity.
*)

    Lemma pre_loaded_with_all_messages_validator_proj_incl
        : VLSM_incl PreLoaded Xi.
    Proof.
        (* reduce inclusion to inclusion of finite traces. *)
        apply VLSM_incl_finite_traces_characterization.
        intros.
        split; [|apply H].
        induction H using finite_valid_trace_rev_ind.
        - apply (finite_valid_trace_from_empty Xi). apply initial_state_is_valid. assumption.
        - apply (extend_right_finite_trace_from Xi);[assumption|].
          destruct Hx as [Hvx Htx].
          split; [|assumption].
          apply projection_valid_input_valid.
          apply Hvalidator.
          assumption.
    Qed.

(**
Given that any projection is included in the [pre_loaded_with_all_messages_vlsm]
of its component (Lemma [proj_pre_loaded_with_all_messages_incl]), we conclude
that <<Preloaded>> and <<Xi>> are trace-equal.  This means that all the
byzantine behavior of a component which is a validator
is exhibited by its corresponding projection.
*)
    Lemma pre_loaded_with_all_messages_validator_proj_eq
        : VLSM_eq PreLoaded Xi.
    Proof.
        split.
        - apply pre_loaded_with_all_messages_validator_proj_incl.
        - apply proj_pre_loaded_with_all_messages_incl.
    Qed.

End pre_loaded_with_all_messages_validator_proj.

End projection_validator.

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

Definition self_validator_vlsm_prop
    :=
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
    (PreLoaded := pre_loaded_with_all_messages_vlsm X)
    .

(**
Let <<PreLoaded>> be the [pre_loaded_with_all_messages_vlsm] associated to X.
From Lemma [vlsm_incl_pre_loaded_with_all_messages_vlsm] we know that <<X>> is
included in <<PreLoaded>>.

To prove the converse we use the [self_validator_vlsm_prop]erty to
verify the conditions of meta-lemma [VLSM_incl_finite_traces_characterization].
*)

    Lemma pre_loaded_with_all_messages_self_validator_vlsm_incl
        : VLSM_incl PreLoaded X.
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
We conclude that <<X>> and <<Preloaded>> are trace-equal.
*)

    Lemma pre_loaded_with_all_messages_self_validator_vlsm_eq
        : VLSM_eq PreLoaded X.
    Proof.
        split.
        - apply pre_loaded_with_all_messages_self_validator_vlsm_incl.
        - pose (vlsm_incl_pre_loaded_with_all_messages_vlsm X) as Hincl.
          destruct X as (T, (S, M)).
          apply Hincl.
    Qed.

End self_validator_vlsm.
