From stdpp Require Import prelude.
From VLSM.Lib Require Import Preamble.
From VLSM.Core Require Import VLSM VLSMProjections Composition Equivocation.

(** * Core: VLSM No-Equivocation Composition Constraints *)

Section sec_no_equivocations.

Context
  {message : Type}
  (vlsm : VLSM message)
  `{HasBeenSentCapability message vlsm}
  .

(**
  An equivocating transition can be prevented by checking that the message
  to be received [has_been_sent] previously in the state about to receive it.

  However, since we might allow certain other messages, such as initial
  messages, we give a slightly more general definition, that of
  [no_equivocation_except_from] those specified by a given predicate.
*)

Definition no_equivocations_except_from
  (exception : message -> Prop) (l : label vlsm) (som : state vlsm * option message) : Prop :=
  let (s, om) := som in
    from_option (fun m => has_been_sent vlsm s m \/ exception m) True om.

(**
  The [no_equivocations] constraint does not allow any exceptions
  (messages being received must have been previously sent).
*)
Definition no_equivocations
  (l : label vlsm) (som : state vlsm * option message) : Prop :=
    no_equivocations_except_from (fun m => False) l som.

End sec_no_equivocations.

(** ** No-Equivocation Invariants

  In this section we show that under [no_equivocations] assumptions:

  - for any valid state all messages [directly_observed_were_sent].
  - the [pre_loaded_with_all_messages_vlsm] is equal to the [no_equivocations] VLSM.
*)

Section sec_no_equivocation_invariants.

Context
  (message : Type)
  (X : VLSM message)
  `{HasBeenSentCapability message X}
  `{HasBeenDirectlyObservedCapability message X}
  (Henforced : forall l s om, input_constrained X l (s, om) -> no_equivocations X l (s, om))
  .

(**
  A VLSM that enforces the [no_equivocations] constraint and also supports
  [has_been_directly_observed] obeys the [directly_observed_were_sent] invariant which states that
  any message that [has_been_directly_observed] in a state, [has_been_sent] in
  the same state, too.
*)

Definition directly_observed_were_sent (s : state X) : Prop :=
  forall msg : message,
    has_been_directly_observed X s msg -> has_been_sent X s msg.

Lemma directly_observed_were_sent_initial :
  forall (s : state X),
    initial_state_prop X s -> directly_observed_were_sent s.
Proof.
  intros s Hinitial msg Hsend.
  by apply has_been_directly_observed_no_inits in Hsend.
Qed.

Lemma directly_observed_were_sent_preserved :
  forall (l : label X) (s : state X) (im : option message) (s' : state X) (om : option message),
    input_valid_transition X l (s, im) (s', om) -> directly_observed_were_sent s ->
      directly_observed_were_sent s'.
Proof.
  intros l s im s' om Hptrans Hprev msg Hobs.
  apply preloaded_weaken_input_valid_transition in Hptrans.
  eapply (oracle_step_update (has_been_directly_observed_stepwise_props X)) in Hobs;
    cbn in Hobs; [| done].
  rewrite has_been_sent_step_update by done.
  destruct Hobs as [[-> | ->] |].
  - (* by [no_equivocations], the incoming message [im] was previously sent *)
    destruct Hptrans as [Hv _].
    by destruct (Henforced l s (Some msg) Hv); [right |].
  - by left.
  - by right; apply Hprev.
Qed.

Lemma directly_observed_were_sent_invariant :
  forall (s : state X),
    valid_state_prop X s -> directly_observed_were_sent s.
Proof.
  induction 1 using valid_state_prop_ind.
  - by apply directly_observed_were_sent_initial.
  - by eapply directly_observed_were_sent_preserved.
Qed.

(**
  If the [valid]ity function satisfies the [no_equivocations] constraint then
  it doesn't matter if we preload the composition with some initial messages,
  since all messages must be sent before being received, which means that
  one cannot use the new messages to create additional traces.
*)
Lemma no_equivocations_preloaded_traces :
  forall (is : state (pre_loaded_with_all_messages_vlsm X)) (tr : list transition_item),
    finite_constrained_trace X is tr -> finite_valid_trace X is tr.
Proof.
  intros is tr Htr.
  induction Htr using finite_valid_trace_rev_ind;
    [by cbn; apply finite_valid_trace_empty |].
  destruct IHHtr as [IHtr His].
  split; [| done].
  rapply extend_right_finite_trace_from; [done |].
  apply finite_valid_trace_last_pstate in IHtr as Hs.
  repeat split; [done | | by apply Hx..].
  destruct iom as [m |]; [| by apply option_valid_message_None].
  eapply sent_valid; [done |].
  destruct Hx as [Hv _].
  by apply Henforced in Hv as [].
Qed.

Lemma preloaded_incl_no_equivocations :
  VLSM_incl (pre_loaded_with_all_messages_vlsm X) X.
Proof.
  specialize no_equivocations_preloaded_traces.
  clear -X. destruct X as [T [S M]].
  by apply VLSM_incl_finite_traces_characterization.
Qed.

Lemma preloaded_eq_no_equivocations :
  VLSM_eq (pre_loaded_with_all_messages_vlsm X) X.
Proof.
  split.
  - by apply preloaded_incl_no_equivocations.
  - by apply (vlsm_incl_pre_loaded_with_all_messages_vlsm X).
Qed.

End sec_no_equivocation_invariants.

Section sec_composite_no_equivocation.

Context
  {message : Type}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  `{forall i, HasBeenSentCapability (IM i)}
  (constraint : composite_label IM -> composite_state IM * option message -> Prop)
  .

Definition sent_except_from
  (exception : message -> Prop) (es : composite_state IM) (iom : option message) : Prop :=
    from_option (fun im => composite_has_been_sent IM es im \/ exception im) True iom.

Definition composite_no_equivocations_except_from
  (exception : message -> Prop) (l : composite_label IM) (som : composite_state IM * option message)
  : Prop :=
    sent_except_from exception som.1 som.2.

(**
  The [composite_no_equivocations] constraint requires that
  messages being received must have been previously sent by a
  machine in the composition.
*)
Definition composite_no_equivocations
  (l : composite_label IM) (som : composite_state IM * option message) : Prop :=
    composite_no_equivocations_except_from (fun m => False) l som.

(** ** Composite No-Equivocation Invariants

  A VLSM composition whose constraint subsumes the [no_equivocations] constraint
  and also supports [has_been_received] (or [has_been_directly_observed]) obeys an
  invariant that any message that tests as [has_been_received]
  (resp. [has_been_directly_observed]) in a state also tests as [has_been_sent]
  in the same state.
*)

Section sec_composite_no_equivocation_invariants.

Context
  `{forall i, HasBeenReceivedCapability (IM i)}
  (X := composite_vlsm IM constraint)
  (Hsubsumed : preloaded_constraint_subsumption (free_composite_vlsm IM) constraint
    composite_no_equivocations)
  .

Definition composite_directly_observed_were_sent (s : state (composite_type IM)) : Prop :=
  forall msg : message,
    composite_has_been_directly_observed IM s msg -> composite_has_been_sent IM s msg.

Lemma composite_directly_observed_were_sent_invariant :
  forall (s : state X),
    valid_state_prop X s -> composite_directly_observed_were_sent s.
Proof.
  intros s Hs m Hobs.
  change (has_been_sent X s m).
  apply (directly_observed_were_sent_invariant message X); [| done |].
  - by intros l s0 om; apply Hsubsumed.
  - by apply composite_has_been_directly_observed_sent_received_iff.
Qed.

End sec_composite_no_equivocation_invariants.

Section sec_seeded_composite_vlsm_no_equivocation.

(** ** Pre-loading a VLSM composition with no equivocations constraint

  When adding initial messages to a VLSM composition with a no equivocation
  constraint, we cannot simply use the [pre_loaded_vlsm] construct
  because the no-equivocation constraint must also be altered to reflect that
  the newly added initial messages are safe to be received at all times.
*)

Section sec_seeded_composite_vlsm_no_equivocation_definition.

Context
  (seed : message -> Prop)
  .

(** Constraint is updated to also allow seeded messages. *)

Definition no_equivocations_additional_constraint_with_pre_loaded
  (l : composite_label IM) (som : composite_state IM * option message) : Prop :=
    composite_no_equivocations_except_from seed l som /\ constraint l som.

Definition composite_no_equivocation_vlsm_with_pre_loaded : VLSM message :=
  pre_loaded_vlsm (composite_vlsm IM no_equivocations_additional_constraint_with_pre_loaded) seed.

Definition free_composite_no_equivocation_vlsm_with_pre_loaded : VLSM message :=
  pre_loaded_vlsm (free_composite_vlsm IM) seed.

Lemma seeded_no_equivocation_incl_preloaded :
  VLSM_incl composite_no_equivocation_vlsm_with_pre_loaded
    (pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM)).
Proof.
  apply (VLSM_incl_trans _ (pre_loaded_with_all_messages_vlsm (composite_vlsm IM _))).
  - by cbn; apply (@pre_loaded_vlsm_incl message (composite_vlsm IM _)).
  - by apply (preloaded_constraint_subsumption_incl_free (free_composite_vlsm IM)).
Qed.

End sec_seeded_composite_vlsm_no_equivocation_definition.

(** Adds a no-equivocations condition on top of an existing constraint. *)
Definition no_equivocations_additional_constraint
  (l : composite_label IM) (som : composite_state IM * option message) : Prop :=
    composite_no_equivocations l som /\ constraint l som.

Lemma false_composite_no_equivocation_vlsm_with_pre_loaded :
  VLSM_eq
    (composite_no_equivocation_vlsm_with_pre_loaded (fun m => False))
    (composite_vlsm IM no_equivocations_additional_constraint).
Proof.
  unfold composite_no_equivocation_vlsm_with_pre_loaded.
  apply VLSM_eq_trans with
    (composite_vlsm IM (no_equivocations_additional_constraint_with_pre_loaded (fun _ =>  False))).
  - by apply VLSM_eq_sym, vlsm_is_pre_loaded_with_False.
  - by split; apply (constraint_subsumption_incl (free_composite_vlsm IM));
      intros l [s [m |]] Hpv; apply Hpv.
Qed.

End sec_seeded_composite_vlsm_no_equivocation.

End sec_composite_no_equivocation.
