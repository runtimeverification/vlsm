From stdpp Require Import prelude.
From VLSM.Lib Require Import Preamble.
From VLSM.Core Require Import VLSM VLSMProjections Composition Equivocation.

(** * VLSM No Equivocation Composition Constraints *)

Section sec_no_equivocations.

Context
  {message : Type}
  (vlsm : VLSM message)
  .

(**
  An equivocating transition can be prevented by checking that the message
  to be received [has_been_sent] previously in the state about to receive it.

  However, since we might allow certain other messages, such as initial
  messages, we give a slightly more general definition, that of
  [no_equivocation_except_from] those specified by a given predicate.
*)

Definition no_equivocations_except_from
  `{HasBeenSentCapability message vlsm}
  (exception : message -> Prop)
  (l : vlabel vlsm)
  (som : state * option message)
  :=
  let (s, om) := som in
  from_option (fun m => has_been_sent vlsm s m \/ exception m) True om.

(**
  The [no_equivocations] constraint does not allow any exceptions
  (messages being received must have been previously sent).
*)
Definition no_equivocations
  `{HasBeenSentCapability message vlsm}
  (l : vlabel vlsm)
  (som : state * option message)
  : Prop
  :=
  no_equivocations_except_from (fun m => False) l som.

End sec_no_equivocations.

(** ** No-Equivocation Invariants

  In this section we show that under [no_equivocations] assumptions:

  - for any valid state all messages [directly_observed_were_sent].
  - the [pre_loaded_with_all_messages_vlsm] is equal to the [no_equivocations] VLSM.
*)

Section sec_no_equivocation_invariants.

Context
  message
  (X : VLSM message)
  `{HasBeenSentCapability message X}
  `{HasBeenDirectlyObservedCapability message X}
  (Henforced : forall l s om, input_valid (pre_loaded_with_all_messages_vlsm X) l (s, om) ->
    no_equivocations X l (s, om))
  .

(**
  A VLSM that enforces the [no_equivocations] constraint and also supports
  [has_been_directly_observed] obeys the [directly_observed_were_sent] invariant which states that
  any message that [has_been_directly_observed] in a state, [has_been_sent] in
  the same state, too.
*)

Definition directly_observed_were_sent (s : state) : Prop :=
  forall msg, has_been_directly_observed X s msg -> has_been_sent X s msg.

Lemma directly_observed_were_sent_initial s :
  vinitial_state_prop X s ->
  directly_observed_were_sent s.
Proof.
  intros Hinitial msg Hsend.
  by apply has_been_directly_observed_no_inits in Hsend.
Qed.

Lemma directly_observed_were_sent_preserved l s im s' om :
  input_valid_transition X l (s, im) (s', om) ->
  directly_observed_were_sent s ->
  directly_observed_were_sent s'.
Proof.
  intros Hptrans Hprev msg Hobs.
  specialize (Hprev msg).
  apply preloaded_weaken_input_valid_transition in Hptrans.
  eapply (oracle_step_update (has_been_directly_observed_stepwise_props X) _ _ _ _ _ Hptrans)
    in Hobs; simpl in Hobs.
  specialize (Henforced l s (Some msg)).
  rewrite (has_been_sent_step_update Hptrans).
  destruct Hptrans as [Hv _].
  destruct Hobs as [[Hin | Hout] | Hobs]; subst.
  - (* by [no_equivocations], the incoming message [im] was previously sent *)
    specialize (Henforced Hv).
    by destruct Henforced; [right |].
  - by left.
  - by right; apply Hprev.
Qed.

(* TODO(wkolowski): make notation uniform accross the file. *)
Lemma directly_observed_were_sent_invariant s:
  valid_state_prop X s ->
  directly_observed_were_sent s.
Proof.
  intro Hproto.
  induction Hproto using valid_state_prop_ind.
  - by apply directly_observed_were_sent_initial.
  - by eapply directly_observed_were_sent_preserved.
Qed.

(**
  If the [valid]ity function satisfies the [no_equivocations] constraint then
  it doesn't matter if we preload the composition with some initial messages,
  since all messages must be sent before being received, which means that
  one cannot use the new messages to create additional traces.
*)
Lemma no_equivocations_preloaded_traces
  (is : state)
  (tr : list transition_item)
  : finite_valid_trace (pre_loaded_with_all_messages_vlsm X) is tr -> finite_valid_trace X is tr.
Proof.
  intro Htr.
  induction Htr using finite_valid_trace_rev_ind.
  - split; [| done].
    rapply @finite_valid_trace_from_empty.
    by apply initial_state_is_valid.
  - destruct IHHtr as [IHtr His].
    split; [| done].
    rapply extend_right_finite_trace_from; [done |].
    apply finite_valid_trace_last_pstate in IHtr as Hs.
    cut (option_valid_message_prop X iom); [by firstorder |].
    destruct iom as [m |]; [| by apply option_valid_message_None].
    destruct Hx as [Hv _].
    apply Henforced in Hv.
    destruct Hv as [Hbsm | []].
    by eapply sent_valid.
Qed.

Lemma preloaded_incl_no_equivocations
  : VLSM_incl (pre_loaded_with_all_messages_vlsm X) X.
Proof.
  specialize no_equivocations_preloaded_traces.
  clear -X. destruct X as [T [S M]].
  by apply VLSM_incl_finite_traces_characterization.
Qed.

Lemma preloaded_eq_no_equivocations
  : VLSM_eq (pre_loaded_with_all_messages_vlsm X) X.
Proof.
  specialize preloaded_incl_no_equivocations.
  specialize (vlsm_incl_pre_loaded_with_all_messages_vlsm X).
  clear -X. destruct X as [T [S M]].
  intros Hincl Hincl'.
  by apply VLSM_eq_incl_iff.
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

Definition sent_except_from exception es iom : Prop :=
  from_option (fun im => composite_has_been_sent IM es im \/ exception im) True iom.

Definition composite_no_equivocations_except_from
  (exception : message -> Prop)
  (l : composite_label IM)
  (som : composite_state IM * option message)
  :=
  sent_except_from exception som.1 som.2.

(**
  The [composite_no_equivocations] constraint requires that
  messages being received must have been previously sent by a
  machine in the composition.
*)
Definition composite_no_equivocations
  (l : composite_label IM)
  (som : composite_state IM * option message)
  : Prop
  :=
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
  (Hsubsumed : preloaded_constraint_subsumption IM constraint composite_no_equivocations)
  .

Definition composite_directly_observed_were_sent (s : state) : Prop :=
  forall msg, composite_has_been_directly_observed IM s msg -> composite_has_been_sent IM s msg.

Lemma composite_directly_observed_were_sent_invariant s :
  valid_state_prop X s ->
  composite_directly_observed_were_sent s.
Proof.
  intros Hs m.
  rewrite composite_has_been_directly_observed_sent_received_iff.
  intros Hobs.
  cut (has_been_sent X s m); [done |].
  apply (directly_observed_were_sent_invariant message X); [| done ..].
  by intros l s0 om; apply Hsubsumed.
Qed.

End sec_composite_no_equivocation_invariants.

Section sec_seeded_composite_vlsm_no_equivocation.

(** ** Pre-loading a VLSM composition with no equivocations constraint

  When adding initial messages to a VLSM composition with a no equivocation
  constraint, we cannot simply use the [pre_loaded_vlsm] construct
  because the no-equivocation constraint must also be altered to reflect that
  the newly added initial messages are safe to be received at all times.
*)

Context
  (X := free_composite_vlsm IM)
  .

Section sec_seeded_composite_vlsm_no_equivocation_definition.

Context
  (seed : message -> Prop)
  .

(** Constraint is updated to also allow seeded messages. *)

Definition no_equivocations_additional_constraint_with_pre_loaded
  (l : composite_label IM)
  (som : composite_state IM * option message)
  :=
  composite_no_equivocations_except_from seed l som
  /\ constraint l som.

Definition composite_no_equivocation_vlsm_with_pre_loaded
  : VLSM message
  :=
  pre_loaded_vlsm (composite_vlsm IM no_equivocations_additional_constraint_with_pre_loaded) seed.

Lemma seeded_no_equivocation_incl_preloaded :
  VLSM_incl composite_no_equivocation_vlsm_with_pre_loaded
    (pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM)).
Proof.
  unfold composite_no_equivocation_vlsm_with_pre_loaded.
  match goal with
  |- VLSM_incl (pre_loaded_vlsm ?v _) _ =>
    specialize (pre_loaded_with_all_messages_vlsm_is_pre_loaded_with_True v) as Hprev
  end.
  apply VLSM_eq_incl_iff in Hprev. apply proj2 in Hprev.
  match type of Hprev with
  | VLSM_incl (mk_vlsm ?m) _ => apply VLSM_incl_trans with m
  end
  ; [by apply pre_loaded_vlsm_incl |].
  match type of Hprev with
  | VLSM_incl _ (mk_vlsm ?m) => apply VLSM_incl_trans with m
  end
  ; [done |].
  unfold free_composite_vlsm; cbn.
  by apply preloaded_constraint_subsumption_incl.
Qed.

End sec_seeded_composite_vlsm_no_equivocation_definition.

(** Adds a no-equivocations condition on top of an existing constraint. *)
Definition no_equivocations_additional_constraint
  (l : composite_label IM)
  (som : composite_state IM * option message)
  :=
  composite_no_equivocations l som
  /\ constraint l som.

Context
  (SeededNoeqvFalse := composite_no_equivocation_vlsm_with_pre_loaded (fun m => False))
  (Noeqv := composite_vlsm IM no_equivocations_additional_constraint)
  (SeededNoeqvTrue := composite_no_equivocation_vlsm_with_pre_loaded (fun m => True))
  (PreFree := pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM))
  .

Lemma false_composite_no_equivocation_vlsm_with_pre_loaded
  : VLSM_eq SeededNoeqvFalse Noeqv.
Proof.
  unfold SeededNoeqvFalse.
  unfold composite_no_equivocation_vlsm_with_pre_loaded.
  match goal with
  |- VLSM_eq (pre_loaded_vlsm ?m _) _ => specialize (vlsm_is_pre_loaded_with_False m) as Heq
  end.
  apply VLSM_eq_sym in Heq.
  match type of Heq with
  | VLSM_eq _ ?v => apply VLSM_eq_trans with (machine v)
  end
  ; [done |].
  apply VLSM_eq_incl_iff.
  specialize (constraint_subsumption_incl IM) as Hincl.
  unfold no_equivocations_additional_constraint_with_pre_loaded.
  by split; apply Hincl; intros l [s [m |]] Hpv; apply Hpv.
Qed.

End sec_seeded_composite_vlsm_no_equivocation.

End sec_composite_no_equivocation.
