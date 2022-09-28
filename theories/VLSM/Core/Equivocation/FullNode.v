From stdpp Require Import prelude.
From VLSM.Core Require Import VLSM VLSMProjections Composition.
From VLSM.Core Require Import Equivocation.

Section full_node_constraint.

Context
  `{EqDecision message}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  (Free := free_composite_vlsm IM)
  `{forall i : index, HasBeenSentCapability (IM i)}
  `{forall i : index, HasBeenReceivedCapability (IM i)}
  (admissible_index : composite_state IM -> index -> Prop)
  (** admissible equivocator index: this index can equivocate from given state *)
  .

(**
  Given a composite state <<s>>, a message <<m>>, and a node index <<i>>
  if there is a machine we say that message <<m>> can be
  [node_generated_without_further_equivocation] by node <<i>> if the message
  can be produced by node <<i>> pre_loaded with all messages in a trace in which
  all message equivocation is done through messages causing
  [no_additional_equivocations] to state <<s>> (message [has_been_directly_observed] in <<s>>).
*)
Definition node_generated_without_further_equivocation
  (s : composite_state IM)
  (m : message)
  (i : index)
  : Prop
  := exists (si : vstate (IM i)),
    can_produce (pre_loaded_with_all_messages_vlsm (IM i)) si m /\
    state_received_not_sent_invariant (IM i) si (composite_has_been_directly_observed IM s).

(**
  Similar to the condition above, but now the message is required to be
  generated by the machine pre-loaded only with messages causing
  [no_additional_equivocations] to state <<s>>.
*)
Definition node_generated_without_further_equivocation_alt
  (s : composite_state IM)
  (m : message)
  (i : index)
  : Prop
  := can_emit (pre_loaded_vlsm (IM i) (composite_has_been_directly_observed IM s)) m.

(**
  The equivocation-based abstract definition of the full node condition
  stipulates that a message can be received in a state <<s>> if either it causes
  [no_additional_equivocations] to state <<s>>, or it can be
  [node_generated_without_further_equivocation] by an admissible node.
*)
Definition full_node_condition_for_admissible_equivocators
  (l : composite_label IM)
  (som : composite_state IM * option message)
  : Prop
  :=
  let (s, om) := som in
  match om with
  | None => True
  | Some m =>
    composite_has_been_directly_observed IM s m \/
    exists (i : index), admissible_index s i /\ node_generated_without_further_equivocation s m i
  end.

(**
  Similar to the condition above, but using the
  [node_generated_without_further_equivocation_alt] property.
*)
Definition full_node_condition_for_admissible_equivocators_alt
  (l : composite_label IM)
  (som : composite_state IM * option message)
  : Prop
  :=
  let (s, om) := som in
  match om with
  | None => True
  | Some m =>
    composite_has_been_directly_observed IM s m \/
    exists (i : index), admissible_index s i /\
    node_generated_without_further_equivocation_alt s m i
  end.

(**
  We here show that if a machine has the [cannot_resend_message_stepwise_prop]erty,
  then the [node_generated_without_further_equivocation] property is stronger
  than the [node_generated_without_further_equivocation_alt] property.
*)
Lemma node_generated_without_further_equivocation_weaken
  (i : index)
  (Hno_resend : cannot_resend_message_stepwise_prop (IM i))
  (s: composite_state IM)
  (Hs: valid_state_prop
     (pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM)) s)
  (m : message)
  (Hsmi : node_generated_without_further_equivocation s m i)
  : node_generated_without_further_equivocation_alt s m i.
Proof.
  destruct Hsmi as [si [Hsim Hsi]].
  apply can_emit_iff. exists si.
  revert Hsim.
  by eapply lift_generated_to_seeded.
Qed.

(**
  if all machines satisfy the [cannot_resend_message_stepwise_prop]erty,
  then the [full_node_condition_for_admissible_equivocators] is stronger than
  the [full_node_condition_for_admissible_equivocators_alt].
*)
Lemma full_node_condition_for_admissible_equivocators_subsumption
  (Hno_resend : forall i : index, cannot_resend_message_stepwise_prop (IM i))
  : preloaded_constraint_subsumption IM
      full_node_condition_for_admissible_equivocators
      full_node_condition_for_admissible_equivocators_alt.
Proof.
  intros l (s, [m|]) [Hs [_ [_ Hc]]]; [| done].
  destruct Hc as [Hno_equiv | Hfull]; [by left |].
  right.
  destruct Hfull as [i [Hi Hfull]].
  exists i. split; [done |].
  specialize (Hno_resend i).
  apply node_generated_without_further_equivocation_weaken; [done | | done].
  revert Hs.
  apply VLSM_incl_valid_state.
  apply preloaded_constraint_free_incl.
Qed.

End full_node_constraint.
