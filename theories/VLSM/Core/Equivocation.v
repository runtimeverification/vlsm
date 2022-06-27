From Cdcl Require Import Itauto. Local Tactic Notation "itauto" := itauto auto.
From Coq Require Import Streams FinFun Rdefinitions.
From stdpp Require Import prelude finite.
From VLSM.Lib Require Import Preamble ListExtras StdppListSet.
From VLSM.Lib Require Import ListSetExtras Measurable FinFunExtras.
From VLSM.Core Require Import VLSM VLSMProjections Composition ProjectionTraces Validator.

(** * VLSM Equivocation Definitions **)

(**
 This module is dedicated to building the vocabulary for discussing equivocation.
 Equivocation occurs on the receipt of a message which has not been previously sent.
 The designated sender (validator) of the message is then said to be equivocating.
 Our main purpose is to keep track of equivocating senders in a composite context
 and limit equivocation by means of a composition constraint.
**)

Lemma exists_proj1_sig {A:Type} (P:A -> Prop) (a:A):
  (exists xP:{x | P x}, proj1_sig xP = a) <-> P a.
Proof.
  split.
  - by intros [[x Hx] [= ->]].
  - by intro Ha; exists (exist _ a Ha).
Qed.

(** ** Basic equivocation **)

Class ReachableThreshold V `{Hm : Measurable V} :=
  { threshold : {r | (r >= 0)%R}
  ; reachable_threshold : exists (vs:list V), NoDup vs /\ (sum_weights vs > proj1_sig threshold)%R
  }.

(** Assuming a set of <<state>>s, and a set of <<validator>>s,
which is [Measurable] and has a [ReachableThreshold], we can define
[BasicEquivocation] starting from a computable [is_equivocating_fn]
deciding whether a validator is equivocating in a state.

To avoid a [Finite] constraint on the entire set of validators, we will
assume that there is a finite set of validators for each state, which
can be retrieved through the [state_validators] function.
This can be taken to be entire set of validators when that is finite,
or the set of senders for all messages in the state for
[state_encapsulating_messages].

This allows us to determine the [equivocating_validators] for a given
state as those equivocating in that state.

The [equivocation_fault] is determined the as the sum of weights of the
[equivocating_validators].

We call a state [not_heavy] if its corresponding [equivocation_fault]
is lower than the [threshold] set for the <<validator>>s type.
**)

Class BasicEquivocation
  (state validator : Type)
  {measurable_V : Measurable validator}
  {reachable_threshold : ReachableThreshold validator}
  :=
  { is_equivocating (s : state) (v : validator) : Prop
  ; is_equivocating_dec : RelDecision is_equivocating

    (** retrieves a set containing all possible validators for a state. **)

  ; state_validators (s : state) : set validator

  ; state_validators_nodup : forall (s : state), NoDup (state_validators s)

    (** All validators which are equivocating in a given composite state **)

  ; equivocating_validators
      (s : state)
      : list validator
      := filter (fun v => is_equivocating s v) (state_validators s)

     (** The equivocation fault sum: the sum of the weights of equivocating
     validators **)

  ; equivocation_fault
      (s : state)
      : R
      :=
      sum_weights (equivocating_validators s)

  ; not_heavy
      (s : state)
      := (equivocation_fault s <= proj1_sig threshold)%R
 }.

Lemma equivocating_validators_nodup
  `{Heqv: BasicEquivocation st validator }
  (s : st)
  : NoDup (equivocating_validators s).
Proof.
  apply NoDup_filter. apply state_validators_nodup.
Qed.

Lemma eq_equivocating_validators_equivocation_fault
  `{Heqv: BasicEquivocation st validator }
  `{EqDecision validator}
  : forall s1 s2,
    set_eq (equivocating_validators s1) (equivocating_validators s2) ->
    equivocation_fault s1 = equivocation_fault s2.
Proof.
  intros.
  apply (set_eq_nodup_sum_weight_eq
          (equivocating_validators s1)
          (equivocating_validators s2))
  ; [| | done]
  ; apply equivocating_validators_nodup.
Qed.

Lemma incl_equivocating_validators_equivocation_fault
  `{Heqv: BasicEquivocation st validator }
  `{EqDecision validator}
  : forall s1 s2,
    (equivocating_validators s1) ⊆ (equivocating_validators s2) ->
    (equivocation_fault s1 <= equivocation_fault s2)%R.
Proof.
  intros.
  apply (sum_weights_subseteq
          (equivocating_validators s1)
          (equivocating_validators s2))
  ; [| | done]
  ; apply equivocating_validators_nodup.
Qed.

(** *** State-message oracles and endowing states with history

    Our first step is to define some useful concepts in the context of a single VLSM.

    Apart from basic definitions of equivocation, we introduce the concept of a
    [state_message_oracle]. Such an oracle can, given a state and a message,
    decide whether the message has been sent (or received) in the history leading
    to the current state. Formally, we say that a [message] <m> [has_been_sent]
    if we're in  [state] <s> iff every valid trace which produces <s> contains <m>
    as a sent message somewhere along the way.

    The existence of such oracles, which practically imply endowing states with history,
    is necessary if we are to detect equivocation using a composition constaint, as these
    constraints act upon states, not traces.
 **)

Section Simple.
    Context
      {message : Type}
      (vlsm : VLSM message)
      (pre_vlsm := pre_loaded_with_all_messages_vlsm vlsm)
      .

(** The following property detects equivocation in a given trace for a given message. **)

    Definition equivocation_in_trace
      (msg : message)
      (tr : list (vtransition_item vlsm))
      : Prop
      :=
      exists
        (prefix : list transition_item)
        (item : transition_item)
        (suffix : list transition_item),
        tr = prefix ++ item :: suffix
        /\ input item = Some msg
        /\ ~trace_has_message (field_selector output) msg prefix.

    Instance equivocation_in_trace_dec
      `{EqDecision message}
      : RelDecision equivocation_in_trace.
    Proof.
      intros msg tr.
      apply @Decision_iff with
        (List.Exists (fun d => match d with (prefix, item, _) =>
          input item = Some msg /\ ~trace_has_message (field_selector output) msg prefix
        end) (one_element_decompositions tr)).
      - rewrite Exists_exists.  split.
        + intros [((prefix, item), suffix) [Hitem Heqv]].
          exists prefix, item, suffix.
          by apply elem_of_list_In, in_one_element_decompositions_iff in Hitem.
        + intros [prefix [item [suffix [Hitem Heqv]]]].
          exists ((prefix, item), suffix).
          by rewrite elem_of_list_In, in_one_element_decompositions_iff.
      - apply Exists_dec. intros ((prefix, item), suffix).
        apply Decision_and.
        + apply option_eq_dec.
        + apply Decision_not. apply Exists_dec. intros pitem.
          apply option_eq_dec.
    Qed.

    Lemma no_equivocation_in_empty_trace m
      : ~ equivocation_in_trace m [].
    Proof.
      intros [prefix [suffix [item [Hitem _]]]].
      destruct prefix; inversion Hitem.
    Qed.

    Lemma equivocation_in_trace_prefix
      (msg : message)
      (prefix : list (vtransition_item vlsm))
      (suffix : list (vtransition_item vlsm))
      : equivocation_in_trace msg prefix -> equivocation_in_trace msg (prefix ++ suffix).
    Proof.
      intros (pre & item & suf & -> & Hinput & Hnoutput).
      exists pre, item, (suf ++ suffix).
      by rewrite app_comm_cons, <- !app_assoc.
    Qed.

    Lemma equivocation_in_trace_last_char
      (msg : message)
      (tr : list (vtransition_item vlsm))
      (item : vtransition_item vlsm)
      : equivocation_in_trace msg (tr ++ [item]) <->
        equivocation_in_trace msg tr \/
        input item = Some msg /\ ~trace_has_message (field_selector output) msg tr.
    Proof.
      split.
      - intros [prefix [item' [suffix [Heq_tr_item' [Hinput Hnoutput]]]]].
        destruct_list_last suffix suffix' _item Heq_suffix.
        + by apply app_inj_tail in Heq_tr_item' as [-> ->]; right.
        + rewrite app_comm_cons, !app_assoc in Heq_tr_item'.
          apply app_inj_tail in Heq_tr_item' as [-> ->].
          left. by exists prefix, item', suffix'.
      - intros
          [[prefix [item' [suffix [-> [Hinput Hnoutput]]]]]
          | [Hinput Hnoutput]].
        + exists prefix, item', (suffix ++ [item]).
          by rewrite <- app_assoc.
        + by exists tr, item, [].
    Qed.

(** We intend to give define several message oracles: [has_been_sent], [has_not_been_sent],
    [has_been_received] and [has_not_been_received]. To avoid repetition, we give
    build some generic definitions first. **)

(** General signature of a message oracle **)

    Definition state_message_oracle
      := vstate vlsm -> message -> Prop.

    Definition specialized_selected_message_exists_in_all_traces
      (X : VLSM message)
      (message_selector : message -> transition_item -> Prop)
      (s : state)
      (m : message)
      : Prop
      :=
      forall
      (start : state)
      (tr : list transition_item)
      (Htr : finite_valid_trace_init_to X start s tr),
      trace_has_message message_selector m tr.

    Definition selected_message_exists_in_all_preloaded_traces
      := specialized_selected_message_exists_in_all_traces pre_vlsm.

    Definition specialized_selected_message_exists_in_some_traces
      (X : VLSM message)
      (message_selector : message -> transition_item -> Prop)
      (s : state)
      (m : message)
      : Prop
      :=
      exists
      (start : state)
      (tr : list transition_item)
      (Htr : finite_valid_trace_init_to X start s tr),
      trace_has_message message_selector m tr.

    Definition selected_message_exists_in_some_preloaded_traces: forall
      (message_selector : message -> transition_item -> Prop)
      (s : state)
      (m : message),
        Prop
      := specialized_selected_message_exists_in_some_traces pre_vlsm.

    Definition specialized_selected_message_exists_in_no_trace
      (X : VLSM message)
      (message_selector : message -> transition_item -> Prop)
      (s : state)
      (m : message)
      : Prop
      :=
      forall
      (start : state)
      (tr : list transition_item)
      (Htr : finite_valid_trace_init_to X start s tr),
      ~trace_has_message message_selector m tr.

    Definition selected_message_exists_in_no_preloaded_trace :=
      specialized_selected_message_exists_in_no_trace pre_vlsm.

    Lemma selected_message_exists_not_some_iff_no
      (X : VLSM message)
      (message_selector : message -> transition_item -> Prop)
      (s : state)
      (m : message)
      : ~ specialized_selected_message_exists_in_some_traces X message_selector s m
        <-> specialized_selected_message_exists_in_no_trace X message_selector s m.
    Proof.
      split.
      - by intros Hnot is tr Htr Hsend; apply Hnot; exists is, tr, Htr.
      - by intros Hno (is & tr & Htr & Hsend); eapply Hno.
    Qed.

    Lemma selected_message_exists_preloaded_not_some_iff_no
      (message_selector : message -> transition_item -> Prop)
      (s : state)
      (m : message)
      : ~ selected_message_exists_in_some_preloaded_traces message_selector s m
        <-> selected_message_exists_in_no_preloaded_trace message_selector s m.
    Proof.
      apply selected_message_exists_not_some_iff_no.
    Qed.

    (** Sufficient condition for 'specialized_selected_message_exists_in_some_traces'
    *)
    Lemma specialized_selected_message_exists_in_some_traces_from
      (X : VLSM message)
      (message_selector : message -> transition_item -> Prop)
      (s : state)
      (m : message)
      (start : state)
      (tr : list transition_item)
      (Htr : finite_valid_trace_from_to X start s tr)
      (Hsome : trace_has_message message_selector m tr)
      : specialized_selected_message_exists_in_some_traces X message_selector s m.
    Proof.
      assert (valid_state_prop X start) as Hstart
        by (apply valid_trace_first_pstate in Htr; done).
      apply valid_state_has_trace in Hstart.
      destruct Hstart as [is [tr' Htr']].
      assert (finite_valid_trace_init_to X is s (tr'++tr)).
      {
        destruct Htr'.
        by split; [apply finite_valid_trace_from_to_app with start |].
      }
      exists _, _, H.
      by apply Exists_app; right.
    Qed.

    Definition selected_messages_consistency_prop
      (message_selector : message -> transition_item -> Prop)
      (s : vstate vlsm)
      (m : message)
      : Prop
      :=
      selected_message_exists_in_some_preloaded_traces message_selector s m
      <-> selected_message_exists_in_all_preloaded_traces message_selector s m.

    Lemma selected_message_exists_in_all_traces_initial_state
      (s : vstate vlsm)
      (Hs : vinitial_state_prop vlsm s)
      (message_selector : message -> transition_item -> Prop)
      (m : message)
      : ~ selected_message_exists_in_all_preloaded_traces message_selector s m.
    Proof.
      intro Hselected.
      assert (Hps : valid_state_prop pre_vlsm s)
        by (apply initial_state_is_valid; done).
      assert (Htr : finite_valid_trace_init_to pre_vlsm s s []).
      { by split; [constructor |]. }
      specialize (Hselected s [] Htr).
      unfold trace_has_message in Hselected.
      by rewrite Exists_nil in Hselected.
    Qed.

(** Checks if all [valid_trace]s leading to a certain state contain a certain message.
    The [message_selector] argument specifices whether we're looking for received or sent
    messages.

    Notably, the [valid_trace]s over which we are iterating belong to the preloaded
    version of the target VLSM. This is because we want VLSMs to have oracles which
    are valid irrespective of the composition they take part in. As we know,
    the behaviour preloaded VLSMs includes behaviours of its projections in any
    composition. **)

    Definition all_traces_have_message_prop
      (message_selector : message -> transition_item -> Prop)
      (oracle : state_message_oracle)
      (s : state)
      (m : message)
      : Prop
      :=
      oracle s m <-> selected_message_exists_in_all_preloaded_traces message_selector s m.

    Definition no_traces_have_message_prop
      (message_selector : message -> transition_item -> Prop)
      (oracle : state_message_oracle)
      (s : state)
      (m : message)
      : Prop
      :=
      oracle s m <-> selected_message_exists_in_no_preloaded_trace message_selector s m.

    Definition has_been_sent_prop : state_message_oracle -> state -> message -> Prop
      := (all_traces_have_message_prop (field_selector output)).

    Definition has_not_been_sent_prop : state_message_oracle -> state -> message -> Prop
      := (no_traces_have_message_prop (field_selector output)).

    Definition has_been_received_prop : state_message_oracle -> state -> message -> Prop
      := (all_traces_have_message_prop (field_selector input)).

    Definition has_not_been_received_prop : state_message_oracle -> state -> message -> Prop
      := (no_traces_have_message_prop (field_selector input)).

(** Per the vocabulary of the official VLSM document, we say that VLSMs endowed
    with a [state_message_oracle] for sent messages have the [has_been_sent] capability.
    Capabilities for receiving messages are treated analogously, so we omit mentioning
    them explicitly.

    Notably, we also define the [has_not_been_sent] oracle, which decides if a message
    has definitely not been sent, on any of the traces producing a current state.

    Furthermore, we require a [sent_excluded_middle] property, which stipulates
    that any argument to the oracle should return true in exactly one of
    [has_been_sent] and [has_not_been_sent]. **)

    Class HasBeenSentCapability := {
      has_been_sent: state_message_oracle;
      has_been_sent_dec :> RelDecision has_been_sent;

      proper_sent:
        forall (s : state)
               (Hs : valid_state_prop pre_vlsm s)
               (m : message),
               (has_been_sent_prop has_been_sent s m);

      has_not_been_sent: state_message_oracle
        := fun (s : state) (m : message) => ~ has_been_sent s m;

      proper_not_sent:
        forall (s : state)
               (Hs : valid_state_prop pre_vlsm s)
               (m : message),
               has_not_been_sent_prop has_not_been_sent s m;
    }.

    (** Reverse implication for 'selected_messages_consistency_prop'
    always holds. *)
    Lemma consistency_from_valid_state_proj2
      (s : state)
      (Hs: valid_state_prop pre_vlsm s)
      (m : message)
      (selector : message -> transition_item -> Prop)
      (Hall : selected_message_exists_in_all_preloaded_traces selector s m)
      : selected_message_exists_in_some_preloaded_traces selector s m.
    Proof.
      apply valid_state_has_trace in Hs.
      destruct Hs as [is [tr Htr]].
      exists _, _, Htr.
      apply (Hall _ _ Htr).
    Qed.

    Lemma has_been_sent_consistency
      `{HasBeenSentCapability}
      (s : state)
      (Hs : valid_state_prop pre_vlsm s)
      (m : message)
      : selected_messages_consistency_prop (field_selector output) s m.
    Proof.
      split.
      - intro Hsome.
        destruct (decide (has_been_sent s m)) as [Hsm|Hsm].
        + by apply proper_sent in Hsm.
        + apply proper_not_sent in Hsm; [| done].
          destruct Hsome as [is [tr [Htr Hmsg]]].
          by elim (Hsm _ _ Htr).
      - by apply consistency_from_valid_state_proj2.
    Qed.

    Lemma can_produce_has_been_sent
      `{HasBeenSentCapability}
      (s : state)
      (m : message)
      (Hsm : can_produce pre_vlsm s m)
      : has_been_sent s m.
    Proof.
      assert (valid_state_prop pre_vlsm s).
      { by apply can_produce_valid in Hsm; eexists. }
      apply proper_sent; [done |].
      apply has_been_sent_consistency; [done |].
      apply non_empty_valid_trace_from_can_produce in Hsm.
      destruct Hsm as [is [tr [lst_tr [Htr [Hlst [Hs Hm]]]]]].
      destruct_list_last tr tr' _lst_tr Heqtr; [inversion Hlst|].
      rewrite last_error_is_last in Hlst.
      inversion Hlst; subst _lst_tr; clear Hlst.
      apply valid_trace_add_default_last in Htr.
      rewrite finite_trace_last_is_last, Hs in Htr.
      eexists _, _, Htr.
      by apply Exists_app; right; left.
    Qed.

    (** Sufficent condition for 'proper_sent' avoiding the
    'pre_loaded_with_all_messages_vlsm'
    *)
    Lemma specialized_proper_sent
      `{HasBeenSentCapability}
      (s : state)
      (Hs : valid_state_prop vlsm s)
      (m : message)
      (Hsome : specialized_selected_message_exists_in_some_traces vlsm (field_selector output) s m)
      : has_been_sent s m.
    Proof.
      destruct Hs as [_om Hs].
      assert (Hpres : valid_state_prop pre_vlsm s).
      { exists _om. by apply pre_loaded_with_all_messages_valid_state_message_preservation. }
      apply proper_sent; [done |].
      specialize (has_been_sent_consistency s Hpres m) as Hcons.
      apply Hcons.
      destruct Hsome as [is [tr [Htr Hsome]]].
      exists is, tr.
      split; [| done].
      revert Htr.
      unfold pre_vlsm;clear.
      destruct vlsm as (T,M).
      apply VLSM_incl_finite_valid_trace_init_to.
      apply vlsm_incl_pre_loaded_with_all_messages_vlsm.
    Qed.

    (** 'proper_sent' condition specialized to regular vlsm traces
    (avoiding 'pre_loaded_with_all_messages_vlsm')
    *)
    Lemma specialized_proper_sent_rev
      `{HasBeenSentCapability}
      (s : state)
      (Hs : valid_state_prop vlsm s)
      (m : message)
      (Hsm : has_been_sent s m)
      : specialized_selected_message_exists_in_all_traces vlsm (field_selector output) s m.
    Proof.
      destruct Hs as [_om Hs].
      assert (Hpres : valid_state_prop pre_vlsm s).
      { exists _om. by apply pre_loaded_with_all_messages_valid_state_message_preservation. }
      apply proper_sent in Hsm; [| done].
      intros is tr Htr.
      specialize (Hsm is tr).
      spec Hsm; [| done].
      revert Htr.
      unfold pre_vlsm;clear.
      destruct vlsm as (T,M).
      apply VLSM_incl_finite_valid_trace_init_to.
      apply vlsm_incl_pre_loaded_with_all_messages_vlsm.
    Qed.

    Lemma has_been_sent_consistency_proper_not_sent
      (has_been_sent: state_message_oracle)
      (has_been_sent_dec: RelDecision has_been_sent)
      (s : state)
      (m : message)
      (proper_sent: has_been_sent_prop has_been_sent s m)
      (has_not_been_sent
        := fun (s : state) (m : message) => ~ has_been_sent s m)
      (Hconsistency : selected_messages_consistency_prop (field_selector output) s m)
      : has_not_been_sent_prop has_not_been_sent s m.
    Proof.
      unfold has_not_been_sent_prop.
      unfold no_traces_have_message_prop.
      unfold has_not_been_sent.
      rewrite <- selected_message_exists_preloaded_not_some_iff_no.
      by apply not_iff_compat, (iff_trans proper_sent).
    Qed.


    Class HasBeenReceivedCapability := {
      has_been_received: state_message_oracle;
      has_been_received_dec :> RelDecision has_been_received;

      proper_received:
        forall (s : state)
               (Hs : valid_state_prop pre_vlsm s)
               (m : message),
               (has_been_received_prop has_been_received s m);

      has_not_been_received: state_message_oracle
        := fun (s : state) (m : message) => ~ has_been_received s m;

      proper_not_received:
        forall (s : state)
               (Hs : valid_state_prop pre_vlsm s)
               (m : message),
               has_not_been_received_prop has_not_been_received s m;
    }.

    Lemma has_been_received_consistency
      `{HasBeenReceivedCapability}
      (s : state)
      (Hs : valid_state_prop pre_vlsm s)
      (m : message)
      : selected_messages_consistency_prop (field_selector input) s m.
    Proof.
      split.
      - intro Hsome.
        destruct (decide (has_been_received s m)) as [Hsm|Hsm];
          [by apply proper_received in Hsm |].
        apply proper_not_received in Hsm; [| done].
        destruct Hsome as [is [tr [Htr Hsome]]].
        by elim (Hsm _ _ Htr).
      - by apply consistency_from_valid_state_proj2.
    Qed.

    Lemma has_been_received_consistency_proper_not_received
      (has_been_received: state_message_oracle)
      (has_been_received_dec: RelDecision has_been_received)
      (s : state)
      (m : message)
      (proper_received: has_been_received_prop has_been_received s m)
      (has_not_been_received
        := fun (s : state) (m : message) => ~ has_been_received s m)
      (Hconsistency : selected_messages_consistency_prop (field_selector input) s m)
      : has_not_been_received_prop has_not_been_received s m.
    Proof.
      unfold has_not_been_received_prop.
      unfold no_traces_have_message_prop.
      unfold has_not_been_received.
      split.
      - intros Hsm is tr Htr Hsome.
        assert (Hsm' : selected_message_exists_in_some_preloaded_traces (field_selector input) s m)
          by (exists is; exists tr; exists Htr; done).
        apply Hconsistency in Hsm'.
        by apply proper_received in Hsm'.
      - intro Hnone. destruct (decide (has_been_received s m)) as [Hsm | Hsm]; [| done].
        apply proper_received in Hsm. apply Hconsistency in Hsm.
        destruct Hsm as [is [tr [Htr Hsm]]].
        by elim (Hnone is tr Htr).
    Qed.

    Definition sent_messages
      (s : vstate vlsm)
      : Type
      :=
      sig (fun m => selected_message_exists_in_some_preloaded_traces (field_selector output) s m).

    Lemma sent_messages_proper
      `{HasBeenSentCapability}
      (s : vstate vlsm)
      (Hs : valid_state_prop pre_vlsm s)
      (m : message)
      : has_been_sent s m <-> exists (m' : sent_messages s), proj1_sig m' = m.
    Proof.
      unfold sent_messages. rewrite exists_proj1_sig.
      specialize (proper_sent s Hs m) as Hbs.
      unfold has_been_sent_prop,all_traces_have_message_prop in Hbs.
      rewrite Hbs.
      symmetry.
      by apply has_been_sent_consistency.
    Qed.

    Definition received_messages
      (s : vstate vlsm)
      : Type
      :=
      sig (fun m => selected_message_exists_in_some_preloaded_traces (field_selector input) s m).

    Lemma received_messages_proper
      `{HasBeenReceivedCapability}
      (s : vstate vlsm)
      (Hs : valid_state_prop pre_vlsm s)
      (m : message)
      : has_been_received s m <-> exists (m' : received_messages s), proj1_sig m' = m.
    Proof.
      unfold received_messages. rewrite exists_proj1_sig.
      specialize (proper_received s Hs m) as Hbs.
      unfold has_been_received_prop,all_traces_have_message_prop in Hbs.
      rewrite Hbs.
      symmetry.
      by apply has_been_received_consistency.
    Qed.

    Class ComputableSentMessages := {
      sent_messages_fn : vstate vlsm -> list message;

      sent_messages_full :
        forall (s : vstate vlsm) (Hs : valid_state_prop pre_vlsm s) (m : message),
          m ∈ (sent_messages_fn s) <-> exists (sm : sent_messages s), proj1_sig sm = m;

      sent_messages_consistency :
        forall
          (s : vstate vlsm)
          (Hs : valid_state_prop pre_vlsm s)
          (m : message),
          selected_messages_consistency_prop (field_selector output) s m
    }.

    Lemma ComputableSentMessages_initial_state_empty
      {Hrm : ComputableSentMessages}
      (s : vinitial_state vlsm)
      : sent_messages_fn (proj1_sig s) = [].
    Proof.
      assert (Hps : valid_state_prop pre_vlsm (proj1_sig s))
        by (apply initial_state_is_valid; apply proj2_sig).
      destruct s as [s Hs]. simpl in *.
      destruct (sent_messages_fn s) as [|m l] eqn: Hsm; [done |].
      specialize (sent_messages_full s Hps m) as Hl. apply proj1 in Hl.
      spec Hl; [by rewrite Hsm; left |].
      destruct Hl as [[m0 Hm] Heq]. simpl in Heq. subst m0.
      apply sent_messages_consistency in Hm; [| done].
      by apply selected_message_exists_in_all_traces_initial_state in Hm.
    Qed.

    Definition ComputableSentMessages_has_been_sent
      {Hsm : ComputableSentMessages}
      (s : vstate vlsm)
      (m : message)
      : Prop
      :=
      m ∈ (sent_messages_fn s).

    Global Instance computable_sent_message_has_been_sent_dec
      {Hsm : ComputableSentMessages}
      `{EqDecision message}
      : RelDecision ComputableSentMessages_has_been_sent :=
      fun s m => decide_rel _ _ (sent_messages_fn s).

    Lemma ComputableSentMessages_has_been_sent_proper
      {Hsm : ComputableSentMessages}
      (s : state)
      (Hs : valid_state_prop pre_vlsm s)
      (m : message)
      : has_been_sent_prop ComputableSentMessages_has_been_sent s m.
    Proof.
      unfold has_been_sent_prop. unfold all_traces_have_message_prop.
      unfold ComputableSentMessages_has_been_sent.
      split.
      - intro Hin.
        apply sent_messages_full in Hin; [| done].
        destruct Hin as [[m0 Hm0] [= ->]].
        by apply (sent_messages_consistency s Hs m).
      - intro H.
        apply (sent_messages_consistency s Hs m) in H.
        apply sent_messages_full; [done |].
        by exists (exist _ m H).
    Qed.

    Definition ComputableSentMessages_has_not_been_sent
      {Hsm : ComputableSentMessages}
      (s : vstate vlsm)
      (m : message)
      : Prop
      :=
      ~ ComputableSentMessages_has_been_sent s m.

    Lemma ComputableSentMessages_has_not_been_sent_proper
      {Hsm : ComputableSentMessages}
      (s : state)
      (Hs : valid_state_prop pre_vlsm s)
      (m : message)
      : has_not_been_sent_prop ComputableSentMessages_has_not_been_sent s m.
    Proof.
      unfold has_not_been_sent_prop. unfold no_traces_have_message_prop.
      unfold ComputableSentMessages_has_not_been_sent.
      unfold ComputableSentMessages_has_been_sent.
      split.
      - intro Hin.
        cut (~ selected_message_exists_in_some_preloaded_traces (field_selector output) s m).
        { intros Hno is tr Htr Hexists.
          contradict Hno. by exists is, tr, Htr.
        }
        contradict Hin.
        apply sent_messages_full; [done |].
        by exists (exist _ m Hin).
      - intros Htrace Hin.
        apply sent_messages_full in Hin; [| done].
        destruct Hin as [[m0 Hm] Heq];simpl in Heq;subst m0.
        destruct Hm as [is [tr [Htr Hex]]].
        apply (Htrace is tr Htr Hex).
    Qed.

    Definition ComputableSentMessages_HasBeenSentCapability
      {Hsm : ComputableSentMessages}
      `{EqDecision message}
      : HasBeenSentCapability
      :=
      {|
        has_been_sent := ComputableSentMessages_has_been_sent;
        proper_sent := ComputableSentMessages_has_been_sent_proper;
        proper_not_sent := ComputableSentMessages_has_not_been_sent_proper
      |}.

    Class ComputableReceivedMessages := {
      received_messages_fn : vstate vlsm -> list message;

      received_messages_full :
        forall (s : vstate vlsm) (Hs : valid_state_prop pre_vlsm s) (m : message),
          m ∈ (received_messages_fn s) <-> exists (sm : received_messages s), proj1_sig sm = m;

      received_messages_consistency :
        forall
          (s : vstate vlsm)
          (Hs : valid_state_prop pre_vlsm s)
          (m : message),
          selected_messages_consistency_prop (field_selector input) s m
    }.

    Lemma ComputableReceivedMessages_initial_state_empty
      {Hrm : ComputableReceivedMessages}
      (s : vinitial_state vlsm)
      : received_messages_fn (proj1_sig s) = [].
    Proof.
      assert (Hps : valid_state_prop pre_vlsm (proj1_sig s))
        by (apply initial_state_is_valid;apply proj2_sig).
      destruct s as [s Hs]. simpl in *.
      destruct (received_messages_fn s) as [|m l] eqn: Hrcv; [done |].
      specialize (received_messages_full s Hps m) as Hl. apply proj1 in Hl.
      spec Hl; [by rewrite Hrcv; left |].
      destruct Hl as [[m0 Hm] Heq]. simpl in Heq. subst m0.
      apply received_messages_consistency in Hm; [| done].
      by apply selected_message_exists_in_all_traces_initial_state in Hm.
    Qed.

    Definition ComputableReceivedMessages_has_been_received
      {Hsm : ComputableReceivedMessages}
      (s : vstate vlsm)
      (m : message)
      : Prop
      :=
      m ∈ (received_messages_fn s).

    Global Instance ComputableReceivedMessages_has_been_received_dec
      {Hsm : ComputableReceivedMessages}
      `{EqDecision message}
      : RelDecision ComputableReceivedMessages_has_been_received
      := fun s m => decide_rel _ _ (received_messages_fn s).

    Lemma ComputableReceivedMessages_has_been_received_proper
      {Hsm : ComputableReceivedMessages}
      (s : state)
      (Hs : valid_state_prop pre_vlsm s)
      (m : message)
      : has_been_received_prop ComputableReceivedMessages_has_been_received s m.
    Proof.
      unfold has_been_received_prop. unfold all_traces_have_message_prop.
      unfold ComputableReceivedMessages_has_been_received.
      split.
      - intro Hin.
        apply received_messages_full in Hin; [| done].
        destruct Hin as [[m0 Hm] Heq];simpl in Heq;subst m0.
        by apply received_messages_consistency.
      - intro H. apply received_messages_full; [done |].
        apply (received_messages_consistency s Hs m) in H.
        by exists (exist _ m H).
    Qed.

    Definition ComputableReceivedMessages_has_not_been_received
      {Hsm : ComputableReceivedMessages}
      (s : vstate vlsm)
      (m : message)
      : Prop
      :=
      ~ ComputableReceivedMessages_has_been_received s m.

    Lemma ComputableReceivedMessages_has_not_been_received_proper
      {Hsm : ComputableReceivedMessages}
      (s : state)
      (Hs : valid_state_prop pre_vlsm s)
      (m : message)
      : has_not_been_received_prop ComputableReceivedMessages_has_not_been_received s m.
    Proof.
      unfold has_not_been_received_prop. unfold no_traces_have_message_prop.
      unfold ComputableReceivedMessages_has_not_been_received.
      unfold ComputableReceivedMessages_has_been_received.
      rewrite <- selected_message_exists_preloaded_not_some_iff_no.
      apply not_iff_compat.
      rewrite received_messages_full; [| done].
      unfold received_messages.
      by rewrite exists_proj1_sig.
    Qed.

    Definition ComputableReceivedMessages_HasBeenReceivedCapability
      {Hsm : ComputableReceivedMessages}
      `{EqDecision message}
      : HasBeenReceivedCapability
      :=
      {|
        has_been_received := ComputableReceivedMessages_has_been_received;
        proper_received := ComputableReceivedMessages_has_been_received_proper;
        proper_not_received := ComputableReceivedMessages_has_not_been_received_proper
      |}.
End Simple.

Global Hint Mode HasBeenSentCapability - ! : typeclass_instances.
Global Hint Mode HasBeenReceivedCapability - ! : typeclass_instances.

(** *** Stepwise consistency properties for [state_message_oracle]

 The above definitions like [all_traces_have_message_prop]
 connect a [state_message_oracle] to a predicate on
 [transition_item] by relating the oracle holding on a state
 to a satsifying transition existing in all traces.

 This is equivalent to two local properties,
 one is that the oracle cannot only for any initial state,
 the other is that the oracle judgement is appropriately
 related for the starting and [destination] states of
 any [input_valid_transition].

 These conditions are defined in the record [oracle_stepwise_props]
 *)

Record oracle_stepwise_props
       [message] [vlsm: VLSM message]
       (message_selector: message -> transition_item -> Prop)
       (oracle: state_message_oracle vlsm) : Prop :=
  {oracle_no_inits: forall (s: vstate vlsm),
      initial_state_prop (VLSMMachine:=vmachine vlsm) s ->
      forall m, ~oracle s m;
   oracle_step_update:
       forall l s im s' om,
         input_valid_transition (pre_loaded_with_all_messages_vlsm vlsm) l (s,im) (s',om) ->
         forall msg, oracle s' msg <->
                     (message_selector msg {|l:=l; input:=im; destination:=s'; output:=om|}
                      \/ oracle s msg)
  }.
Arguments oracle_no_inits {message} {vlsm} {message_selector} {oracle} _.
Arguments oracle_step_update {message} {vlsm} {message_selector} {oracle} _.

Lemma oracle_partial_trace_update
      [message] [vlsm: VLSM message]
      [selector: message -> transition_item -> Prop]
      [oracle: state_message_oracle vlsm]
      (Horacle: oracle_stepwise_props selector oracle)
      s0 s tr
         (Htr: finite_valid_trace_from_to (pre_loaded_with_all_messages_vlsm vlsm) s0 s tr):
    forall m,
      oracle s m
      <-> (trace_has_message selector m tr \/ oracle s0 m).
Proof.
  induction Htr.
  - intro m.
    unfold trace_has_message.
    rewrite Exists_nil.
    itauto.
  - intro m. specialize (IHHtr m).
    unfold trace_has_message.
    rewrite Exists_cons.
    apply (Horacle.(oracle_step_update)) with (msg:=m) in Ht.
    itauto.
Qed.

Lemma oracle_initial_trace_update
      [message] [vlsm: VLSM message]
      [selector]
      [oracle : state_message_oracle vlsm]
      (Horacle: oracle_stepwise_props selector oracle)
      s0 s tr
      (Htr: finite_valid_trace_init_to (pre_loaded_with_all_messages_vlsm vlsm) s0 s tr):
  forall m,
    oracle s m <-> trace_has_message selector m tr.
Proof.
  intros m.
  pose proof (oracle_partial_trace_update Horacle _ _ _ (proj1 Htr) m).
  pose proof (oracle_no_inits Horacle s0 (proj2 Htr) m).
  clear -H H0. itauto.
Qed.

(* TODO(wkolowski): make notation uniform accross the file. *)
Lemma oracle_stepwise_props_change_selector
      [message] [vlsm: VLSM message]
      [selector]
      [oracle : state_message_oracle vlsm]
      (Horacle: oracle_stepwise_props selector oracle)
      selector'
      (Heqv :
        forall s item,
          input_valid_transition_item (pre_loaded_with_all_messages_vlsm vlsm) s item ->
          forall m, selector m item <-> selector' m item)
      : oracle_stepwise_props selector' oracle.
Proof.
  destruct Horacle as [Hinits Hupdate].
  constructor; [done |].
  intros l s om s' om' Ht msg.
  by simpl; rewrite Hupdate, Heqv.
Qed.

(**
   Proving the trace properties from the stepwise properties
   begins with a lemma using induction along a trace to
   prove that given a [finite_valid_trace] to a state,
   the oracle holds at that state for some message iff
   a satsifying transition item exists in the trace.

   The theorems for [all_traces_have_message_prop]
   and [no_traces_have_message_prop] are mostly rearraning
   quantifiers to use this lemma, also using [valid_state_prop]
   to choose a trace to the state for the directions where
   one is not given.
 *)
Section TraceFromStepwise.
  Context
    (message : Type)
    (vlsm: VLSM message)
    (selector : message -> transition_item -> Prop)
    (oracle : state_message_oracle vlsm)
    (oracle_props : oracle_stepwise_props selector oracle)
    .

  Local Lemma H_valid_trace_prop
        [s0 s tr]
        (Htr: finite_valid_trace_init_to (pre_loaded_with_all_messages_vlsm vlsm) s0 s tr):
    forall m,
      oracle s m <-> trace_has_message selector m tr.
  Proof.
    intro m.
    destruct Htr as [Htr Hinit].
    rewrite (oracle_partial_trace_update oracle_props _ _ _ Htr).
    assert (~oracle s0 m).
    apply oracle_props, Hinit.
    itauto.
  Qed.

  Lemma prove_all_have_message_from_stepwise:
    forall (s : state)
           (Hs : valid_state_prop (pre_loaded_with_all_messages_vlsm vlsm) s)
           (m : message),
      (all_traces_have_message_prop vlsm selector oracle s m).
  Proof.
    intros s Hproto m.
    unfold all_traces_have_message_prop.
    split.
    - intros Hsent s0 tr Htr.
      by eapply H_valid_trace_prop.
    - intro H_all_traces.
      apply valid_state_has_trace in Hproto.
      destruct Hproto as [s0 [tr Htr]].
      apply (H_valid_trace_prop Htr).
      by specialize (H_all_traces s0 tr Htr).
  Qed.

  Lemma prove_none_have_message_from_stepwise:
    forall (s : state)
           (Hs : valid_state_prop (pre_loaded_with_all_messages_vlsm vlsm) s)
           (m : message),
      no_traces_have_message_prop vlsm selector (fun s m => ~oracle s m) s m.
  Proof.
    intros s Hproto m.
    pose proof (H_valid_trace_prop).
    split.
    - intros H_not_sent start tr Htr.
      contradict H_not_sent.
      by apply (H_valid_trace_prop Htr).
    - intros H_no_traces.
      apply valid_state_has_trace in Hproto.
      destruct Hproto as [s0 [tr Htr]].
      specialize (H_no_traces s0 tr Htr).
      contradict H_no_traces.
      by apply (H_valid_trace_prop Htr).
  Qed.

  Lemma selected_messages_consistency_prop_from_stepwise
      (oracle_dec: RelDecision oracle)
      (s : state)
      (Hs : valid_state_prop (pre_loaded_with_all_messages_vlsm vlsm) s)
      (m : message)
      : selected_messages_consistency_prop vlsm selector s m.
  Proof.
    split.
    - intro Hsome.
      destruct (decide (oracle s m)) as [Hsm|Hsm].
      + by apply prove_all_have_message_from_stepwise in Hsm.
      + apply prove_none_have_message_from_stepwise in Hsm; [| done].
        destruct Hsome as [is [tr [Htr Hmsg]]].
        by elim (Hsm _ _ Htr).
    - by apply consistency_from_valid_state_proj2.
  Qed.

  Lemma in_futures_preserving_oracle_from_stepwise:
    forall (s1 s2: state)
      (Hfutures : in_futures (pre_loaded_with_all_messages_vlsm vlsm) s1 s2)
      (m : message),
      oracle s1 m -> oracle  s2 m.
  Proof.
    intros s1 s2 [tr Htr] m Hs1m.
    by eapply oracle_partial_trace_update; [| | right].
  Qed.

End TraceFromStepwise.

(**
   The stepwise properties are proven from the trace properties
   by considering the empty trace to prove the [oracle_no_inits]
   property, and by considering a trace that ends with the given
   [input_valid_transition] to prove the [oracle_step_update] property.
 *)
Section StepwiseFromTrace.
  Context
    (message : Type)
    (vlsm: VLSM message)
    (selector: message -> transition_item -> Prop)
    (oracle: state_message_oracle vlsm)
    (oracle_dec: RelDecision oracle)
    (Horacle_all_have:
       forall s (Hs: valid_state_prop (pre_loaded_with_all_messages_vlsm vlsm) s) m,
        all_traces_have_message_prop vlsm selector oracle s m)
    (Hnot_oracle_none_have:
       forall s (Hs: valid_state_prop (pre_loaded_with_all_messages_vlsm vlsm) s) m,
         no_traces_have_message_prop vlsm selector (fun m s => ~oracle m s) s m).

  Lemma oracle_no_inits_from_trace:
    forall (s: vstate vlsm), initial_state_prop (VLSMMachine:=vmachine vlsm) s ->
                             forall m, ~oracle s m.
  Proof.
    intros s Hinit m Horacle.
    assert (Hproto : valid_state_prop (pre_loaded_with_all_messages_vlsm vlsm) s)
      by (apply initial_state_is_valid; done).
    apply Horacle_all_have in Horacle;[| done].
    specialize (Horacle s nil).
    eapply Exists_nil;apply Horacle;clear Horacle.
    by split; [constructor |].
  Qed.

  Lemma examine_one_trace:
    forall is s tr,
      finite_valid_trace_init_to (pre_loaded_with_all_messages_vlsm vlsm) is s tr ->
    forall m,
      oracle s m <->
      trace_has_message selector m tr.
  Proof.
    intros is s tr Htr m.
    assert (valid_state_prop (pre_loaded_with_all_messages_vlsm vlsm) s)
      by (apply valid_trace_last_pstate in Htr; done).
    split.
    - intros Horacle.
      apply Horacle_all_have in Horacle; [| done].
      by specialize (Horacle is tr Htr).
    - intro Hexists.
      apply dec_stable.
      intro Hnot.
      apply Hnot_oracle_none_have in Hnot; [| done].
      rewrite <- selected_message_exists_preloaded_not_some_iff_no in Hnot.
      apply Hnot.
      by exists is, tr, Htr.
  Qed.

  Lemma oracle_step_property_from_trace:
       forall l s im s' om,
         input_valid_transition (pre_loaded_with_all_messages_vlsm vlsm) l (s,im) (s',om) ->
         forall msg, oracle s' msg
                     <-> (selector msg {| l:=l; input:=im; destination:=s'; output:=om |}
                          \/ oracle s msg).
  Proof.
    intros l s im s' om Htrans msg.
    rename Htrans into Htrans'.
    pose proof Htrans' as [[Hproto_s [Hproto_m Hvalid]] Htrans].
    set (preloaded:= pre_loaded_with_all_messages_vlsm vlsm) in * |- *.

    pose proof (valid_state_has_trace _ _ Hproto_s)
      as [is [tr [Htr Hinit]]].

    pose proof (Htr' := extend_right_finite_trace_from_to _ Htr Htrans').

    rewrite (examine_one_trace _ _ _ (conj Htr Hinit) msg).
    rewrite (examine_one_trace _ _ _ (conj Htr' Hinit) msg).
    clear.
    progress cbn. unfold trace_has_message.
    rewrite Exists_app, Exists_cons, Exists_nil.
    itauto.
  Qed.

  Lemma stepwise_props_from_trace : oracle_stepwise_props selector oracle.
  Proof.
    constructor.
    refine oracle_no_inits_from_trace.
    refine oracle_step_property_from_trace.
  Defined.
End StepwiseFromTrace.

(** ** Stepwise view of [HasBeenSentCapability]

This reduces the proof obligations in [HasBeenSentCapability]
to proving the stepwise properties of [oracle_stepwise_props].
[has_been_step_stepwise_props] is a specialization of [oracle_stepwise_props]
to the right <<message_selector>>.

There are also lemmas for accessing the stepwise properties about
a [has_been_sent] predicate given an instance of [HasBeenSentCapability], to allow using
[HasBeenSentCapability_from_stepwise] to define a [HasBeenSentCapability]
for composite VLSMs, or for proofs (e.g, about invariants) where
these are more convenient.
 **)

Definition has_been_sent_stepwise_props
       [message] [vlsm: VLSM message] (has_been_sent_pred: state_message_oracle vlsm) : Prop :=
  (oracle_stepwise_props (field_selector output) has_been_sent_pred).

Lemma HasBeenSentCapability_from_stepwise
      [message : Type]
      [vlsm: VLSM message]
      [has_been_sent_pred: state_message_oracle vlsm]
      (has_been_sent_pred_dec: RelDecision has_been_sent_pred)
      (has_been_sent_alt_props: has_been_sent_stepwise_props has_been_sent_pred):
  HasBeenSentCapability vlsm.
Proof.
  refine ({|has_been_sent:=has_been_sent_pred|}).
  - by apply prove_all_have_message_from_stepwise.
  - by apply prove_none_have_message_from_stepwise.
Defined.

Lemma has_been_sent_stepwise_from_trace
      [message : Type]
      (vlsm: VLSM message)
      `{HasBeenSentCapability message vlsm}:
  oracle_stepwise_props (field_selector output) (has_been_sent vlsm).
Proof.
  apply stepwise_props_from_trace.
  apply has_been_sent_dec.
  apply proper_sent.
  apply proper_not_sent.
Defined.

Lemma preloaded_has_been_sent_stepwise_props
      [message : Type]
      (vlsm: VLSM message)
      `{HasBeenSentCapability message vlsm}
      (seed : message -> Prop)
      (X := pre_loaded_vlsm vlsm seed):
  has_been_sent_stepwise_props (vlsm := X) (has_been_sent vlsm).
Proof.
  by destruct (has_been_sent_stepwise_from_trace vlsm).
Qed.

Global Instance preloaded_HasBeenSentCapability
      [message : Type]
      (vlsm: VLSM message)
      `{HasBeenSentCapability message vlsm}
      (seed : message -> Prop):
  HasBeenSentCapability (pre_loaded_vlsm vlsm seed).
Proof.
  eapply HasBeenSentCapability_from_stepwise.
  - apply (has_been_sent_dec vlsm).
  - apply preloaded_has_been_sent_stepwise_props.
Defined.

Lemma has_been_sent_step_update
      `{HasBeenSentCapability message vlsm}:
  forall [l s im s' om],
    input_valid_transition (pre_loaded_with_all_messages_vlsm vlsm) l (s,im) (s',om) ->
    forall m,
      has_been_sent vlsm s' m <-> (om = Some m \/ has_been_sent vlsm s m).
Proof.
  exact (oracle_step_update (has_been_sent_stepwise_from_trace vlsm)).
Qed.

Lemma has_been_sent_examine_one_trace
  `{HasBeenSentCapability message vlsm}:
  forall is s tr,
    finite_valid_trace_init_to (pre_loaded_with_all_messages_vlsm vlsm) is s tr ->
  forall m,
    has_been_sent vlsm s m <->
    trace_has_message (field_selector output) m tr.
Proof.
  apply examine_one_trace.
  - apply has_been_sent_dec.
  - apply proper_sent.
  - apply proper_not_sent.
Qed.

(** ** Stepwise view of [HasBeenReceivedCapability] *)

Definition has_been_received_stepwise_props
       [message] [vlsm: VLSM message] (has_been_received_pred: state_message_oracle vlsm) : Prop :=
  (oracle_stepwise_props (field_selector input) has_been_received_pred).

Lemma HasBeenReceivedCapability_from_stepwise
      [message : Type]
      [vlsm: VLSM message]
      [has_been_received_pred: state_message_oracle vlsm]
      (has_been_received_pred_dec: RelDecision has_been_received_pred)
      (has_been_sent_alt_props: has_been_received_stepwise_props has_been_received_pred):
  HasBeenReceivedCapability vlsm.
Proof.
  refine ({|has_been_received:=has_been_received_pred|}).
  - by apply prove_all_have_message_from_stepwise.
  - by apply prove_none_have_message_from_stepwise.
Defined.

Lemma has_been_received_stepwise_from_trace
      [message : Type]
      (vlsm: VLSM message)
      `{HasBeenReceivedCapability message vlsm}:
  oracle_stepwise_props (field_selector input) (has_been_received vlsm).
Proof.
  apply stepwise_props_from_trace.
  - apply has_been_received_dec.
  - apply proper_received.
  - apply proper_not_received.
Defined.

Lemma preloaded_has_been_received_stepwise_props
      {message : Type}
      (vlsm: VLSM message)
      `{HasBeenReceivedCapability message vlsm}
      (seed : message -> Prop)
      (X := pre_loaded_vlsm vlsm seed):
  has_been_received_stepwise_props (vlsm := X) (has_been_received vlsm).
Proof.
  by destruct (has_been_received_stepwise_from_trace vlsm).
Qed.

Global Instance preloaded_HasBeenReceivedCapability
      {message : Type}
      (vlsm: VLSM message)
      `{HasBeenReceivedCapability message vlsm}
      (seed : message -> Prop):
  HasBeenReceivedCapability (pre_loaded_vlsm vlsm seed).
Proof.
  eapply HasBeenReceivedCapability_from_stepwise.
  - apply (has_been_received_dec vlsm).
  - apply preloaded_has_been_received_stepwise_props.
Defined.

Lemma has_been_received_step_update
      `{HasBeenReceivedCapability message vlsm}:
  forall [l s im s' om],
    input_valid_transition (pre_loaded_with_all_messages_vlsm vlsm) l (s,im) (s',om) ->
    forall m,
      has_been_received vlsm s' m <-> (im = Some m \/ has_been_received vlsm s m).
Proof.
  exact (oracle_step_update (has_been_received_stepwise_from_trace vlsm)).
Qed.

Lemma has_been_received_examine_one_trace
  `{HasBeenReceivedCapability message vlsm}:
  forall is s tr,
    finite_valid_trace_init_to (pre_loaded_with_all_messages_vlsm vlsm) is s tr ->
  forall m,
    has_been_received vlsm s m <->
    trace_has_message (field_selector input) m tr.
Proof.
  apply examine_one_trace.
  - apply has_been_received_dec.
  - apply proper_received.
  - apply proper_not_received.
Qed.

Lemma trace_to_initial_state_has_no_inputs
  {message} vlsm
  `{HasBeenReceivedCapability message vlsm}
  is s tr
  (Htr : finite_valid_trace_init_to (pre_loaded_with_all_messages_vlsm vlsm) is s tr)
  (Hs : vinitial_state_prop vlsm s)
  : forall item, In item tr -> input item = None.
Proof.
  intros item Hitem.
  destruct (input item) as [m|] eqn:Heqm; [| done].
  elim (selected_message_exists_in_all_traces_initial_state _ _ Hs (field_selector input) m).
  apply has_been_received_consistency; [done | by apply initial_state_is_valid|].
  eexists _,_, Htr.
  apply Exists_exists. exists item. split; [| done].
  by apply elem_of_list_In.
Qed.

(** ** A state message oracle for messages sent or received

In protocols like the CBC full node protocol, validators often
work with the set of all messages they have directly observed,
which includes the messages the node sent itself along with
messages that were received.
The [has_been_directly_observed] oracle holds for a message if the
message was sent or received in any transition.
*)

Class HasBeenDirectlyObservedCapability {message} (vlsm: VLSM message) :=
  {
  has_been_directly_observed: state_message_oracle vlsm;
  has_been_directly_observed_dec :> RelDecision has_been_directly_observed;
  has_been_directly_observed_stepwise_props: oracle_stepwise_props item_sends_or_receives has_been_directly_observed;
  }.
Arguments has_been_directly_observed {message} vlsm {_}.
Arguments has_been_directly_observed_dec {message} vlsm {_}.
Arguments has_been_directly_observed_stepwise_props {message} vlsm {_}.

Global Hint Mode HasBeenDirectlyObservedCapability - ! : typeclass_instances.

Definition has_been_directly_observed_no_inits `[HasBeenDirectlyObservedCapability message vlsm]
  := oracle_no_inits (has_been_directly_observed_stepwise_props vlsm).

Definition has_been_directly_observed_step_update `{HasBeenDirectlyObservedCapability message vlsm} :
  forall l s im s' om,
    input_valid_transition (pre_loaded_with_all_messages_vlsm vlsm) l (s, im) (s', om) ->
    forall msg,
      has_been_directly_observed vlsm s' msg <->
      ((im = Some msg \/ om = Some msg) \/ has_been_directly_observed vlsm s msg)
  := oracle_step_update (has_been_directly_observed_stepwise_props vlsm).

Lemma proper_directly_observed {message} (vlsm : VLSM message) `{HasBeenDirectlyObservedCapability message vlsm}:
  forall (s:state),
    valid_state_prop (pre_loaded_with_all_messages_vlsm vlsm) s ->
    forall m,
      all_traces_have_message_prop vlsm item_sends_or_receives (has_been_directly_observed vlsm) s m.
Proof.
  intros.
  apply prove_all_have_message_from_stepwise; [| done].
  apply has_been_directly_observed_stepwise_props.
Qed.

Lemma proper_not_directly_observed `(vlsm : VLSM message) `{HasBeenDirectlyObservedCapability message vlsm}:
  forall (s:state),
    valid_state_prop (pre_loaded_with_all_messages_vlsm vlsm) s ->
    forall m,
      no_traces_have_message_prop vlsm item_sends_or_receives
                                  (fun s m => ~has_been_directly_observed vlsm s m) s m.
Proof.
  intros.
  apply prove_none_have_message_from_stepwise; [| done].
  apply has_been_directly_observed_stepwise_props.
Qed.

Lemma has_been_directly_observed_examine_one_trace
  {message} (vlsm : VLSM message) `{HasBeenDirectlyObservedCapability message vlsm}:
  forall is s tr,
    finite_valid_trace_init_to (pre_loaded_with_all_messages_vlsm vlsm) is s tr ->
  forall m,
    has_been_directly_observed vlsm s m <->
    trace_has_message item_sends_or_receives m tr.
Proof.
  apply examine_one_trace.
  - apply has_been_directly_observed_dec.
  - apply proper_directly_observed.
  - apply proper_not_directly_observed.
Qed.

(** A received message introduces no additional equivocations to a state
    if it has already been observed in s.
*)
Definition no_additional_equivocations
  {message : Type}
  (vlsm : VLSM message)
  `{HasBeenDirectlyObservedCapability message vlsm}
  (s : state)
  (m : message)
  : Prop
  :=
  has_been_directly_observed vlsm s m.

(** [no_additional_equivocations] is decidable.
*)

Lemma no_additional_equivocations_dec
  {message : Type}
  (vlsm : VLSM message)
  `{HasBeenDirectlyObservedCapability message vlsm}
  : RelDecision (no_additional_equivocations vlsm).
Proof.
  apply has_been_directly_observed_dec.
Qed.

Definition no_additional_equivocations_constraint
  {message : Type}
  (vlsm : VLSM message)
  `{HasBeenDirectlyObservedCapability message vlsm}
  (l : vlabel vlsm)
  (som : state * option message)
  : Prop
  :=
  let (s, om) := som in
  from_option (no_additional_equivocations vlsm s) True om.

Section sent_received_observed_capabilities.

Context
  {message : Type}
  (vlsm : VLSM message)
  `{HasBeenReceivedCapability message vlsm}
  `{HasBeenSentCapability message vlsm}
  .

Lemma has_been_directly_observed_sent_received_iff
  `{HasBeenDirectlyObservedCapability message vlsm}
  (s : state)
  (Hs : valid_state_prop (pre_loaded_with_all_messages_vlsm vlsm) s)
  (m : message)
  : has_been_directly_observed vlsm s m <-> has_been_received vlsm s m \/ has_been_sent vlsm s m.
Proof.
  specialize
    (prove_all_have_message_from_stepwise message vlsm  item_sends_or_receives
    (has_been_directly_observed vlsm) (has_been_directly_observed_stepwise_props _) _ Hs m) as Hall.
  split.
  - intro Hobs. destruct Hall as [Hall _]. specialize (Hall Hobs).
    apply consistency_from_valid_state_proj2 in Hall; [| done].
    destruct Hall as [is [tr [Htr Hexists]]].
    apply Exists_or_inv in Hexists.
    destruct Hexists as [Hsent | Hreceived].
    + left. specialize (has_been_received_consistency vlsm _ Hs m) as Hcons.
      apply proper_received; [done |].
      apply Hcons. by exists is, tr, Htr.
    + right. specialize (has_been_sent_consistency vlsm _ Hs m) as Hcons.
      apply proper_sent; [done |].
      apply Hcons. by exists is, tr, Htr.
  - intros [Hreceived | Hsent]; apply Hall; intros is tr Htr.
    + apply proper_received in Hreceived; [| done].
      apply Exists_or. left.
      by eapply Hreceived.
    + apply proper_sent in Hsent; [| done].
      apply Exists_or. right.
      by eapply Hsent.
Qed.

Definition has_been_directly_observed_from_sent_received
  (s : vstate vlsm)
  (m : message)
  : Prop
  := has_been_sent vlsm s m \/ has_been_received vlsm s m.

Lemma has_been_directly_observed_from_sent_received_dec
  : RelDecision has_been_directly_observed_from_sent_received.
Proof.
  intros s m.
  apply Decision_or.
  - apply has_been_sent_dec.
  - apply has_been_received_dec.
Qed.

Lemma has_been_directly_observed_from_sent_received_stepwise_props
  : oracle_stepwise_props item_sends_or_receives has_been_directly_observed_from_sent_received.
Proof.
  apply stepwise_props_from_trace
  ; [apply has_been_directly_observed_from_sent_received_dec|..]
  ; intros; split.
  - intros [Hsent | Hreceived] start tr Htr.
    + apply proper_sent in Hsent; [| done].
      apply Exists_or; right.
      by eapply Hsent.
    + apply proper_received in Hreceived; [| done].
      apply Exists_or; left.
      by eapply Hreceived.
  - intros Hobs.
    apply consistency_from_valid_state_proj2 in Hobs; [| done].
    destruct Hobs as (is & tr & Htr & Hexists).
    apply Exists_or_inv in Hexists as [Hsent | Hreceived].
    + right. apply proper_received; [done |].
      apply has_been_received_consistency; [done | done |].
      by exists is, tr, Htr.
    + left. apply proper_sent; [done |].
      apply has_been_sent_consistency; [done | done |].
      by exists is, tr, Htr.
  - intros Hnobs start tr Htr Hexists.
    contradict Hnobs.
    apply Exists_or_inv in Hexists.
    destruct Hexists as [Hexists| Hexists].
    + right. apply proper_received; [done |].
      apply has_been_received_consistency; [done | done |].
      by exists start, tr, Htr.
    + left. apply proper_sent; [done |].
      apply has_been_sent_consistency; [done | done |].
      by exists start, tr, Htr.
  - intros Hnobs  [Hobs | Hobs].
    + apply proper_sent in Hobs; [| done].
      apply has_been_sent_consistency in Hobs; [| done | done].
      destruct Hobs as [is [tr [Htr Hexists]]].
      eapply Hnobs; [done |].
      by apply Exists_or; right.
    + apply proper_received in Hobs; [| done].
      apply has_been_received_consistency in Hobs; [| done | done].
      destruct Hobs as [is [tr [Htr Hexists]]].
      eapply Hnobs; [done |].
      by apply Exists_or; left.
Qed.

Global Program Instance HasBeenDirectlyObservedCapability_from_sent_received
  : HasBeenDirectlyObservedCapability vlsm
  :=
  { has_been_directly_observed := has_been_directly_observed_from_sent_received;
    has_been_directly_observed_dec := has_been_directly_observed_from_sent_received_dec;

    has_been_directly_observed_stepwise_props := has_been_directly_observed_from_sent_received_stepwise_props
  }.

  Lemma has_been_directly_observed_consistency
    `{HasBeenDirectlyObservedCapability message vlsm}
    (s : state)
    (Hs : valid_state_prop (pre_loaded_with_all_messages_vlsm vlsm) s)
    (m : message)
    : selected_messages_consistency_prop vlsm item_sends_or_receives s m.
  Proof.
    split.
    - intro Hsome.
      destruct (decide (has_been_directly_observed vlsm s m)) as [Hsm|Hsm].
      + by apply proper_directly_observed in Hsm.
      + apply proper_not_directly_observed in Hsm; [| done].
        destruct Hsome as [is [tr [Htr Hmsg]]].
        by elim (Hsm _ _ Htr).
    - by apply consistency_from_valid_state_proj2.
  Qed.

End sent_received_observed_capabilities.

Lemma sent_can_emit
  [message]
  (X : VLSM message)
  `{HasBeenSentCapability message X}
  (s : state)
  (Hs : valid_state_prop X s)
  (m : message)
  (Hsent : has_been_sent X s m) :
  can_emit X m.
Proof.
  apply valid_state_has_trace in Hs as (is & tr & Htr).
  assert (Hpre_tr: finite_valid_trace_init_to (pre_loaded_with_all_messages_vlsm X) is s tr).
  {
    clear -Htr; destruct X;
      by eapply VLSM_incl_finite_valid_trace_init_to;
        [apply vlsm_incl_pre_loaded_with_all_messages_vlsm |].
  }
  eapply has_been_sent_examine_one_trace, Exists_exists in Hsent
    as (item_z & Hitem_z & Hz); [| done].
  apply elem_of_list_split in Hitem_z as (pre_z & suf_z & ->).
  destruct Htr as [Htr _].
  eapply valid_trace_forget_last, input_valid_transition_to in Htr; [| done].
  cbn in Hz; rewrite Hz in Htr.
  by eexists _,_,_.
Qed.

Lemma preloaded_sent_can_emit
  [message]
  (X : VLSM message)
  `{HasBeenSentCapability message X}
  (s : state)
  (Hs : valid_state_prop (pre_loaded_with_all_messages_vlsm X) s)
  (m : message)
  (Hsent : has_been_sent X s m) :
  can_emit (pre_loaded_with_all_messages_vlsm X) m.
Proof.
  pose (Heq := pre_loaded_with_all_messages_vlsm_is_pre_loaded_with_True X).
  rewrite (VLSM_eq_can_emit Heq).
  by cbn; eapply sent_can_emit; [apply (VLSM_eq_valid_state Heq) |].
Qed.

Lemma sent_valid
    [message]
    (X : VLSM message)
    `{HasBeenSentCapability message X}
    (s : state)
    (Hs : valid_state_prop X s)
    (m : message)
    (Hsent : has_been_sent X s m) :
    valid_message_prop X m.
Proof.
  by apply emitted_messages_are_valid_iff; right; eapply sent_can_emit.
Qed.

Lemma received_valid
    [message]
    (X : VLSM message)
    `{HasBeenReceivedCapability message X}
    (s : state)
    (Hs : valid_state_prop X s)
    (m : message)
    (Hreceived : has_been_received X s m) :
    valid_message_prop X m.
Proof.
  induction Hs using valid_state_prop_ind.
  - contradict Hreceived.
    eapply oracle_no_inits; [| done].
    apply has_been_received_stepwise_from_trace.
  - apply input_valid_transition_in in Ht as Hom'.
    apply preloaded_weaken_input_valid_transition in Ht.
    erewrite oracle_step_update in Hreceived
    ; [| apply has_been_received_stepwise_from_trace | done].
    destruct Hreceived as [[= ->] |]; auto.
Qed.

Lemma directly_observed_valid
    [message]
    (X : VLSM message)
    `{HasBeenSentCapability message X}
    `{HasBeenReceivedCapability message X}
    (s : state)
    (Hs : valid_state_prop X s)
    (m : message)
    (Hobserved : has_been_directly_observed X s m) :
    valid_message_prop X m.
Proof.
  destruct Hobserved.
  - by eapply sent_valid.
  - by eapply received_valid.
Qed.

(** *** Equivocation in compositions

 We now move on to a composite context. Each component of our composition
    will have [has_been_sent] and [has_been_received] capabilities.

    We introduce [validator]s along with their respective [Weight]s, the
    [A] function which maps validators to indices of component VLSMs and
    the [sender] function which maps messages to their (unique) designated
    sender (if any).

    For the equivocation fault sum to be computable, we also require that
    the number of [validator]s and the number of machines in the
    composition are both finite. See [finite_index], [finite_validator].
**)

Section Composite.

  Context {message : Type}
          `{finite.Finite index}
          (IM : index -> VLSM message)
          (Free := free_composite_vlsm IM)
          `{forall i : index, (HasBeenSentCapability (IM i))}
          `{forall i : index, (HasBeenReceivedCapability (IM i))}
          .

  Section StepwiseProps.
    Context
      [message_selectors: forall i : index, message -> vtransition_item (IM i) -> Prop]
      [oracles: forall i, state_message_oracle (IM i)]
      (stepwise_props: forall i, oracle_stepwise_props (message_selectors i) (oracles i))
      .

      Definition composite_message_selector : message -> composite_transition_item IM -> Prop.
      Proof.
        intros msg [[i li] input s output].
        apply (message_selectors i msg).
        exact {|l:=li;input:=input;destination:=s i;output:=output|}.
      Defined.

      Definition composite_oracle : composite_state IM -> message -> Prop :=
        fun s msg => exists i, oracles i (s i) msg.

      Lemma composite_stepwise_props
        (constraint : composite_label IM -> composite_state IM * option message -> Prop)
        (X := composite_vlsm IM constraint)
        : oracle_stepwise_props (vlsm := X) composite_message_selector composite_oracle.
      Proof.
        split.
        - (* initial states not claim *)
          intros s Hs m [i Horacle].
          revert Horacle.
          apply (oracle_no_inits (stepwise_props i)).
          apply Hs.
        - (* step update property *)
          intros l s im s' om Hproto msg.
          destruct l as [i li].
          simpl.
          assert (Hsj : forall j, s j = s' j \/ j = i).
          {
            intro j.
            apply (input_valid_transition_preloaded_project_any j) in Hproto.
            destruct Hproto as [|(lj & Hlj & _)]; [by left | right; congruence].
          }
          apply input_valid_transition_preloaded_project_active in Hproto;simpl in Hproto.
          apply (oracle_step_update (stepwise_props i)) with (msg:=msg) in Hproto.
          split.
          + intros [j Hj].
            destruct (Hsj j) as [Hunchanged|Hji].
            * by right; exists j; rewrite Hunchanged.
            * subst j.
              apply Hproto in Hj.
              by destruct Hj; [left | right; exists i].
          + intros [Hnow | [j Hbefore]].
            * by exists i; apply Hproto; left.
            * exists j.
              destruct (Hsj j) as [Hunchanged| ->].
              -- by rewrite <- Hunchanged.
              -- by apply Hproto; right.
      Qed.

      Lemma oracle_component_selected_previously
        [constraint : composite_label IM -> composite_state IM * option message -> Prop]
        (X := composite_vlsm IM constraint)
        [s : composite_state IM]
        (Hs : valid_state_prop X s)
        [i : index]
        [m : message]
        (Horacle : oracles i (s i) m) :
        exists s_item item,
          input_valid_transition_item X s_item item /\
          in_futures X (destination item) s /\
          projT1 (l item) = i /\
          composite_message_selector m item.
      Proof.
        apply valid_state_has_trace in Hs as (is & tr & Htr).
        eapply VLSM_incl_finite_valid_trace_init_to in Htr as Hpre_tr
        ; [|apply constraint_preloaded_free_incl].
        apply (VLSM_projection_finite_valid_trace_init_to
                (preloaded_component_projection IM i))
           in Hpre_tr.
        eapply prove_all_have_message_from_stepwise in Horacle
        ; [| apply stepwise_props |eapply finite_valid_trace_from_to_last_pstate, Hpre_tr].
        specialize (Horacle _ _ Hpre_tr); clear Hpre_tr.
        apply Exists_exists in Horacle as (item & Hitem & Hout).
        apply elem_of_map_option in Hitem as (itemX & HitemX & HitemX_pr).
        apply elem_of_list_split in HitemX as (pre & suf & Htr_pr).
        exists (finite_trace_last is pre), itemX.
        rewrite cons_middle in Htr_pr.
        eapply (input_valid_transition_to X) in Htr_pr as Ht
        ; [cbn in Ht | apply valid_trace_forget_last in Htr; apply Htr].
        unfold pre_VLSM_projection_transition_item_project,
               composite_project_label in HitemX_pr; cbn in HitemX_pr.
        rewrite app_assoc in Htr_pr.
        case_decide as Hi; [|congruence]; apply Some_inj in HitemX_pr
        ; subst i item tr; cbn in *.
        apply proj1, finite_valid_trace_from_to_app_split, proj2 in Htr.
        rewrite finite_trace_last_is_last in Htr.
        destruct itemX, l; cbn in *.
        by split_and!; [|exists suf|..].
      Qed.

  End StepwiseProps.

  (** A message 'has_been_sent' for a composite state if it 'has_been_sent' for any of
  its components.*)
  Definition composite_has_been_sent
    (s : composite_state IM)
    (m : message)
    : Prop
    := exists (i : index), has_been_sent (IM i) (s i) m.

  (** 'composite_has_been_sent' is decidable. *)
  Lemma composite_has_been_sent_dec : RelDecision composite_has_been_sent.
  Proof.
    intros s m.
    apply (Decision_iff (P:=List.Exists (fun i => has_been_sent (IM i) (s i) m) (enum index))).
    - by rewrite Exists_finite.
    - typeclasses eauto.
  Qed.

  Lemma composite_has_been_sent_stepwise_props
    (constraint : composite_label IM -> composite_state IM * option message -> Prop)
    (X := composite_vlsm IM constraint)
    : has_been_sent_stepwise_props (vlsm := X) composite_has_been_sent.
  Proof.
    unfold has_been_sent_stepwise_props.
    pose proof (composite_stepwise_props
                  (fun i => has_been_sent_stepwise_from_trace
                              (IM i)))
         as [Hinits Hstep].
    split; [done |].
    by intros l; specialize (Hstep l); destruct l.
  Qed.

  Global Instance composite_HasBeenSentCapability
    (constraint : composite_label IM -> composite_state IM * option message -> Prop)
    (X := composite_vlsm IM constraint)
    : HasBeenSentCapability X :=
    HasBeenSentCapability_from_stepwise (vlsm := X)
      composite_has_been_sent_dec
      (composite_has_been_sent_stepwise_props constraint).

  Lemma composite_proper_sent
    (s : state)
    (Hs : valid_state_prop (pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM)) s)
    (m : message)
    : has_been_sent_prop (free_composite_vlsm IM) composite_has_been_sent s m.
  Proof.
    specialize (proper_sent (free_composite_vlsm IM)) as Hproper_sent.
    by apply Hproper_sent.
  Qed.

  Section composite_has_been_received.

  (** A message 'has_been_received' for a composite state if it 'has_been_received' for any of
  its components.*)
  Definition composite_has_been_received
    (s : composite_state IM)
    (m : message)
    : Prop
    := exists (i : index), has_been_received (IM i) (s i) m.

  (** 'composite_has_been_received' is decidable. *)
  Lemma composite_has_been_received_dec : RelDecision composite_has_been_received.
  Proof.
    intros s m.
    apply (Decision_iff (P:=List.Exists (fun i => has_been_received (IM i) (s i) m) (enum index))).
    - by rewrite Exists_finite.
    - typeclasses eauto.
  Qed.

  Lemma composite_has_been_received_stepwise_props
    (constraint : composite_label IM -> composite_state IM * option message -> Prop)
    (X := composite_vlsm IM constraint)
    : has_been_received_stepwise_props (vlsm := X) composite_has_been_received.
  Proof.
    unfold has_been_received_stepwise_props.
    pose proof (composite_stepwise_props
                  (fun i => has_been_received_stepwise_from_trace
                              (IM i)))
         as [Hinits Hstep].
    split; [done |].
    by intros l; specialize (Hstep l); destruct l.
  Qed.

  Global Instance composite_HasBeenReceivedCapability
    (constraint : composite_label IM -> composite_state IM * option message -> Prop)
    (X := composite_vlsm IM constraint)
    : HasBeenReceivedCapability X :=
    HasBeenReceivedCapability_from_stepwise (vlsm := X)
      composite_has_been_received_dec
      (composite_has_been_received_stepwise_props constraint).

  Global Instance composite_HasBeenDirectlyObservedCapability
    (constraint : composite_label IM -> composite_state IM * option message -> Prop)
    (X := composite_vlsm IM constraint)
    : HasBeenDirectlyObservedCapability X :=
    HasBeenDirectlyObservedCapability_from_sent_received X.

  Lemma preloaded_composite_has_been_received_stepwise_props
    (constraint : composite_label IM -> composite_state IM * option message -> Prop)
    (seed : message -> Prop)
    (X := pre_loaded_vlsm (composite_vlsm IM constraint) seed)
    : has_been_received_stepwise_props (vlsm := X) composite_has_been_received.
  Proof.
    unfold has_been_received_stepwise_props.
    specialize (composite_stepwise_props
                  (fun i => has_been_received_stepwise_from_trace (IM i)))
         as [Hinits Hstep].
    split; [done |].
    by intros l; specialize (Hstep l); destruct l.
  Qed.

  Definition preloaded_composite_HasBeenReceivedCapability
    (constraint : composite_label IM -> composite_state IM * option message -> Prop)
    (seed : message -> Prop)
    (X := pre_loaded_vlsm (composite_vlsm IM constraint) seed)
    : HasBeenReceivedCapability X :=
    HasBeenReceivedCapability_from_stepwise (vlsm := X)
      composite_has_been_received_dec
      (preloaded_composite_has_been_received_stepwise_props constraint seed).

  End composite_has_been_received.


  (**
  A message [has_been_directly_observed] for a composite state if it
  [has_been_directly_observed] for any of its components.
  *)
  Definition composite_has_been_directly_observed
    (s : composite_state IM)
    (m : message)
    : Prop
    := exists (i : index), has_been_directly_observed (IM i) (s i) m.

  (** 'composite_has_been_directly_observed' is decidable. *)
  Lemma composite_has_been_directly_observed_dec : RelDecision composite_has_been_directly_observed.
  Proof.
    intros s m.
    apply (Decision_iff (P:=List.Exists (fun i => has_been_directly_observed (IM i) (s i) m) (enum index))).
    - by rewrite Exists_finite.
    - typeclasses eauto.
  Qed.

  Lemma composite_has_been_directly_observed_stepwise_props
    (constraint : composite_label IM -> composite_state IM * option message -> Prop)
    (X := composite_vlsm IM constraint)
    : oracle_stepwise_props (vlsm := X) item_sends_or_receives composite_has_been_directly_observed.
  Proof.
    pose proof (composite_stepwise_props
                  (fun i => (has_been_directly_observed_stepwise_props (IM i))))
         as [Hinits Hstep].
    split; [done |].
    by intros l; specialize (Hstep l); destruct l.
  Qed.

  Definition composite_HasBeenDirectlyObservedCapability_from_stepwise
    (constraint : composite_label IM -> composite_state IM * option message -> Prop)
    (X := composite_vlsm IM constraint)
    : HasBeenDirectlyObservedCapability X.
  Proof.
    exists composite_has_been_directly_observed.
    - apply composite_has_been_directly_observed_dec.
    - apply (composite_has_been_directly_observed_stepwise_props constraint).
  Defined.

  Context
        {validator : Type}
        (A : validator -> index)
        (sender : message -> option validator)
        .

  Definition node_signed_message (node_idx : index) (m : message) : Prop :=
    option_map A (sender m) = Some node_idx.

  (** Definitions for safety and nontriviality of the [sender] function.
      Safety means that if we designate a validator as the sender
      of a certain messsage, then it is impossible for other components
      to produce that message

      Weak/strong nontriviality say that each validator should
      be designated sender for at least one/all its valid
      messages.
  **)
  Definition sender_safety_prop : Prop :=
    forall
    (m : message)
    (v : validator)
    (Hsender : sender m = Some v),
    forall (j : index)
           (Hdif : j <> A v),
           ~can_emit (pre_loaded_with_all_messages_vlsm (IM j)) m.

   (** An alternative, possibly friendlier, formulation. Note that it is
       slightly weaker, in that it does not require that the sender
       is able to send the message. **)

  Definition sender_safety_alt_prop : Prop :=
    forall
    (m : message)
    (v : validator)
    (Hsender : sender m = Some v),
    forall (i : index),
    can_emit (pre_loaded_with_all_messages_vlsm (IM i)) m ->
    A v = i.

  Lemma sender_safety_alt_iff
    : sender_safety_prop <-> sender_safety_alt_prop.
  Proof.
    split; intros Hsender_safety m; intros.
    - specialize (Hsender_safety m v Hsender).
      destruct (decide (i = A v)); [done |].
      by elim (Hsender_safety _ n).
    - intro Hemit. elim Hdif.
      by specialize (Hsender_safety m v Hsender _ Hemit).
  Qed.

  Definition channel_authenticated_message (node_idx : index) (m : message) : Prop :=
    option_map A (sender m) = Some node_idx.

  (** The [channel_authentication_prop]erty requires that any sent message must
  be originating with its <<sender>>.
  Note that we don't require that <<sender>> is total, but rather that it is
  defined for all messages which can be emitted.
  *)
  Definition channel_authentication_prop : Prop :=
    forall i m,
    can_emit (pre_loaded_with_all_messages_vlsm (IM i)) m ->
    channel_authenticated_message i m.

  (** Channel authentication guarantees sender safety *)
  Lemma channel_authentication_sender_safety
    : channel_authentication_prop -> sender_safety_alt_prop.
  Proof.
    intros Hsigned m v Hsender i Hemit.
    apply Some_inj.
    change (Some (A v)) with (option_map A (Some v)).
    rewrite <- Hsender.
    by apply Hsigned.
  Qed.

  Definition sender_nontriviality_prop : Prop :=
    forall (v : validator),
    exists (m : message),
    can_emit (pre_loaded_with_all_messages_vlsm (IM (A v))) m /\
    sender m = Some v.

  Definition no_initial_messages_in_IM_prop : Prop :=
    forall i m, ~vinitial_message_prop (IM i) m.

  Lemma composite_no_initial_valid_messages_emitted_by_sender
      (can_emit_signed : channel_authentication_prop)
      (no_initial_messages_in_IM : no_initial_messages_in_IM_prop)
      (constraint : composite_label IM -> composite_state IM * option message -> Prop)
      (X := composite_vlsm IM constraint)
      : forall (m : message), valid_message_prop X m ->
        exists v, sender m = Some v /\
          can_emit (pre_loaded_with_all_messages_vlsm (IM (A v))) m.
  Proof.
    intro m.
    rewrite emitted_messages_are_valid_iff.
    intros [[i [[mi Hmi] _]] | [(s, om) [(i, l) [s' Ht]]]]
    ; [contradict Hmi; apply no_initial_messages_in_IM |].
    apply (VLSM_incl_input_valid_transition (constraint_preloaded_free_incl IM _)) in Ht.
    apply pre_loaded_with_all_messages_projection_input_valid_transition_eq
      with (j := i) in Ht; [| done]; cbn in Ht.
    specialize (can_emit_signed i m).
    spec can_emit_signed; [by eexists _,_,_ |].
    unfold channel_authenticated_message in can_emit_signed.
    destruct (sender m) as [v|] eqn: Hsender; [|inversion can_emit_signed].
    apply Some_inj in can_emit_signed.
    exists v; subst; unfold can_emit; eauto.
  Qed.

  Lemma composite_no_initial_valid_messages_have_sender
      (can_emit_signed : channel_authentication_prop)
      (no_initial_messages_in_IM : no_initial_messages_in_IM_prop)
      (constraint : composite_label IM -> composite_state IM * option message -> Prop)
      (X := composite_vlsm IM constraint)
      : forall (m : message) (Hm : valid_message_prop X m), sender m <> None.
  Proof.
    intros m Hm.
    cut (exists v, sender m = Some v /\
     can_emit (pre_loaded_with_all_messages_vlsm (IM (A v))) m).
    - intros (v & -> & _); congruence.
    - by eapply composite_no_initial_valid_messages_emitted_by_sender.
  Qed.

  Lemma composite_emitted_by_validator_have_sender
      (can_emit_signed : channel_authentication_prop)
      (A_inj : forall v1 v2, A v1 = A v2 -> v1 = v2)
    : forall s item,
        input_valid_transition_item (pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM))
          s item ->
      forall v, A v = projT1 (l item) ->
      forall (m : message), output item = Some m ->
      sender m = Some v.
  Proof.
    intros s item Ht v HAv m Houtput.
    cut (channel_authenticated_message (A v) m).
    {
      unfold channel_authenticated_message; destruct (sender m) as [v' |]; [| done].
      by cbn; intros Hvv'; apply Some_inj, A_inj in Hvv'; subst.
    }
    apply input_valid_transition_preloaded_project_active in Ht as Hti.
    by rewrite Houtput in Hti; apply can_emit_signed; rewrite HAv; eexists _, _, _.
  Qed.
  
  Lemma has_been_sent_iff_by_sender
        (Hsender_safety : sender_safety_alt_prop)
        [is s tr] (Htr : finite_valid_trace_init_to (pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM)) is s tr)
        [m v] (Hsender : sender m = Some v):
    composite_has_been_sent s m <-> has_been_sent (IM (A v)) (s (A v)) m.
  Proof.
    split;[| by exists (A v)].
    intros [i Hi].
    erewrite Hsender_safety; [done | done |].
    assert
      (Htr_pr : finite_valid_trace_init_to
        (pre_loaded_with_all_messages_vlsm (IM i))
        (is i) (s i) (VLSM_projection_finite_trace_project (preloaded_component_projection IM i) tr)).
    {
      by apply (VLSM_projection_finite_valid_trace_init_to (preloaded_component_projection IM i)).
    }
    eapply can_emit_from_valid_trace.
    - by eapply valid_trace_forget_last.
    - eapply proper_sent; [| done | done].
      revert Htr_pr; apply valid_trace_last_pstate.
  Qed.

  Lemma no_additional_equivocations_constraint_dec
    : RelDecision (no_additional_equivocations_constraint Free).
  Proof.
    intros l (s, om).
    destruct om; [| by left].
    apply no_additional_equivocations_dec.
  Qed.

   (** We say that a validator <v> (with associated component <i>) is equivocating wrt.
   to another component <j>, if there exists a message which [has_been_received] by
   <j> but [has_not_been_sent] by <i> **)

  Definition equivocating_wrt
    (v : validator)
    (j : index)
    (sv sj : state)
    (i := A v)
    : Prop
    :=
    exists (m : message),
    sender(m) = Some v /\
    has_not_been_sent  (IM i) sv m /\
    has_been_received  (IM j) sj m.

  (** We can now decide whether a validator is equivocating in a certain state. **)

  Definition is_equivocating_statewise
    (s : composite_state IM)
    (v : validator)
    : Prop
    :=
    exists (j : index),
    equivocating_wrt v j (s (A v)) (s j).

  Lemma initial_state_is_not_equivocating_statewise
    (s : composite_state IM)
    (Hs : composite_initial_state_prop IM s)
    (v : validator)
    : ~ is_equivocating_statewise s v.
  Proof.
    unfold is_equivocating_statewise, equivocating_wrt.
    intros [j [m [Hsender [Hnbs Hrcv]]]].
    revert Hrcv.
    apply has_been_received_stepwise_from_trace.
    apply Hs.
  Qed.

  Context
      `{finite.Finite validator}
      {measurable_V : Measurable validator}
      {threshold_V : ReachableThreshold validator}
      .
  (** For the equivocation sum fault to be computable, we require that
      our is_equivocating property is decidable. The current implementation
      refers to [is_equivocating_statewise], but this might change
      in the future **)

  Definition equivocation_dec_statewise
     (Hdec : RelDecision is_equivocating_statewise)
      : BasicEquivocation (composite_state IM) (validator)
    :=
    {|
      state_validators := fun _ => enum validator;
      state_validators_nodup := fun _ => NoDup_enum validator;
      is_equivocating := is_equivocating_statewise;
      is_equivocating_dec := Hdec
    |}.

  Definition equivocation_fault_constraint
    (Dec : BasicEquivocation (composite_state IM) validator)
    (l : composite_label IM)
    (som : composite_state IM * option message)
    : Prop
    :=
    let (s', om') := (composite_transition IM l som) in
    not_heavy s'.

  Lemma sent_component_sent_previously
    [constraint : composite_label IM -> composite_state IM * option message -> Prop]
    (X := composite_vlsm IM constraint)
    [s : composite_state IM]
    (Hs : valid_state_prop X s)
    [i : index]
    [m : message]
    (Horacle : has_been_sent (IM i) (s i) m) :
    exists s_item item,
      input_valid_transition_item X s_item item /\
      in_futures X (destination item) s /\
      projT1 (l item) = i /\
      output item = Some m.
  Proof.
    clear -Hs Horacle.
    specialize
      (oracle_component_selected_previously
        (fun i => has_been_sent_stepwise_from_trace (IM i))
        Hs Horacle)
      as (s_item & [[] ?] & Ht & Hfutures & Hi & Hselected).
    by eexists _, _.
  Qed.

  Lemma received_component_received_previously
    [constraint : composite_label IM -> composite_state IM * option message -> Prop]
    (X := composite_vlsm IM constraint)
    [s : composite_state IM]
    (Hs : valid_state_prop X s)
    [i : index]
    [m : message]
    (Horacle : has_been_received (IM i) (s i) m) :
    exists s_item item,
      input_valid_transition_item X s_item item /\
      in_futures X (destination item) s /\
      projT1 (l item) = i /\
      input item = Some m.
  Proof.
    clear -Hs Horacle.
    specialize
      (oracle_component_selected_previously
        (fun i => has_been_received_stepwise_from_trace (IM i))
        Hs Horacle)
      as (s_item & [[] ?] & Ht & Hfutures & Hi & Hselected).
    by eexists _, _.
  Qed.

  Lemma messages_sent_from_component_produced_previously
    [constraint : composite_label IM -> composite_state IM * option message -> Prop]
    (X := composite_vlsm IM constraint)
    [s : composite_state IM]
    (Hs : valid_state_prop X s)
    [i : index]
    [m : message]
    (Hsent : has_been_sent (IM i) (s i) m) :
    exists s_m,
      in_futures X s_m s /\
      can_produce (pre_loaded_with_all_messages_vlsm (IM i)) (s_m i) m.
  Proof.
    specialize (sent_component_sent_previously Hs Hsent)
      as (s_item & [] & Ht & Hfutures & <- & Houtput)
    ; destruct l as [i li]; cbn in *; subst output.
    exists destination; split; [done |].
    eapply VLSM_incl_input_valid_transition in Ht; cbn in Ht;
      [|apply constraint_preloaded_free_incl].
    eapply (VLSM_projection_input_valid_transition (preloaded_component_projection IM i))
      in Ht; [by eexists _,_ |].
    apply (composite_project_label_eq IM).
  Qed.

  Lemma messages_sent_from_component_of_valid_state_are_valid
    (constraint : composite_label IM -> composite_state IM * option message -> Prop)
    (X := composite_vlsm IM constraint)
    (s : composite_state IM)
    (Hs : valid_state_prop X s)
    (i : index)
    (m : message)
    (Hsent : has_been_sent (IM i) (s i) m) :
    valid_message_prop X m.
  Proof.
    by apply (sent_valid X s); [| exists i].
  Qed.

  Lemma preloaded_messages_sent_from_component_of_valid_state_are_valid
    (constraint : composite_label IM -> composite_state IM * option message -> Prop)
    (seed : message -> Prop)
    (X := pre_loaded_vlsm (composite_vlsm IM constraint) seed)
    (s : composite_state IM)
    (Hs : valid_state_prop X s)
    (i : index)
    (m : message)
    (Hsent : has_been_sent (IM i) (s i) m) :
    valid_message_prop X m.
  Proof.
    by eapply sent_valid; [| exists i].
  Qed.

  Lemma messages_received_from_component_of_valid_state_are_valid
    (constraint : composite_label IM -> composite_state IM * option message -> Prop)
    (X := composite_vlsm IM constraint)
    (s : composite_state IM)
    (Hs : valid_state_prop X s)
    (i : index)
    (m : message)
    (Hreceived : has_been_received (IM i) (s i) m)
    : valid_message_prop X m.
  Proof.
    by eapply received_valid; [| exists i].
  Qed.

  Lemma preloaded_messages_received_from_component_of_valid_state_are_valid
    (constraint : composite_label IM -> composite_state IM * option message -> Prop)
    (seed : message -> Prop)
    (X := pre_loaded_vlsm (composite_vlsm IM constraint) seed)
    (s : composite_state IM)
    (Hs : valid_state_prop X s)
    (i : index)
    (m : message)
    (Hreceived : has_been_received (IM i) (s i) m)
    : valid_message_prop X m.
  Proof.
    by eapply received_valid; [| exists i].
  Qed.

  Lemma composite_sent_valid
    (constraint : composite_label IM -> composite_state IM * option message -> Prop)
    (X := composite_vlsm IM constraint)
    (s : composite_state IM)
    (Hs : valid_state_prop X s)
    (m : message)
    (Hsent : composite_has_been_sent s m)
    : valid_message_prop X m.
  Proof.
    destruct Hsent as [i Hsent].
    by apply messages_sent_from_component_of_valid_state_are_valid with s i.
  Qed.

  Lemma preloaded_composite_sent_valid
    (constraint : composite_label IM -> composite_state IM * option message -> Prop)
    (seed : message -> Prop)
    (X := pre_loaded_vlsm (composite_vlsm IM constraint) seed)
    (s : composite_state IM)
    (Hs : valid_state_prop X s)
    (m : message)
    (Hsent : composite_has_been_sent s m)
    : valid_message_prop X m.
  Proof.
    destruct Hsent as [i Hsent].
    by apply preloaded_messages_sent_from_component_of_valid_state_are_valid with s i.
  Qed.

  Lemma composite_received_valid
    (constraint : composite_label IM -> composite_state IM * option message -> Prop)
    (X := composite_vlsm IM constraint)
    (s : composite_state IM)
    (Hs : valid_state_prop X s)
    (m : message)
    (Hreceived : composite_has_been_received s m)
    : valid_message_prop X m.
  Proof.
    destruct Hreceived as [i Hreceived].
    by apply messages_received_from_component_of_valid_state_are_valid with s i.
  Qed.

  Lemma preloaded_composite_received_valid
    (constraint : composite_label IM -> composite_state IM * option message -> Prop)
    (seed : message -> Prop)
    (X := pre_loaded_vlsm (composite_vlsm IM constraint) seed)
    (s : composite_state IM)
    (Hs : valid_state_prop X s)
    (m : message)
    (Hreceived : composite_has_been_received s m)
    : valid_message_prop X m.
  Proof.
    destruct Hreceived as [i Hreceived].
    by apply preloaded_messages_received_from_component_of_valid_state_are_valid with s i.
  Qed.

  Lemma composite_directly_observed_valid
    (constraint : composite_label IM -> composite_state IM * option message -> Prop)
    (X := composite_vlsm IM constraint)
    (s : composite_state IM)
    (Hs : valid_state_prop X s)
    (m : message)
    (Hobserved : composite_has_been_directly_observed s m)
    : valid_message_prop X m.
  Proof.
    destruct Hobserved as [i Hobserved].
    apply (has_been_directly_observed_sent_received_iff (IM i)) in Hobserved.
    - destruct Hobserved as [Hreceived | Hsent].
      + by eapply messages_received_from_component_of_valid_state_are_valid.
      + by eapply messages_sent_from_component_of_valid_state_are_valid.
    - by eapply valid_state_project_preloaded.
  Qed.

  Lemma preloaded_composite_directly_observed_valid
    (constraint : composite_label IM -> composite_state IM * option message -> Prop)
    (seed : message -> Prop)
    (X := pre_loaded_vlsm (composite_vlsm IM constraint) seed)
    (s : composite_state IM)
    (Hs : valid_state_prop X s)
    (m : message)
    (Hobserved : composite_has_been_directly_observed s m)
    : valid_message_prop X m.
  Proof.
    destruct Hobserved as [i Hobserved].
    apply (has_been_directly_observed_sent_received_iff (IM i)) in Hobserved.
    - destruct Hobserved as [Hreceived | Hsent].
      + by eapply preloaded_messages_received_from_component_of_valid_state_are_valid.
      + by eapply preloaded_messages_sent_from_component_of_valid_state_are_valid.
    - eapply valid_state_project_preloaded_to_preloaded.
      eapply VLSM_incl_valid_state; [| done].
      apply pre_loaded_vlsm_incl_pre_loaded_with_all_messages.
  Qed.

End Composite.

  Lemma composite_has_been_directly_observed_sent_received_iff
    {message}
    `{EqDecision index}
    (IM : index -> VLSM message)
    `{forall i : index, HasBeenSentCapability (IM i)}
    `{forall i : index, HasBeenReceivedCapability (IM i)}
    (s : composite_state IM)
    (m : message)
    : composite_has_been_directly_observed IM s m <-> composite_has_been_sent IM s m \/ composite_has_been_received IM s m.
  Proof.
    split.
    - by intros [i [Hs|Hr]]; [left | right]; exists i.
    - by intros [[i Hs] | [i Hr]]; exists i; [left | right].
  Qed.

  Lemma composite_has_been_directly_observed_free_iff
    {message}
    `{finite.Finite index}
    (IM : index -> VLSM message)
    `{forall i : index, HasBeenSentCapability (IM i)}
    `{forall i : index, HasBeenReceivedCapability (IM i)}
    (s : vstate (free_composite_vlsm IM))
    (m : message)
    : composite_has_been_directly_observed IM s m <-> has_been_directly_observed (free_composite_vlsm IM) s m.
  Proof.
    unfold has_been_directly_observed; cbn; unfold has_been_directly_observed_from_sent_received; cbn.
    apply composite_has_been_directly_observed_sent_received_iff.
  Qed.

  Lemma composite_has_been_directly_observed_from_component
    {message}
    `{finite.Finite index}
    (IM : index -> VLSM message)
    `{forall i : index, HasBeenSentCapability (IM i)}
    `{forall i : index, HasBeenReceivedCapability (IM i)}
    (s : composite_state IM)
    (i : index)
    (m : message)
    : has_been_directly_observed (IM i) (s i) m -> composite_has_been_directly_observed IM s m.
  Proof. by exists i. Qed.

  Lemma composite_has_been_directly_observed_lift
    {message}
    `{finite.Finite index}
    (IM : index -> VLSM message)
    `{forall i : index, HasBeenSentCapability (IM i)}
    `{forall i : index, HasBeenReceivedCapability (IM i)}
    (i : index)
    (s : vstate (IM i))
    (Hs : valid_state_prop (pre_loaded_with_all_messages_vlsm (IM i)) s)
    (m : message)
    : composite_has_been_directly_observed IM (lift_to_composite_state' IM i s) m <-> has_been_directly_observed (IM i) s m.
  Proof.
    pose (free_composite_vlsm IM) as Free.
    assert
      (Hlift_s : valid_state_prop (pre_loaded_with_all_messages_vlsm Free) (lift_to_composite_state' IM i s)).
    { revert Hs.  apply valid_state_preloaded_composite_free_lift. }
    split; intros Hobs.
    - apply (proper_directly_observed (IM i)); [done |].
      intros is tr Htr.
      apply composite_has_been_directly_observed_free_iff, proper_directly_observed in Hobs
      ; [| done].
      apply (VLSM_full_projection_finite_valid_trace_init_to (lift_to_composite_preloaded_vlsm_full_projection IM i)) in Htr as Hpre_tr.
      specialize (Hobs _ _ Hpre_tr).
      apply Exists_exists.
      apply Exists_exists in Hobs.
      destruct Hobs as [composite_item [Hcomposite_item Hx]].
      apply elem_of_list_fmap_2 in Hcomposite_item as [item [Hcomposite_item Hitem]].
      exists item.
      split; [done |].
      subst composite_item.
      by destruct item.
    - apply composite_has_been_directly_observed_free_iff, proper_directly_observed; [done |].
      apply has_been_directly_observed_consistency; [typeclasses eauto | done |].
      apply proper_directly_observed in Hobs ; [| done].
      apply has_been_directly_observed_consistency in Hobs; [| typeclasses eauto | done].
      destruct Hobs as [is [tr [Htr Hobs]]].
      apply (VLSM_full_projection_finite_valid_trace_init_to (lift_to_composite_preloaded_vlsm_full_projection IM i)) in Htr as Hpre_tr.
      eexists. eexists. exists Hpre_tr.
      apply Exists_exists.
      apply Exists_exists in Hobs.
      destruct Hobs as [item [Hitem Hx]].
      exists (lift_to_composite_transition_item' IM i item).
      split; [| by destruct item].
      apply elem_of_list_In.
      apply in_map_iff. exists item.
      apply elem_of_list_In in Hitem.
      by destruct item.
  Qed.

Section cannot_resend_message.
Context
  {message : Type}
  `{EqDecision message}
  (X : VLSM message)
  (PreX := pre_loaded_with_all_messages_vlsm X)
  `{HasBeenSentCapability message X}
  `{HasBeenReceivedCapability message X}
  .

Definition state_received_not_sent (s : state) (m : message) : Prop :=
  has_been_received X s m /\ ~ has_been_sent X s m.

Lemma state_received_not_sent_trace_iff
  (m : message)
  (s : state)
  (is : state)
  (tr : list transition_item)
  (Htr : finite_valid_trace_init_to PreX is s tr)
  : state_received_not_sent s m <-> trace_received_not_sent_before_or_after tr m.
Proof.
  assert (Hs : valid_state_prop PreX s).
  { by apply proj1, valid_trace_last_pstate in Htr. }
  split; intros [Hbrm Hnbsm].
  - apply proper_received in Hbrm; [| done].
    specialize (Hbrm is tr Htr).
    split; [done |].
    intro Hbsm. elim Hnbsm.
    apply proper_sent; [done |].
    by apply has_been_sent_consistency; [..|exists is, tr, Htr].
  - split.
    + apply proper_received; [done |].
      by apply has_been_received_consistency; [..|exists is, tr, Htr].
    + intro Hbsm. elim Hnbsm.
      by apply proper_sent in Hbsm; [eapply Hbsm|].
Qed.

Definition state_received_not_sent_invariant
  (s : state)
  (P : message -> Prop)
  : Prop
  := forall m, state_received_not_sent s m -> P m.

Lemma state_received_not_sent_invariant_trace_iff
  (P : message -> Prop)
  (s : state)
  (is : state)
  (tr : list transition_item)
  (Htr : finite_valid_trace_init_to PreX is s tr)
  : state_received_not_sent_invariant s P <->
    trace_received_not_sent_before_or_after_invariant tr P.
Proof.
  by split; intros Hinv m Hm
  ; apply Hinv
  ; apply (state_received_not_sent_trace_iff m s is tr Htr).
Qed.

(**
A sent message cannot have been previously sent or received.
*)
Definition cannot_resend_message_stepwise_prop : Prop :=
  forall l s oim s' m,
    input_valid_transition (pre_loaded_with_all_messages_vlsm X) l (s,oim) (s',Some m) ->
    ~has_been_sent X s m /\ ~has_been_received X s' m.

Lemma cannot_resend_received_message_in_future
  (Hno_resend : cannot_resend_message_stepwise_prop)
  (s1 s2 : state)
  (Hfuture : in_futures PreX s1 s2)
  : forall m : message,
    state_received_not_sent s1 m -> state_received_not_sent s2 m.
Proof.
  intros m Hm.
  destruct Hfuture as [tr2 Htr2].
  induction Htr2; [done |].
  apply IHHtr2;clear IHHtr2.
  specialize (has_been_received_step_update Ht m) as Hrupd.
  specialize (has_been_sent_step_update Ht m) as Hmupd.
  destruct Hm as [Hr Hs].
  eapply or_intror in Hr; apply Hrupd in Hr.
  split; [done |].
  intros [-> |]%Hmupd; [| by apply Hs].
  by apply Hno_resend in Ht as [_ []].
Qed.

  Context
    (Hno_resend : cannot_resend_message_stepwise_prop).

  Lemma input_valid_transition_received_not_resent l s m s' om'
    (Ht : input_valid_transition (pre_loaded_with_all_messages_vlsm X) l (s,Some m) (s', om'))
    : om' <> Some m.
  Proof.
    destruct om' as [m'|]; [|congruence].
    intro Heq. inversion Heq. subst m'. clear Heq.
    destruct (Hno_resend _ _ _ _ _ Ht) as [_ Hnbr_m].
    elim Hnbr_m. clear Hnbr_m.
    apply exists_right_finite_trace_from in Ht.
    destruct Ht as [is [tr [Htr Hs]]].
    apply proj1 in Htr as Hlst. apply finite_valid_trace_from_to_last_pstate in Hlst.
    apply proper_received; [done |].
    apply has_been_received_consistency; [done | done |].
    exists _,_,Htr.
    by apply Exists_app; right; apply Exists_cons; left.
  Qed.

  Lemma lift_preloaded_trace_to_seeded
    (P : message -> Prop)
    (tr: list transition_item)
    (Htrm: trace_received_not_sent_before_or_after_invariant tr P)
    (is: state)
    (Htr: finite_valid_trace PreX is tr)
    : finite_valid_trace (pre_loaded_vlsm X P) is tr.
  Proof.
    unfold trace_received_not_sent_before_or_after_invariant in Htrm.
    split; [|apply Htr].
    induction Htr using finite_valid_trace_rev_ind; intros.
    - rapply @finite_valid_trace_from_empty.
      by apply initial_state_is_valid.
    - assert (trace_received_not_sent_before_or_after_invariant tr P) as Htrm'.
      { intros m [Hrecv Hsend]. apply (Htrm m);clear Htrm.
        split; [by apply Exists_app; left |].
        contradict Hsend.
        unfold trace_has_message in Hsend.
        rewrite Exists_app, Exists_cons, Exists_nil in Hsend.
        simpl in Hsend.
        cut (oom <> Some m);[tauto|clear Hsend].
        intros ->.
        cut (has_been_received X sf m);[apply (Hno_resend _ _ _ _ _ Hx)|].
        apply (has_been_received_step_update Hx);right.
        erewrite oracle_partial_trace_update.
        - by left.
        - by apply has_been_received_stepwise_from_trace.
        - by apply valid_trace_add_default_last; apply Htr.
      }
      specialize (IHHtr Htrm').
      apply (extend_right_finite_trace_from _ IHHtr).
      repeat split;try apply Hx;
      [by apply finite_valid_trace_last_pstate |].
      destruct iom as [m|];[|apply option_valid_message_None].
      (* If m was sent during tr, it is valid because it was
         produced in a valid (by IHHtr) trace.
         If m was not sent during tr,
       *)
      assert (Decision (trace_has_message (field_selector output) m tr)) as [Hsent|Hnot_sent].
      apply (@Exists_dec _). intros. apply decide_eq.
      + by eapply valid_trace_output_is_valid.
      + apply initial_message_is_valid.
        right. apply Htrm.
        split.
        * by apply Exists_app; right; apply Exists_cons; left.
        * intro Hsent;destruct Hnot_sent.
          unfold trace_has_message in Hsent.
          rewrite Exists_app, Exists_cons, Exists_nil in Hsent.
          destruct Hsent as [Hsent | [[= ->] | []]]; [done | exfalso].
          apply Hno_resend in Hx as Hx'.
          apply (proj2 Hx');clear Hx'.
          by rewrite (has_been_received_step_update Hx); left.
  Qed.

  Lemma lift_preloaded_state_to_seeded
    (P : message -> Prop)
    (s: state)
    (Hequiv_s: state_received_not_sent_invariant s P)
    (Hs: valid_state_prop PreX s)
    : valid_state_prop (pre_loaded_vlsm X P) s.
  Proof.
    apply valid_state_has_trace in Hs as Htr.
    destruct Htr as [is [tr Htr]].
    specialize (lift_preloaded_trace_to_seeded P tr) as Hlift.
    spec Hlift.
    { revert Hequiv_s.
      by apply state_received_not_sent_invariant_trace_iff with is.
    }
    specialize (Hlift _ (valid_trace_forget_last Htr)).
    apply proj1 in Hlift.
    apply finite_valid_trace_last_pstate in Hlift.
    by rewrite <- (valid_trace_get_last Htr).
  Qed.

  Lemma lift_generated_to_seeded
    (P : message -> Prop)
    (s : state)
    (Hequiv_s: state_received_not_sent_invariant s P)
    (m : message)
    (Hgen : can_produce PreX s m)
    : can_produce (pre_loaded_vlsm X P) s m.
  Proof.
    apply non_empty_valid_trace_from_can_produce.
    apply non_empty_valid_trace_from_can_produce in Hgen.
    destruct Hgen as [is [tr [item [Htr Hgen]]]].
    exists is, tr, item. split; [| done].
    specialize (lift_preloaded_trace_to_seeded P tr) as Hlift.
    apply Hlift; [| done].
    revert Hequiv_s.
    apply state_received_not_sent_invariant_trace_iff with is.
    apply valid_trace_add_last; [done |].
    apply last_error_destination_last.
    by destruct Hgen as [-> [<- _]].
  Qed.

End cannot_resend_message.

Section has_been_sent_irrelevance.

(**
  As we have several ways of obtaining the 'has_been_sent' property, we need to
  sometime show that they are equivalent.
*)

  Context
    {message : Type}
    (X : VLSM message)
    (Hbs1 : HasBeenSentCapability X)
    (Hbs2 : HasBeenSentCapability X)
    (has_been_sent1 := @has_been_sent _ X Hbs1)
    (has_been_sent2 := @has_been_sent _ X Hbs2)
    .

  Lemma has_been_sent_irrelevance
    (s : state)
    (m : message)
    (Hs : valid_state_prop (pre_loaded_with_all_messages_vlsm X) s)
    : has_been_sent1 s m -> has_been_sent2 s m.
  Proof.
    intro H.
    apply proper_sent in H; [| done].
    by apply proper_sent.
  Qed.

End has_been_sent_irrelevance.

Section all_traces_to_valid_state_are_valid.

Context
  {message : Type}
  {index : Type}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  `{forall i : index, (HasBeenReceivedCapability (IM i))}
  (constraint : composite_label IM -> composite_state IM * option message -> Prop)
  (X := composite_vlsm IM constraint)
  (PreX := pre_loaded_with_all_messages_vlsm X)
  .


(**
Under [HasBeenReceivedCapability] assumptions, and given the fact that
any valid state <<s>> has a valid trace leading to it,
in which all (received) messages are valid, it follows that
any message which [has_been_received] for state <<s>> is valid.

Hence, given any pre_loaded trace leading to <<s>>, all messages received
within it must be valid, thus the trace itself is valid.
*)
Lemma all_pre_traces_to_valid_state_are_valid
  s
  (Hs : valid_state_prop X s)
  is tr
  (Htr : finite_valid_trace_init_to PreX is s tr)
  : finite_valid_trace_init_to X is s tr.
Proof.
  apply pre_traces_with_valid_inputs_are_valid in Htr; [done |].
  apply valid_trace_last_pstate in Htr as Hspre.
  intros.
  eapply composite_received_valid; [done |].
  specialize (proper_received _ s Hspre m) as Hproper.
  apply proj2 in Hproper. apply Hproper.
  apply has_been_received_consistency; [typeclasses eauto | done |].
  by exists is, tr, Htr.
Qed.

End all_traces_to_valid_state_are_valid.

Section has_been_received_in_state.

  Context
    {message : Type}
    (X : VLSM message)
    `{HasBeenReceivedCapability message X}
  .

  Lemma has_been_received_in_state s1 m:
    valid_state_prop X s1 ->
    has_been_received X s1 m ->
    exists (s0 : state) (item : transition_item) (tr : list transition_item),
      input item = Some m /\
      finite_valid_trace_from_to X s0 s1 (item :: tr).
  Proof.
    intros Hpsp Hhbr.
    pose proof (Hetr := valid_state_has_trace _ _ Hpsp).
    destruct Hetr as [ist [tr Hetr]].
    apply proper_received in Hhbr.
    2: { apply pre_loaded_with_all_messages_valid_state_prop.
         apply Hpsp.
    }

    unfold selected_message_exists_in_all_preloaded_traces in Hhbr.
    unfold specialized_selected_message_exists_in_all_traces in Hhbr.
    specialize (Hhbr ist tr).
    unfold finite_valid_trace_init_to in Hhbr.
    unfold finite_valid_trace_init_to in Hetr.
    destruct Hetr as [Hfptf Hisp].
    pose proof (Hfptf' := preloaded_weaken_finite_valid_trace_from_to _ _ _ _ Hfptf).
    specialize (Hhbr (conj Hfptf' Hisp)).
    clear Hfptf'.

    unfold trace_has_message in Hhbr. unfold field_selector in Hhbr.
    apply Exists_exists in Hhbr.
    destruct Hhbr as [tritem [Htritemin Hintritem]].
    apply elem_of_list_split in Htritemin.
    destruct Htritemin as [l1 [l2 Heqtr]].
    rewrite Heqtr in Hfptf.
    apply (finite_valid_trace_from_to_app_split X) in Hfptf.
    destruct Hfptf as [Htr1 Htr2].
    destruct tritem eqn:Heqtritem.
    simpl in Hintritem. subst input.
    eexists. eexists. eexists.
    by split; [| apply  Htr2].
  Qed.

  Lemma has_been_received_in_state_preloaded s1 m:
    valid_state_prop (pre_loaded_with_all_messages_vlsm X) s1 ->
    has_been_received X s1 m ->
    exists (s0 : state) (item : transition_item) (tr : list transition_item),
      input item = Some m /\
      finite_valid_trace_from_to (pre_loaded_with_all_messages_vlsm X) s0 s1 (item :: tr).
  Proof.
    intros Hpsp Hhbr.
    pose proof (Hetr := valid_state_has_trace _ _ Hpsp).
    destruct Hetr as [ist [tr Hetr]].
    apply proper_received in Hhbr.
    2: { apply Hpsp. }

    unfold selected_message_exists_in_all_preloaded_traces in Hhbr.
    unfold specialized_selected_message_exists_in_all_traces in Hhbr.
    specialize (Hhbr ist tr).
    unfold finite_valid_trace_init_to in Hhbr.
    unfold finite_valid_trace_init_to in Hetr.
    destruct Hetr as [Hfptf Hisp].
    specialize (Hhbr (conj Hfptf Hisp)).

    unfold trace_has_message in Hhbr. unfold field_selector in Hhbr.
    apply Exists_exists in Hhbr.
    destruct Hhbr as [tritem [Htritemin Hintritem]].
    apply elem_of_list_split in Htritemin.
    destruct Htritemin as [l1 [l2 Heqtr]].
    rewrite Heqtr in Hfptf.
    apply (finite_valid_trace_from_to_app_split (pre_loaded_with_all_messages_vlsm X)) in Hfptf.
    destruct Hfptf as [Htr1 Htr2].
    destruct tritem eqn:Heqtritem.
    simpl in Hintritem. subst input.
    eexists. eexists. eexists.
    by split; [| apply  Htr2].
  Qed.

End has_been_received_in_state.
