From VLSM.Lib Require Import Itauto.
From Coq Require Import Streams Rdefinitions.
From stdpp Require Import prelude finite.
From VLSM.Lib Require Import Preamble ListExtras StdppListSet StdppExtras.
From VLSM.Lib Require Import ListSetExtras Measurable.
From VLSM.Core Require Import VLSM VLSMProjections Composition ProjectionTraces Validator.
From VLSM.Core Require Export ReachableThreshold.

(** * VLSM Equivocation Definitions

  This module is dedicated to building the vocabulary for discussing equivocation.
  Equivocation occurs on the receipt of a message which has not been previously sent.
  The designated sender (validator) of the message is then said to be equivocating.
  Our main purpose is to keep track of equivocating senders in a composite context
  and limit equivocation by means of a composition constraint.
*)

Lemma exists_proj1_sig {A : Type} (P : A -> Prop) (a : A) :
  (exists xP : {x | P x}, proj1_sig xP = a) <-> P a.
Proof.
  split.
  - by intros [[x Hx] [= ->]].
  - by intro Ha; exists (exist _ a Ha).
Qed.

(** ** Basic equivocation

  Assuming a set of <<state>>s, and a set of <<validator>>s,
  which is [Measurable] and has a [ReachableThreshold], we can define
  [BasicEquivocation] starting from an [is_equivocating] relation
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
*)

Class BasicEquivocation
  (state validator Cv : Type)
  (threshold : R)
  {measurable_V : Measurable validator}
  `{ReachableThreshold validator Cv threshold}
  : Type :=
{
  is_equivocating (s : state) (v : validator) : Prop;
  is_equivocating_dec : RelDecision is_equivocating;
  (** retrieves a set containing all possible validators for a state *)
  state_validators (s : state) : Cv;
  (** all validators which are equivocating in a given composite state *)
  equivocating_validators (s : state) : Cv :=
    filter (fun v => is_equivocating s v) (state_validators s);
  (** equivocation fault sum: the sum of the weights of equivocating validators *)
  equivocation_fault (s : state) : R :=
    sum_weights (equivocating_validators s);
  not_heavy (s : state) : Prop := (equivocation_fault s <= threshold)%R
}.

Lemma eq_equivocating_validators_equivocation_fault
   `{BasicEquivocation st validator Cv}
   : forall s1 s2,
    equivocating_validators s1 ≡@{Cv} equivocating_validators s2 ->
    equivocation_fault s1 = equivocation_fault s2.
Proof.
  by intros; apply sum_weights_proper.
Qed.

Lemma incl_equivocating_validators_equivocation_fault
  `{Heqv : BasicEquivocation st validator }
  `{EqDecision validator}
  : forall s1 s2,
    equivocating_validators s1 ⊆ equivocating_validators s2 ->
    (equivocation_fault s1 <= equivocation_fault s2)%R.
Proof.
  intros s1 s2 H_incl.
  by apply sum_weights_subseteq.
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
  is necessary if we are to detect equivocation using a composition constraint, as these
  constraints act upon states, not traces.
*)

Section sec_simple.

Context
  {message : Type}
  (vlsm : VLSM message)
  (pre_vlsm := pre_loaded_with_all_messages_vlsm vlsm)
  .

(**
  The following property detects equivocation in a given
  trace for a given message.
*)
Definition equivocation_in_trace
  (msg : message)
  (tr : list (transition_item vlsm))
  : Prop
  :=
  exists
    (prefix : list transition_item)
    (item : transition_item)
    (suffix : list transition_item),
    tr = prefix ++ item :: suffix
    /\ input item = Some msg
    /\ ~ trace_has_message (field_selector output) msg prefix.

#[export] Instance equivocation_in_trace_dec
  `{EqDecision message}
  : RelDecision equivocation_in_trace.
Proof.
  intros msg tr.
  apply @Decision_iff with
    (List.Exists (fun d => match d with (prefix, item, _) =>
      input item = Some msg /\ ~ trace_has_message (field_selector output) msg prefix
    end) (one_element_decompositions tr)).
  - rewrite Exists_exists.  split.
    + intros [((prefix, item), suffix) [Hitem Heqv]].
      exists prefix, item, suffix.
      by apply elem_of_one_element_decompositions in Hitem.
    + intros [prefix [item [suffix [Hitem Heqv]]]].
      exists ((prefix, item), suffix).
      by rewrite elem_of_one_element_decompositions.
  - apply Exists_dec. intros ((prefix, item), suffix).
    apply and_dec.
    + by apply option_eq_dec.
    + apply not_dec. apply Exists_dec. intros pitem.
      by apply option_eq_dec.
Qed.

Lemma no_equivocation_in_empty_trace m
  : ~ equivocation_in_trace m [].
Proof.
  intros [prefix [suffix [item [Hitem _]]]].
  by destruct prefix; inversion Hitem.
Qed.

Lemma equivocation_in_trace_prefix
  (msg : message)
  (prefix : list (transition_item vlsm))
  (suffix : list (transition_item vlsm))
  : equivocation_in_trace msg prefix -> equivocation_in_trace msg (prefix ++ suffix).
Proof.
  intros (pre & item & suf & -> & Hinput & Hnoutput).
  exists pre, item, (suf ++ suffix).
  by rewrite app_comm_cons, <- !app_assoc.
Qed.

Lemma equivocation_in_trace_last_char
  (msg : message)
  (tr : list (transition_item vlsm))
  (item : transition_item vlsm)
  : equivocation_in_trace msg (tr ++ [item]) <->
    equivocation_in_trace msg tr \/
    input item = Some msg /\ ~ trace_has_message (field_selector output) msg tr.
Proof.
  split.
  - intros [prefix [item' [suffix [Heq_tr_item' [Hinput Hnoutput]]]]].
    destruct_list_last suffix suffix' _item Heq_suffix.
    + by apply app_inj_tail in Heq_tr_item' as [-> ->]; right.
    + rewrite app_comm_cons, !app_assoc in Heq_tr_item'.
      apply app_inj_tail in Heq_tr_item' as [-> ->].
      by left; exists prefix, item', suffix'.
  - intros
      [[prefix [item' [suffix [-> [Hinput Hnoutput]]]]]
      | [Hinput Hnoutput]].
    + exists prefix, item', (suffix ++ [item]).
      by rewrite <- app_assoc.
    + by exists tr, item, [].
Qed.

(**
  We intend to give define several message oracles: [has_been_sent],
  [has_not_been_sent], [has_been_received] and [has_not_been_received].
  To avoid repetition, we give build some generic definitions first.
*)

(** General signature of a message oracle *)

Definition state_message_oracle
  := state vlsm -> message -> Prop.

Definition negate_oracle (o : state_message_oracle) : state_message_oracle :=
  fun s m => ~ o s m.

Definition specialized_selected_message_exists_in_all_traces
  (X : VLSM message)
  (message_selector : message -> transition_item -> Prop)
  (s : state X)
  (m : message)
  : Prop
  :=
  forall
  (start : state X)
  (tr : list transition_item)
  (Htr : finite_valid_trace_init_to X start s tr),
  trace_has_message message_selector m tr.

Definition selected_message_exists_in_all_preloaded_traces
  := specialized_selected_message_exists_in_all_traces pre_vlsm.

Definition specialized_selected_message_exists_in_some_traces
  (X : VLSM message)
  (message_selector : message -> transition_item -> Prop)
  (s : state X)
  (m : message)
  : Prop
  :=
  exists
  (start : state X)
  (tr : list transition_item)
  (Htr : finite_valid_trace_init_to X start s tr),
  trace_has_message message_selector m tr.

Definition selected_message_exists_in_some_preloaded_traces : forall
  (message_selector : message -> transition_item -> Prop)
  (s : state pre_vlsm)
  (m : message),
    Prop
  := specialized_selected_message_exists_in_some_traces pre_vlsm.

Definition specialized_selected_message_exists_in_no_trace
  (X : VLSM message)
  (message_selector : message -> transition_item -> Prop)
  (s : state X)
  (m : message)
  : Prop
  :=
  forall
  (start : state X)
  (tr : list transition_item)
  (Htr : finite_valid_trace_init_to X start s tr),
  ~ trace_has_message message_selector m tr.

Definition selected_message_exists_in_no_preloaded_trace :=
  specialized_selected_message_exists_in_no_trace pre_vlsm.

Lemma selected_message_exists_not_some_iff_no
  (X : VLSM message)
  (message_selector : message -> transition_item -> Prop)
  (s : state X)
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
  (s : state pre_vlsm)
  (m : message)
  : ~ selected_message_exists_in_some_preloaded_traces message_selector s m
    <-> selected_message_exists_in_no_preloaded_trace message_selector s m.
Proof.
  by apply selected_message_exists_not_some_iff_no.
Qed.

(** Sufficient condition for [specialized_selected_message_exists_in_some_traces]. *)
Lemma specialized_selected_message_exists_in_some_traces_from
  (X : VLSM message)
  (message_selector : message -> transition_item -> Prop)
  (s : state X)
  (m : message)
  (start : state X)
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
  (s : state vlsm)
  (m : message)
  : Prop
  :=
  selected_message_exists_in_some_preloaded_traces message_selector s m
  <-> selected_message_exists_in_all_preloaded_traces message_selector s m.

Lemma selected_message_exists_in_all_traces_initial_state
  (s : state vlsm)
  (Hs : initial_state_prop vlsm s)
  (message_selector : message -> transition_item -> Prop)
  (m : message)
  : ~ selected_message_exists_in_all_preloaded_traces message_selector s m.
Proof.
  intro Hselected.
  assert (Hps : valid_state_prop pre_vlsm s) by (apply initial_state_is_valid; done).
  assert (Htr : finite_valid_trace_init_to pre_vlsm s s []) by (split; [constructor |]; done).
  specialize (Hselected s [] Htr).
  unfold trace_has_message in Hselected.
  by rewrite Exists_nil in Hselected.
Qed.

(**
  The oracle should check if all valid traces leading to the state contain the given message.
  The [message_selector] argument checks whether a single transition contains the
  message, and can be used to check for received messages or sent messages.

  Notably, the traces we are considering are any traces valid in the preloaded
  version of the target VLSM. This is because we want VLSMs to have oracles which
  are valid irrespective of the composition they take part in. As we know,
  the behaviors of the projection of a VLSM from a composition are all included
  in the behaviors of the preloaded version of the VLSM.

  It is impossible to define a correct oracle for a [message_selector]
  if there is some valid state that has multiple histories, and some message
  that is in some of those histories but not in others (according to the selector).
*)

Definition all_traces_have_message_prop
  (message_selector : message -> transition_item -> Prop)
  (oracle : state_message_oracle)
  (s : state vlsm)
  (m : message)
  : Prop
  :=
  oracle s m <-> selected_message_exists_in_all_preloaded_traces message_selector s m.

Definition no_traces_have_message_prop
  (message_selector : message -> transition_item -> Prop)
  (oracle : state_message_oracle)
  (s : state vlsm)
  (m : message)
  : Prop
  :=
  oracle s m <-> selected_message_exists_in_no_preloaded_trace message_selector s m.

Record oracle_tracewise_props
  (message_selector : message -> transition_item -> Prop)
  (oracle : state_message_oracle) : Prop :=
{
  proper_oracle_holds :
    forall (s : state pre_vlsm) (Hs : valid_state_prop pre_vlsm s) (m : message),
      all_traces_have_message_prop message_selector oracle s m;
  proper_not_oracle_holds :
    forall (s : state pre_vlsm) (Hs : valid_state_prop pre_vlsm s) (m : message),
      no_traces_have_message_prop message_selector (negate_oracle oracle) s m;
}.

(** *** Stepwise consistency properties for [state_message_oracle]

  The above definitions like [all_traces_have_message_prop]
  connect a [state_message_oracle] to a message selector predicate on
  [transition_item] by requiring the oracle to hold (or not hold)
  for a state and message iff all traces (resp. no trace) reaching the
  state have a transition satisfying the message selector with the given message.

  We will prove that this is equivalent to two more local properties:
  - [oracle_no_inits] is that the oracle cannot hold for any message in any initial state.
  - [oracle_step_update] is that the oracle is coherent around a single
    [input_valid_transition]:
    - If the oracle holds for a message in the starting state, it must
      also hold for that message in the destination state.
    - If the [message_selector] finds a message in the transition, the
      oracle must hold for that message in the destination state.
    - If the oracle holds for a message in the destination, at least
      one of the above cases hold.

  These conditions are defined in the record [oracle_stepwise_props].
  We prove these conditions hold iff [oracle_tracewise_props] holds.
*)

Record oracle_stepwise_props
  (message_selector : message -> transition_item -> Prop)
  (oracle : state_message_oracle)
  : Prop :=
{
  oracle_no_inits :
    forall (s : state vlsm),
      initial_state_prop vlsm s ->
      forall (m : message), ~ oracle s m;
  oracle_step_update :
    forall (l : label _) (s : state _) (im : option message) (s' : state _) (om : option message),
      input_valid_transition (pre_loaded_with_all_messages_vlsm vlsm) l (s, im) (s', om) ->
      forall (msg : message),
      oracle s' msg
        <->
      message_selector msg
        {| l := l; input := im; destination := s'; output := om |} \/ oracle s msg;
}.

Lemma oracle_partial_trace_update
  [selector : message -> transition_item -> Prop]
  [oracle : state_message_oracle]
  (Horacle : oracle_stepwise_props selector oracle)
  s0 s tr
  (Htr : finite_valid_trace_from_to (pre_loaded_with_all_messages_vlsm vlsm) s0 s tr) :
    forall (m : message),
      oracle s m <-> (trace_has_message selector m tr \/ oracle s0 m).
Proof.
  induction Htr; intros m; unfold trace_has_message.
  - rewrite Exists_nil.
    by itauto.
  - rewrite Exists_cons, IHHtr.
    apply (Horacle.(oracle_step_update _ _)) with (msg := m) in Ht.
    by itauto.
Qed.

(*
  It would seem more flexible to take [m] after the other parameters,
  but [Htr] is placed last so that <<apply in>> an existing
  [finite_valid_trace_init_to] hypothesis works.
*)
Lemma oracle_initial_trace_update
  [selector]
  [oracle : state_message_oracle]
  (Horacle : oracle_stepwise_props selector oracle)
  s m
  [s0 tr]
  (Htr : finite_valid_trace_init_to (pre_loaded_with_all_messages_vlsm vlsm) s0 s tr) :
    oracle s m <-> trace_has_message selector m tr.
Proof.
  rewrite (oracle_partial_trace_update Horacle) by apply Htr.
  assert (~ oracle s0 m) by (eapply oracle_no_inits, Htr; done).
  by itauto.
Qed.

(* TODO(wkolowski): make notation uniform accross the file. *)
Lemma oracle_stepwise_props_change_selector
  [selector : message -> transition_item -> Prop]
  [oracle : state_message_oracle]
  (Horacle : oracle_stepwise_props selector oracle)
  (selector' : message -> transition_item -> Prop)
  (Heqv :
    forall s item,
      input_valid_transition_item (pre_loaded_with_all_messages_vlsm vlsm) s item ->
      forall m, selector m item <-> selector' m item)
  : oracle_stepwise_props selector' oracle.
Proof.
  destruct Horacle as [Hinits Hupdate].
  constructor; [done |].
  by intros; rewrite Hupdate, Heqv.
Qed.

Lemma oracle_trace_props_from_stepwise
  [selector : message -> transition_item -> Prop]
  [oracle : state_message_oracle]
  (Horacle : oracle_stepwise_props selector oracle) :
  oracle_tracewise_props selector oracle.
Proof.
  constructor; intros s Hs m.
  - red; unfold selected_message_exists_in_all_preloaded_traces,
      specialized_selected_message_exists_in_all_traces.
    split.
    + intros Hholds s0 tr Htr.
      by eapply (oracle_initial_trace_update Horacle).
    + apply pre_loaded_with_all_messages_valid_state_prop,
        valid_state_has_trace in Hs as (start & tr & Htr).
      intro H; specialize (H start tr Htr).
      by eapply oracle_initial_trace_update.
  - red; unfold negate_oracle, selected_message_exists_in_no_preloaded_trace,
      specialized_selected_message_exists_in_no_trace.
    split.
    + intros Hclaim start tr Htr.
      contradict Hclaim.
      by eapply oracle_initial_trace_update.
    + apply pre_loaded_with_all_messages_valid_state_prop,
        valid_state_has_trace in Hs as (start & tr & Htr).
      intro H; specialize (H start tr Htr); contradict H.
      by eapply (oracle_initial_trace_update Horacle).
Qed.

(**
  The most basic [state_message_oracle]s just check whether the message is
  - *sent* - is the output of the transition
  - *received* - is the output of the transition
  - *observed* - is either sent or received in the transition.
 *)

Definition has_been_sent_prop : state_message_oracle -> state vlsm -> message -> Prop :=
  all_traces_have_message_prop (field_selector output).

Definition has_not_been_sent_prop : state_message_oracle -> state vlsm -> message -> Prop :=
  no_traces_have_message_prop (field_selector output).

Definition has_been_received_prop : state_message_oracle -> state vlsm -> message -> Prop :=
  all_traces_have_message_prop (field_selector input).

Definition has_not_been_received_prop
  : state_message_oracle -> state vlsm -> message -> Prop :=
  no_traces_have_message_prop (field_selector input).

(**
  Per the vocabulary of the official VLSM document, we say that VLSMs endowed
  with a [state_message_oracle] for sent messages have the [has_been_sent] capability.
  Capabilities for receiving messages are treated analogously, so we omit mentioning
  them explicitly.

  Notably, we also define the [has_not_been_sent] oracle, which decides if a message
  has definitely not been sent, on any of the traces producing a current state.

  Furthermore, we require a [sent_excluded_middle] property, which stipulates
  that any argument to the oracle should return true in exactly one of
  [has_been_sent] and [has_not_been_sent].
*)

Definition has_been_sent_stepwise_prop
    (has_been_sent_pred : state_message_oracle) : Prop :=
  oracle_stepwise_props (field_selector output) has_been_sent_pred.

Class HasBeenSentCapability : Type :=
{
  has_been_sent : state_message_oracle;
  has_been_sent_dec :> RelDecision has_been_sent;
  has_been_sent_stepwise_props : has_been_sent_stepwise_prop has_been_sent;
}.

Definition has_not_been_sent `{HasBeenSentCapability} : state_message_oracle :=
  negate_oracle has_been_sent.

Definition has_been_sent_no_inits `{HasBeenSentCapability} :
  forall s : state vlsm,
    initial_state_prop vlsm s -> ∀ m : message, ~ has_been_sent s m
  := oracle_no_inits _ _ (has_been_sent_stepwise_props).

Definition has_been_sent_step_update `{HasBeenSentCapability} :
  forall (l : label _) (s : state _) (im : option message) (s' : state _) (om : option message),
    input_valid_transition (pre_loaded_with_all_messages_vlsm vlsm) l (s, im) (s', om) ->
  forall msg,
    has_been_sent s' msg <-> (om = Some msg \/ has_been_sent s msg)
  := oracle_step_update _ _ has_been_sent_stepwise_props.

Definition has_been_sent_tracewise_prop
    (has_been_sent_pred : state_message_oracle) : Prop :=
  oracle_tracewise_props (field_selector output) has_been_sent_pred.

Lemma has_been_sent_tracewise_props `{HasBeenSentCapability} :
  has_been_sent_tracewise_prop has_been_sent.
Proof.
  by exact (oracle_trace_props_from_stepwise has_been_sent_stepwise_props).
Qed.

Lemma proper_sent `{HasBeenSentCapability} :
  forall (s : state pre_vlsm) (Hs : valid_state_prop pre_vlsm s) (m : message),
    has_been_sent_prop has_been_sent s m.
Proof.
  by intros; apply has_been_sent_tracewise_props.
Qed.

Lemma proper_not_sent `{HasBeenSentCapability} :
  forall (s : state pre_vlsm) (Hs : valid_state_prop pre_vlsm s) (m : message),
    has_not_been_sent_prop has_not_been_sent s m.
Proof.
  by intros; apply has_been_sent_tracewise_props.
Qed.

(** Reverse implication for 'selected_messages_consistency_prop' always holds. *)
Lemma consistency_from_valid_state_proj2
  (s : state pre_vlsm)
  (Hs : valid_state_prop pre_vlsm s)
  (m : message)
  (selector : message -> transition_item -> Prop)
  (Hall : selected_message_exists_in_all_preloaded_traces selector s m)
  : selected_message_exists_in_some_preloaded_traces selector s m.
Proof.
  apply valid_state_has_trace in Hs.
  destruct Hs as [is [tr Htr]].
  exists _, _, Htr.
  by apply (Hall _ _ Htr).
Qed.

Lemma has_been_sent_consistency
  `{HasBeenSentCapability}
  (s : state pre_vlsm)
  (Hs : valid_state_prop pre_vlsm s)
  (m : message)
  : selected_messages_consistency_prop (field_selector output) s m.
Proof.
  split; [| by apply consistency_from_valid_state_proj2].
  intro Hsome.
  destruct (decide (has_been_sent s m)) as [Hsm | Hsm].
  - by apply proper_sent in Hsm.
  - apply proper_not_sent in Hsm; [| done].
    destruct Hsome as [is [tr [Htr Hmsg]]].
    by elim (Hsm _ _ Htr).
Qed.

Lemma can_produce_has_been_sent
  `{HasBeenSentCapability}
  (s : state pre_vlsm)
  (m : message)
  (Hsm : can_produce pre_vlsm s m)
  : has_been_sent s m.
Proof.
  assert (valid_state_prop pre_vlsm s) by (apply can_produce_valid in Hsm; eexists; done).
  apply proper_sent; [done |].
  apply has_been_sent_consistency; [done |].
  apply non_empty_valid_trace_from_can_produce in Hsm.
  destruct Hsm as [is [tr [lst_tr [Htr [Hlst [Hs Hm]]]]]].
  destruct_list_last tr tr' _lst_tr Heqtr; [by inversion Hlst |].
  rewrite last_error_is_last in Hlst.
  inversion Hlst; subst _lst_tr; clear Hlst.
  apply valid_trace_add_default_last in Htr.
  rewrite finite_trace_last_is_last, Hs in Htr.
  eexists _, _, Htr.
  by apply Exists_app; right; left.
Qed.

(**
  Sufficient condition for [proper_sent] avoiding the
  [pre_loaded_with_all_messages_vlsm].
*)
Lemma specialized_proper_sent
  `{HasBeenSentCapability}
  (s : state vlsm)
  (Hs : valid_state_prop vlsm s)
  (m : message)
  (Hsome : specialized_selected_message_exists_in_some_traces vlsm (field_selector output) s m)
  : has_been_sent s m.
Proof.
  destruct Hs as [_om Hs].
  assert (Hpres : valid_state_prop pre_vlsm s)
    by (exists _om; apply pre_loaded_with_all_messages_valid_state_message_preservation; done).
  apply proper_sent; [done |].
  specialize (has_been_sent_consistency s Hpres m) as Hcons.
  apply Hcons.
  destruct Hsome as [is [tr [Htr Hsome]]].
  exists is, tr.
  split; [| done].
  revert Htr.
  unfold pre_vlsm; clear.
  destruct vlsm as (T, M).
  by apply VLSM_incl_finite_valid_trace_init_to, vlsm_incl_pre_loaded_with_all_messages_vlsm.
Qed.

(**
  [proper_sent] condition specialized to regular VLSM traces
  (avoiding [pre_loaded_with_all_messages_vlsm]).
*)
Lemma specialized_proper_sent_rev
  `{HasBeenSentCapability}
  (s : state vlsm)
  (Hs : valid_state_prop vlsm s)
  (m : message)
  (Hsm : has_been_sent s m)
  : specialized_selected_message_exists_in_all_traces vlsm (field_selector output) s m.
Proof.
  destruct Hs as [_om Hs].
  assert (Hpres : valid_state_prop pre_vlsm s)
    by (exists _om; apply pre_loaded_with_all_messages_valid_state_message_preservation; done).
  apply proper_sent in Hsm; [| done].
  intros is tr Htr.
  specialize (Hsm is tr).
  spec Hsm; [| done].
  revert Htr.
  unfold pre_vlsm; clear.
  destruct vlsm as (T, M).
  by apply VLSM_incl_finite_valid_trace_init_to, vlsm_incl_pre_loaded_with_all_messages_vlsm.
Qed.

Lemma has_been_sent_consistency_proper_not_sent
  (has_been_sent : state_message_oracle)
  (has_been_sent_dec : RelDecision has_been_sent)
  (s : state vlsm)
  (m : message)
  (proper_sent : has_been_sent_prop has_been_sent s m)
  (has_not_been_sent
    := fun (s : state vlsm) (m : message) => ~ has_been_sent s m)
  (Hconsistency : selected_messages_consistency_prop (field_selector output) s m)
  : has_not_been_sent_prop has_not_been_sent s m.
Proof.
  unfold has_not_been_sent_prop.
  unfold no_traces_have_message_prop.
  unfold has_not_been_sent.
  rewrite <- selected_message_exists_preloaded_not_some_iff_no.
  by apply not_iff_compat, (iff_trans proper_sent).
Qed.

Definition has_been_received_stepwise_prop
  (has_been_received_pred : state_message_oracle) : Prop :=
    oracle_stepwise_props (field_selector input) has_been_received_pred.

Class HasBeenReceivedCapability : Type :=
{
  has_been_received : state_message_oracle;
  has_been_received_dec :> RelDecision has_been_received;
  has_been_received_stepwise_props :
    has_been_received_stepwise_prop has_been_received;
}.

Definition has_not_been_received `{HasBeenReceivedCapability} : state_message_oracle :=
  negate_oracle has_been_received.

Definition has_been_received_no_inits `{HasBeenReceivedCapability} :
  forall s : state vlsm,
    initial_state_prop vlsm s -> ∀ m : message, ~ has_been_received s m
  := oracle_no_inits _ _ has_been_received_stepwise_props.

Definition has_been_received_step_update `{HasBeenReceivedCapability} :
  forall [l : label _] [s : state _] [im : option message] [s' : state _] [om : option message],
    input_valid_transition (pre_loaded_with_all_messages_vlsm vlsm) l (s, im) (s', om) ->
  forall msg,
    has_been_received s' msg <-> (im = Some msg \/ has_been_received s msg)
  := oracle_step_update _ _ has_been_received_stepwise_props.

Definition has_been_received_tracewise_prop
  (has_been_received_pred : state_message_oracle) : Prop :=
    oracle_tracewise_props (field_selector input) has_been_received_pred.

Lemma has_been_received_tracewise_props `{HasBeenReceivedCapability} :
  has_been_received_tracewise_prop has_been_received.
Proof.
  by apply oracle_trace_props_from_stepwise, has_been_received_stepwise_props.
Qed.

Lemma proper_received `{HasBeenReceivedCapability} :
  forall (s : state pre_vlsm) (Hs : valid_state_prop pre_vlsm s) (m : message),
    has_been_received_prop has_been_received s m.
Proof.
  by apply proper_oracle_holds, has_been_received_tracewise_props.
Qed.

Lemma proper_not_received `{HasBeenReceivedCapability} :
  forall (s : state pre_vlsm) (Hs : valid_state_prop pre_vlsm s) (m : message),
    has_not_been_received_prop has_not_been_received s m.
Proof.
  by apply proper_not_oracle_holds, has_been_received_tracewise_props.
Qed.

Lemma has_been_received_consistency
  `{HasBeenReceivedCapability}
  (s : state pre_vlsm)
  (Hs : valid_state_prop pre_vlsm s)
  (m : message)
  : selected_messages_consistency_prop (field_selector input) s m.
Proof.
  split; [| by apply consistency_from_valid_state_proj2].
  intro Hsome.
  destruct (decide (has_been_received s m)) as [Hsm | Hsm];
    [by apply proper_received in Hsm |].
  apply proper_not_received in Hsm; [| done].
  destruct Hsome as [is [tr [Htr Hsome]]].
  by elim (Hsm _ _ Htr).
Qed.

Lemma has_been_received_consistency_proper_not_received
  (has_been_received : state_message_oracle)
  (has_been_received_dec : RelDecision has_been_received)
  (s : state vlsm)
  (m : message)
  (proper_received : has_been_received_prop has_been_received s m)
  (has_not_been_received
    := fun (s : state vlsm) (m : message) => ~ has_been_received s m)
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
  (s : state vlsm)
  : Type
  :=
  sig (fun m => selected_message_exists_in_some_preloaded_traces (field_selector output) s m).

Lemma sent_messages_proper
  `{HasBeenSentCapability}
  (s : state vlsm)
  (Hs : valid_state_prop pre_vlsm s)
  (m : message)
  : has_been_sent s m <-> exists (m' : sent_messages s), proj1_sig m' = m.
Proof.
  unfold sent_messages. rewrite exists_proj1_sig.
  specialize (proper_sent s Hs m) as Hbs.
  unfold has_been_sent_prop, all_traces_have_message_prop in Hbs.
  rewrite Hbs.
  symmetry.
  by apply has_been_sent_consistency.
Qed.

Definition received_messages
  (s : state vlsm)
  : Type
  :=
  sig (fun m => selected_message_exists_in_some_preloaded_traces (field_selector input) s m).

Lemma received_messages_proper
  `{HasBeenReceivedCapability}
  (s : state vlsm)
  (Hs : valid_state_prop pre_vlsm s)
  (m : message)
  : has_been_received s m <-> exists (m' : received_messages s), proj1_sig m' = m.
Proof.
  unfold received_messages. rewrite exists_proj1_sig.
  specialize (proper_received s Hs m) as Hbs.
  unfold has_been_received_prop, all_traces_have_message_prop in Hbs.
  rewrite Hbs.
  symmetry.
  by apply has_been_received_consistency.
Qed.

End sec_simple.

Arguments oracle_stepwise_props {message} {vlsm} message_selector oracle.
Arguments oracle_no_inits       {message} {vlsm} {message_selector} {oracle}.
Arguments oracle_step_update    {message} {vlsm} {message_selector} {oracle}.

Arguments has_been_sent_stepwise_prop     {message} {vlsm} _.
Arguments has_been_received_stepwise_prop {message} {vlsm} _.

#[global] Hint Mode HasBeenSentCapability - ! : typeclass_instances.
#[global] Hint Mode HasBeenReceivedCapability - ! : typeclass_instances.

Arguments has_been_sent_stepwise_props     {message} vlsm {_}.
Arguments has_been_received_stepwise_props {message} vlsm {_}.

Arguments has_been_sent_step_update     {message} {vlsm H} [l s im s' om] _ msg.
Arguments has_been_received_step_update {message} {vlsm H} [l s im s' om] _ msg.

(**
  Proving the trace properties from the stepwise properties
  is based on [oracle_initial_trace_update].
  The theorems for [all_traces_have_message_prop]
  and [no_traces_have_message_prop] are mostly rearranging
  quantifiers to use this lemma, also using [valid_state_has_trace]
  to choose a trace reaching the state when one is not given.
*)

Section sec_trace_from_stepwise.

Context
  (message : Type)
  (vlsm : VLSM message)
  (selector : message -> transition_item -> Prop)
  (oracle : state_message_oracle vlsm)
  (oracle_props : oracle_stepwise_props selector oracle)
  .

Lemma prove_all_have_message_from_stepwise :
  forall (s : state _)
         (Hs : valid_state_prop (pre_loaded_with_all_messages_vlsm vlsm) s)
         (m : message),
    all_traces_have_message_prop vlsm selector oracle s m.
Proof.
  intros s Hproto m.
  unfold all_traces_have_message_prop.
  split.
  - intros Hholds s0 tr Htr; revert Htr Hholds.
    by apply oracle_initial_trace_update.
  - intro H_all_traces.
    apply valid_state_has_trace in Hproto as (s0 & tr & Htr).
    rewrite oracle_initial_trace_update; [| done..].
    by apply H_all_traces in Htr.
Qed.

Lemma prove_none_have_message_from_stepwise :
  forall (s : state (pre_loaded_with_all_messages_vlsm vlsm))
         (Hs : valid_state_prop (pre_loaded_with_all_messages_vlsm vlsm) s)
         (m : message),
    no_traces_have_message_prop vlsm selector (fun s m => ~ oracle s m) s m.
Proof.
  intros s Hproto m.
  split.
  - intros H_not_holds start tr Htr.
    contradict H_not_holds.
    by eapply oracle_initial_trace_update.
  - intros H_no_traces H_oracle.
    apply valid_state_has_trace in Hproto as (s0 & tr & Htr).
    destruct (H_no_traces s0 tr Htr).
    by rewrite <- oracle_initial_trace_update.
Qed.

Lemma selected_messages_consistency_prop_from_stepwise
    (oracle_dec : RelDecision oracle)
    (s : state (pre_loaded_with_all_messages_vlsm vlsm))
    (Hs : valid_state_prop (pre_loaded_with_all_messages_vlsm vlsm) s)
    (m : message)
    : selected_messages_consistency_prop vlsm selector s m.
Proof.
  split; [| by apply consistency_from_valid_state_proj2].
  intro Hsome.
  destruct (decide (oracle s m)) as [Hsm | Hsm].
  - by apply prove_all_have_message_from_stepwise in Hsm.
  - apply prove_none_have_message_from_stepwise in Hsm; [| done].
    destruct Hsome as [is [tr [Htr Hmsg]]].
    by elim (Hsm _ _ Htr).
Qed.

Lemma in_futures_preserving_oracle_from_stepwise :
  forall (s1 s2 : state (pre_loaded_with_all_messages_vlsm vlsm))
    (Hfutures : in_futures (pre_loaded_with_all_messages_vlsm vlsm) s1 s2)
    (m : message),
    oracle s1 m -> oracle  s2 m.
Proof.
  intros s1 s2 [tr Htr] m Hs1m.
  by eapply oracle_partial_trace_update; [| | right].
Qed.

End sec_trace_from_stepwise.

(**
  The stepwise properties are proven from the trace properties
  by considering the empty trace to prove the [oracle_no_inits]
  property, and by considering a trace that ends with the given
  [input_valid_transition] to prove the [oracle_step_update] property.
*)

Section sec_stepwise_from_trace.

Context
  (message : Type)
  (vlsm : VLSM message)
  (selector : message -> transition_item -> Prop)
  (oracle : state_message_oracle vlsm)
  (oracle_dec : RelDecision oracle)
  (Horacle_all_have :
     forall s (Hs : valid_state_prop (pre_loaded_with_all_messages_vlsm vlsm) s) m,
      all_traces_have_message_prop vlsm selector oracle s m)
  (Hnot_oracle_none_have :
     forall s (Hs : valid_state_prop (pre_loaded_with_all_messages_vlsm vlsm) s) m,
       no_traces_have_message_prop vlsm selector (fun m s => ~ oracle m s) s m).

Lemma oracle_no_inits_from_trace :
  forall (s : state vlsm), initial_state_prop vlsm s ->
                           forall m, ~ oracle s m.
Proof.
  intros s Hinit m Horacle.
  assert (Hproto : valid_state_prop (pre_loaded_with_all_messages_vlsm vlsm) s)
    by (apply initial_state_is_valid; done).
  apply Horacle_all_have in Horacle; [| done].
  specialize (Horacle s nil).
  eapply Exists_nil; apply Horacle; clear Horacle.
  by split; [constructor |].
Qed.

Lemma examine_one_trace :
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

Lemma oracle_step_property_from_trace :
     forall l s im s' om,
       input_valid_transition (pre_loaded_with_all_messages_vlsm vlsm) l (s, im) (s', om) ->
       forall msg, oracle s' msg
                   <-> (selector msg {| l := l; input := im; destination := s'; output := om |}
                        \/ oracle s msg).
Proof.
  intros l s im s' om Htrans msg.
  rename Htrans into Htrans'.
  pose proof Htrans' as [[Hproto_s [Hproto_m Hvalid]] Htrans].
  set (preloaded := pre_loaded_with_all_messages_vlsm vlsm) in * |- *.
  pose proof (valid_state_has_trace _ _ Hproto_s)
    as [is [tr [Htr Hinit]]].
  pose proof (Htr' := extend_right_finite_trace_from_to _ Htr Htrans').
  rewrite (examine_one_trace _ _ _ (conj Htr Hinit) msg).
  rewrite (examine_one_trace _ _ _ (conj Htr' Hinit) msg).
  clear.
  progress cbn. unfold trace_has_message.
  rewrite Exists_app, Exists_cons, Exists_nil.
  by itauto.
Qed.

Lemma stepwise_props_from_trace : oracle_stepwise_props selector oracle.
Proof.
  constructor.
  - by apply oracle_no_inits_from_trace.
  - by apply oracle_step_property_from_trace.
Defined.

End sec_stepwise_from_trace.

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
*)

(* TODO - move up with HasBeenSent *)

Lemma preloaded_has_been_sent_stepwise_props
      [message : Type]
      (vlsm : VLSM message)
      `{HasBeenSentCapability message vlsm}
      (seed : message -> Prop)
      (X := pre_loaded_vlsm vlsm seed) :
  has_been_sent_stepwise_prop (vlsm := X) (has_been_sent vlsm).
Proof.
  by destruct (has_been_sent_stepwise_props vlsm).
Qed.

#[export] Instance preloaded_HasBeenSentCapability
      [message : Type]
      (vlsm : VLSM message)
      `{HasBeenSentCapability message vlsm}
      (seed : message -> Prop) :
  HasBeenSentCapability (pre_loaded_vlsm vlsm seed).
Proof.
  econstructor.
  - by apply (has_been_sent_dec vlsm).
  - by apply preloaded_has_been_sent_stepwise_props.
Defined.

Lemma has_been_sent_examine_one_trace
  `{HasBeenSentCapability message vlsm} :
  forall is s tr,
    finite_valid_trace_init_to (pre_loaded_with_all_messages_vlsm vlsm) is s tr ->
  forall m,
    has_been_sent vlsm s m <->
    trace_has_message (field_selector output) m tr.
Proof.
  apply examine_one_trace.
  - by apply has_been_sent_dec.
  - by apply proper_sent.
  - by apply proper_not_sent.
Qed.

Lemma preloaded_has_been_received_stepwise_props
      {message : Type}
      (vlsm : VLSM message)
      `{HasBeenReceivedCapability message vlsm}
      (seed : message -> Prop)
      (X := pre_loaded_vlsm vlsm seed) :
  has_been_received_stepwise_prop (vlsm := X) (has_been_received vlsm).
Proof.
  by destruct (has_been_received_stepwise_props vlsm).
Qed.

#[export] Instance preloaded_HasBeenReceivedCapability
      {message : Type}
      (vlsm : VLSM message)
      `{HasBeenReceivedCapability message vlsm}
      (seed : message -> Prop) :
  HasBeenReceivedCapability (pre_loaded_vlsm vlsm seed).
Proof.
  econstructor.
  - by apply (has_been_received_dec vlsm).
  - by apply preloaded_has_been_received_stepwise_props.
Defined.

Lemma has_been_received_examine_one_trace
  `{HasBeenReceivedCapability message vlsm} :
  forall is s tr,
    finite_valid_trace_init_to (pre_loaded_with_all_messages_vlsm vlsm) is s tr ->
  forall m,
    has_been_received vlsm s m <->
    trace_has_message (field_selector input) m tr.
Proof.
  apply examine_one_trace.
  - by apply has_been_received_dec.
  - by apply proper_received.
  - by apply proper_not_received.
Qed.

Lemma trace_to_initial_state_has_no_inputs
  {message} vlsm
  `{HasBeenReceivedCapability message vlsm}
  is s tr
  (Htr : finite_valid_trace_init_to (pre_loaded_with_all_messages_vlsm vlsm) is s tr)
  (Hs : initial_state_prop vlsm s)
  : forall item, item ∈ tr -> input item = None.
Proof.
  intros item Hitem.
  destruct (input item) as [m |] eqn: Heqm; [| done].
  elim (selected_message_exists_in_all_traces_initial_state _ _ Hs (field_selector input) m).
  apply has_been_received_consistency; [done | by apply initial_state_is_valid |].
  eexists _, _, Htr.
  apply Exists_exists.
  by exists item.
Qed.

(** ** A state message oracle for messages sent or received

  In protocols like the CBC full node protocol, validators often
  work with the set of all messages they have directly observed,
  which includes the messages the node sent itself along with
  messages that were received.
  The [has_been_directly_observed] oracle tells whether the given message was sent
  or received during any trace leading to the given state.
*)

Class HasBeenDirectlyObservedCapability {message} (vlsm : VLSM message) : Type :=
{
  has_been_directly_observed : state_message_oracle vlsm;
  has_been_directly_observed_dec :> RelDecision has_been_directly_observed;
  has_been_directly_observed_stepwise_props :
    oracle_stepwise_props item_sends_or_receives has_been_directly_observed;
}.

Arguments has_been_directly_observed {message} vlsm {_}.
Arguments has_been_directly_observed_dec {message} vlsm {_}.
Arguments has_been_directly_observed_stepwise_props {message} vlsm {_}.

#[global] Hint Mode HasBeenDirectlyObservedCapability - ! : typeclass_instances.

Definition has_been_directly_observed_no_inits `[HasBeenDirectlyObservedCapability message vlsm]
  := oracle_no_inits (has_been_directly_observed_stepwise_props vlsm).

Definition has_been_directly_observed_step_update `{HasBeenDirectlyObservedCapability message vlsm} :
  forall l s im s' om,
    input_valid_transition (pre_loaded_with_all_messages_vlsm vlsm) l (s, im) (s', om) ->
    forall msg,
      has_been_directly_observed vlsm s' msg <->
      ((im = Some msg \/ om = Some msg) \/ has_been_directly_observed vlsm s msg)
  := oracle_step_update (has_been_directly_observed_stepwise_props vlsm).

Lemma proper_directly_observed
  {message} (vlsm : VLSM message) `{HasBeenDirectlyObservedCapability message vlsm} :
  forall (s : state (pre_loaded_with_all_messages_vlsm vlsm)),
    valid_state_prop (pre_loaded_with_all_messages_vlsm vlsm) s ->
    forall m,
      all_traces_have_message_prop vlsm item_sends_or_receives (has_been_directly_observed vlsm) s m.
Proof.
  by apply proper_oracle_holds, oracle_trace_props_from_stepwise,
    has_been_directly_observed_stepwise_props.
Qed.

Lemma proper_not_directly_observed
  `(vlsm : VLSM message) `{HasBeenDirectlyObservedCapability message vlsm} :
  forall (s : state (pre_loaded_with_all_messages_vlsm vlsm)),
    valid_state_prop (pre_loaded_with_all_messages_vlsm vlsm) s ->
    forall m,
      no_traces_have_message_prop vlsm item_sends_or_receives
                                  (fun s m => ~ has_been_directly_observed vlsm s m) s m.
Proof.
  by apply proper_not_oracle_holds, oracle_trace_props_from_stepwise,
    has_been_directly_observed_stepwise_props.
Qed.

Lemma has_been_directly_observed_examine_one_trace
  {message} (vlsm : VLSM message) `{HasBeenDirectlyObservedCapability message vlsm} :
  forall is s tr,
    finite_valid_trace_init_to (pre_loaded_with_all_messages_vlsm vlsm) is s tr ->
  forall m,
    has_been_directly_observed vlsm s m <->
    trace_has_message item_sends_or_receives m tr.
Proof.
  apply examine_one_trace.
  - by apply has_been_directly_observed_dec.
  - by apply proper_directly_observed.
  - by apply proper_not_directly_observed.
Qed.

(**
  A received message introduces no additional equivocations to a state
  if it has already been observed in <<s>>.
*)
Definition no_additional_equivocations
  {message : Type}
  (vlsm : VLSM message)
  `{HasBeenDirectlyObservedCapability message vlsm}
  (s : state vlsm)
  (m : message)
  : Prop
  :=
  has_been_directly_observed vlsm s m.

(** [no_additional_equivocations] is decidable. *)

Lemma no_additional_equivocations_dec
  {message : Type}
  (vlsm : VLSM message)
  `{HasBeenDirectlyObservedCapability message vlsm}
  : RelDecision (no_additional_equivocations vlsm).
Proof.
  by apply has_been_directly_observed_dec.
Qed.

Definition no_additional_equivocations_constraint
  {message : Type}
  (vlsm : VLSM message)
  `{HasBeenDirectlyObservedCapability message vlsm}
  (l : label vlsm)
  (som : state vlsm * option message)
  : Prop
  :=
  let (s, om) := som in
  from_option (no_additional_equivocations vlsm s) True om.

Section sec_sent_received_observed_capabilities.

Context
  {message : Type}
  (vlsm : VLSM message)
  `{HasBeenReceivedCapability message vlsm}
  `{HasBeenSentCapability message vlsm}
  .

Lemma has_been_directly_observed_sent_received_iff
  `{HasBeenDirectlyObservedCapability message vlsm}
  (s : state (pre_loaded_with_all_messages_vlsm vlsm))
  (Hs : valid_state_prop (pre_loaded_with_all_messages_vlsm vlsm) s)
  (m : message)
  : has_been_directly_observed vlsm s m <-> has_been_received vlsm s m \/ has_been_sent vlsm s m.
Proof.
  induction Hs using valid_state_prop_ind.
  - split.
    + by intros ?%has_been_directly_observed_no_inits.
    + by intros [?%has_been_received_no_inits | ?%has_been_sent_no_inits].
  - rewrite has_been_directly_observed_step_update by done.
    rewrite has_been_received_step_update by done.
    rewrite has_been_sent_step_update by done.
    by itauto.
Qed.

Definition has_been_directly_observed_from_sent_received
  (s : state vlsm)
  (m : message)
  : Prop
  := has_been_sent vlsm s m \/ has_been_received vlsm s m.

Lemma has_been_directly_observed_from_sent_received_dec
  : RelDecision has_been_directly_observed_from_sent_received.
Proof.
  intros s m.
  apply or_dec.
  - by apply has_been_sent_dec.
  - by apply has_been_received_dec.
Qed.

Lemma has_been_directly_observed_from_sent_received_stepwise_props
  : oracle_stepwise_props item_sends_or_receives has_been_directly_observed_from_sent_received.
Proof.
  unfold has_been_directly_observed_from_sent_received.
  split.
  - intros s Hs m [Hsent | Hrecv].
    + by apply has_been_sent_no_inits in Hsent.
    + by apply has_been_received_no_inits in Hrecv.
  - intros l s im s' om Ht m. cbn.
    rewrite has_been_sent_step_update by done.
    rewrite has_been_received_step_update by done.
    by itauto.
Qed.

#[export] Program Instance HasBeenDirectlyObservedCapability_from_sent_received
  : HasBeenDirectlyObservedCapability vlsm
  :=
  { has_been_directly_observed := has_been_directly_observed_from_sent_received;
    has_been_directly_observed_dec := has_been_directly_observed_from_sent_received_dec;
    has_been_directly_observed_stepwise_props :=
      has_been_directly_observed_from_sent_received_stepwise_props
  }.

Lemma has_been_directly_observed_consistency
  `{HasBeenDirectlyObservedCapability message vlsm}
  (s : state (pre_loaded_with_all_messages_vlsm vlsm))
  (Hs : valid_state_prop (pre_loaded_with_all_messages_vlsm vlsm) s)
  (m : message)
  : selected_messages_consistency_prop vlsm item_sends_or_receives s m.
Proof.
  split; [| by apply consistency_from_valid_state_proj2].
  intro Hsome.
  destruct (decide (has_been_directly_observed vlsm s m)) as [Hsm | Hsm].
  - by apply proper_directly_observed in Hsm.
  - apply proper_not_directly_observed in Hsm; [| done].
    destruct Hsome as [is [tr [Htr Hmsg]]].
    by elim (Hsm _ _ Htr).
Qed.

End sec_sent_received_observed_capabilities.

Definition computable_messages_oracle
  `(vlsm : VLSM message)
  (oracle_set : state vlsm -> set message)
  (message_selector : message -> transition_item -> Prop) : Prop :=
    oracle_stepwise_props message_selector (fun s m => m ∈ oracle_set s).

Class ComputableSentMessages `(vlsm : VLSM message) : Type :=
{
  sent_messages_set : state vlsm -> list message;
  csm_computable_oracle :
    computable_messages_oracle vlsm sent_messages_set (field_selector output);
}.

Global Hint Mode ComputableSentMessages - ! : typeclass_instances.

Class ComputableReceivedMessages `(vlsm : VLSM message) : Type :=
{
  received_messages_set : state vlsm -> list message;
  crm_computable_oracle :
    computable_messages_oracle vlsm received_messages_set (field_selector input);
}.

Global Hint Mode ComputableReceivedMessages - ! : typeclass_instances.

(** ** Properties of Computable Message Oracles

  In this section we prove several generic results about [computable_messages_oracle]s,
  derive [HasBeenSentCapability] and [HasBeenReceivedCapability] from
  [ComputableSentMessages] and [ComputableReceivedMessages] and some basic results
  about computable (directly) observed messages.
*)

Section sec_computable_sent_received_observed.

Context
  `(vlsm : VLSM message).

Lemma computable_messages_oracle_initial_state_empty
  `(Hrm : computable_messages_oracle vlsm oracle_set message_selector)
  (s : state vlsm)
  (Hs : initial_state_prop vlsm s)
  : oracle_set s = [].
Proof.
  apply elem_of_nil_inv; intro.
  by eapply oracle_no_inits in Hs; [| apply Hrm]; cbn in Hs.
Qed.

Definition computable_messages_oracle_rel
  `(Hrm : computable_messages_oracle vlsm oracle_set message_selector)
  (s : state vlsm)
  (m : message)
  : Prop :=
  m ∈ oracle_set s.

Definition computable_messages_oracle_rel_dec
  `(Hrm : computable_messages_oracle vlsm oracle_set message_selector)
  `{EqDecision message}
  : RelDecision (computable_messages_oracle_rel Hrm) :=
  fun s m => decide_rel _ _ (oracle_set s).

Lemma ComputableSentMessages_initial_state_empty
  `{!ComputableSentMessages vlsm}
  (s : initial_state vlsm)
  : sent_messages_set (proj1_sig s) = [].
Proof.
  by eapply computable_messages_oracle_initial_state_empty;
    [apply csm_computable_oracle | destruct s].
Qed.

Definition ComputableSentMessages_has_been_sent
  `{!ComputableSentMessages vlsm}
  : state vlsm -> message -> Prop :=
  computable_messages_oracle_rel csm_computable_oracle.

#[export] Instance computable_sent_message_has_been_sent_dec
  `{!ComputableSentMessages vlsm}
  `{EqDecision message}
  : RelDecision ComputableSentMessages_has_been_sent :=
  computable_messages_oracle_rel_dec csm_computable_oracle.

#[export] Instance ComputableSentMessages_HasBeenSentCapability
  `{!ComputableSentMessages vlsm}
  `{EqDecision message}
  : HasBeenSentCapability vlsm.
Proof.
  econstructor; cycle 1.
  - by apply csm_computable_oracle.
  - by typeclasses eauto.
Defined.

Lemma elem_of_sent_messages_set
  `{!ComputableSentMessages vlsm}
  `{EqDecision message}
  : forall (s : state vlsm) (m : message),
      m ∈ sent_messages_set s
        <->
      has_been_sent vlsm s m.
Proof. done. Qed.

Lemma ComputableReceivedMessages_initial_state_empty
  `{!ComputableReceivedMessages vlsm}
  (s : initial_state vlsm)
  : received_messages_set (proj1_sig s) = [].
Proof.
  by eapply computable_messages_oracle_initial_state_empty;
    [apply crm_computable_oracle | destruct s].
Qed.

Definition ComputableReceivedMessages_has_been_sent
  `{!ComputableReceivedMessages vlsm}
  : state vlsm -> message -> Prop
  := computable_messages_oracle_rel crm_computable_oracle.

#[export] Instance computable_received_message_has_been_sent_dec
  `{!ComputableReceivedMessages vlsm}
  `{EqDecision message}
  : RelDecision ComputableReceivedMessages_has_been_sent :=
  computable_messages_oracle_rel_dec crm_computable_oracle.

#[export] Instance ComputableReceivedMessages_HasBeenReceivedCapability
  `{!ComputableReceivedMessages vlsm}
  `{EqDecision message}
  : HasBeenReceivedCapability vlsm.
Proof.
  econstructor; cycle 1.
  - by apply crm_computable_oracle.
  - by typeclasses eauto.
Defined.

Lemma has_been_received_messages_set_iff
  `{!ComputableReceivedMessages vlsm}
  `{EqDecision message}
  : forall (s : state vlsm) (m : message),
      m ∈ received_messages_set s
        <->
      has_been_received vlsm s m.
Proof. done. Qed.

(** *** Computable (Directly) Observed Messages

  We here derive [directly_observed_messages_set] from [ComputableSentMessages]
  and [ComputableReceivedMessages] and relate it to the [has_been_directly_observed]
  predicate.
*)

Section sec_computable_observed.

Context
  `{EqDecision message}
  `{!ComputableSentMessages vlsm}
  `{!ComputableReceivedMessages vlsm}
  .

Definition directly_observed_messages_set (s : state vlsm) : list message :=
  sent_messages_set s ++ received_messages_set s.

Lemma directly_observed_messages_set_iff :
  forall (s : state vlsm), valid_state_prop (pre_loaded_with_all_messages_vlsm vlsm) s ->
  forall (m : message),
    m ∈ directly_observed_messages_set s
      <->
    has_been_directly_observed vlsm s m.
Proof.
  by intros; split; setoid_rewrite elem_of_app;
    rewrite has_been_received_messages_set_iff, elem_of_sent_messages_set.
Qed.

Lemma com_computable_oracle :
  computable_messages_oracle vlsm directly_observed_messages_set item_sends_or_receives.
Proof.
  constructor; intros.
  - setoid_rewrite directly_observed_messages_set_iff.
    + by apply has_been_directly_observed_stepwise_props.
    + by apply initial_state_is_valid.
  - setoid_rewrite directly_observed_messages_set_iff.
    + by apply has_been_directly_observed_stepwise_props.
    + by eapply input_valid_transition_destination.
    + by eapply input_valid_transition_origin.
Qed.

End sec_computable_observed.

End sec_computable_sent_received_observed.

Lemma sent_can_emit
  [message]
  (X : VLSM message)
  `{HasBeenSentCapability message X}
  (s : state X)
  (Hs : valid_state_prop X s)
  (m : message)
  (Hsent : has_been_sent X s m) :
  can_emit X m.
Proof.
  apply valid_state_has_trace in Hs as (is & tr & Htr).
  assert (Hpre_tr : finite_valid_trace_init_to (pre_loaded_with_all_messages_vlsm X) is s tr).
  {
    by clear -Htr; destruct X;
      eapply VLSM_incl_finite_valid_trace_init_to;
      [apply vlsm_incl_pre_loaded_with_all_messages_vlsm |].
  }
  unfold can_emit.
  eapply has_been_sent_examine_one_trace, Exists_exists in Hsent
    as (item_z & Hitem_z & Hz); [| done].
  apply elem_of_list_split in Hitem_z as (pre_z & suf_z & ->).
  destruct Htr as [Htr _].
  eapply valid_trace_forget_last, input_valid_transition_to in Htr; [| done].
  cbn in Hz; rewrite Hz in Htr.
  by eexists _, _, _.
Qed.

Lemma preloaded_sent_can_emit
  [message]
  (X : VLSM message)
  `{HasBeenSentCapability message X}
  (s : state (pre_loaded_with_all_messages_vlsm X))
  (Hs : valid_state_prop (pre_loaded_with_all_messages_vlsm X) s)
  (m : message)
  (Hsent : has_been_sent X s m) :
  can_emit (pre_loaded_with_all_messages_vlsm X) m.
Proof.
  pose proof (Heq := pre_loaded_with_all_messages_vlsm_is_pre_loaded_with_True X).
  rewrite (VLSM_eq_can_emit Heq); cbn.
  eapply sent_can_emit; [| done].
  by apply (VLSM_eq_valid_state Heq).
Qed.

Lemma sent_valid
    [message]
    (X : VLSM message)
    `{HasBeenSentCapability message X}
    (s : state X)
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
    (s : state X)
    (Hs : valid_state_prop X s)
    (m : message)
    (Hreceived : has_been_received X s m) :
    valid_message_prop X m.
Proof.
  induction Hs using valid_state_prop_ind.
  - by apply has_been_received_no_inits in Hreceived.
  - apply input_valid_transition_in in Ht as Hom'.
    apply preloaded_weaken_input_valid_transition in Ht.
    erewrite has_been_received_step_update in Hreceived by done.
    by destruct Hreceived as [[= ->] |]; auto.
Qed.

Lemma directly_observed_valid
    [message]
    (X : VLSM message)
    `{HasBeenSentCapability message X}
    `{HasBeenReceivedCapability message X}
    (s : state X)
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

  We introduce [validator]s along with their respective [weight]s, the
  [A] function which maps validators to indices of component VLSMs and
  the [sender] function which maps messages to their (unique) designated
  sender (if any).

  For the equivocation fault sum to be computable, we also require that
  the number of [validator]s and the number of machines in the
  composition are both finite. See [finite_index], [finite_validator].
*)

Section sec_composite.

Context
  {message : Type}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  (Free := free_composite_vlsm IM)
  `{forall i : index, (HasBeenSentCapability (IM i))}
  `{forall i : index, (HasBeenReceivedCapability (IM i))}
  .

Section sec_stepwise_props.

Context
  [message_selectors : forall i : index, message -> transition_item (IM i) -> Prop]
  [oracles : forall i, state_message_oracle (IM i)]
  (stepwise_props : forall i, oracle_stepwise_props (message_selectors i) (oracles i))
  .

Definition composite_message_selector : message -> composite_transition_item IM -> Prop.
Proof.
  intros msg [[i li] input s output].
  apply (message_selectors i msg).
  exact {| l := li; input := input; destination := s i; output := output |}.
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
    by apply Hs.
  - (* step update property *)
    intros l s im s' om Hproto msg.
    destruct l as [i li].
    simpl.
    assert (Hsj : forall j, s j = s' j \/ j = i).
    {
      intro j.
      apply (input_valid_transition_preloaded_project_any j) in Hproto.
      by destruct Hproto as [| (lj & Hlj & _)]; [left | right; congruence].
    }
    apply input_valid_transition_preloaded_project_active in Hproto; simpl in Hproto.
    apply (oracle_step_update (stepwise_props i)) with (msg := msg) in Hproto.
    split.
    + intros [j Hj].
      destruct (Hsj j) as [Hunchanged | Hji].
      * by right; exists j; rewrite Hunchanged.
      * subst j.
        apply Hproto in Hj.
        by destruct Hj; [left | right; exists i].
    + intros [Hnow | [j Hbefore]].
      * by exists i; apply Hproto; left.
      * exists j.
        destruct (Hsj j) as [Hunchanged | ->].
        -- by rewrite <- Hunchanged.
        -- by apply Hproto; right.
Qed.

Lemma free_composite_stepwise_props :
  oracle_stepwise_props (vlsm := free_composite_vlsm IM) composite_message_selector composite_oracle.
Proof.
  split.
  - (* initial states not claim *)
    intros s Hs m [i Horacle].
    revert Horacle.
    apply (oracle_no_inits (stepwise_props i)).
    by apply Hs.
  - (* step update property *)
    intros l s im s' om Hproto msg.
    destruct l as [i li].
    simpl.
    assert (Hsj : forall j, s j = s' j \/ j = i).
    {
      intro j.
      apply (input_valid_transition_preloaded_project_any_free j) in Hproto.
      by destruct Hproto as [| (lj & Hlj & _)]; [left | right; congruence].
    }
    apply input_valid_transition_preloaded_project_active_free in Hproto; simpl in Hproto.
    apply (oracle_step_update (stepwise_props i)) with (msg := msg) in Hproto.
    split.
    + intros [j Hj].
      destruct (Hsj j) as [Hunchanged | Hji].
      * by right; exists j; rewrite Hunchanged.
      * subst j.
        apply Hproto in Hj.
        by destruct Hj; [left | right; exists i].
    + intros [Hnow | [j Hbefore]].
      * by exists i; apply Hproto; left.
      * exists j.
        destruct (Hsj j) as [Hunchanged | ->].
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
  ; [| by apply constraint_preloaded_free_incl].
  apply (VLSM_projection_finite_valid_trace_init_to
          (preloaded_component_projection IM i))
     in Hpre_tr.
  eapply prove_all_have_message_from_stepwise in Horacle
  ; [| by apply stepwise_props | by eapply finite_valid_trace_from_to_last_pstate, Hpre_tr].
  specialize (Horacle _ _ Hpre_tr); clear Hpre_tr.
  apply Exists_exists in Horacle as (item & Hitem & Hout).
  apply elem_of_map_option in Hitem as (itemX & HitemX & HitemX_pr).
  apply elem_of_list_split in HitemX as (pre & suf & Htr_pr).
  exists (finite_trace_last is pre), itemX.
  rewrite cons_middle in Htr_pr.
  eapply (input_valid_transition_to X) in Htr_pr as Ht
  ; [cbn in Ht | by apply valid_trace_forget_last in Htr; apply Htr].
  unfold pre_VLSM_projection_transition_item_project,
         composite_project_label in HitemX_pr; cbn in HitemX_pr.
  rewrite app_assoc in Htr_pr.
  case_decide as Hi; [| by congruence]; apply Some_inj in HitemX_pr
  ; subst i item tr; cbn in *.
  apply proj1, finite_valid_trace_from_to_app_split, proj2 in Htr.
  rewrite finite_trace_last_is_last in Htr.
  destruct itemX, l; cbn in *.
  by split_and!; [| exists suf | ..].
Qed.

End sec_stepwise_props.

(**
  A message [has_been_sent] for a composite state if it [has_been_sent]
  for any of its components.
*)
Definition composite_has_been_sent
  (s : composite_state IM)
  (m : message)
  : Prop
  := exists (i : index), has_been_sent (IM i) (s i) m.

(** [composite_has_been_sent] is decidable. *)
Lemma composite_has_been_sent_dec : RelDecision composite_has_been_sent.
Proof.
  intros s m.
  apply (Decision_iff (P := List.Exists (fun i => has_been_sent (IM i) (s i) m) (enum index))).
  - by rewrite Exists_finite.
  - by typeclasses eauto.
Qed.

Lemma composite_has_been_sent_stepwise_props
  (constraint : composite_label IM -> composite_state IM * option message -> Prop)
  (X := composite_vlsm IM constraint)
  : has_been_sent_stepwise_prop (vlsm := X) composite_has_been_sent.
Proof.
  unfold has_been_sent_stepwise_props.
  pose proof (composite_stepwise_props (fun i => has_been_sent_stepwise_props (IM i)))
    as [Hinits Hstep].
  split; [done |].
  by intros l; specialize (Hstep l); destruct l.
Qed.

#[export] Instance composite_HasBeenSentCapability
  (constraint : composite_label IM -> composite_state IM * option message -> Prop)
  (X := composite_vlsm IM constraint)
  : HasBeenSentCapability X :=
  Build_HasBeenSentCapability X
    composite_has_been_sent
    composite_has_been_sent_dec
    (composite_has_been_sent_stepwise_props constraint).

(** Analogous stuff for [free_composite_vlsm]. *)

Lemma free_composite_has_been_sent_stepwise_props
  (X := free_composite_vlsm IM)
  : has_been_sent_stepwise_prop (vlsm := X) composite_has_been_sent.
Proof.
  unfold has_been_sent_stepwise_props.
  pose proof (free_composite_stepwise_props (fun i => has_been_sent_stepwise_props (IM i)))
    as [Hinits Hstep].
  split; [done |].
  by intros l; specialize (Hstep l); destruct l.
Qed.

#[export] Instance free_composite_HasBeenSentCapability
  (X := free_composite_vlsm IM)
  : HasBeenSentCapability X :=
  Build_HasBeenSentCapability X
    composite_has_been_sent
    composite_has_been_sent_dec
    free_composite_has_been_sent_stepwise_props.

Lemma composite_proper_sent
  (s : state (pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM)))
  (Hs : valid_state_prop (pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM)) s)
  (m : message)
  : has_been_sent_prop (free_composite_vlsm IM) composite_has_been_sent s m.
Proof.
  specialize (proper_sent (free_composite_vlsm IM)) as Hproper_sent.
  by apply Hproper_sent.
Qed.

Section sec_composite_has_been_received.

(**
  A message [has_been_received] for a composite state
  if it [has_been_received] for any of its components.
*)
Definition composite_has_been_received
  (s : composite_state IM)
  (m : message)
  : Prop
  := exists (i : index), has_been_received (IM i) (s i) m.

(** [composite_has_been_received] is decidable. *)
Lemma composite_has_been_received_dec : RelDecision composite_has_been_received.
Proof.
  intros s m.
  apply (Decision_iff (P := List.Exists (fun i => has_been_received (IM i) (s i) m) (enum index))).
  - by rewrite Exists_finite.
  - by typeclasses eauto.
Qed.

Lemma composite_has_been_received_stepwise_props
  (constraint : composite_label IM -> composite_state IM * option message -> Prop)
  (X := composite_vlsm IM constraint)
  : has_been_received_stepwise_prop (vlsm := X) composite_has_been_received.
Proof.
  unfold has_been_received_stepwise_props.
  pose proof (composite_stepwise_props (fun i => has_been_received_stepwise_props (IM i)))
    as [Hinits Hstep].
  split; [done |].
  by intros l; specialize (Hstep l); destruct l.
Qed.

#[export] Instance composite_HasBeenReceivedCapability
  (constraint : composite_label IM -> composite_state IM * option message -> Prop)
  (X := composite_vlsm IM constraint)
  : HasBeenReceivedCapability X :=
  Build_HasBeenReceivedCapability X
    composite_has_been_received
    composite_has_been_received_dec
    (composite_has_been_received_stepwise_props constraint).

#[export] Instance composite_HasBeenDirectlyObservedCapability
  (constraint : composite_label IM -> composite_state IM * option message -> Prop)
  (X := composite_vlsm IM constraint)
  : HasBeenDirectlyObservedCapability X :=
  HasBeenDirectlyObservedCapability_from_sent_received X.

Lemma free_composite_has_been_received_stepwise_props
  (X := free_composite_vlsm IM)
  : has_been_received_stepwise_prop (vlsm := X) composite_has_been_received.
Proof.
  unfold has_been_received_stepwise_props.
  pose proof (free_composite_stepwise_props (fun i => has_been_received_stepwise_props (IM i)))
    as [Hinits Hstep].
  split; [done |].
  by intros l; specialize (Hstep l); destruct l.
Qed.

#[export] Instance free_composite_HasBeenReceivedCapability
  (X := free_composite_vlsm IM)
  : HasBeenReceivedCapability X :=
  Build_HasBeenReceivedCapability X
    composite_has_been_received
    composite_has_been_received_dec
    free_composite_has_been_received_stepwise_props.

#[export] Instance free_composite_HasBeenDirectlyObservedCapability
  (X := free_composite_vlsm IM)
  : HasBeenDirectlyObservedCapability X :=
  HasBeenDirectlyObservedCapability_from_sent_received X.

Lemma preloaded_composite_has_been_received_stepwise_props
  (constraint : composite_label IM -> composite_state IM * option message -> Prop)
  (seed : message -> Prop)
  (X := pre_loaded_vlsm (composite_vlsm IM constraint) seed)
  : has_been_received_stepwise_prop (vlsm := X) composite_has_been_received.
Proof.
  unfold has_been_received_stepwise_props.
  specialize (composite_stepwise_props (fun i => has_been_received_stepwise_props (IM i)))
    as [Hinits Hstep].
  split; [done |].
  by intros l; specialize (Hstep l); destruct l.
Qed.

Definition preloaded_composite_HasBeenReceivedCapability
  (constraint : composite_label IM -> composite_state IM * option message -> Prop)
  (seed : message -> Prop)
  (X := pre_loaded_vlsm (composite_vlsm IM constraint) seed)
  : HasBeenReceivedCapability X :=
  Build_HasBeenReceivedCapability X
    composite_has_been_received
    composite_has_been_received_dec
    (preloaded_composite_has_been_received_stepwise_props constraint seed).

End sec_composite_has_been_received.

(**
  A message [has_been_directly_observed] in a composite state if it
  [has_been_directly_observed] in any of its components.
*)
Definition composite_has_been_directly_observed
  (s : composite_state IM)
  (m : message)
  : Prop
  := exists (i : index), has_been_directly_observed (IM i) (s i) m.

(** [composite_has_been_directly_observed] is decidable. *)
Lemma composite_has_been_directly_observed_dec : RelDecision composite_has_been_directly_observed.
Proof.
  intros s m.
  apply (Decision_iff
    (P := List.Exists (fun i => has_been_directly_observed (IM i) (s i) m) (enum index))).
  - by rewrite Exists_finite.
  - by typeclasses eauto.
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

Lemma free_composite_has_been_directly_observed_stepwise_props :
  oracle_stepwise_props (vlsm := free_composite_vlsm IM) item_sends_or_receives
    composite_has_been_directly_observed.
Proof.
  destruct (free_composite_stepwise_props (fun i =>
    has_been_directly_observed_stepwise_props (IM i))) as [Hinits Hstep].
  split; [done |].
  by intros l; specialize (Hstep l); destruct l.
Qed.

Definition composite_HasBeenDirectlyObservedCapability_from_stepwise
  (constraint : composite_label IM -> composite_state IM * option message -> Prop)
  (X := composite_vlsm IM constraint)
  : HasBeenDirectlyObservedCapability X.
Proof.
  exists composite_has_been_directly_observed.
  - by apply composite_has_been_directly_observed_dec.
  - by apply (composite_has_been_directly_observed_stepwise_props constraint).
Defined.

Context
      {validator : Type}
      `{finite.Finite validator}
      {measurable_V : Measurable validator}
      (threshold : R)
      `{FinSet validator Cv}
      `{!ReachableThreshold validator Cv threshold}
      (A : validator -> index)
      (sender : message -> option validator)
      .

Definition node_signed_message (node_idx : index) (m : message) : Prop :=
  option_map A (sender m) = Some node_idx.

(**
  Definitions for safety and nontriviality of the [sender] function.
  Safety means that if we designate a validator as the sender
  of a certain message, then it is impossible for other components
  to produce that message

  Weak/strong nontriviality say that each validator should
  be designated sender for at least one/all its valid
  messages.
*)
Definition sender_safety_prop : Prop :=
  forall
  (m : message)
  (v : validator)
  (Hsender : sender m = Some v),
  forall (j : index)
         (Hdif : j <> A v),
         ~ can_emit (pre_loaded_with_all_messages_vlsm (IM j)) m.

(**
  An alternative, possibly friendlier, formulation. Note that it is
  slightly weaker, in that it does not require that the sender
  is able to send the message.
*)

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

(**
  The [channel_authentication_prop]erty requires that any sent message must
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
  forall i m, ~ initial_message_prop (IM i) m.

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
  ; [by contradict Hmi; apply no_initial_messages_in_IM |].
  apply (VLSM_incl_input_valid_transition (constraint_preloaded_free_incl IM _)) in Ht.
  apply pre_loaded_with_all_messages_projection_input_valid_transition_eq
    with (j := i) in Ht; [| done]; cbn in Ht.
  specialize (can_emit_signed i m).
  spec can_emit_signed; [by eexists _, _, _ |].
  unfold channel_authenticated_message in can_emit_signed.
  destruct (sender m) as [v |] eqn: Hsender; [| by inversion can_emit_signed].
  apply Some_inj in can_emit_signed.
  by exists v; subst; unfold can_emit; eauto.
Qed.

Lemma free_composite_no_initial_valid_messages_emitted_by_sender
  (can_emit_signed : channel_authentication_prop)
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop)
  (X := free_composite_vlsm IM)
  : forall (m : message), valid_message_prop X m ->
    exists v, sender m = Some v /\
      can_emit (pre_loaded_with_all_messages_vlsm (IM (A v))) m.
Proof.
  intro m.
  rewrite emitted_messages_are_valid_iff.
  intros [[i [[mi Hmi] _]] | [(s, om) [(i, l) [s' Ht]]]]
  ; [by contradict Hmi; apply no_initial_messages_in_IM |].
  apply (VLSM_incl_input_valid_transition (preloaded_free_incl IM)) in Ht.
  apply pre_loaded_with_all_messages_projection_input_valid_transition_eq
    with (j := i) in Ht; [| done]; cbn in Ht.
  specialize (can_emit_signed i m).
  spec can_emit_signed; [by eexists _, _, _ |].
  unfold channel_authenticated_message in can_emit_signed.
  destruct (sender m) as [v |] eqn: Hsender; [| by inversion can_emit_signed].
  apply Some_inj in can_emit_signed.
  by exists v; subst; unfold can_emit; eauto.
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
  - by intros (v & -> & _); congruence.
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
  apply input_valid_transition_preloaded_project_active_free in Ht as Hti.
  by rewrite Houtput in Hti; apply can_emit_signed; rewrite HAv; eexists _, _, _.
Qed.

Lemma has_been_sent_iff_by_sender
  (Hsender_safety : sender_safety_alt_prop) [is s tr]
  (Htr : finite_valid_trace_init_to
    (pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM)) is s tr)
  [m v] (Hsender : sender m = Some v) :
  composite_has_been_sent s m <-> has_been_sent (IM (A v)) (s (A v)) m.
Proof.
  split; [| by exists (A v)].
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
    by revert Htr_pr; apply valid_trace_last_pstate.
Qed.

Lemma no_additional_equivocations_constraint_dec
  : RelDecision (no_additional_equivocations_constraint Free).
Proof.
  intros l (s, om).
  destruct om; [| by left].
  by apply no_additional_equivocations_dec.
Qed.

(**
  We say that a validator <v> (with associated component <i>) is equivocating wrt.
  to another component <j>, if there exists a message which [has_been_received] by
  <j> but [has_not_been_sent] by <i>.
*)

Definition equivocating_wrt
  (v : validator)
  (j : index)
  (sv : state (IM (A v)))
  (sj : state (IM j))
  (i := A v)
  : Prop
  :=
  exists (m : message),
  sender(m) = Some v /\
  has_not_been_sent  (IM i) sv m /\
  has_been_received  (IM j) sj m.

(** We can now decide whether a validator is equivocating in a certain state. *)

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
  intros (j & m & Hsender & Hnbs & Hrcv).
  by revert Hrcv; apply has_been_received_stepwise_props, Hs.
Qed.

(**
  For the equivocation sum fault to be computable, we require that
  our is_equivocating property is decidable. The current implementation
  refers to [is_equivocating_statewise], but this might change
  in the future.
*)

Definition equivocation_dec_statewise
   (Hdec : RelDecision is_equivocating_statewise)
    : BasicEquivocation (composite_state IM) validator Cv threshold
  :=
  {|
    state_validators := fun _ => list_to_set (enum validator);
    is_equivocating := is_equivocating_statewise;
    is_equivocating_dec := Hdec
  |}.

Definition equivocation_fault_constraint
  (Dec : BasicEquivocation (composite_state IM) validator Cv threshold)
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
      (fun i => has_been_sent_stepwise_props (IM i))
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
      (fun i => has_been_received_stepwise_props (IM i))
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
    [| by apply constraint_preloaded_free_incl].
  eapply (VLSM_projection_input_valid_transition (preloaded_component_projection IM i))
    in Ht; [by eexists _, _ |].
  by apply (composite_project_label_eq IM).
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

Lemma preloaded_messages_sent_from_component_of_valid_state_are_valid_free
  (seed : message -> Prop)
  (X := pre_loaded_vlsm (free_composite_vlsm IM) seed)
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

Lemma preloaded_messages_received_from_component_of_valid_state_are_valid_free
  (seed : message -> Prop)
  (X := pre_loaded_vlsm (free_composite_vlsm IM) seed)
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
    by apply pre_loaded_vlsm_incl_pre_loaded_with_all_messages.
Qed.

Lemma preloaded_free_composite_directly_observed_valid
  (seed : message -> Prop)
  (X := pre_loaded_vlsm (free_composite_vlsm IM) seed)
  (s : composite_state IM)
  (Hs : valid_state_prop X s)
  (m : message)
  (Hobserved : composite_has_been_directly_observed s m)
  : valid_message_prop X m.
Proof.
  destruct Hobserved as [i Hobserved].
  apply (has_been_directly_observed_sent_received_iff (IM i)) in Hobserved.
  - destruct Hobserved as [Hreceived | Hsent].
    + by eapply preloaded_messages_received_from_component_of_valid_state_are_valid_free.
    + by eapply preloaded_messages_sent_from_component_of_valid_state_are_valid_free.
  - eapply valid_state_project_preloaded_to_preloaded_free.
    eapply VLSM_incl_valid_state; [| done].
    by apply pre_loaded_vlsm_incl_pre_loaded_with_all_messages.
Qed.

End sec_composite.

Lemma composite_has_been_directly_observed_sent_received_iff
  {message}
  `{EqDecision index}
  (IM : index -> VLSM message)
  `{forall i : index, HasBeenSentCapability (IM i)}
  `{forall i : index, HasBeenReceivedCapability (IM i)}
  (s : composite_state IM)
  (m : message)
  : composite_has_been_directly_observed IM s m <->
    composite_has_been_sent IM s m \/ composite_has_been_received IM s m.
Proof.
  split.
  - by intros [i [Hs | Hr]]; [left | right]; exists i.
  - by intros [[i Hs] | [i Hr]]; exists i; [left | right].
Qed.

Lemma composite_has_been_directly_observed_free_iff
  {message}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  `{forall i : index, HasBeenSentCapability (IM i)}
  `{forall i : index, HasBeenReceivedCapability (IM i)}
  (s : state (free_composite_vlsm IM))
  (m : message)
  : composite_has_been_directly_observed IM s m
      <->
    has_been_directly_observed (free_composite_vlsm IM) s m.
Proof.
  unfold has_been_directly_observed; cbn; unfold has_been_directly_observed_from_sent_received; cbn.
  by apply composite_has_been_directly_observed_sent_received_iff.
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
  (s : state (IM i))
  (Hs : valid_state_prop (pre_loaded_with_all_messages_vlsm (IM i)) s)
  (m : message)
  : composite_has_been_directly_observed IM (lift_to_composite_state' IM i s) m
      <->
    has_been_directly_observed (IM i) s m.
Proof.
  pose (free_composite_vlsm IM) as Free.
  assert (Hlift_s :
    valid_state_prop (pre_loaded_with_all_messages_vlsm Free) (lift_to_composite_state' IM i s)).
  { revert Hs.  apply valid_state_preloaded_composite_free_lift. }
  split; intros Hobs.
  - apply (proper_directly_observed (IM i)); [done |].
    intros is tr Htr.
    apply composite_has_been_directly_observed_free_iff, proper_directly_observed in Hobs
    ; [| done].
    apply (VLSM_embedding_finite_valid_trace_init_to
      (lift_to_composite_preloaded_VLSM_embedding IM i)) in Htr as Hpre_tr.
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
    apply has_been_directly_observed_consistency; [by typeclasses eauto | done |].
    apply proper_directly_observed in Hobs ; [| done].
    apply has_been_directly_observed_consistency in Hobs; [| by typeclasses eauto | done].
    destruct Hobs as [is [tr [Htr Hobs]]].
    apply (VLSM_embedding_finite_valid_trace_init_to
      (lift_to_composite_preloaded_VLSM_embedding IM i)) in Htr as Hpre_tr.
    eexists. eexists. exists Hpre_tr.
    apply Exists_exists.
    apply Exists_exists in Hobs.
    destruct Hobs as [item [Hitem Hx]].
    exists (lift_to_composite_transition_item' IM i item).
    split; [| by destruct item].
    apply elem_of_list_fmap.
    by exists item.
Qed.

Section sec_CompositeComputableMessages.

Context
  `{EqDecision message}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  (indexed_oracle_set : forall i, state (IM i) -> set message)
  (indexed_message_selector : forall i, message -> transition_item (IM i) -> Prop)
  (Free := free_composite_vlsm IM)
  .

Definition composite_oracle_set (s : composite_state IM) : set message :=
  concat (map (fun i => indexed_oracle_set i (s i)) (enum index)).

Lemma elem_of_composite_oracle_set :
  forall (s : composite_state IM) (m : message),
    m ∈ composite_oracle_set s <-> exists i, m ∈ indexed_oracle_set i (s i).
Proof.
  intros; split; setoid_rewrite elem_of_list_In; setoid_rewrite in_concat;
    setoid_rewrite in_map_iff.
  - by intros (? & (? & <- & _) & ?); eexists.
  - by intros []; repeat esplit; [apply elem_of_list_In, elem_of_enum |].
Qed.

Lemma composite_computable_messages_oracle
   (Hcmos : forall i,
      computable_messages_oracle (IM i)
        (indexed_oracle_set i) (indexed_message_selector i))
  : computable_messages_oracle Free composite_oracle_set
      (composite_message_selector IM (message_selectors := indexed_message_selector)).
Proof.
  by constructor; intros
  ; setoid_rewrite elem_of_composite_oracle_set
  ; apply free_composite_stepwise_props
     with (message_selectors := indexed_message_selector)
          (oracles := fun (i : index) (s : state (IM i)) (m : message) =>
            m ∈ indexed_oracle_set i s)
  ; [| done | | done]; intro; apply Hcmos.
Qed.

End sec_CompositeComputableMessages.

Section sec_composite_computable_sent_received_observed.

Context
  `{EqDecision message}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  `{forall i, ComputableSentMessages (IM i)}
  `{forall i, ComputableReceivedMessages (IM i)}
  .

Definition composite_received_messages_set : composite_state IM -> list message :=
  composite_oracle_set IM (fun i => received_messages_set).

Definition composite_sent_messages_set : composite_state IM -> list message :=
  composite_oracle_set IM (fun i => sent_messages_set).

Definition composite_observed_messages_set (s : composite_state IM) : list message :=
  composite_sent_messages_set s ++ composite_received_messages_set s.

Lemma elem_of_composite_received_messages_set :
  forall (s : composite_state IM) (m : message),
    composite_has_been_received IM s m
      <->
    m ∈ composite_received_messages_set s.
Proof.
  setoid_rewrite elem_of_composite_oracle_set.
  by split; intros [i Hi]; exists i; apply has_been_received_messages_set_iff.
Qed.

Lemma elem_of_composite_sent_messages_set :
  forall (s : composite_state IM) (m : message),
    composite_has_been_sent IM s m
      <->
    m ∈ composite_sent_messages_set s.
Proof.
  setoid_rewrite elem_of_composite_oracle_set.
  by split; intros [i Hi]; exists i; apply elem_of_sent_messages_set.
Qed.

Lemma elem_of_composite_observed_messages_set :
  forall (s : composite_state IM) (m : message),
    composite_has_been_directly_observed IM s m
      <->
    m ∈ composite_observed_messages_set s.
Proof.
  intros s m.
  unfold composite_observed_messages_set.
  by rewrite elem_of_app, composite_has_been_directly_observed_sent_received_iff,
     elem_of_composite_sent_messages_set, elem_of_composite_received_messages_set.
Qed.

End sec_composite_computable_sent_received_observed.

Section sec_cannot_resend_message.

Context
  {message : Type}
  `{EqDecision message}
  (X : VLSM message)
  (PreX := pre_loaded_with_all_messages_vlsm X)
  `{HasBeenSentCapability message X}
  `{HasBeenReceivedCapability message X}
  .

Definition state_received_not_sent (s : state X) (m : message) : Prop :=
  has_been_received X s m /\ ~ has_been_sent X s m.

Lemma state_received_not_sent_trace_iff
  (m : message)
  (s is : state (PreX))
  (tr : list transition_item)
  (Htr : finite_valid_trace_init_to PreX is s tr)
  : state_received_not_sent s m <-> trace_received_not_sent_before_or_after tr m.
Proof.
  assert (Hs : valid_state_prop PreX s)
    by (apply proj1, valid_trace_last_pstate in Htr; done).
  split; intros [Hbrm Hnbsm].
  - apply proper_received in Hbrm; [| done].
    specialize (Hbrm is tr Htr).
    split; [done |].
    intro Hbsm. elim Hnbsm.
    apply proper_sent; [done |].
    by apply has_been_sent_consistency; [.. | exists is, tr, Htr].
  - split.
    + apply proper_received; [done |].
      by apply has_been_received_consistency; [.. | exists is, tr, Htr].
    + intro Hbsm. elim Hnbsm.
      by apply proper_sent in Hbsm; [eapply Hbsm |].
Qed.

Definition state_received_not_sent_invariant
  (s : state X)
  (P : message -> Prop)
  : Prop
  := forall m, state_received_not_sent s m -> P m.

Lemma state_received_not_sent_invariant_trace_iff
  (P : message -> Prop)
  (s is : state (PreX))
  (tr : list transition_item)
  (Htr : finite_valid_trace_init_to PreX is s tr)
  : state_received_not_sent_invariant s P <->
    trace_received_not_sent_before_or_after_invariant tr P.
Proof.
  by split; intros Hinv m Hm
  ; apply Hinv
  ; apply (state_received_not_sent_trace_iff m s is tr Htr).
Qed.

(** A sent message cannot have been previously sent or received. *)
Definition cannot_resend_message_stepwise_prop : Prop :=
  forall l s oim s' m,
    input_valid_transition (pre_loaded_with_all_messages_vlsm X) l (s, oim) (s', Some m) ->
    ~ has_been_sent X s m /\ ~ has_been_received X s' m.

Lemma cannot_resend_received_message_in_future
  (Hno_resend : cannot_resend_message_stepwise_prop)
  (s1 s2 : state (PreX))
  (Hfuture : in_futures PreX s1 s2)
  : forall m : message,
    state_received_not_sent s1 m -> state_received_not_sent s2 m.
Proof.
  intros m Hm.
  destruct Hfuture as [tr2 Htr2].
  induction Htr2; [done |].
  apply IHHtr2; clear IHHtr2.
  pose proof (Hrupd := has_been_received_step_update Ht m).
  pose proof (Hmupd := has_been_sent_step_update Ht m).
  destruct Hm as [Hr Hs].
  split; [by itauto |].
  intros [-> |]%Hmupd; [| by apply Hs].
  by apply Hno_resend in Ht; itauto.
Qed.

Context
  (Hno_resend : cannot_resend_message_stepwise_prop).

Lemma input_valid_transition_received_not_resent l s m s' om'
  (Ht : input_valid_transition (pre_loaded_with_all_messages_vlsm X) l (s, Some m) (s', om'))
  : om' <> Some m.
Proof.
  destruct om' as [m' |]; [| by congruence].
  intro Heq. inversion Heq. subst m'. clear Heq.
  destruct (Hno_resend _ _ _ _ _ Ht) as [_ Hnbr_m].
  elim Hnbr_m. clear Hnbr_m.
  apply exists_right_finite_trace_from in Ht.
  destruct Ht as [is [tr [Htr Hs]]].
  apply proj1 in Htr as Hlst. apply finite_valid_trace_from_to_last_pstate in Hlst.
  apply proper_received; [done |].
  apply has_been_received_consistency; [done | done |].
  exists _, _, Htr.
  by apply Exists_app; right; apply Exists_cons; left.
Qed.

Lemma lift_preloaded_trace_to_seeded
  (P : message -> Prop)
  (tr : list transition_item)
  (Htrm : trace_received_not_sent_before_or_after_invariant tr P)
  (is : state (PreX))
  (Htr : finite_valid_trace PreX is tr)
  : finite_valid_trace (pre_loaded_vlsm X P) is tr.
Proof.
  unfold trace_received_not_sent_before_or_after_invariant in Htrm.
  split; [| by apply Htr].
  induction Htr using finite_valid_trace_rev_ind; intros.
  - rapply @finite_valid_trace_from_empty.
    by apply initial_state_is_valid.
  - assert (trace_received_not_sent_before_or_after_invariant tr P) as Htrm'.
    { intros m [Hrecv Hsend]. apply (Htrm m); clear Htrm.
      split; [by apply Exists_app; left |].
      contradict Hsend.
      unfold trace_has_message in Hsend.
      rewrite Exists_app, Exists_cons, Exists_nil in Hsend.
      simpl in Hsend.
      cut (oom <> Some m); [by itauto |].
      intros ->.
      cut (has_been_received X sf m); [by apply (Hno_resend _ _ _ _ _ Hx) |].
      apply (has_been_received_step_update Hx); right.
      erewrite oracle_partial_trace_update.
      - by left.
      - by apply has_been_received_stepwise_props.
      - by apply valid_trace_add_default_last; apply Htr.
    }
    specialize (IHHtr Htrm').
    apply (extend_right_finite_trace_from _ IHHtr).
    repeat split; try apply Hx;
    [by apply finite_valid_trace_last_pstate |].
    destruct iom as [m |]; [| by apply option_valid_message_None].
    (*
      If m was sent during tr, it is valid because it was
      produced in a valid (by IHHtr) trace.
      If m was not sent during tr,
    *)
    assert (Decision (trace_has_message (field_selector output) m tr)) as [Hsent | Hnot_sent].
    apply (@Exists_dec _). intros. apply decide_eq.
    + by eapply valid_trace_output_is_valid.
    + apply initial_message_is_valid.
      right. apply Htrm.
      split.
      * by apply Exists_app; right; apply Exists_cons; left.
      * intro Hsent; destruct Hnot_sent.
        unfold trace_has_message in Hsent.
        rewrite Exists_app, Exists_cons, Exists_nil in Hsent.
        destruct Hsent as [Hsent | [[= ->] | []]]; [done | exfalso].
        apply Hno_resend in Hx as Hx'.
        apply (proj2 Hx'); clear Hx'.
        by rewrite (has_been_received_step_update Hx); left.
Qed.

Lemma lift_preloaded_state_to_seeded
  (P : message -> Prop)
  (s : state X)
  (Hequiv_s : state_received_not_sent_invariant s P)
  (Hs : valid_state_prop PreX s)
  : valid_state_prop (pre_loaded_vlsm X P) s.
Proof.
  apply valid_state_has_trace in Hs as Htr.
  destruct Htr as [is [tr Htr]].
  specialize (lift_preloaded_trace_to_seeded P tr) as Hlift.
  spec Hlift; [by revert Hequiv_s; apply state_received_not_sent_invariant_trace_iff with is |].
  specialize (Hlift _ (valid_trace_forget_last Htr)).
  apply proj1 in Hlift.
  apply finite_valid_trace_last_pstate in Hlift.
  by rewrite <- (valid_trace_get_last Htr).
Qed.

Lemma lift_generated_to_seeded
  (P : message -> Prop)
  (s : state X)
  (Hequiv_s : state_received_not_sent_invariant s P)
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

End sec_cannot_resend_message.

Section sec_has_been_sent_irrelevance.

(**
  Since we have several ways of obtaining the [has_been_sent] property,
  we sometimes need to show that they are equivalent.
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
  (s : state (pre_loaded_with_all_messages_vlsm X))
  (m : message)
  (Hs : valid_state_prop (pre_loaded_with_all_messages_vlsm X) s)
  : has_been_sent1 s m -> has_been_sent2 s m.
Proof.
  intro H.
  apply proper_sent in H; [| done].
  by apply proper_sent.
Qed.

End sec_has_been_sent_irrelevance.

Section sec_all_traces_to_valid_state_are_valid.

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
  apply has_been_received_consistency; [by typeclasses eauto | done |].
  by exists is, tr, Htr.
Qed.

End sec_all_traces_to_valid_state_are_valid.

Section sec_has_been_received_in_state.

Context
  {message : Type}
  (X : VLSM message)
  `{HasBeenReceivedCapability message X}
.

Lemma has_been_received_in_state s1 m :
  valid_state_prop X s1 ->
  has_been_received X s1 m ->
  exists (s0 : state X) (item : transition_item) (tr : list transition_item),
    input item = Some m /\
    finite_valid_trace_from_to X s0 s1 (item :: tr).
Proof.
  intros Hpsp Hhbr.
  pose proof (Hetr := valid_state_has_trace _ _ Hpsp).
  destruct Hetr as [ist [tr Hetr]].
  apply proper_received in Hhbr; [| by apply pre_loaded_with_all_messages_valid_state_prop, Hpsp].
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
  destruct tritem eqn: Heqtritem.
  simpl in Hintritem. subst input.
  eexists. eexists. eexists.
  by split; [| apply  Htr2].
Qed.

Lemma has_been_received_in_state_preloaded s1 m :
  valid_state_prop (pre_loaded_with_all_messages_vlsm X) s1 ->
  has_been_received X s1 m ->
  exists (s0 : state (pre_loaded_with_all_messages_vlsm X))
    (item : transition_item) (tr : list transition_item),
    input item = Some m /\
    finite_valid_trace_from_to (pre_loaded_with_all_messages_vlsm X) s0 s1 (item :: tr).
Proof.
  intros Hpsp Hhbr.
  pose proof (Hetr := valid_state_has_trace _ _ Hpsp).
  destruct Hetr as [ist [tr Hetr]].
  apply proper_received in Hhbr; [| by apply Hpsp].
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
  destruct tritem eqn: Heqtritem.
  simpl in Hintritem. subst input.
  eexists. eexists. eexists.
  by split; [| apply  Htr2].
Qed.

End sec_has_been_received_in_state.
