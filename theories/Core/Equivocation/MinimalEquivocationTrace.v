From stdpp Require Import prelude finite.
From Coq Require Import Reals.
From VLSM.Lib Require Import Preamble ListExtras StdppListSet StdppExtras NatExtras.
From VLSM.Lib Require Import Measurable EquationsExtras.
From VLSM.Core Require Import VLSM Composition.
From VLSM.Core Require Import Equivocation MessageDependencies TraceableVLSM.
From VLSM.Core Require Import AnnotatedVLSM MsgDepLimitedEquivocation.

(** * Core: Minimally Equivocating Traces

  In this module, we define a [choice_function] and [minimal_equivocation_choice],
  guaranteeing that the transition it chooses does not decrease the set of
  validators which are equivocating according to the [msg_dep_is_globally_equivocating]
  relation (see [minimal_equivocation_choice_monotone]).

  We then show that the trace determined by [state_to_trace] using this choice
  function yields a minimally equivocating constrained trace reaching that state
  (see [state_to_minimal_equivocation_trace_equivocation_monotonic]).
*)

Section sec_minimal_equivocation_choice.

(** ** The minimal equivocation choice function *)

Context
  `{EqDecision message}
  `{finite.Finite index}
  `{Inhabited index}
  (IM : index -> VLSM message)
  `{forall i, ComputableSentMessages (IM i)}
  `{forall i, ComputableReceivedMessages (IM i)}
  `{FullMessageDependencies message Cm message_dependencies full_message_dependencies}
  `{forall i, MessageDependencies (IM i) message_dependencies}
  (state_destructor : forall i, state (IM i) -> set (transition_item (IM i) * state (IM i)))
  (state_size : forall i, state (IM i) -> nat)
  `{forall i, TraceableVLSM (IM i) (state_destructor i) (state_size i)}
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  `(sender : message -> option validator)
  `{!Irreflexive (tc_composite_observed_before_send IM message_dependencies)}
  (A : validator -> index)
  (Hchannel : channel_authentication_prop IM A sender)
  (Free := free_composite_vlsm IM)
  (RFree := pre_loaded_with_all_messages_vlsm Free)
  .

(**
  The <<n>>th (composite) transition from the given list is not sending
  any message.
*)
Inductive CompositeNthNotSend
  (transitions : set (composite_transition_item IM * composite_state IM)) (n : nat) : Prop :=
| composite_nth_not_send :
    forall item s, transitions !! n = Some (item, s) -> output item = None ->
      CompositeNthNotSend transitions n.

Lemma not_CompositeNthNotSend_is_sent :
  forall (ts : set (composite_transition_item IM * composite_state IM)) (n : nat),
    ~ CompositeNthNotSend ts n ->
    forall item s, ts !! n = Some (item, s) -> exists m, output item = Some m.
Proof.
  intros * Hnsend **.
  destruct (output item) eqn: Houtput; [by eexists |].
  by contradict Hnsend; econstructor.
Qed.

(**
  The <<n>>th transition reaching <<s'>> from component <<i>> is not sending
  any message.
*)
Definition composite_latest_not_send_prop (s' : composite_state IM) (i : index) (n : nat) : Prop :=
  CompositeNthNotSend (composite_state_destructor IM state_destructor s' i) n.

#[local] Instance composite_latest_not_send_dec s' :
  RelDecision (composite_latest_not_send_prop s').
Proof.
  intros i n.
  destruct (composite_state_destructor IM state_destructor s' i !! n) as [[item s] |] eqn: Hdestruct.
  - destruct (output item) as [m |] eqn: Hinput; [| by left; econstructor].
    right; inversion 1 as [_item _s].
    replace (_ !! n) with (Some (_item, _s)) in Hdestruct.
    by inversion Hdestruct; congruence.
  - by right; inversion 1; cbv in *; congruence.
Qed.

(**
  The <<n>>th (composite) transition from the given list is sending a message
  which hasn't been previously observed.
*)
Inductive CompositeNthSentNotObserved
  (transitions : set (composite_transition_item IM * composite_state IM)) (n : nat) : Prop :=
| composite_nth_sent_not_observed :
    forall item s,
      transitions !! n = Some (item, s) ->
      forall m, output item = Some m ->
      ~ CompositeHasBeenObserved IM message_dependencies s m ->
      CompositeNthSentNotObserved transitions n.

Lemma not_CompositeNthSentNotObserved_is_observed :
  forall (ts : set (composite_transition_item IM * composite_state IM)) (n : nat),
    ~ CompositeNthSentNotObserved ts n ->
    forall item s,
      ts !! n = Some (item, s) ->
      forall m, output item = Some m ->
      CompositeHasBeenObserved IM message_dependencies s m.
Proof.
  intros * Hnobs **.
  destruct (decide (CompositeHasBeenObserved IM message_dependencies s m)); [done |].
  by contradict Hnobs; econstructor.
Qed.

(**
  The <<n>>th transition reaching <<s'>> from component <<i>> is  sending a
  message which hasn't been previously observed.
*)
Definition composite_latest_sent_not_observed_prop
  (s' : composite_state IM) (i : index) (n : nat) : Prop :=
  CompositeNthSentNotObserved (composite_state_destructor IM state_destructor s' i) n.

#[local] Instance composite_latest_sent_not_observed_dec s' :
  RelDecision (composite_latest_sent_not_observed_prop s').
Proof.
  intros i n.
  destruct (composite_state_destructor IM state_destructor s' i !! n)
    as [[item s] |] eqn: Hdestruct;
    [| by right; inversion 1; cbv in *; congruence].
  destruct (output item) as [m |] eqn: Houtput.
  - destruct (decide (CompositeHasBeenObserved IM message_dependencies s m));
      [| by left; econstructor].
    right; inversion 1 as [_item _s].
    replace (_ !! n) with (Some (_item, _s)) in Hdestruct.
    by inversion Hdestruct; congruence.
  - right; inversion 1 as [_item _s].
    replace (_ !! n) with (Some (_item, _s)) in Hdestruct.
    by inversion Hdestruct; congruence.
Qed.

(**
  The first transition reaching <<s'>> from component <<i>> is sending a message
  which has been previously observed from the <<j>>th component of the state.
*)
Record CompositeLatestSentObservedIn
  (s' : composite_state IM)  (i : index)  (j : index)
  (s : composite_state IM) (item : composite_transition_item IM) (m : message)
  : Prop :=
{
  clsoi_destructor :
    head (composite_state_destructor IM state_destructor s' i) = Some (item, s);
  clsoi_output : output item = Some m;
  clsoi_observed : HasBeenObserved (IM j) message_dependencies (s j) m;
}.

(**
  Characterizes the fact that:

  - the first transition reaching <<s'>> from component <<i>> is sending a
    message <<m_i>>,
  - the first transition reaching <<s'>> from component <<j>> is sending a
    message <<m_j>>, and
  - <<m_i>> and <<m_j>> are in the [tc_composite_observed_before_send] relation.
*)
Record LatestCompositeObservedBeforeSend
  (s' : composite_state IM) (i : index) (j : index)
  (s_i : composite_state IM) (item_i : composite_transition_item IM) (m_i : message)
  (s_j : composite_state IM) (item_j : composite_transition_item IM) (m_j : message)
  : Prop :=
{
  lcobs_destruct_i : head (composite_state_destructor IM state_destructor s' i) = Some (item_i, s_i);
  lcobs_output_i : output item_i = Some m_i;
  lcobs_destruct_j : head (composite_state_destructor IM state_destructor s' j) = Some (item_j, s_j);
  lcobs_output_j : output item_j = Some m_j;
  lcobs_rel : tc_composite_observed_before_send IM message_dependencies m_i m_j;
}.

(**
  [LatestCompositeObservedBeforeSend] as a binary relation on indices of
  components for a given composite state.
*)
Definition latest_composite_observed_before_send
  (s' : composite_state IM) (i j : index) : Prop :=
  exists s_i item_i m_i s_j item_j m_j,
    LatestCompositeObservedBeforeSend s' i j s_i item_i m_i s_j item_j m_j.

#[local] Instance latest_composite_observed_before_send_trans s' :
  Transitive (latest_composite_observed_before_send s').
Proof.
  intros i j k
    (s_i & item_i & m_i & s_j & item_j & m_j
      & [Hdestruct_i Houtput_i Hdestruct_j Houtput_j Hij])
    (_s_j & _item_j & _m_j & s_k & item_k & m_k
      & [H_destruct_j H_output_j Hdestruct_k Houtput_k Hjk]).
  eexists _, _, _, _, _, _; constructor; [done.. |].
  etransitivity; [done |].
  rewrite Hdestruct_j in H_destruct_j; inversion H_destruct_j;
    subst _s_j _item_j; clear H_destruct_j.
  by rewrite Houtput_j in H_output_j; inversion H_output_j; subst.
Qed.

#[local] Instance latest_composite_observed_before_send_irreflexive s' :
  Irreflexive (latest_composite_observed_before_send s').
Proof.
  intros a (s_i & item_i & m_i & s_j & item_j & m_j & [Hdestruct Houtput H_destruct H_output Hrel]).
  rewrite Hdestruct in H_destruct; inversion H_destruct; subst; clear H_destruct.
  rewrite Houtput in H_output; inversion H_output; subst.
  by eapply irreflexivity.
Qed.

Lemma composite_latest_sent_observed_in_before_send
  (s' : composite_state IM) (i : index) (j : index)
  (s : composite_state IM) (item : composite_transition_item IM) (m : message)
  (Hij : CompositeLatestSentObservedIn s' i j s item m)
  (s_j : composite_state IM) (item_j : composite_transition_item IM) (m_j : message)
  : valid_state_prop RFree s' ->
    head (composite_state_destructor IM state_destructor s' j) = Some (item_j, s_j) ->
    output item_j = Some m_j ->
    latest_composite_observed_before_send s' i j.
Proof.
  intros Hs' Hdestruct_j Houtput_j.
  eapply composite_state_destructor_head_reachable in Hdestruct_j as Htj; [| done..].
  destruct Hij as [Hdestruct_i Houtput_i Hobs].
  exists s, item, m, s_j, item_j, m_j; constructor; [done.. |]; constructor.
  apply head_Some_elem_of in Hdestruct_j as H_destruct_j.
  eapply composite_tv_state_destructor_index in H_destruct_j as Hlj.
  apply input_valid_transition_preloaded_project_active_free in Htj as Htj'.
  eapply composite_tv_state_destructor_destination in H_destruct_j as Hdestination_j; [| done].
  destruct item_j, l as [_j lj]; cbn in *; subst _j destination.
  destruct (decide (i = j)).
  - subst; rewrite Hdestruct_i in Hdestruct_j.
    inversion Hdestruct_j; subst item s_j; clear Hdestruct_j.
    by eexists _, _; constructor; [.. | constructor].
  - eapply composite_state_destructor_head_reachable in Hdestruct_i as Hti; [| done..].
    eapply head_Some_elem_of, composite_tv_state_destructor_destination
      in Hdestruct_i as Hdestination_i; [| done].
    eapply composite_tv_state_destructor_index in Hdestruct_i as Hli.
    destruct item, l as [_i li]; cbn in *; subst _i destination.
    replace (s j) with (s' j) in Hobs; cycle 1.
    {
      destruct Hti as [_ Hti]; cbn in Hti.
      destruct (transition _ _ _) as [si' om'].
      by inversion Hti; rewrite state_update_neq.
    }
    eapply HasBeenObserved_step_update in Hobs as [Hobs | Hnow];
      [by eexists s_j, _; constructor; [.. | constructor 1] | | done].
    destruct Hnow as (_mj & [H_input | H_output] & [Hnow | Hbefore]); subst.
    + by eexists s_j, _; constructor; [done.. | constructor 2].
    + by eexists s_j, _; constructor; [done.. | constructor 3].
    + apply Some_inj in H_output as <-.
      contradict n.
      apply input_valid_transition_preloaded_project_active_free in Hti as Hti'; cbn in Hti'.
      specialize (Hchannel i m_j) as Hchannel_i.
      spec Hchannel_i; [by eexists _, _, _ |].
      specialize (Hchannel j m_j) as Hchannel_j.
      spec Hchannel_j; [by eexists _, _, _ |].
      by congruence.
    + apply Some_inj in H_output as <-.
      apply tc_r_iff in Hbefore as [Hdm | (m' & Hbefore & Hdm)].
      * by eapply composite_observed_before_send_subsumes_msg_dep_rel;
          [| eexists _, _, _ |].
      * eapply @message_dependencies_are_necessary with (X := IM j) in Hdm as Hobs;
          [| done | by eexists _, _].
        eapply has_been_directly_observed_step_update in Hobs; [| done].
        eexists s_j, _; constructor; [done.. |]; cbn.
        destruct Hobs as [[| Houtput] |]; subst; [by constructor | | by do 2 econstructor].
        apply Some_inj in Houtput; subst m_j.
        by contradict Hdm; apply tc_reflect_irreflexive; typeclasses eauto.
Qed.

(**
  [CompositeLatestSentObservedIn] as a binary relation on indices of
  components for a given composite state.
*)
Definition composite_latest_sent_observed_in
  (s' : composite_state IM) (i j : index) : Prop :=
  exists item s m, CompositeLatestSentObservedIn s' i j item s m.

Lemma traceable_vlsm_initial_state_dec :
  forall (i : index) (si : state (IM i)),
    valid_state_prop (pre_loaded_with_all_messages_vlsm (IM i)) si ->
    Decision (initial_state_prop (IM i) si).
Proof.
  intros; destruct (decide (state_destructor i si = nil)).
  - by left; apply tv_state_destructor_initial.
  - by right; contradict n; apply tv_state_destructor_initial.
Qed.

(**
  Given a list of indices and a composite constrained state, select from the given
  list of indices the ones whose corresponding component state is initial.
*)
Program Definition initial_indices
  (s : composite_state IM) (Hs : valid_state_prop RFree s) (is : list index)
  : list index :=
  @filter _ _ _ (fun i => initial_state_prop (IM i) (s i)) _ is.
Next Obligation.
Proof.
  by intros; eapply traceable_vlsm_initial_state_dec,
    valid_state_project_preloaded_to_preloaded_free.
Qed.

(**
  Given a predicate on lists of transitions and positions in those lists,
  a composite state and a list of indices, finds the first index (say <<i>>)
  and the largest position in the list of transitions from component <<i>>
  reaching the given state for which the predicate holds.
*)
Definition find_decomposition
  (P : set (composite_transition_item IM * composite_state IM) -> nat -> Prop)
  `{forall s, RelDecision (fun i => P (composite_state_destructor IM state_destructor s i))}
  (s : composite_state IM)
  (indices : list index)
  : option (index * nat) :=
  find_first_indexed_largest_nat_with_propery_bounded
    (fun i => P (composite_state_destructor IM state_destructor s i))
    (fun i => length (composite_state_destructor IM state_destructor s i)) indices.

(**
  Given a composite state and a list of indices, finds first index <<i>> in the
  list and the largest position in the list of transitions from component <<i>>
  reaching the given state such that the corresponding transition is not
  sending any message.
*)
Definition find_not_send_decomposition
  (s : composite_state IM) (is : list index) : option (index * nat) :=
  find_decomposition CompositeNthNotSend s is.

(**
  Given a composite state and a list of indices, finds first index <<i>> in the
  list and the largest position in the list of transitions from component <<i>>
  reaching the given state such that the corresponding transition is sending
  a message which has not been previously observed in the composite state.
*)
Definition find_sent_not_observed_decomposition
  (s : composite_state IM) (is : list index) : option (index * nat) :=
  find_decomposition CompositeNthSentNotObserved s is.

(**
  A [choice_function] selecting a transition that does not hide equivocation
  (according to the [msg_dep_is_globally_equivocating] definition).

  To do so, it selects a transition which is either not sending a message,
  or sending a previously not observed message. The existence of such
  a transition is guaranteed by [at_least_one_send_not_previously_observed].
*)
Definition minimal_equivocation_choice
  (s : composite_state IM)
  (Hs : valid_state_prop RFree s)
  (is : list index)
  : index * nat :=
  match initial_indices s Hs is with
  | i :: _ => (i, 0)
  | [] =>
    match find_not_send_decomposition s is with
    | Some (i, n) => (i, n)
    | None =>
      match find_sent_not_observed_decomposition s is with
      | Some (i, n) => (i, n)
      | None => (hd inhabitant is, 0)
      end
    end
  end.

Lemma minimal_equivocation_choice_is_choosing_well :
  choosing_well IM state_destructor minimal_equivocation_choice.
Proof.
  intros ? * Hnodup Hinit; constructor; cycle 1.
  - intros Hindices; unfold minimal_equivocation_choice.
    destruct initial_indices eqn: Heq_ii;
      [destruct (find_not_send_decomposition s' indices) as [[i n] |] eqn: Heq_ns |];
      [| destruct (find_sent_not_observed_decomposition s' indices) as [[i n] |] eqn: Heq_sno |];
      cbn in *.
    + by eapply find_first_indexed_largest_nat_with_propery_bounded_Some; [| done].
    + by eapply find_first_indexed_largest_nat_with_propery_bounded_Some; [| done].
    + by destruct indices; [| left].
    + cut (i ∈ initial_indices s' Hs' indices); [| by rewrite Heq_ii; left].
      by intros Hi; apply elem_of_list_filter in Hi as [].
  - intros i n; unfold minimal_equivocation_choice.
    destruct initial_indices eqn: Heq_ii;
      [destruct (find_not_send_decomposition s' indices) as [[_i _n] |] eqn: Heq_ns |];
      [| destruct (find_sent_not_observed_decomposition s' indices) as [[_i _n] |] eqn: Heq_sno |];
      cbn in *; intro Heq; inversion Heq; subst; clear Heq; intros Hninit.
      + apply lookup_lt_is_Some_2.
        apply find_first_indexed_largest_nat_with_propery_bounded_Some
          in Heq_ns as (_ & Hn & _); [| done].
        by apply find_largest_nat_with_property_bounded_Some in Hn as [[Hn _] _].
      + apply lookup_lt_is_Some_2.
        apply find_first_indexed_largest_nat_with_propery_bounded_Some
          in Heq_sno as (_ & Hn & _); [| done].
        by apply find_largest_nat_with_property_bounded_Some in Hn as [[Hn _] _].
      + apply lookup_lt_is_Some_2.
        cut (composite_state_destructor IM state_destructor s' (hd inhabitant indices) <> []);
          [| by contradict Hninit; eapply composite_tv_state_destructor_initial].
        by destruct (composite_state_destructor); simpl; [| lia].
      + contradict Hninit.
        cut (i ∈ initial_indices s' Hs' indices); [| by rewrite Heq_ii; left].
        by intro Hi; apply elem_of_list_filter in Hi as [].
  - intro; unfold minimal_equivocation_choice.
    by unfold initial_indices; erewrite list_filter_iff.
Qed.

(**
  Suppose we have a composite state and a list of indices such that for each
  index from the list, the latest transition from the corresponding component of
  the composite state to this index is sending a message which has been
  previously observed in another component (the [composite_latest_sent_observed_in]
  relation).

  Then we can create a new list of indices, using only indices from the initial
  list of indices, which is longer than the initial list of indices and which is
  a chain wrt to the [composite_latest_sent_observed_in] relation.

  Note that since the new list is longer than the initial one, but doesn't use
  new indices, it implies that there is at least one index in the new list of
  indices which appears at least twice in the new list.
*)
Lemma composite_latest_sent_observed_in_chain
  (is : list index)
  (Hne : is <> [])
  (s : composite_state IM)
  (Hs : valid_state_prop RFree s)
  (Hall_sent_observed : forall x : index, x ∈ is ->
    exists y, y ∈ is /\
    composite_latest_sent_observed_in s x y)
  : exists is', is' ⊆ is /\ length is' > length is /\
      ForAllSuffix2 (flip (composite_latest_sent_observed_in s)) is'.
Proof.
  cut (forall n, exists is', length is' = n /\ is' ⊆ is /\
        ForAllSuffix2 (flip (composite_latest_sent_observed_in s)) is').
  {
    intros Hn; destruct (Hn (S (length is))) as (is' & Hlen & Hsub & Hall).
    by exists is'; split_and!; [| lia |].
  }
  induction n; [exists []; repeat split; [by inversion 1 | by constructor] |].
  destruct n.
  - destruct is as [| i is]; [done |].
    exists [i]; repeat split; [| repeat constructor].
    by intros _i; rewrite elem_of_list_singleton; intros ->; left.
  - destruct IHn as (is' & Hlen & Hsub & Hall).
    destruct is' as [| i is']; [by cbn in Hlen |].
    destruct (Hall_sent_observed i) as (i' & Hi' & Hcomposite); [by apply Hsub; left |].
    exists (i' :: i :: is').
    split_and!; [by rewrite <- Hlen | ..].
    + by inversion 1; subst; [| apply Hsub].
    + by constructor.
Qed.

(**
  Under the assumptions of [composite_latest_sent_observed_in_chain],
  all adjacent indices in the obtained chain are in the
  [latest_composite_observed_before_send] relation.
*)
Lemma all_latest_composite_observed_before_send_one_step
  (s : composite_state IM)
  (Hs : valid_state_prop RFree s)
  (is is' : list index)
  (Hsub : is' ⊆ is)
  (Hall_sent_observed : forall x : index, x ∈ is ->
    exists y, y ∈ is /\
    composite_latest_sent_observed_in s x y)
  : ForAllSuffix2 (flip (composite_latest_sent_observed_in s)) is' ->
    forall j : nat,
    forall isj, is' !! j = Some isj ->
    forall isi, is' !! (S j) = Some isi ->
    latest_composite_observed_before_send s isi isj.
Proof.
  intros Hall j isj Hisj isi Hisi.
  eapply ForAllSuffix2_lookup in Hisj as Hobs_j; [| done..].
  destruct Hobs_j as (s_isi & item_isi & m_isi & Hobs_j).
  destruct (Hall_sent_observed isj) as (y & Hy & s_isj & item_isj & m_isj & []);
    [by eapply Hsub, elem_of_list_lookup_2 |].
  by eapply composite_latest_sent_observed_in_before_send.
Qed.

(**
  Under the assumptions of [composite_latest_sent_observed_in_chain],
  all pairs of indices from the obtained chain are in the
  [latest_composite_observed_before_send] relation.
*)
Lemma all_latest_composite_observed_before_send
  (s : composite_state IM)
  (Hs : valid_state_prop RFree s)
  (is is' : list index)
  (Hsub : is' ⊆ is)
  (Hall_sent_observed : forall x : index, x ∈ is ->
    exists y, y ∈ is /\
    composite_latest_sent_observed_in s x y)
  : ForAllSuffix2 (flip (composite_latest_sent_observed_in s)) is' ->
    forall i j : nat, i > j ->
    forall isi, is' !! i = Some isi ->
    forall isj, is' !! j = Some isj ->
    latest_composite_observed_before_send s isi isj.
Proof.
  intros Hall i j Hij; unfold gt, lt in Hij; remember (S j) as k.
  revert j Heqk; induction Hij; intros j -> isi Hisi isj Hisj.
  - by eapply all_latest_composite_observed_before_send_one_step.
  - specialize (IHHij _ eq_refl).
    cut (is_Some (is' !! m)).
    {
      intros [isi' Hisi'].
      transitivity isi'; [| by apply IHHij].
      by eapply all_latest_composite_observed_before_send_one_step.
    }
    by apply list_lookup_lt with (S m); [| lia].
Qed.

(**
  We would like to formalize the following idea:

  If all possible transitions to the given state are send transitions, then
  at least one of the sent messages must not have been previously observed.

  To do so, we will prove the following statement matching more closely the
  definition of [minimal_equivocation_choice]:

  If there are no components in the initial state and if all possible transitions
  are sent and if all sent messages have been previously observed, then
  we have a contradiction.

  Proof sketch:
  - Use [composite_latest_sent_observed_in_chain] to build a chain of
    indices larger than the initial list of indices, thus guaranteeing that at
    least one index, say <<i>> appears twice in the chain.
  - Instantiate [all_latest_composite_observed_before_send], for the pair
    between the <<i>> above and itself to obtain that <<i>> is in relation
    [latest_composite_observed_before_send] with itself
  - Contradiction by [latest_composite_observed_before_send_irreflexive].
*)
Lemma at_least_one_send_not_previously_observed
  (s' : composite_state IM)
  (Hs' : valid_state_prop RFree s')
  (is : list index)
  (His : is <> [])
  (Hnodup : NoDup is)
  (Hinitial_outside : not_in_indices_initial_prop IM s' is)
  : initial_indices s' Hs' is = [] ->
    find_not_send_decomposition s' is = None ->
    find_sent_not_observed_decomposition s' is = None ->
      False.
Proof.
  intros Hinitial Hnot_send Hsent_not_obs.
  assert (Hall_sent_observed :
    forall x : index, x ∈ is ->
      exists y, y ∈ is /\ composite_latest_sent_observed_in s' x y).
  {
    intros i Hi.
    eapply Forall_filter_nil, Forall_forall in Hinitial; [| done].
    eapply find_first_indexed_largest_nat_with_propery_bounded_None in Hnot_send, Hsent_not_obs;
      [| done..].
    rewrite find_largest_nat_with_property_bounded_None in Hsent_not_obs, Hnot_send.
    rewrite composite_tv_state_destructor_initial in Hinitial;
      [| by typeclasses eauto | done].
    destruct composite_state_destructor as [| [item s]] eqn: Hdestruct;
      [done | clear Hinitial]; cbn in *.
    specialize (Hnot_send 0); spec Hnot_send; [lia |].
    specialize (Hsent_not_obs 0); spec Hsent_not_obs; [lia |].
    eapply not_CompositeNthNotSend_is_sent in Hnot_send as [m Houtput]; [| done].
    eapply not_CompositeNthSentNotObserved_is_observed in Hsent_not_obs; [| done..].
    apply composite_HasBeenObserved_iff in Hsent_not_obs as [y Hobs].
    exists y; split.
    - destruct (decide (elem_of y is)); [done | exfalso].
      cut (initial_state_prop (IM y) (s y)).
      {
        by intro; inversion Hobs; eapply has_been_directly_observed_no_inits.
      }
      eapply composite_tv_state_destructor_preserves_not_in_indices_initial
        with (n := 0) in Hinitial_outside;
        [| typeclasses eauto | done | by rewrite Hdestruct].
      by apply Hinitial_outside.
    - by exists s, item, m; constructor; [rewrite Hdestruct | ..].
  }
  destruct (composite_latest_sent_observed_in_chain _ His _ Hs' Hall_sent_observed)
    as (is' & Hsub & Hlen & Hall).
  destruct (longer_subseteq_has_dups _ _ Hsub Hlen)
    as (k1 & k2 & i' & Hnk12 & Hi1 & Hi2).
  assert (k1 > k2 \/ k2 > k1) as [Hk12 | Hk21] by lia.
  - eapply irreflexivity.
    + by apply latest_composite_observed_before_send_irreflexive.
    + by apply (all_latest_composite_observed_before_send _ Hs' _ _ Hsub
        Hall_sent_observed Hall _ _ Hk12 i' Hi1 i' Hi2).
  - eapply irreflexivity.
    + by apply latest_composite_observed_before_send_irreflexive.
    + by apply (all_latest_composite_observed_before_send _ Hs' _ _ Hsub
        Hall_sent_observed Hall _ _ Hk21 i' Hi2 i' Hi1).
Qed.

(**
  The main result of this section: the transition chosen by the
  [minimal_equivocation_choice] function does not hide existing equivocation.
*)
Lemma minimal_equivocation_choice_monotone :
  forall (is : list index), NoDup is ->
  forall (s' : composite_state IM) (Hs' : valid_state_prop RFree s'),
    not_in_indices_initial_prop IM s' is ->
    forall (i : index) (Hi : i ∈ is) (n : nat),
      minimal_equivocation_choice s' Hs' is  = (i, n) ->
      forall (s : composite_state IM) (item : composite_transition_item IM),
        composite_state_destructor IM state_destructor s' i !! n = Some (item, s) ->
        forall v : validator,
          msg_dep_is_globally_equivocating IM message_dependencies sender s v ->
          msg_dep_is_globally_equivocating IM message_dependencies sender s' v.
Proof.
  intros is Hnodup s' Hs' Hnis i Hi n Hchoice s item Hdestruct v [m []].
  eapply composite_state_destructor_lookup_reachable in Hdestruct as Ht;
    [| typeclasses eauto | done].
  eapply transition_preserves_CompositeHasBeenObserved
    in mdgee_rec_observed as Hobs'; [| done].
  assert (destination item = s') as <-
    by (eapply composite_tv_state_destructor_destination, elem_of_list_lookup_2; eauto).
  exists m; constructor; [done.. |].
  cut (output item <> Some m).
  {
    intro.
    destruct (free_composite_has_been_sent_stepwise_props IM) as [_].
    rewrite oracle_step_update by done; cbn.
    by intros [].
  }
  unfold minimal_equivocation_choice in Hchoice.
  destruct initial_indices eqn: Heq_ii;
    [destruct find_not_send_decomposition as [[_i _n] |] eqn: Heq_ns |];
    [| destruct find_sent_not_observed_decomposition as [[_i _n] |] eqn: Heq_sno |];
    cbn in *; inversion Hchoice; subst; clear Hchoice.
  - apply find_first_indexed_largest_nat_with_propery_bounded_Some
      in Heq_ns as (_ & Hn & _); [| done].
    apply find_largest_nat_with_property_bounded_Some
      in Hn as [[_ [_item _s H_destruct Houtput]] _].
    cbv in Hdestruct, H_destruct; rewrite H_destruct in Hdestruct; clear H_destruct.
    inversion Hdestruct; subst.
    by rewrite Houtput.
  - apply find_first_indexed_largest_nat_with_propery_bounded_Some
      in Heq_sno as (_ & Hn & _); [| done].
    apply find_largest_nat_with_property_bounded_Some
      in Hn as [[_ [_item _s H_destruct _m Houtput Hno]] _].
    cbv in Hdestruct, H_destruct; rewrite H_destruct in Hdestruct; clear H_destruct.
    inversion Hdestruct; subst.
    rewrite Houtput.
    by destruct (decide (_m = m)); [subst | congruence].
  - destruct (decide (is = [])); [by subst; inversion Hi |].
    by exfalso; eapply at_least_one_send_not_previously_observed.
  - assert (Hii : i ∈ initial_indices (destination item) Hs' is) by (rewrite Heq_ii; left).
    apply elem_of_list_filter in Hii as [Hii _].
    eapply composite_tv_state_destructor_initial in Hii; [| typeclasses eauto | done].
    by rewrite Hii in Hdestruct.
Qed.

End sec_minimal_equivocation_choice.

Section sec_minimal_equivocation_trace.

(** ** Extracting a minimally-equivocating trace *)

Context
  `{EqDecision message}
  `{finite.Finite index}
  `{Inhabited index}
  (IM : index -> VLSM message)
  `{forall i, ComputableSentMessages (IM i)}
  `{forall i, ComputableReceivedMessages (IM i)}
  `{FullMessageDependencies message Cm message_dependencies full_message_dependencies}
  `{forall i, MessageDependencies (IM i) message_dependencies}
  `{forall i s, Decision (initial_state_prop (IM i) s)}
  (state_destructor : forall i, state (IM i) -> set (transition_item (IM i) * state (IM i)))
  (state_size : forall i, state (IM i) -> nat)
  `{forall i, TraceableVLSM (IM i) (state_destructor i) (state_size i)}
  `(sender : message -> option validator)
  `{!Irreflexive (tc_composite_observed_before_send IM message_dependencies)}
  (A : validator -> index)
  (Hchannel : channel_authentication_prop IM A sender)
  (Free := free_composite_vlsm IM)
  (RFree := pre_loaded_with_all_messages_vlsm Free)
  .

(**
  The minimally-equivocating trace is obtained by instantiating
  [composite_state_to_trace] with the [minimal_equivocation_choice] function.

  By [reachable_composite_state_to_trace], we know that the obtained trace is
  a constrained trace.
*)
Definition state_to_minimal_equivocation_trace
  (s : composite_state IM) (Hs : valid_state_prop RFree s)
  : composite_state IM * list (composite_transition_item IM) :=
  composite_state_to_trace IM state_destructor state_size
    (minimal_equivocation_choice IM state_destructor state_size) s Hs.

(**
  The trace obtained through [state_to_minimal_equivocation_trace] is not
  hiding equivocation at any step, therefore being indeed a
  minimally-equivocating trace reaching its final state.
*)
Lemma state_to_minimal_equivocation_trace_equivocation_monotonic :
  forall (s : composite_state IM) (Hs : valid_state_prop RFree s),
  forall is tr, state_to_minimal_equivocation_trace s Hs = (is, tr) ->
  forall (pre suf : list (composite_transition_item IM))
    (item : composite_transition_item IM),
    tr = pre ++ [item] ++ suf ->
    forall v : validator,
      msg_dep_is_globally_equivocating IM message_dependencies sender
        (finite_trace_last is pre) v ->
      msg_dep_is_globally_equivocating IM message_dependencies sender
        (destination item) v.
Proof.
  intros.
  eapply composite_state_to_trace_P_monotonic with
    (P := fun s => msg_dep_is_globally_equivocating IM message_dependencies sender s v);
    [by eapply minimal_equivocation_choice_is_choosing_well | | done..].
  by intros ? **; eapply minimal_equivocation_choice_monotone.
Qed.

End sec_minimal_equivocation_trace.
