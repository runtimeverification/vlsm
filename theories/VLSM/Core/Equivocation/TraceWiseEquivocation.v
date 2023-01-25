From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude finite.
From Coq Require Import FinFun Rdefinitions.
From VLSM.Lib Require Import Preamble ListExtras StdppListSet Measurable.
From VLSM.Core Require Import VLSM Composition ProjectionTraces.
From VLSM.Core Require Import Equivocation.
From VLSM.Lib Require Import Preamble StdppExtras.

(** * VLSM Trace-wise Equivocation

  In this section we define a more precise notion of message equivocation,
  based on analyzing (all) traces leading to a state. Although in some cases
  we might be able to actually compute this, its purpose is more to identify
  the ideal notion of detectable equivocation which would be used to
  establish the connection between limited (observed) message equivocation
  and limited state equivocation.
*)

Section sec_tracewise_equivocation.

Context
  `{EqDecision message}
  `{EqDecision index}
  (IM : index -> VLSM message)
  `{forall i : index, HasBeenSentCapability (IM i)}
  `{forall i : index, HasBeenReceivedCapability (IM i)}
  `{EqDecision validator}
  (threshold : R)
  `{Hmeasurable_V : Measurable validator}
  `{FinSet validator Cv}
  `{!ReachableThreshold validator Cv threshold}
  `{finite.Finite validator}
  (A : validator -> index)
  (sender : message -> option validator)
  (PreFree := pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM))
  .

(**
  An item is equivocating in a trace containing it if it receives
  a message which has not been previously sent in that trace.
*)
Definition item_equivocating_in_trace
  (item : composite_transition_item IM)
  (tr : list (composite_transition_item IM))
  : Prop
  := from_option (fun m => ~ trace_has_message (field_selector output) m tr) False (input item).

#[local] Instance item_equivocating_in_trace_dec : RelDecision item_equivocating_in_trace.
Proof.
  intros item tr.
  destruct item. destruct input as [m |]; [| by right; itauto].
  unfold item_equivocating_in_trace, trace_has_message, field_selector; cbn.
  by typeclasses eauto.
Qed.

(**
  Given a trace, we can precisely identify the validators equivocating
  in that trace based on identifying every [item_equivocating_in_trace].
*)
Definition equivocating_senders_in_trace
  (tr : list (composite_transition_item IM))
  : set validator
  :=
  let decompositions := one_element_decompositions tr in
  let test := (fun d => match d with (pre, item, _) =>
      item_equivocating_in_trace item pre
    end) in
  let equivocating_items :=
    map (fun d => match d with (_, item, _) => item end)
      (filter test decompositions) in
  let equivocating_messages := map_option input equivocating_items in
  let equivocating_senders := map_option sender equivocating_messages in
  remove_dups equivocating_senders.

Lemma no_input_no_equivocating_senders_in_trace tr
  (Hinput_none : forall item, item ∈ tr -> input item = None)
  : equivocating_senders_in_trace tr = [].
Proof.
  apply elem_of_nil_inv.
  intros v Hv.
  unfold equivocating_senders_in_trace in Hv.
  rewrite elem_of_remove_dups in Hv.
  apply elem_of_map_option in Hv as [msg [Hmsg Hv]].
  apply elem_of_map_option in Hmsg as [item [Hitem Hmsg]].
  apply elem_of_list_fmap in Hitem as [((pre, _item), _suf) [Heq_item Hitem]].
  apply elem_of_list_filter, proj2, elem_of_one_element_decompositions in Hitem.
  subst tr _item.
  specialize (Hinput_none item).
  spec Hinput_none; [| by congruence].
  by apply elem_of_app; right; apply elem_of_app; do 2 left.
Qed.

Lemma elem_of_equivocating_senders_in_trace
  (tr : list (composite_transition_item IM))
  (v : validator)
  : v ∈ equivocating_senders_in_trace tr <->
    exists (m : message),
    (sender m = Some v) /\
    equivocation_in_trace PreFree m tr.
Proof.
  unfold equivocating_senders_in_trace.
  rewrite elem_of_remove_dups, elem_of_map_option.
  setoid_rewrite elem_of_map_option.
  setoid_rewrite elem_of_list_fmap.
  split.
  - intros [im [[item [[((prefix, _item), suffix) [Heq_item Hfilter]] Hinput]] Hsender]].
    apply elem_of_list_filter in Hfilter.
    destruct Hfilter as [Heqv Hdec].
    subst _item.
    exists im. split; [done |].
    exists prefix, item, suffix.
    apply elem_of_one_element_decompositions in Hdec. simpl in Hdec.
    split; [by subst |].
    split; [done |].
    by unfold item_equivocating_in_trace in Heqv; rewrite Hinput in Heqv.
  - intros [im [Hsender [prefix [item [suffix [Heq_tr [Hinput Heqv]]]]]]].
    exists im. split; [| done]. exists item.
    split; [| done]. exists ((prefix, item), suffix).
    split; [done |].
    apply elem_of_list_filter.
    unfold item_equivocating_in_trace.
    simpl in *.  rewrite Hinput.
    split; [done |].
    by apply elem_of_one_element_decompositions.
Qed.

Lemma equivocating_senders_in_trace_prefix prefix suffix
  : equivocating_senders_in_trace prefix ⊆ equivocating_senders_in_trace (prefix ++ suffix).
Proof.
  intros v. rewrite !elem_of_equivocating_senders_in_trace.
  intros [m [Hm Heqv]].
  exists m. split; [done |].
  by apply equivocation_in_trace_prefix.
Qed.

(**
  An alternative definition for detecting equivocation in a certain state,
  which checks that for _every_ valid trace (using any messages) reaching
  that state there exists an equivocation involving the given validator.

  Notably, this definition is not generally equivalent to [is_equivocating_statewise],
  which does not verify the order in which receiving and sending occurred.
*)
Definition is_equivocating_tracewise
  (s : composite_state IM)
  (v : validator)
  (j := A v)
  : Prop
  :=
  forall is tr
  (Hpr : finite_valid_trace_init_to PreFree is s tr),
  exists (m : message),
  (sender m = Some v) /\
  exists prefix elem suffix (lprefix := finite_trace_last is prefix),
  tr = prefix ++ elem :: suffix
  /\ input elem = Some m
  /\ ~ has_been_sent (IM j) (lprefix j) m.

(**
  A possibly friendlier version using a previously defined primitive.
  Note that this definition does not require the [HasBeenSentCapability].
*)
Definition is_equivocating_tracewise_no_has_been_sent
  (s : composite_state IM)
  (v : validator)
  (j := A v)
  : Prop
  :=
  forall is tr
  (Htr : finite_valid_trace_init_to PreFree is s tr),
  exists (m : message),
  (sender m = Some v) /\
  equivocation_in_trace PreFree m tr.

Lemma is_equivocating_tracewise_no_has_been_sent_equivocating_senders_in_trace
  (s : composite_state IM)
  (v : validator)
  : is_equivocating_tracewise_no_has_been_sent s v <->
    forall is tr
    (Htr : finite_valid_trace_init_to PreFree is s tr),
    v ∈ equivocating_senders_in_trace tr.
Proof.
  by split; intros Heqv is tr Htr; specialize (Heqv _ _ Htr)
  ; apply elem_of_equivocating_senders_in_trace.
Qed.

(**
  If any message can only be emitted by node corresponding to its sender
  ([sender_safety_alt_prop]), then [is_equivocating_tracewise] is equivalent
  to [is_equivocating_tracewise_no_has_been_sent].
*)
Lemma is_equivocating_tracewise_no_has_been_sent_iff
  (Hsender_safety : sender_safety_alt_prop IM A sender)
  s v
  : is_equivocating_tracewise_no_has_been_sent s v <-> is_equivocating_tracewise s v.
Proof.
  unfold is_equivocating_tracewise, equivocation_in_trace,
    is_equivocating_tracewise_no_has_been_sent.
  apply forall_proper; intros is.
  apply forall_proper; intros.
  apply forall_proper; intros [].
  apply exist_proper; intros.
  apply and_proper_l; intro.
  apply exist_proper; intro prefix.
  apply exist_proper; intro.
  apply exist_proper; intro.
  apply and_proper_l; intros ->.
  apply and_iff_compat_l, not_iff_compat; cbn.
  cut (finite_valid_trace_init_to PreFree is (finite_trace_last is prefix) prefix).
  {
    intros.
    erewrite <- oracle_initial_trace_update
      with (vlsm := free_composite_vlsm IM); cycle 1.
    - by apply composite_has_been_sent_stepwise_props.
    - done.
    - by eapply has_been_sent_iff_by_sender.
  }
  split; [| done].
  by eapply  finite_valid_trace_from_to_app_split.
Qed.

Lemma transition_is_equivocating_tracewise_char
  l s om s' om'
  (Ht : input_valid_transition PreFree l (s, om) (s', om'))
  (v : validator)
  : is_equivocating_tracewise_no_has_been_sent s' v ->
    is_equivocating_tracewise_no_has_been_sent s v \/
    option_bind _ _ sender om = Some v.
Proof.
  destruct (decide (option_bind _ _ sender om = Some v))
  ; [by intro; right |].
  intros Heqv. left. intros is tr [Htr Hinit].
  specialize (extend_right_finite_trace_from_to _ Htr Ht) as Htr'.
  specialize (Heqv _ _ (conj Htr' Hinit)).
  destruct Heqv as [m [Hv [prefix [item [suffix [Heq Heqv]]]]]].
  exists m. split; [done |]. exists prefix.
  destruct_list_last suffix suffix' item' Heqsuffix.
  { exfalso. subst. apply app_inj_tail, proj2 in Heq. subst item. apply proj1 in Heqv. simpl in Heqv.
    subst om. simpl in n. congruence. }
  exists item, suffix'. split; [| done].
  replace (prefix ++ item :: suffix' ++ [item']) with ((prefix ++ item :: suffix') ++ [item']) in Heq.
  - apply app_inj_tail in Heq. apply Heq.
  - by rewrite <- app_assoc.
Qed.

Lemma transition_receiving_no_sender_reflects_is_equivocating_tracewise
  l s om s' om'
  (Ht : input_valid_transition PreFree l (s, om) (s', om'))
  (Hno_sender : option_bind _ _ sender om = None)
  (v : validator)
  : is_equivocating_tracewise_no_has_been_sent s' v -> is_equivocating_tracewise_no_has_been_sent s v.
Proof.
  intro Hs'.
  by destruct (transition_is_equivocating_tracewise_char _ _ _ _ _ Ht v Hs'); [| congruence].
Qed.

Lemma is_equivocating_statewise_implies_is_equivocating_tracewise s v
  : is_equivocating_statewise IM A sender s v -> is_equivocating_tracewise s v.
Proof.
  intros [j [m [Hm [Hnbs_m Hbr_m]]]] is tr Htr.
  exists m. split; [done |].
  apply (preloaded_finite_valid_trace_init_to_projection _ j) in Htr as Htrj.
  apply proj1 in Htrj as Hlstj.
  apply finite_valid_trace_from_to_last_pstate in Hlstj.
  apply proper_received in Hbr_m; [| done].
  specialize (Hbr_m _ _ Htrj).
  apply Exists_exists in Hbr_m.
  destruct Hbr_m as [itemj [Hitemj Hinput]].
  apply (finite_trace_projection_list_in_rev IM) in Hitemj
    as [item [Hitem [_ [Heq_input _]]]].
  simpl in Hinput. rewrite <- Heq_input in Hinput. clear Heq_input.
  apply elem_of_list_split in Hitem.
  destruct Hitem as [prefix [suffix Heq_tr]].
  exists prefix, item, suffix. split; [done |]. split; [done |].
  subst.
  clear -Hnbs_m Htr.
  apply preloaded_finite_valid_trace_init_to_projection with (j := A v) in Htr as Htrv.
  apply proj1, finite_valid_trace_from_to_app_split, proj1
    , preloaded_finite_valid_trace_from_to_projection with (j := A v)
    , finite_valid_trace_from_to_last in Htr.
  rewrite (VLSMTotalProjection.VLSM_projection_finite_trace_project_app
    (preloaded_component_projection IM (A v))) in Htrv.
  apply proj1, (finite_valid_trace_from_to_app_split (pre_loaded_with_all_messages_vlsm (IM (A v))))
    in Htrv as [_ Htrv].
  rewrite Htr in Htrv.
  intro Hbs_m. elim Hnbs_m. clear Hnbs_m.
  revert Hbs_m.
  apply in_futures_preserving_oracle_from_stepwise with (field_selector output).
  - by apply has_been_sent_stepwise_props.
  - by eexists.
Qed.

Lemma initial_state_not_is_equivocating_tracewise
  (s : composite_state IM)
  (Hs : composite_initial_state_prop IM s)
  (v : validator)
  : ~ is_equivocating_tracewise_no_has_been_sent s v.
Proof.
  intros Heqv.
  specialize (Heqv s []).
  spec Heqv; [by split; [| done]; constructor; apply initial_state_is_valid |].
  destruct Heqv as [m [_ [prefix [suf [item [Heq _]]]]]].
  by destruct prefix; inversion Heq.
Qed.

Context
  `{RelDecision _ _ is_equivocating_tracewise_no_has_been_sent}
  .

#[local] Program Instance equivocation_dec_tracewise
  : BasicEquivocation (composite_state IM) validator Cv threshold :=
  {
    state_validators := fun _ => list_to_set (enum validator);
    is_equivocating := is_equivocating_tracewise_no_has_been_sent;
  }.

Lemma equivocating_validators_is_equivocating_tracewise_iff s v
  : v ∈ equivocating_validators s <-> is_equivocating_tracewise_no_has_been_sent s v.
Proof.
  unfold equivocating_validators.
  simpl.
  rewrite elem_of_filter, elem_of_list_to_set.
  by itauto (apply elem_of_enum).
Qed.

Lemma equivocating_validators_empty_in_initial_state
  (s : composite_state IM)
  (His : composite_initial_state_prop IM s)
  : equivocating_validators s ≡@{Cv} ∅.
Proof.
  intro v. split.
  - rewrite equivocating_validators_is_equivocating_tracewise_iff.
    by apply initial_state_not_is_equivocating_tracewise with (v := v) in His.
  - by intro HV; contradict HV; apply not_elem_of_empty.
Qed.

Lemma input_valid_transition_receiving_no_sender_reflects_equivocating_validators
  l s om s' om'
  (Ht : input_valid_transition PreFree l (s, om) (s', om'))
  (Hno_sender : option_bind _ _ sender om = None)
  : equivocating_validators s' ⊆ equivocating_validators s.
Proof.
  intros v Hs'%equivocating_validators_is_equivocating_tracewise_iff.
  by eapply equivocating_validators_is_equivocating_tracewise_iff,
            transition_receiving_no_sender_reflects_is_equivocating_tracewise.
Qed.

Lemma initial_state_equivocators_weight
  (s : composite_state IM)
  (Hs : composite_initial_state_prop IM s)
  : equivocation_fault s = 0%R.
Proof.
  apply equivocating_validators_empty_in_initial_state, elements_empty_iff in Hs.
  unfold equivocation_fault.
  by apply sum_weights_empty, elements_empty_iff.
Qed.

Lemma composite_transition_no_sender_equivocators_weight
  l s om s' om'
  (Ht : input_valid_transition PreFree l (s, om) (s', om'))
  (Hno_sender : option_bind _ _ sender om = None)
  : (equivocation_fault s' <= equivocation_fault s)%R.
Proof.
  specialize (input_valid_transition_receiving_no_sender_reflects_equivocating_validators
    _ _ _ _ _ Ht Hno_sender) as Heqv.
  by apply incl_equivocating_validators_equivocation_fault.
Qed.

End sec_tracewise_equivocation.
