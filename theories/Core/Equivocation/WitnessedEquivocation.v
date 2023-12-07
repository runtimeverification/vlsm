From stdpp Require Import prelude.
From Coq Require Import Reals.
From VLSM.Lib Require Import Preamble ListExtras ListSetExtras FinSetExtras.
From VLSM.Core Require Import VLSM VLSMProjections Composition.
From VLSM.Core Require Import SubProjectionTraces MessageDependencies Equivocation.
From VLSM.Core Require Import NoEquivocation FixedSetEquivocation TraceWiseEquivocation.

(** * Core: Witnessed Equivocation

  Although [is_equivocating_tracewise] provides a very precise notion of
  equivocation, it does not guarantee the monotonicity of the set of equivocators
  along a trace.

  The witnessed equivocation assumption is a possible way to address this issue.

  Starting from the (reasonable) assumption that for any state <<s>>, there is
  a trace ending in <<s>> whose [equivocating_senders_in_trace] are precisely
  the equivocators of <<s>> (the [WitnessedEquivocationCapability]),
  we can show that for each Free valid state there exists
  a valid trace with the [strong_trace_witnessing_equivocation_prop]erty,
  i.e., a trace whose every prefix is a witness for its corresponding end state
  (Lemma [free_has_strong_trace_witnessing_equivocation_prop]).
  In particular, the set of equivocators is monotonically increasing for such a
  trace (Lemma [strong_witness_equivocating_validators_prefix_monotonicity]).

  We then use this result to show that any free valid state is also a valid
  state for a composition under the [fixed_equivocation_constraint]
  induced by its set of equivocators.
*)

Section sec_witnessed_equivocation.

Context
  `{EqDecision message}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  `{forall i : index, HasBeenSentCapability (IM i)}
  `{forall i : index, HasBeenReceivedCapability (IM i)}
  (Free := free_composite_vlsm IM)
  (PreFree := pre_loaded_with_all_messages_vlsm Free)
  (threshold : R)
  `{ReachableThreshold validator Cv threshold}
  `{!finite.Finite validator}
  (A : validator -> index)
  (sender : message -> option validator)
  `{!RelDecision (constrained_composite_state_is_equivocating_tracewise IM A sender)}
  (Htracewise_BasicEquivocation : BasicEquivocation (valid_state PreFree) validator Cv threshold
    := equivocation_dec_tracewise IM threshold A sender)
  (equivocating_validators :=
    equivocating_validators (BasicEquivocation := Htracewise_BasicEquivocation))
  .

(**
  A trace witnesses the equivocation of its final state <<s>> if its set of
  equivocators is precisely that of the [equivocating_validators] of <<s>>.
*)
Definition trace_witnessing_equivocation_prop
  {is s : composite_state IM} {tr : list (composite_transition_item IM)}
  (Htr : finite_valid_trace_init_to PreFree is s tr)
  : Prop :=
  forall v, v ∈ equivocating_validators (exist _ s (valid_trace_last_pstate Htr)) <->
    exists (m : message), (sender m = Some v) /\ equivocation_in_trace PreFree m tr.

Lemma trace_witnessing_equivocation_prop_pi
  (is s s' : composite_state IM) (tr : list (composite_transition_item IM))
  (Htr : finite_valid_trace_init_to PreFree is s tr)
  (Htr' : finite_valid_trace_init_to PreFree is s' tr) :
  trace_witnessing_equivocation_prop Htr
    <->
  trace_witnessing_equivocation_prop Htr'.
Proof.
  unfold trace_witnessing_equivocation_prop.
  remember (exist _ _ _) as sigma.
  remember  (exist _ _ (valid_trace_last_pstate Htr')) as sigma'.
  apply valid_trace_get_last in Htr as Heqs.
  apply valid_trace_get_last in Htr' as Heqs'.
  subst s s'.
  assert (Heqv : sigma ≡ sigma') by (subst; done).
  unshelve eapply valid_state_equivocating_validators_proper
    with (Cv := Cv) in Heqv; try typeclasses eauto.
  apply forall_proper; intro v.
  by split; intros <-; [symmetry |]; apply Heqv.
Qed.

Lemma equivocating_senders_in_trace_witnessing_equivocation_prop
  {is s : composite_state IM} {tr : list (composite_transition_item IM)}
  (Htr : finite_valid_trace_init_to PreFree is s tr)
  (Hwitness : trace_witnessing_equivocation_prop Htr)
  : set_eq
    (elements (equivocating_validators (exist _ s (valid_trace_last_pstate Htr))))
    (equivocating_senders_in_trace IM sender tr).
Proof.
  split; intros v Hv.
  - by apply elem_of_elements, Hwitness in Hv; apply elem_of_equivocating_senders_in_trace.
  - by eapply elem_of_elements, Hwitness, elem_of_equivocating_senders_in_trace.
Qed.

(**
  A composition of VLSMs has the witnessed equivocation capability if towards any
  valid states there exist a trace witnessing its equivocation.
*)
Class WitnessedEquivocationCapability : Prop :=
{
  is_equivocating_tracewise_witness :
    forall (s : composite_state IM), valid_state_prop PreFree s ->
    exists is tr (Htr : finite_valid_trace_init_to PreFree is s tr),
      trace_witnessing_equivocation_prop Htr
}.

Section sec_witnessed_equivocation_properties.

Context
  (Hke : WitnessedEquivocationCapability)
  (Hsender_safety : sender_safety_alt_prop IM A sender)
  .

Lemma initial_state_witnessing_equivocation_prop
  s (Hs : composite_initial_state_prop IM s) :
  trace_witnessing_equivocation_prop
    (conj (finite_valid_trace_from_to_empty _ _ (initial_state_is_valid PreFree _ Hs)) Hs).
Proof.
  split.
  - intros Hv; contradict Hv; apply elem_of_equiv_empty, equiv_empty.
    clear v; intros v Hv.
    eapply valid_state_equivocating_validators_proper
      with (x := exist _ s (initial_state_is_valid PreFree _ Hs)) in Hv; [| done].
    by eapply equivocating_validators_empty_in_initial_state.
  - intros [m [_ Hmsg]].
    by elim (no_equivocation_in_empty_trace PreFree m).
Qed.

(**
  For any trace having the [trace_witnessing_equivocation_prop]erty,
  its final transition is monotonic w.r.t. the [equivocating_validators].
*)
Lemma equivocating_validators_witness_monotonicity
  (is s' : composite_state IM)
  (tr : list (composite_transition_item IM))
  (item : composite_transition_item IM)
  (Htr : finite_valid_trace_init_to PreFree is s' (tr ++ [item]))
  (Hwitness : trace_witnessing_equivocation_prop Htr)
  (s := finite_trace_last is tr)
  (Htr' := finite_valid_trace_init_to_prefix_1 PreFree Htr) :
  equivocating_validators (exist _ s (valid_trace_last_pstate Htr'))
    ⊆
  equivocating_validators (exist _ s' (valid_trace_last_pstate Htr)).
Proof.
  intros v Hv; apply Hwitness.
  apply equivocating_validators_is_equivocating_tracewise_iff in Hv.
  specialize (Hv _ _ Htr') as [m [Hmsg Heqv]].
  exists m. split; [done |].
  by apply equivocation_in_trace_prefix.
Qed.

(**
  Given a trace with the [trace_witnessing_equivocation_prop]erty,
  if the [equivocating_validators] for the destination of its last transition
  are  included in the [equivocating_validators] for the source of its last
  transition, the the trace without its last transition also has the
  [trace_witnessing_equivocation_prop]erty.
*)
Lemma input_valid_transition_reflects_trace_witnessing_equivocation_prop
  (is s' : composite_state IM)
  (tr : list (composite_transition_item IM))
  (item : composite_transition_item IM)
  (Htr : finite_valid_trace_init_to PreFree is s' (tr ++ [item]))
  (s := finite_trace_last is tr)
  (Htr' := finite_valid_trace_init_to_prefix_1 PreFree Htr)
  (Hincl : equivocating_validators (exist _ s' (valid_trace_last_pstate Htr))
    ⊆
   equivocating_validators (exist _ s (valid_trace_last_pstate Htr'))) :
  trace_witnessing_equivocation_prop Htr ->
  trace_witnessing_equivocation_prop Htr'.
Proof.
  intros Hwitness v; split.
  - intros Hv.
    by unshelve eapply equivocating_validators_is_equivocating_tracewise_iff
      with (Cv := Cv); try typeclasses eauto; cycle 3.
  - intros (msg & Hsender & Heqv).
    apply Hincl, Hwitness.
    exists msg. split; [done |].
    by apply equivocation_in_trace_prefix.
Qed.

(**
  An equivocator for the destination of a transition is either an equivocation
  for the source as well, or it is the sender of the received message and that
  message is not sent by any trace witnessing the source of the transition.
*)
Lemma equivocating_validators_step_update
    l s om s' om'
    (Ht : input_valid_transition PreFree l (s, om) (s', om'))
    v
    : v ∈ equivocating_validators (exist _ s' (input_valid_transition_destination _ Ht)) ->
      v ∈ equivocating_validators (exist _ s (input_valid_transition_origin _ Ht)) \/
      (exists m, om = Some m /\
      sender m = Some v /\
      forall is tr
      (Htr : finite_valid_trace_init_to PreFree is s tr)
      (Hwitness : trace_witnessing_equivocation_prop Htr),
      ~ trace_has_message (field_selector output) m tr).
Proof.
  intro Hv.
  destruct (decide (v ∈ equivocating_validators (s ↾ input_valid_transition_origin PreFree Ht)))
    as [Hnv | Hnv]; [by left | right].
  apply equivocating_validators_is_equivocating_tracewise_iff in Hv.
  destruct (transition_is_equivocating_tracewise_char IM A sender  _ _ _ _ _ Ht _ Hv)
    as [| Hom];
    [by contradict Hnv; apply equivocating_validators_is_equivocating_tracewise_iff |].
  destruct om as [m |]; simpl in Hom; [| by congruence].
  exists m; split_and!; [done.. |].
  intros is tr [Htr Hinit] Hwitness.
  specialize (extend_right_finite_trace_from_to _ Htr Ht) as Htr'.
  specialize (Hv _ _ (conj Htr' Hinit)).
  destruct Hv as [m' [Hm' [prefix [item [suffix [Heq Heqv]]]]]].
  destruct_list_last suffix suffix' item' Heqsuffix.
  - apply app_inj_tail in Heq. destruct Heq; subst.
    simpl in Heqv. destruct Heqv as [Heq_m Heqv].
    by inversion Heq_m.
  - elim Hnv.
    specialize (Hwitness v).
    eapply valid_state_equivocating_validators_proper;
      cycle 1; [apply Hwitness | done].
    exists m'. split; [done |].
    exists prefix, item, suffix'.
    split; [| done].
    change (item :: suffix' ++ [item']) with ([item] ++ suffix' ++ [item']) in Heq.
    rewrite !app_assoc in Heq; apply app_inj_tail in Heq; rewrite <- !app_assoc in Heq.
    by destruct Heq as [-> _].
Qed.

(**
  Given a non-empty trace with the [trace_witnessing_equivocation_prop]erty,
  there are two disjoint possibilities concerning its last transition.

  (1) either it preserves the set of [equivocating_validators] and, in that case,
  the trace without the last transition has the
  [trace_witnessing_equivocation_prop]erty as well; or

  (2) The set of [equivocating_validators] of its destination is obtained
  by adding the sender of the message received in the transition to the
  set of [equivocating_validators] of its source, and, in that case, that message
  is not sent by any trace witnessing the source of the transition.
*)
Lemma equivocating_validators_witness_last_char
  (is s' : composite_state IM)
  (tr : list (composite_transition_item IM))
  (item : composite_transition_item IM)
  (Htr_item : finite_valid_trace_init_to PreFree is s' (tr ++ [item]))
  (Hwitness : trace_witnessing_equivocation_prop Htr_item)
  (s := finite_trace_last is tr)
  (Htr := finite_valid_trace_init_to_prefix_1 PreFree Htr_item) :
  equivocating_validators (exist _ s (valid_trace_last_pstate Htr))
    ≡@{Cv}
  equivocating_validators (exist _ s' (valid_trace_last_pstate Htr_item))
    /\ trace_witnessing_equivocation_prop Htr
    \/
    (exists m, input item = Some m /\
     exists v, sender m = Some v /\
     v ∉ equivocating_validators (exist _ s (valid_trace_last_pstate Htr)) /\
     equivocating_validators (exist _ s' (valid_trace_last_pstate Htr_item))
       ≡@{Cv}
     {[ v ]} ∪ (equivocating_validators (exist _ s (valid_trace_last_pstate Htr))) /\
     forall (is : composite_state IM) (tr : list transition_item)
        (Htr : finite_valid_trace_init_to PreFree is s tr),
        trace_witnessing_equivocation_prop Htr ->
        ~ trace_has_message (field_selector output) m tr).
Proof.
  destruct item as [l om _s' om'].
  apply finite_valid_trace_init_to_snoc in Htr_item as H_tr.
  destruct H_tr as (H_tr & Hitem & Hdestination).
  cbn in Hdestination; subst _s'.
  inversion Hitem.
  apply equivocating_validators_witness_monotonicity in Hwitness as Hincl.
  destruct (om ≫= sender) as [v |] eqn: Heq_v.
  - destruct om as [m |]; [| by inversion Heq_v]. simpl in Heq_v.
    destruct (decide
      (equivocating_validators (s ↾ valid_trace_last_pstate Htr)
        ≡ equivocating_validators (s' ↾ valid_trace_last_pstate Htr_item)))
      as [Hequiv | Hnequiv].
    + left; split; [done |].
      apply input_valid_transition_reflects_trace_witnessing_equivocation_prop;
        [| done].
      rewrite <- Hequiv.
      by apply set_equiv_subseteq, valid_state_equivocating_validators_proper.
    + right. exists m; split; [done |]. exists v; split; [done |].
      specialize (equivocating_validators_step_update _ _ _ _ _ Hitem) as Honly_v.
      assert (exists v,
        v ∈ equivocating_validators (exist _ s' (valid_trace_last_pstate Htr_item))
          /\
        v ∉ equivocating_validators (exist _ s (valid_trace_last_pstate Htr)))
        as (v'& Heqv & Hneqv).
      {
        setoid_rewrite <- elem_of_elements.
        apply Exists_exists.
        apply neg_Forall_Exists_neg; [by intro; apply elem_of_list_dec |].
        contradict Hnequiv; split.
        - intros Hx; apply Hincl.
          by eapply valid_state_equivocating_validators_proper; cycle 1.
        - rewrite <- !elem_of_elements.
          by rewrite Forall_forall in Hnequiv; apply Hnequiv.
      }
      destruct (Honly_v v') as [| [_m [Heq_m [Heq_v' Hweqv]]]];
        [by eapply valid_state_equivocating_validators_proper; cycle 1
        | by contradict Hneqv; eapply valid_state_equivocating_validators_proper; cycle 1
        |].
      apply Some_inj in Heq_m as <-.
      rewrite Heq_v in Heq_v'; apply Some_inj in Heq_v' as <-.
      split; [done |]. split; [| by subst].
      intro v'; split; intro Hv'.
      * apply elem_of_union.
        destruct (decide (v' ∈ equivocating_validators (s ↾ valid_trace_last_pstate Htr)))
          as [Hveqv | Hveqv]; [by right | left].
        apply elem_of_singleton.
        destruct (Honly_v v') as [| [_m [Heq_m [Heq_v' _]]]];
        [by eapply valid_state_equivocating_validators_proper; cycle 1
        | by contradict Hveqv; eapply valid_state_equivocating_validators_proper; cycle 1
        |].
        by apply Some_inj in Heq_m as <-; congruence.
      * by apply elem_of_union in Hv' as [Heq_v' | Hs'0]
        ; [by apply elem_of_singleton in Heq_v'; subst v' | by apply Hincl].
  - left; split.
    + subst; intro v; split; [by apply Hincl |].
      intros Hvs'.
      unshelve eapply valid_state_equivocating_validators_proper,
        input_valid_transition_receiving_no_sender_reflects_equivocating_validators;
        cycle 5; [done | done | done |..].
      by eapply valid_state_equivocating_validators_proper; cycle 1.
    + eapply input_valid_transition_reflects_trace_witnessing_equivocation_prop; [| done].
      intros v Hv.
      unshelve eapply valid_state_equivocating_validators_proper,
        input_valid_transition_receiving_no_sender_reflects_equivocating_validators;
        cycle 5; [done | done | done |..].
      by eapply valid_state_equivocating_validators_proper; cycle 1.
Qed.

(** ** Strongly witnessed equivocation

  A stronger [trace_witnessing_equivocation_prop]erty requires that any
  prefix of a trace is witnessing equivocation for its corresponding final state.
*)
Definition strong_trace_witnessing_equivocation_prop
  {is s} {tr} (Htr : finite_valid_trace_init_to PreFree is s tr) :=
    forall prefix (Hprefix : prefix `prefix_of` tr),
      trace_witnessing_equivocation_prop
        (finite_valid_trace_init_to_prefix _ Htr Hprefix).

Lemma strong_trace_witnessing_equivocation_prop_stronger
  {is s} {tr} (Htr : finite_valid_trace_init_to PreFree is s tr) :
  strong_trace_witnessing_equivocation_prop Htr ->
  trace_witnessing_equivocation_prop Htr.
Proof.
  intros Hstrong.
  unshelve eapply trace_witnessing_equivocation_prop_pi, Hstrong.
  by eexists []; rewrite app_nil_r.
Qed.

Lemma strong_trace_witnessing_equivocation_prop_pi
  (is s s' : composite_state IM) (tr : list (composite_transition_item IM))
  (Htr : finite_valid_trace_init_to PreFree is s tr)
  (Htr' : finite_valid_trace_init_to PreFree is s' tr) :
  strong_trace_witnessing_equivocation_prop Htr
    <->
  strong_trace_witnessing_equivocation_prop Htr'.
Proof.
  apply forall_proper; intro prefix.
  apply forall_proper; intro Hprefix.
  by apply trace_witnessing_equivocation_prop_pi.
Qed.

Lemma strong_trace_witnessing_equivocation_prop_prefix
  (is s : composite_state IM) (tr : list (composite_transition_item IM))
  (Htr : finite_valid_trace_init_to PreFree is s tr) :
  strong_trace_witnessing_equivocation_prop Htr ->
  forall prefix (Hprefix : prefix `prefix_of` tr),
    strong_trace_witnessing_equivocation_prop
      (finite_valid_trace_init_to_prefix _ Htr Hprefix).
Proof.
  intros Hwitness prefix His_prefix pre His_pre.
  unshelve eapply trace_witnessing_equivocation_prop_pi, Hwitness.
  by etransitivity.
Qed.

(**
  An advantage of the [strong_trace_witnessing_equivocation_prop]erty
  is that it guarantees monotonicity of [equivocating_validators] along the trace.
*)
Lemma strong_witness_equivocating_validators_prefix_monotonicity
  (is s : composite_state IM)
  (tr : list (composite_transition_item IM))
  (Htr : finite_valid_trace_init_to PreFree is s tr)
  (Hwitness : strong_trace_witnessing_equivocation_prop Htr)
  prefix
  (His_prefix : prefix `prefix_of` tr)
  (Hprefix := finite_valid_trace_init_to_prefix _ Htr His_prefix)
  (ps := finite_trace_last is prefix) :
  equivocating_validators (exist _ ps (valid_trace_last_pstate Hprefix))
    ⊆
  equivocating_validators (exist _ s (valid_trace_last_pstate Htr)).
Proof.
  revert s Htr Hwitness prefix His_prefix Hprefix ps.
  induction tr using rev_ind; intros.
  - destruct Htr as [Htr Hinit]; inversion Htr; subst.
    apply prefix_nil_inv in His_prefix as Heq_prefix; subst.
    by apply set_equiv_subseteq, valid_state_equivocating_validators_proper.
  - apply finite_valid_trace_init_to_snoc in Htr as Htrx.
    destruct Htrx as [H_tr Hx].
    assert (Hwitness_tr : strong_trace_witnessing_equivocation_prop H_tr).
    {
      intros pre Hpre.
      unshelve eapply trace_witnessing_equivocation_prop_pi, Hwitness.
      by apply prefix_app_r.
    }
    destruct (Datatypes.id His_prefix) as [suffix Heqtr].
    destruct_list_last suffix suffix' item Heqsuffix; subst.
    + rewrite app_nil_r in Heqtr. subst. subst ps.
      apply valid_trace_get_last in Htr as Heqs; subst.
      by apply set_equiv_subseteq, valid_state_equivocating_validators_proper.
    + rewrite app_assoc in Heqtr. apply app_inj_tail in Heqtr as [-> ->].
      intros v Hv.
      eapply equivocating_validators_witness_monotonicity;
        [by apply strong_trace_witnessing_equivocation_prop_stronger |].
      eapply valid_state_equivocating_validators_proper; cycle 1;
        [unshelve eapply (IHtr _ _ Hwitness_tr prefix); [by eexists |] | done].
      by eapply valid_state_equivocating_validators_proper; cycle 1.
Qed.

(**
  The next two lemmas show that the [strong_trace_witnessing_equivocation_prop]erty
  is preserved by transitions in both the cases yielded by Lemma
  [equivocating_validators_witness_last_char] as part of the induction step in
  the proof of Lemma [preloaded_has_strong_trace_witnessing_equivocation_prop].
*)
Lemma strong_trace_witnessing_equivocation_prop_extend_eq
  s is tr' (Htr' : finite_valid_trace_init_to PreFree is s tr')
  item (Hitem : input_valid_transition_item PreFree s item)
  (Htr'_item := finite_valid_trace_init_to_snoc_rev _ Htr' Hitem)
  is' tr'' (Htr'' : finite_valid_trace_init_to PreFree is' s tr'')
  (Htr''_item := finite_valid_trace_init_to_snoc_rev _ Htr'' Hitem)
  (Hprefix : strong_trace_witnessing_equivocation_prop Htr'')
  (Hwitness : trace_witnessing_equivocation_prop Htr'_item)
  (Heq :
    equivocating_validators (exist _ s (valid_trace_last_pstate Htr'))
      ≡@{Cv}
    equivocating_validators (exist _ (destination item) (input_valid_transition_destination _ Hitem)))
  : strong_trace_witnessing_equivocation_prop Htr''_item.
Proof.
  intros prefix His_prefix.
  destruct (Datatypes.id His_prefix) as [suffix Heq_tr''_item].
  destruct_list_last suffix suffix' sitem Hsuffix_eq.
  - rewrite app_nil_r in Heq_tr''_item; subst.
    intro v.
    specialize (Hprefix tr'').
    split.
    + intros Hv.
      eapply valid_state_equivocating_validators_proper
        with (x := destination item ↾ input_valid_transition_destination PreFree Hitem),
        Heq in Hv;
        [| by symmetry; apply finite_trace_last_is_last].
      unshelve eapply valid_state_equivocating_validators_proper, Hprefix in Hv
        as (m & Hmsg & Heqv);
        [by exists []; rewrite app_nil_r | | by apply (valid_trace_get_last Htr'')].
      exists m. split; [done |].
      by apply equivocation_in_trace_prefix.
    + intros (m & Hmsg & Heqv).
      apply equivocation_in_trace_last_char in Heqv.
      destruct Heqv as [Heqv | Heqv].
      * eapply valid_state_equivocating_validators_proper
          with (x := destination item ↾ input_valid_transition_destination PreFree Hitem);
          [by unfold equiv, valid_state_equiv; cbn; rewrite finite_trace_last_is_last |].
        apply Heq.
        unshelve eapply valid_state_equivocating_validators_proper, Hprefix;
          [by exists []; rewrite app_nil_r | by symmetry; apply (valid_trace_get_last Htr'') |].
        by exists m.
      * destruct Heqv as [Heq_om Heqv].
        assert (Heqv' : ~ trace_has_message (field_selector output) m tr').
        { intro Heqv'. elim Heqv.
          apply valid_trace_last_pstate in Htr' as Htr'_lst.
          destruct
            (has_been_sent_consistency Free
              _ Htr'_lst m)
            as [Hconsistency _].
          spec Hconsistency; [by exists is, tr', Htr' |].
          by specialize (Hconsistency is' tr'' Htr'').
        }
        eapply valid_state_equivocating_validators_proper, Hwitness;
          [by apply finite_trace_last_is_last |].
        subst. exists m. split; [done |].
        by eexists tr', _, [].
  - rewrite app_assoc in Heq_tr''_item. apply app_inj_tail in Heq_tr''_item.
    destruct Heq_tr''_item as [Heq_tr'' Heq_item].
    by unshelve eapply trace_witnessing_equivocation_prop_pi, Hprefix; eexists.
Qed.

Lemma strong_trace_witnessing_equivocation_prop_extend_neq
  s is tr (Htr : finite_valid_trace_init_to PreFree is s tr)
  (Hprefix : strong_trace_witnessing_equivocation_prop Htr)
  item (Hitem : input_valid_transition_item PreFree s item)
  msg
  (Hmsg : input item = Some msg)
  (Hwneq : ¬ trace_has_message (field_selector output) msg tr)
  v
  (Hsender : sender msg = Some v)
  (Hneq :
    equivocating_validators (exist _ (destination item) (input_valid_transition_destination _ Hitem))
      ≡@{Cv}
    {[ v ]} ∪ (equivocating_validators (exist _ s (valid_trace_last_pstate Htr)))) :
  strong_trace_witnessing_equivocation_prop
    (finite_valid_trace_init_to_snoc_rev PreFree Htr Hitem).
Proof.
  intros prefix His_prefix.
  destruct (Datatypes.id His_prefix) as [suffix Heq_tr''_item].
  destruct_list_last suffix suffix' sitem Hsuffix_eq.
  - rewrite app_nil_r in Heq_tr''_item; subst.
    intro v'; split.
    + intros Hv'.
      eapply valid_state_equivocating_validators_proper, Hneq in Hv';
        [| by symmetry; apply finite_trace_last_is_last].
      rewrite elem_of_union, elem_of_singleton in Hv'.
      destruct Hv' as [-> | Hv'].
      * exists msg. split; [done |].
        by eexists tr, _, [].
      * unshelve eapply valid_state_equivocating_validators_proper, Hprefix
          in Hv' as (m & ? & Heqv);
          [| by exists []; rewrite app_nil_r | | by apply valid_trace_get_last in Htr as Hlst].
        exists m. split; [done |].
        by apply equivocation_in_trace_prefix.
    + intros (m & ? & Heqv).
      apply equivocation_in_trace_last_char in Heqv.
      eapply valid_state_equivocating_validators_proper, Hneq;
        [by apply finite_trace_last_is_last |].
      rewrite elem_of_union, elem_of_singleton.
      destruct Heqv as [Heqv | Heqv].
      * right.
        unshelve eapply valid_state_equivocating_validators_proper, Hprefix;
          [ | by exists []; rewrite app_nil_r | by symmetry; apply valid_trace_get_last in Htr as Hlst | ].
        by exists m.
      * left. destruct Heqv as [Heqv _]; rewrite Hmsg in Heqv.
        by apply Some_inj in Heqv; congruence.
  - rewrite app_assoc in Heq_tr''_item. apply app_inj_tail in Heq_tr''_item.
    destruct Heq_tr''_item as [Heq_tr'' Heq_item].
    unshelve eapply trace_witnessing_equivocation_prop_pi, Hprefix.
    by eexists.
Qed.

(**
  Proving that any state <<s>> has the [strong_trace_witnessing_equivocation_prop]erty
  proceeds via a more technical double induction over both:

  (1) the length of a trace witnessing the equivocation of <<s>>; and
  (2) the size of the set of equivocators of <<s>>.

  For the induction step we assume that the witnessing trace leading to <<s>> is
  of the form <<tr ++ [item>>. By Lemma [equivocating_validators_witness_last_char]
  we know that either <<tr>> is also a witnessing trace, in which case we can use
  the induction hypothesis via property (1), or the set of equivocators for the
  last state of <<tr>> is strictly included in that of <<s>>, allowing us to use
  the induction hypothesis via property (2).

  The conclusion then follows by the two helper lemmas above.
*)
Lemma preloaded_has_strong_trace_witnessing_equivocation_prop s
  (Hs : valid_state_prop PreFree s)
  : exists is' tr' (Htr' : finite_valid_trace_init_to PreFree is' s tr'),
    strong_trace_witnessing_equivocation_prop Htr'.
Proof.
  apply is_equivocating_tracewise_witness in Hs.
  destruct Hs as (is & tr & Htr & Hwitness).
  apply valid_trace_get_last in Htr as Hlst; subst s.
  remember (length tr) as n.
  remember
    (size (equivocating_validators
      (exist _ (finite_trace_last is tr) (valid_trace_last_pstate Htr)))) as m.
  revert m n is tr Htr Heqm Heqn Hwitness.
  pose
    (Pr m n :=
    forall is tr (Htr : finite_valid_trace_init_to PreFree is (finite_trace_last is tr) tr),
    m = size (equivocating_validators (finite_trace_last is tr ↾ valid_trace_last_pstate Htr)) ->
    n = length tr ->
    trace_witnessing_equivocation_prop Htr ->
    exists (is' : state PreFree) (tr' : list transition_item)
      (Htr' : finite_valid_trace_init_to PreFree is' (finite_trace_last is tr) tr'),
      strong_trace_witnessing_equivocation_prop Htr').
  apply (Wf_nat.lt_wf_double_ind Pr); subst Pr; cbn.
  intros m n IHm IHn. intros is tr.
  destruct_list_last tr tr' item Htr_eq.
  - subst.
    intros Htr _ _ _.
    exists is, [], Htr.
    intros prefix His_prefix.
    destruct (Datatypes.id His_prefix) as [suffix Heq_tr].
    symmetry in Heq_tr; apply app_eq_nil in Heq_tr as [-> ->].
    unshelve eapply trace_witnessing_equivocation_prop_pi, initial_state_witnessing_equivocation_prop.
    by apply Htr.
  - intros Htr'_item ? Hn Hwitness.
    apply finite_valid_trace_init_to_snoc in Htr'_item as H_tr'_item.
    destruct H_tr'_item as (Htr' & Hitem & Hdestination).

    destruct item as [l om s' om']. simpl in *.
    destruct (equivocating_validators_witness_last_char _ _ _ _ Htr'_item Hwitness)
      as [[Heq Hwitness'] | (msg & Heq_om & v & Hsender & Hnv & Hneq)].
    + specialize (IHn (length tr')).
      rewrite app_length in Hn. simpl in Hn.
      spec IHn; [lia |].
      specialize (IHn is tr' Htr').
      spec IHn.
      {
        subst m; symmetry; apply set_size_proper.
        by etransitivity; [| etransitivity; [exact Heq |]];
          apply valid_state_equivocating_validators_proper.
      }
      specialize (IHn eq_refl).
      spec IHn.
      {
        eapply trace_witnessing_equivocation_prop_pi, Hwitness'.
      }
      destruct IHn as (is' & tr'' & Htr'' & Hprefix).
      pose proof (Htr''_item := finite_valid_trace_init_to_snoc_rev PreFree Htr'' Hitem).
      rewrite finite_trace_last_is_last; cbn.
      eexists _, _, Htr''_item.
      unshelve eapply strong_trace_witnessing_equivocation_prop_pi,
        strong_trace_witnessing_equivocation_prop_extend_eq; cycle 6;
        [done | by eapply trace_witnessing_equivocation_prop_pi |..].
      * etransitivity; [done |].
        by eapply valid_state_equivocating_validators_proper,
          finite_trace_last_is_last.
      * done.
    + subst. destruct Hneq as [Hneq Hwneq].

      destruct
        (is_equivocating_tracewise_witness (finite_trace_last is tr')
          (valid_trace_last_pstate Htr'))
        as (is' & tr''& Htr'' & Hwitness').
      specialize (IHm
          (size (equivocating_validators
            (finite_trace_last is tr' ↾
              valid_trace_last_pstate
                (finite_valid_trace_init_to_prefix_1 PreFree Htr'_item))))
          (length tr'')).
      spec IHm.
      {
        replace (size (equivocating_validators (exist _ (finite_trace_last is (tr' ++ _)) _)))
          with (size ({[v]} ∪ equivocating_validators
            (finite_trace_last is tr' ↾ valid_trace_last_pstate (finite_valid_trace_init_to_prefix_1 PreFree Htr'_item)))).
        - rewrite size_union, size_singleton; [by unfold size; lia |].
          by intro v'; rewrite elem_of_singleton; intros ->.
        - rewrite <- Hneq.
          by apply set_size_proper, valid_state_equivocating_validators_proper.
      }
      specialize (IHm is' tr'' (valid_trace_add_default_last (valid_trace_forget_last Htr''))).
      apply finite_valid_trace_init_to_last in Htr'' as Htr''_lst.
      spec IHm.
      {
        by apply set_size_proper, valid_state_equivocating_validators_proper.
      }
      specialize (IHm eq_refl).
      spec IHm.
      {
        by eapply trace_witnessing_equivocation_prop_pi, Hwitness'.
      }
      destruct IHm as (is'' & tr''' & Htr''' & Hprefix).
      assert (H_tr''' : finite_valid_trace_init_to PreFree is'' (finite_trace_last is tr') tr''').
      {
        by clear -Htr''' Htr''_lst; rewrite <- Htr''_lst.
      }
      pose proof (Htr'''_item := finite_valid_trace_init_to_snoc_rev _ H_tr''' Hitem).
      eexists is'', _.
      rewrite finite_trace_last_is_last.
      exists Htr'''_item.
      unshelve eapply strong_trace_witnessing_equivocation_prop_pi,
        strong_trace_witnessing_equivocation_prop_extend_neq; cycle 5;
        [done | done | | done |..].
      * by unshelve eapply Hwneq, strong_trace_witnessing_equivocation_prop_stronger;
          [| done | eapply strong_trace_witnessing_equivocation_prop_pi].
      * etransitivity; [| etransitivity; [exact Hneq |]];
          [by symmetry; eapply valid_state_equivocating_validators_proper |].
        apply sets.union_proper; [done |].
        by symmetry; apply valid_state_equivocating_validators_proper.
      * by cbn in Htr''_lst |- *; rewrite Htr''_lst.
Qed.

(**
  A version of Lemma [preloaded_has_strong_trace_witnessing_equivocation_prop]
  guaranteeing that for any [valid_state] w.r.t. the Free composition there is
  a trace ending in that state which is valid w.r.t. the Free composition and
  it has the [strong_trace_witnessing_equivocation_prop]erty.
*)
Lemma free_has_strong_trace_witnessing_equivocation_prop s
  (Hs : valid_state_prop Free s)
  : exists is' tr' (Htr' : finite_valid_trace_init_to PreFree is' s tr'),
    finite_valid_trace_init_to Free is' s tr' /\
    strong_trace_witnessing_equivocation_prop Htr'.
Proof.
  apply (VLSM_incl_valid_state (vlsm_incl_pre_loaded_with_all_messages_vlsm Free))
    in Hs as Hpre_s.
  apply preloaded_has_strong_trace_witnessing_equivocation_prop in Hpre_s
    as (is & tr & Htr & Hwitness).
  exists is, tr, Htr; split; [| done].
  by apply (all_pre_traces_to_valid_state_are_valid_free IM).
Qed.

End sec_witnessed_equivocation_properties.

End sec_witnessed_equivocation.

(** ** Witnessed equivocation and fixed-set equivocation

  The main result of this module is that, under witnessed equivocation
  assumptions, any trace with the [strong_trace_witnessing_equivocation_prop]erty
  which is valid for the free composition (guaranteed to exist by
  Lemma [free_has_strong_trace_witnessing_equivocation_prop]) is also valid
  for the composition constrained by the [fixed_equivocation_constrained] induced
  by the [equivocating_validators] of its final state.
*)

Section sec_witnessed_equivocation_fixed_set.

Context
  {message : Type}
  `{FinSet index Ci}
  `{!finite.Finite index}
  (IM : index -> VLSM message)
  `{forall i, HasBeenSentCapability (IM i)}
  `{forall i, HasBeenReceivedCapability (IM i)}
  (threshold : R)
  `{ReachableThreshold validator Cv threshold}
  `{!finite.Finite validator}
  (A : validator -> index)
  (sender : message -> option validator)
  (Free := free_composite_vlsm IM)
  (PreFree := pre_loaded_with_all_messages_vlsm Free)
  `{!RelDecision (constrained_composite_state_is_equivocating_tracewise IM A sender)}
  (Htracewise_BasicEquivocation : BasicEquivocation (valid_state PreFree) validator Cv threshold
    := equivocation_dec_tracewise IM threshold A sender)
  `{FinSet message Cm}
  (message_dependencies : message -> Cm)
  `{!Irreflexive (msg_dep_happens_before message_dependencies)}
  `{forall i, MessageDependencies (IM i) message_dependencies}
  (Hfull : forall i, message_dependencies_full_node_condition_prop (IM i) message_dependencies)
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  (can_emit_signed : channel_authentication_prop IM A sender)
  (Hsender_safety : sender_safety_alt_prop IM A sender :=
    channel_authentication_sender_safety IM A sender can_emit_signed)
  (Free_has_sender :=
    free_composite_no_initial_valid_messages_have_sender IM A sender
      can_emit_signed no_initial_messages_in_IM)
  (equivocating_validators :=
    equivocating_validators (BasicEquivocation := Htracewise_BasicEquivocation))
  .

Existing Instance Htracewise_BasicEquivocation.

Definition equivocating_validators_indices
  {s : composite_state IM} (Hs : valid_state_prop PreFree s) : Ci :=
  fin_sets.set_map A (equivocating_validators (exist _ s Hs)).

(**
  Given the fact that the set of [equivocating_validators] can be empty,
  and the definition of the [fixed_equivocation_constraint] requires
  a non-empty set (to allow the composition of equivocators to exist),
  we default the constraint to the [composite_no_equivocation] one
  when there are no [equivocating_validators].
*)
Definition equivocating_validators_fixed_equivocation_constraint
  {s : composite_state IM} (Hs : valid_state_prop PreFree s)
  :=
  fixed_equivocation_constraint IM (equivocating_validators_indices Hs).

Lemma equivocators_can_emit_free m
  (Hmsg : valid_message_prop Free m)
  v
  (Hsender : sender m = Some v)
  sf
  (Hequivocating_v : v ∈ equivocating_validators sf)
  l s
  (Hv : composite_valid IM l (s, Some m))
  : can_emit
    (equivocators_composition_for_directly_observed IM (equivocating_validators_indices (proj2_sig sf)) s)
    m.
Proof.
  apply emitted_messages_are_valid_iff in Hmsg
    as [(_v & [_im Him] & Heqim) | Hiom]
  ; [by elim (no_initial_messages_in_IM _v _im) |].
  apply (VLSM_incl_can_emit (vlsm_incl_pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM)))
    in Hiom.
  apply can_emit_free_composite_project in Hiom as [_v Hiom].
  specialize (Hsender_safety _ _ Hsender _ Hiom) as Heq_v. simpl in Heq_v.
  subst _v.
  eapply message_dependencies_are_sufficient in Hiom.
  unfold pre_loaded_free_equivocating_vlsm_composition, free_equivocating_vlsm_composition.
  specialize
    (@lift_to_composite_generalized_preloaded_VLSM_embedding
      message (sub_index (elements (C := Ci) (fin_sets.set_map A (equivocating_validators sf)))) _
        (sub_IM IM (elements(fin_sets.set_map A (equivocating_validators sf))))
      (fun msg : message => msg ∈ message_dependencies m)
      (composite_has_been_directly_observed IM s))
    as Hproj.
  spec Hproj.
  {
    intros dm Hdm.
    destruct l as (i, li). simpl in Hv.
    apply (Hfull _ _ _ _ Hv) in Hdm.
    by exists i.
  }
  destruct sf; cbn in *.
  eapply VLSM_embedding_can_emit; [| done].
  unshelve eapply (Hproj (dexist (A v) _)).
  by apply elem_of_elements, elem_of_map_2.
Qed.

(** *** Main result of the section

  Any Free valid trace with the
  [strong_trace_witnessing_equivocation_prop]erty is also valid w.r.t. the
  composition using the [equivocating_validators_fixed_equivocation_constraint]
  induced by its final state.

  The proof proceeds by induction on the valid trace property.
  Lemmas [equivocating_validators_witness_monotonicity] and
  [fixed_equivocation_vlsm_composition_index_incl] are used to restate the
  induction hypothesis in terms of the final state after the last transition.
*)

Lemma strong_witness_has_fixed_equivocation is s tr
  (Hpre_s : valid_state_prop PreFree s)
  (Htr : finite_valid_trace_init_to Free is s tr)
  (H_tr := VLSM_incl_finite_valid_trace_init_to
    (vlsm_incl_pre_loaded_with_all_messages_vlsm Free) _ _ _ Htr)
  (Heqv : strong_trace_witnessing_equivocation_prop (Cv := Cv) IM threshold A sender H_tr)
  : finite_valid_trace_init_to (fixed_equivocation_vlsm_composition IM
      (equivocating_validators_indices Hpre_s)) is s tr.
Proof.
  revert s Hpre_s Htr H_tr Heqv.
  induction tr using rev_ind.
  - intros; destruct Htr as [Htr Hinit]; inversion Htr; subst.
    split; [| done].
    by eapply (finite_valid_trace_from_to_empty (fixed_equivocation_vlsm_composition IM _)),
      initial_state_is_valid.
  - intros.
    apply finite_valid_trace_init_to_snoc in Htr as Htrx;
      destruct Htrx as (Htr' & Hx & Hs).
    assert (Hpre_lst : valid_state_prop PreFree (finite_trace_last is tr)).
    {
      apply (VLSM_incl_valid_state (vlsm_incl_pre_loaded_with_all_messages_vlsm Free)).
      by eapply input_valid_transition_origin.
    }
    specialize (IHtr _ Hpre_lst Htr').
    cbn in IHtr. spec IHtr.
    {
      unshelve eapply strong_trace_witnessing_equivocation_prop_pi,
        strong_trace_witnessing_equivocation_prop_prefix; cycle 4; [done |..].
      by eexists.
    }
    assert (Htr_sf : finite_valid_trace_init_to
      (fixed_equivocation_vlsm_composition IM
        (equivocating_validators_indices Hpre_s))
      is (finite_trace_last is tr) tr).
    { revert IHtr.
      apply VLSM_incl_finite_valid_trace_init_to,
               fixed_equivocation_vlsm_composition_index_incl.
      apply elements_subseteq, set_map_subset.
      etransitivity; [| etransitivity]; cycle 1.
      - apply (equivocating_validators_witness_monotonicity IM threshold (Cv := Cv) A sender _ _ _ _ H_tr).
        by apply strong_trace_witnessing_equivocation_prop_stronger.
      - by apply set_equiv_subseteq, valid_state_equivocating_validators_proper.
      - by apply set_equiv_subseteq, valid_state_equivocating_validators_proper.
    }
    clear IHtr.
    subst s.
    eapply (finite_valid_trace_init_to_snoc_rev
      (fixed_equivocation_vlsm_composition IM
        (equivocating_validators_indices Hpre_s))); [done |].
    destruct Hx as [(Hs & Hiom & Hv) Ht].
    apply strong_trace_witnessing_equivocation_prop_stronger in Heqv as Heqv_tr.
    destruct x.
    apply valid_trace_last_pstate in Htr_sf as Hlst.
    destruct input as [im |]; [| by repeat split; auto using option_valid_message_None].
    apply Free_has_sender in Hiom as _Hsender.
    destruct (sender im) as [v |] eqn: Hsender; [| by congruence].
    clear _Hsender.
    specialize (Heqv_tr v); cbn in Heqv_tr.
    destruct (decide (composite_has_been_directly_observed IM (finite_trace_last is tr) im)).
    { repeat split
      ; [done | apply option_valid_message_Some | done | | done].
      - by apply (composite_directly_observed_valid IM _ (finite_trace_last is tr)).
      - by left.
    }
    assert (Hequivocating_v : v ∈ equivocating_validators (exist _ _ Hpre_s)).
    {
      eapply valid_state_equivocating_validators_proper; cycle 1;
        [apply Heqv_tr | done].
      exists im. split; [done |].
      eexists tr, _, [].
      split; [done |].
      split; [done |].
      intros Him_output.
      elim n.
      apply composite_has_been_directly_observed_sent_received_iff.
      left.
      eapply (has_been_sent_examine_one_trace (vlsm := Free)) in Him_output;
        [exact Him_output |].
      by apply (VLSM_incl_finite_valid_trace_init_to
        (vlsm_incl_pre_loaded_with_all_messages_vlsm Free)).
    }
    specialize (equivocators_can_emit_free _ Hiom _ Hsender _ Hequivocating_v  _ _ Hv) as Hemit_im.
    repeat split; [done | | done | by right | done].
    apply emitted_messages_are_valid.
    specialize
      (EquivPreloadedBase_Fixed_weak_embedding IM (Ci := Ci) _ _ (valid_trace_last_pstate Htr_sf)) as Hproj.
    spec Hproj; [by intros; apply no_initial_messages_in_IM |].
    apply (VLSM_weak_embedding_can_emit Hproj).
    by apply (VLSM_incl_can_emit (Equivocators_Fixed_Strong_incl IM _  _ (valid_trace_last_pstate Htr_sf))).
Qed.

(**
  As a corollary of the above, every valid state for the free composition is
  also a valid state for the composition with the
  [equivocating_validators_fixed_equivocation_constraint] induced by it.
*)
Lemma equivocating_validators_fixed_equivocation_characterization
  (Hke : WitnessedEquivocationCapability IM threshold A sender (Cv := Cv))
  : forall s (Hpre_s : valid_state_prop PreFree s),
    valid_state_prop Free s ->
    valid_state_prop
      (composite_vlsm IM (equivocating_validators_fixed_equivocation_constraint Hpre_s)) s.
Proof.
  intros s Hpre_s Hs.
  destruct
    (free_has_strong_trace_witnessing_equivocation_prop IM threshold A sender _ s Hs)
    as (is & tr & Hpre_tr & Htr & Heqv).
  unshelve eapply finite_valid_trace_from_to_last_pstate,
    strong_witness_has_fixed_equivocation; [| | done |].
  by eapply strong_trace_witnessing_equivocation_prop_pi.
Qed.

End sec_witnessed_equivocation_fixed_set.

