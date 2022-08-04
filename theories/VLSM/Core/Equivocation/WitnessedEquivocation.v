From stdpp Require Import prelude.
From VLSM.Lib Require Import Preamble ListExtras StdppListSet ListSetExtras.
From VLSM.Core Require Import VLSM VLSMProjections Composition.
From VLSM.Core Require Import SubProjectionTraces MessageDependencies Equivocation.
From VLSM.Core Require Import Equivocation.NoEquivocation Equivocation.FixedSetEquivocation Equivocation.TraceWiseEquivocation.

(** * Witnessed equivocation

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

We then use this result to show that any Free valid state is also a valid
state for the composition of nodes under the [fixed_equivocation_constraint]
induced by its set of equivocators.
*)
Section witnessed_equivocation.

Context
  `{EqDecision message}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  `{forall i : index, HasBeenSentCapability (IM i)}
  `{forall i : index, HasBeenReceivedCapability (IM i)}
  `{finite.Finite validator}
  (A : validator -> index)
  (sender : message -> option validator)
  (Free := free_composite_vlsm IM)
  (PreFree := pre_loaded_with_all_messages_vlsm Free)
  `{ReachableThreshold validator}
  `{RelDecision _ _ (is_equivocating_tracewise_no_has_been_sent IM A sender)}
  (Htracewise_BasicEquivocation : BasicEquivocation (composite_state IM) validator
    := equivocation_dec_tracewise IM A sender)
  (equivocating_validators := equivocating_validators (BasicEquivocation := Htracewise_BasicEquivocation))
  .

(** A trace witnesses the equivocation of its final state <<s>> if its set of
equivocators is precisely that of the [equivocating_validators] of <<s>>.
*)
Definition trace_witnessing_equivocation_prop
  is tr
  (s := finite_trace_last is tr)
  : Prop :=
  forall v, v ∈ equivocating_validators s <->
    exists (m : message), (sender m = Some v) /\ equivocation_in_trace PreFree m tr.

Lemma equivocating_senders_in_trace_witnessing_equivocation_prop
  is tr
  (Htr : trace_witnessing_equivocation_prop is tr)
  (s := finite_trace_last is tr)
  : set_eq (equivocating_validators s) (equivocating_senders_in_trace IM sender tr).
Proof.
  split; intros v Hv; [apply Htr in Hv| apply Htr].
  - by apply elem_of_equivocating_senders_in_trace.
  - by eapply elem_of_equivocating_senders_in_trace.
Qed.

(**
A composition of VLSMs has the witnessed equivocation capability if towards any
valid states there exist a trace witnessing its equivocation.
*)
Class WitnessedEquivocationCapability
  :=
  { is_equivocating_tracewise_witness :
    forall s, valid_state_prop PreFree s ->
    exists is tr, finite_valid_trace_init_to PreFree is s tr /\
      trace_witnessing_equivocation_prop is tr
  }.

Section witnessed_equivocation_properties.

Context
  (Hke : WitnessedEquivocationCapability)
  (Hsender_safety : sender_safety_alt_prop IM A sender)
  .

Lemma initial_state_witnessing_equivocation_prop
  s
  (Hs : composite_initial_state_prop IM s)
  : trace_witnessing_equivocation_prop s [].
Proof.
  specialize (equivocating_validators_empty_in_initial_state IM A sender s Hs) as Hempty.
  intros v.
  unfold finite_trace_last. simpl.
  replace (equivocating_validators s) with (@nil validator).
  simpl.
  split; [inversion 1|].
  intros [m [_ Hmsg]].
  by elim (no_equivocation_in_empty_trace PreFree m).
Qed.

(** For any trace having the [trace_witnessing_equivocation_prop]erty,
its final transition is monotonic w.r.t. the [equivocating_validators].
*)
Lemma equivocating_validators_witness_monotonicity
  (is s : composite_state IM)
  (tr : list (composite_transition_item IM))
  (Htr : finite_valid_trace_init_to PreFree is s tr)
  (item : composite_transition_item IM)
  (Hwitness : trace_witnessing_equivocation_prop is (tr ++ [item]))
  (s' := destination item)
  : equivocating_validators s ⊆ equivocating_validators s'.
Proof.
  intros v Hv.
  specialize (Hwitness v).
  rewrite finite_trace_last_is_last in Hwitness.
  apply Hwitness.
  apply equivocating_validators_is_equivocating_tracewise_iff in Hv.
  specialize (Hv _ _ Htr) as [m [Hmsg Heqv]].
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
  (is s: composite_state IM)
  (tr: list (composite_transition_item IM))
  (Htr: finite_valid_trace_init_to PreFree is s tr)
  (item : composite_transition_item IM)
  (Hwitness : trace_witnessing_equivocation_prop is (tr ++ [item]))
  (s' := destination item)
  (Hincl : equivocating_validators s' ⊆ equivocating_validators s)
  : trace_witnessing_equivocation_prop is tr.
Proof.
  apply finite_valid_trace_init_to_last in Htr as Hlst.
  intros v; split; simpl in *; rewrite Hlst in *.
  - by intros Hv; eapply equivocating_validators_is_equivocating_tracewise_iff.
  - intros (msg & Hsender & Heqv).
    apply Hincl.
    spec Hwitness v;
    rewrite finite_trace_last_is_last in Hwitness;
    apply Hwitness.
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
    : v ∈ equivocating_validators s' ->
      v ∈ equivocating_validators s \/
      (exists m, om = Some m /\
      sender m = Some v /\
      forall is tr
      (Htr : finite_valid_trace_init_to PreFree is s tr)
      (Hwitness : trace_witnessing_equivocation_prop is tr),
      ~ trace_has_message (field_selector output) m tr).
Proof.
  intro Hv.
  destruct (decide (v ∈ equivocating_validators s))
    as [e | Hnv]
  ; [by left |].
  right. apply equivocating_validators_is_equivocating_tracewise_iff in Hv.
  destruct (transition_is_equivocating_tracewise_char IM A sender  _ _ _ _ _ Ht _ Hv)
    as [| Hom]
  ; [by elim Hnv; apply (equivocating_validators_is_equivocating_tracewise_iff IM A sender) |].
  destruct om as [m|]; simpl in Hom; [|congruence].
  exists m. repeat split; [done |].
  intros is tr [Htr Hinit] Hwitness.
  specialize (extend_right_finite_trace_from_to _ Htr Ht) as Htr'.
  specialize (Hv _ _ (conj Htr' Hinit)).
  destruct Hv as [m' [Hm' [prefix [item [suffix [Heq Heqv]]]]]].
  destruct_list_last suffix suffix' item' Heqsuffix.
  - apply app_inj_tail in Heq. destruct Heq; subst.
    simpl in Heqv. destruct Heqv as [Heq_m Heqv].
    by inversion Heq_m.
  - elim Hnv.
    spec Hwitness v.
    apply finite_valid_trace_from_to_last in Htr as Hs.
    simpl in Hs, Hwitness. rewrite Hs in Hwitness.
    apply Hwitness. exists m'. split; [done |].
    exists prefix, item, suffix'.
    split; [| done].
    change (item :: suffix' ++ [item'])
      with ([item] ++ suffix' ++ [item']) in Heq.
    rewrite !app_assoc in Heq.
    apply app_inj_tail in Heq. rewrite <- !app_assoc in Heq. apply Heq.
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
  (is : composite_state IM)
  (tr : list (composite_transition_item IM))
  (l : composite_label IM)
  (om : option message)
  (s' : composite_state IM)
  (om' : option message)
  (item  := {| l := l; input := om; destination := s'; output := om' |})
  (Htr_item : finite_valid_trace_init_to PreFree is s' (tr ++ [item]))
  (Hwitness : trace_witnessing_equivocation_prop is (tr ++ [item]))
  (s := finite_trace_last is tr)
  : set_eq (equivocating_validators s) (equivocating_validators s')
    /\ trace_witnessing_equivocation_prop is tr
    \/
    (exists m, om = Some m /\
     exists v, sender m = Some v /\
     v ∉ equivocating_validators s /\
     set_eq (equivocating_validators s') (set_add v (equivocating_validators s)) /\
     forall (is : composite_state IM) (tr : list transition_item),
        finite_valid_trace_init_to PreFree is s tr ->
        trace_witnessing_equivocation_prop is tr ->
        ~ trace_has_message (field_selector output) m tr
    ).
Proof.
  destruct Htr_item as [Htr Hinit].
  apply finite_valid_trace_from_to_app_split in Htr.
  destruct Htr as [Htr Hitem].
  inversion_clear Hitem. clear Htl. subst s.
  apply equivocating_validators_witness_monotonicity with (s := (finite_trace_last is tr))
    in Hwitness as Hincl
  ; [| by split].
  specialize (input_valid_transition_receiving_no_sender_reflects_equivocating_validators IM A sender _ _ _  _ _ Ht)
    as Hreflect.
  remember (finite_trace_last is tr) as s.
  destruct (option_bind _ _ sender om) as [v|] eqn:Heq_v.
  - destruct om as [m|]; [|inversion Heq_v]. simpl in Heq_v.
    destruct (decide (set_eq (equivocating_validators s) (equivocating_validators s')))
    ; [left;split; [done |]|].
    + apply
        (input_valid_transition_reflects_trace_witnessing_equivocation_prop
          _ _ _ (conj Htr Hinit) _ Hwitness).
      subst. apply s0.
    + right. exists m; split; [done |]. exists v. split; [done |].
      specialize (equivocating_validators_step_update _ _ _ _ _ Ht) as Honly_v.
      simpl in Honly_v.
      assert (Hv : exists v, v ∈ equivocating_validators s' /\ v ∉ equivocating_validators s).
      { apply Exists_exists.
        apply neg_Forall_Exists_neg; [intro; apply elem_of_list_dec|].
        intro all. elim n.
        split; [done |].
        by rewrite Forall_forall in all.
      }
      destruct Hv as [v' [Heqv Hneqv]].
      apply Honly_v in Heqv as Heq_v'.
      destruct Heq_v' as [|[_m [Heq_m [Heq_v' Hweqv]]]]; [by subst |].
      inversion Heq_m. subst _m. clear Heq_m.
      assert (v' = v) by congruence. subst v'. clear Heq_v'.
      split; [done |]. split; [| by subst].
      split; intros v' Hv'.
      * destruct (decide (v' ∈ equivocating_validators s))
        ; [by apply set_add_intro1 |].
        apply set_add_intro2.
        apply Honly_v in Hv'.
        destruct Hv' as [|[_m [Heq_m [Heq_v' _]]]]; [by subst |].
        congruence.
      * apply set_add_elim in Hv' as [Heq_v' | Hs'0]
        ; [by subst v' | by apply Hincl].
  - specialize (Hreflect eq_refl).
    left. split.
    + by subst.
    + apply
      (input_valid_transition_reflects_trace_witnessing_equivocation_prop
        _ _ _ (conj Htr Hinit) _ Hwitness
      ).
    apply Hreflect.
Qed.

(** ** Strongly witnessed equivocation *)

(** A stronger [trace_witnessing_equivocation_prop]erty requires that any
prefix of a trace is witnessing equivocation for its corresponding final state.
*)
Definition strong_trace_witnessing_equivocation_prop is tr :=
    forall prefix suffix, prefix ++ suffix = tr ->
      trace_witnessing_equivocation_prop is prefix.

(** An advantage of the [strong_trace_witnessing_equivocation_prop]erty
is that it guarantees monotonicity of [equivocating_validators] along the trace.
*)
Lemma strong_witness_equivocating_validators_prefix_monotonicity
  (is s : composite_state IM)
  (tr : list (composite_transition_item IM))
  (Htr : finite_valid_trace_init_to PreFree is s tr)
  (Hwitness : strong_trace_witnessing_equivocation_prop is tr)
  prefix suffix
  (Heqtr : prefix ++ suffix = tr)
  (ps := finite_trace_last is prefix)
  : equivocating_validators ps ⊆ equivocating_validators s.
Proof.
  revert prefix suffix Heqtr ps.
  induction Htr using finite_valid_trace_init_to_rev_ind; intros.
  - by apply app_eq_nil in Heqtr as []; subst.
  - remember {| input := iom |} as item.
    spec IHHtr.
    { intros pre suf Heq.
      specialize (Hwitness pre (suf ++ [item])).
      apply Hwitness.
      subst. apply app_assoc.
    }
    destruct_list_last suffix suffix' _item Heqsuffix.
    + rewrite app_nil_r in Heqtr. subst. subst ps.
      by rewrite finite_trace_last_is_last.
    + rewrite app_assoc in Heqtr. apply app_inj_tail in Heqtr.
      destruct Heqtr as [Heqtr Heq_item]. subst _item.
      specialize (IHHtr _ _ Heqtr).
      transitivity (equivocating_validators s)
      ; [done |].
      specialize (Hwitness (tr ++ [item]) []).
      spec Hwitness. { apply app_nil_r. }
      replace sf with (destination item) by (subst; done).
      apply (equivocating_validators_witness_monotonicity _ _ _ Htr _ Hwitness).
Qed.

(**
The next two lemmas show that the [strong_trace_witnessing_equivocation_prop]erty
is preserved by transitions in both the cases yielded by Lemma
[equivocating_validators_witness_last_char] as part of the induction step in
the proof of Lemma [preloaded_has_strong_trace_witnessing_equivocation_prop].
*)
Lemma strong_trace_witnessing_equivocation_prop_extend_eq
  s
  is tr'
  (Htr': finite_valid_trace_init_to PreFree is s tr')
  is' tr''
  (Htr'': finite_valid_trace_init_to PreFree is' s tr'')
  (Hprefix : strong_trace_witnessing_equivocation_prop is' tr'')
  item
  (Hwitness : trace_witnessing_equivocation_prop is (tr' ++ [item]))
  (Heq: set_eq (equivocating_validators s) (equivocating_validators (destination item)))
  : strong_trace_witnessing_equivocation_prop is' (tr'' ++ [item]).
Proof.
  intros prefix suffix Heq_tr''_item.
  destruct_list_last suffix suffix' sitem Hsuffix_eq.
  - rewrite app_nil_r in Heq_tr''_item.
    subst.
    intro v. rewrite finite_trace_last_is_last.
    specialize (Hprefix tr'' []).
    spec Hprefix; [apply app_nil_r|].
    apply valid_trace_get_last in Htr'' as Hlst'.
    split.
    + intros Hv. apply Heq in Hv.
      rewrite <- Hlst' in Hv.
      apply Hprefix in Hv.
      destruct Hv as [m [Hmsg Heqv]].
      exists m. split; [done |].
      by apply equivocation_in_trace_prefix.
    + intros [m [Hmsg Heqv]].
      apply equivocation_in_trace_last_char in Heqv.
      destruct Heqv as [Heqv | Heqv].
      * apply Heq. rewrite <- Hlst'.
        apply Hprefix.
        by exists m.
      * destruct Heqv as [Heq_om Heqv].
        assert (Heqv' : ~ trace_has_message (field_selector output) m tr').
        { intro Heqv'. elim Heqv.
          apply valid_trace_last_pstate in Htr' as Htr'_lst.
          destruct
            (has_been_sent_consistency Free
              _ Htr'_lst m
            ) as [Hconsistency _].
          spec Hconsistency; [by exists is, tr', Htr' |].
          by spec Hconsistency is' tr'' Htr''.
        }
        spec Hwitness v.
        rewrite finite_trace_last_is_last in Hwitness.
        simpl in Hwitness.
        apply Hwitness.
        subst. exists m. split; [done |].
        by eexists tr', _, [].
  - rewrite app_assoc in Heq_tr''_item. apply app_inj_tail in Heq_tr''_item.
    destruct Heq_tr''_item as [Heq_tr'' Heq_item].
    apply (Hprefix _ _ Heq_tr'').
Qed.

Lemma strong_trace_witnessing_equivocation_prop_extend_neq
  s
  is tr
  (Htr: finite_valid_trace_init_to PreFree is s tr)
  (Hprefix : strong_trace_witnessing_equivocation_prop is tr)
  item
  msg
  (Hmsg : input item = Some msg)
  (Hwneq: ¬ trace_has_message (field_selector output) msg tr)
  v
  (Hsender: sender msg = Some v)
  (Hneq: set_eq (equivocating_validators (destination item)) (set_add v (equivocating_validators s)))
  : strong_trace_witnessing_equivocation_prop is (tr ++ [item]).
Proof.
  intros prefix suffix Heq_tr''_item.
  destruct_list_last suffix suffix' sitem Hsuffix_eq.
  - rewrite app_nil_r in Heq_tr''_item.
    subst prefix suffix.
    intro v'. rewrite finite_trace_last_is_last. simpl.
    specialize (Hprefix tr []).
    spec Hprefix; [apply app_nil_r|].
    apply valid_trace_get_last in Htr as Hlst'.
    split.
    + intros Hv'. apply Hneq in Hv'.
      apply set_add_iff in Hv'.
      rewrite <- Hlst' in Hv'.
      destruct Hv' as [Heq_v | Hv'].
      * subst.
        exists msg. split; [done |].
        by eexists tr, _, [].
      * apply Hprefix in Hv'.
        destruct Hv' as [m [? Heqv]].
        exists m. split; [done |].
        by apply equivocation_in_trace_prefix.
    + intros [m [? Heqv]].
      apply equivocation_in_trace_last_char in Heqv.
      apply Hneq. apply set_add_iff.
      destruct Heqv as [Heqv | Heqv].
      * rewrite <- Hlst'.
        right.
        apply Hprefix.
        by exists m.
      * left. simpl in Heqv.
        destruct Heqv as [Heq_om Heqv].
        congruence.
  - rewrite app_assoc in Heq_tr''_item. apply app_inj_tail in Heq_tr''_item.
    destruct Heq_tr''_item as [Heq_tr'' Heq_item].
    apply (Hprefix _ _ Heq_tr'').
Qed.

(** Proving that any state <<s>> has the [strong_trace_witnessing_equivocation_prop]erty
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
  : exists is' tr',
    finite_valid_trace_init_to PreFree is' s tr' /\
    strong_trace_witnessing_equivocation_prop is' tr'.
Proof.
  apply is_equivocating_tracewise_witness in Hs.
  destruct Hs as [is [tr [Htr Hwitness]]].
  apply finite_valid_trace_init_to_last in Htr as Hlst.
  subst s.
  apply finite_valid_trace_init_to_forget_last in Htr.
  remember (length tr) as n.
  remember (length (equivocating_validators (finite_trace_last is tr))) as m.
  revert m n is tr Heqm Heqn Htr Hwitness.
  pose
    (fun m n =>
    forall is tr,
    m = length (equivocating_validators (finite_trace_last is tr)) ->
    n = length tr ->
    finite_valid_trace PreFree is tr ->
    trace_witnessing_equivocation_prop is tr ->
    let s := finite_trace_last is tr in
    exists (is' : state) (tr' : list transition_item),
      finite_valid_trace_init_to PreFree is' s tr' /\
      (forall prefix suffix : list transition_item,
       prefix ++ suffix = tr' ->
       trace_witnessing_equivocation_prop is' prefix))
    as Pr.
  apply (Wf_nat.lt_wf_double_ind Pr).
  intros m n IHm IHn. intros is tr.
  destruct_list_last tr tr' item Htr_eq.
  - subst.
    intros _ _ Htr _.
    exists is, [].
    split.
    + by apply finite_valid_trace_init_add_last.
    + intros prefix suffix Heq_tr.
      apply app_eq_nil  in Heq_tr. destruct Heq_tr. subst.
      apply initial_state_witnessing_equivocation_prop. apply Htr.
  - rewrite finite_trace_last_is_last.
    intros ? Hn Htr'_item Hwitness.
    apply finite_valid_trace_init_add_last
      with (sf := destination item)
      in Htr'_item
    ; [|apply finite_trace_last_is_last].
    destruct item as [l om s' om']. simpl in *.
    destruct
      (equivocating_validators_witness_last_char _ _ _ _ _ _ Htr'_item Hwitness)
      as [[Heq Hwitness'] | [msg [Heq_om [v [Hsender [Hnv Hneq]]]]]].
    + spec IHn (length tr').
      rewrite app_length in Hn. simpl in Hn.
      spec IHn; [lia|].
      spec IHn is tr'.
      specialize (NoDup_subseteq_length (equivocating_validators_nodup s') (proj2 Heq))
        as Hlen1.
      match type of Hlen1 with
      | _ <= length (equivocating_validators ?st) =>
        pose st as s
      end.
      specialize (NoDup_subseteq_length (equivocating_validators_nodup s) (proj1 Heq))
        as Hlen2.
      spec IHn ; [by subst s m; apply Nat.le_antisymm |].
      specialize (IHn eq_refl).
      destruct Htr'_item as [Htr'_item Hinit].
      apply finite_valid_trace_from_to_app_split in Htr'_item.
      destruct Htr'_item as [Htr' Hitem].
      spec IHn.
      { split; [| done].
        by apply finite_valid_trace_from_to_forget_last in Htr'.
      }
      spec IHn Hwitness'.
      destruct IHn as [is' [tr'' [[Htr'' Hinit'] Hprefix]]].
      specialize
        (finite_valid_trace_from_to_app PreFree _ _ _ _ _ Htr'' Hitem)
        as Htr''_item.
      eexists is', _.
      split; [done |].
      apply (strong_trace_witnessing_equivocation_prop_extend_eq _ is tr' (conj Htr' Hinit))
      ; [by split | done..].
    + subst. destruct Hneq as [Hneq Hwneq].
      match type of Hnv with
      | _ ∉ equivocating_validators ?st =>
        remember st as s
      end.
      specialize (is_equivocating_tracewise_witness s) as Hwitness'.
      spec Hwitness'.
      { apply proj1, finite_valid_trace_from_to_app_split, proj1
          , finite_valid_trace_from_to_last_pstate
          in Htr'_item.
        by subst.
      }
      destruct Hwitness' as [is' [tr''[Htr'' Hwitness']]].
      spec IHm (length (equivocating_validators s)) (length tr'').
      spec IHm.
      {
        assert (Hnodup_v_s : NoDup (set_add v (equivocating_validators s))).
        { apply set_add_nodup. apply equivocating_validators_nodup.
        }
        specialize (NoDup_subseteq_length Hnodup_v_s (proj2 Hneq))
          as Hlen1.
        by rewrite <- set_add_length in Hlen1.
      }
      spec IHm is' tr''.
      apply finite_valid_trace_init_to_last in Htr'' as Htr''_lst.
      simpl in *.
      rewrite Htr''_lst in IHm.
      specialize (IHm eq_refl eq_refl).
      spec IHm.
      { by apply finite_valid_trace_init_to_forget_last in Htr''. }
      spec IHm Hwitness'.
      destruct IHm as [is'' [tr''' [[Htr''' Hinit'] Hprefix]]].
      apply proj1, finite_valid_trace_from_to_app_split, proj2 in Htr'_item as Hitem.
      simpl in *.
      rewrite <- Heqs in Hitem.
      specialize
        (finite_valid_trace_from_to_app PreFree _ _ _ _ _ Htr''' Hitem)
        as Htr'''_item.
      eexists is'', _.
      split; [done |].
      specialize (Hprefix tr''' []) as Hwitness'''.
      spec Hwitness'''; [apply app_nil_r|].
      specialize (Hwneq _ _ (conj Htr''' Hinit') Hwitness''').
      remember {| input := Some msg |} as item.
      specialize
        (strong_trace_witnessing_equivocation_prop_extend_neq _ _ _ (conj Htr''' Hinit') Hprefix item msg)
        as Hextend.
      spec Hextend; [by subst |].
      specialize (Hextend Hwneq _ Hsender).
      by apply Hextend; subst.
Qed.

(** A version of Lemma [preloaded_has_strong_trace_witnessing_equivocation_prop]
guaranteeing that for any [valid_state] w.r.t. the Free composition there is
a trace ending in that state which is valid w.r.t. the Free composition and
it has the [strong_trace_witnessing_equivocation_prop]erty.
*)
Lemma free_has_strong_trace_witnessing_equivocation_prop s
  (Hs : valid_state_prop Free s)
  : exists is' tr',
    finite_valid_trace_init_to Free is' s tr' /\
    strong_trace_witnessing_equivocation_prop is' tr'.
Proof.
  apply (VLSM_incl_valid_state (vlsm_incl_pre_loaded_with_all_messages_vlsm Free))
    in Hs as Hpre_s.
  apply preloaded_has_strong_trace_witnessing_equivocation_prop in Hpre_s.
  destruct Hpre_s as [is [tr [Htr Hwitness]]].
  apply (all_pre_traces_to_valid_state_are_valid IM) in Htr
  ; [| done].
  by exists is, tr.
Qed.

End witnessed_equivocation_properties.

End witnessed_equivocation.

(** ** Witnessed equivocation and fixed-set equivocation

The main result of this module is that, under witnessed equivocation
assumptions, any trace with the [strong_trace_witnessing_equivocation_prop]erty
which is valid for the free composition (guaranteed to exist by
Lemma [free_has_strong_trace_witnessing_equivocation_prop]) is also valid
for the composition constrained by the [fixed_equivocation_constrained] induced
by the [equivocating_validators] of its final state.
*)
Section witnessed_equivocation_fixed_set.

Context
  `{EqDecision message}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  `{forall i, HasBeenSentCapability (IM i)}
  `{forall i, HasBeenReceivedCapability (IM i)}
  (Free := free_composite_vlsm IM)
  (sender : message -> option index)
  `{ReachableThreshold index}
  `{RelDecision _ _ (is_equivocating_tracewise_no_has_been_sent IM id sender)}
  (Htracewise_BasicEquivocation : BasicEquivocation (composite_state IM) index
    := equivocation_dec_tracewise IM id sender)
  (Hke : WitnessedEquivocationCapability IM id sender)
  (message_dependencies : message -> set message)
  `{!Irreflexive (msg_dep_happens_before message_dependencies)}
  `{forall i, MessageDependencies (IM i) message_dependencies}
  (Hfull : forall i, message_dependencies_full_node_condition_prop (IM i) message_dependencies)
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  (can_emit_signed : channel_authentication_prop IM id sender)
  (Hsender_safety : sender_safety_alt_prop IM id sender :=
    channel_authentication_sender_safety IM id sender can_emit_signed)
  (Free_has_sender :=
    composite_no_initial_valid_messages_have_sender IM id sender
      can_emit_signed no_initial_messages_in_IM (free_constraint IM))
  (equivocating_validators := equivocating_validators (BasicEquivocation := Htracewise_BasicEquivocation))
  .

Existing Instance Htracewise_BasicEquivocation.

(**
Given the fact that the set of [equivocating_validators] can be empty,
and the definition of the [fixed_equivocation_constraint] requires
a non-empty set (to allow the composition of equivocators to exist),
we default the constraint to the [composite_no_equivocation] one
when there are no [equivocating_validators].
*)
Definition equivocating_validators_fixed_equivocation_constraint
  (s : composite_state IM)
  :=
  fixed_equivocation_constraint IM (equivocating_validators s).

Lemma equivocators_can_emit_free m
  (Hmsg : valid_message_prop Free m)
  v
  (Hsender: sender m = Some v)
  sf
  (Hequivocating_v: v ∈ equivocating_validators sf)
  l s
  (Hv : composite_valid IM l (s, Some m))
  : can_emit
    (equivocators_composition_for_directly_observed IM (equivocating_validators sf) s)
    m.
Proof.
    apply emitted_messages_are_valid_iff in Hmsg
      as [(_v & [_im Him] & Heqim) | Hiom]
    ; [by elim (no_initial_messages_in_IM _v _im) |].
    apply (VLSM_incl_can_emit (vlsm_incl_pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM)))
      in Hiom.
    apply can_emit_composite_project in Hiom as [_v Hiom].
    specialize (Hsender_safety _ _ Hsender _ Hiom) as Heq_v. simpl in Heq_v.
    subst _v.
    eapply message_dependencies_are_sufficient in Hiom.
    unfold pre_loaded_free_equivocating_vlsm_composition, free_equivocating_vlsm_composition.
      specialize
        (@lift_to_composite_generalized_preloaded_vlsm_full_projection
          message (sub_index (equivocating_validators sf)) _ (sub_IM IM (equivocating_validators sf))
          (λ msg : message, msg ∈ message_dependencies m)
          (composite_has_been_directly_observed IM s))
        as Hproj.
      spec Hproj.
      { intros dm Hdm.
        destruct l as (i, li). simpl in Hv.
        apply (Hfull _ _ _ _ Hv) in Hdm.
        by exists i.
      }
      spec Hproj (@dexist _ _ (fun v => sub_index_prop_dec (equivocating_validators sf) v) v Hequivocating_v).
      by apply (VLSM_full_projection_can_emit Hproj).
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
  (Htr : finite_valid_trace_init_to (free_composite_vlsm IM) is s tr)
  (Heqv: strong_trace_witnessing_equivocation_prop IM id sender is tr)
  : finite_valid_trace_init_to (fixed_equivocation_vlsm_composition IM (equivocating_validators s)) is s tr.
Proof.
  split; [|apply Htr].
  induction Htr using finite_valid_trace_init_to_rev_ind.
  - eapply (finite_valid_trace_from_to_empty (fixed_equivocation_vlsm_composition IM (equivocating_validators si))).
    by apply initial_state_is_valid.
  - spec IHHtr.
    { intros prefix. intros.
      apply (Heqv prefix (suffix ++  [{| l := l; input := iom; destination := sf; output := oom |}])).
      subst. apply app_assoc.
    }
    apply (VLSM_incl_finite_valid_trace_init_to (vlsm_incl_pre_loaded_with_all_messages_vlsm Free))
      in Htr as Hpre_tr.
    specialize
      (equivocating_validators_witness_monotonicity IM id sender
        _ _ _ Hpre_tr {| l := l; input := iom; destination := sf; output := oom |})
      as Hincl.
    simpl in Hincl.
    spec Hincl.
    { specialize
        (Heqv (tr ++ [{| l := l; input := iom; destination := sf; output := oom |}]) []) .
      rewrite app_nil_r in Heqv.
      by apply Heqv.
    }
    assert
      (Htr_sf : finite_valid_trace_from_to
        (fixed_equivocation_vlsm_composition IM (equivocating_validators sf)) si s tr).
    { revert IHHtr.
      by apply VLSM_incl_finite_valid_trace_from_to,
               fixed_equivocation_vlsm_composition_index_incl.
    }
    clear IHHtr.
    apply (extend_right_finite_trace_from_to _ Htr_sf).
    destruct Ht as [[Hs [Hiom [Hv _]]] Ht].
    apply finite_valid_trace_from_to_last_pstate in Htr_sf as Hs'.
    specialize
      (Heqv
        (tr ++ [{| l := l; input := iom; destination := sf; output := oom |}])
        []).
    spec Heqv; [apply app_nil_r|].
    destruct iom as [im|].
    2:{
      repeat split
      ; [done | apply option_valid_message_None | done..].
    }
    apply Free_has_sender in Hiom as _Hsender.
    destruct (sender im) as [v|] eqn:Hsender; [|congruence].
    clear _Hsender.
    spec Heqv v.
    rewrite finite_trace_last_is_last in Heqv.
    simpl in Heqv.
    assert (Hpre_s : valid_state_prop (pre_loaded_with_all_messages_vlsm Free) s).
    { by apply proj1, finite_valid_trace_from_to_last_pstate in Hpre_tr. }
    destruct (@decide _ (composite_has_been_directly_observed_dec IM s im)).
    { repeat split
      ; [done | apply option_valid_message_Some | done | | done].
      - by apply (composite_directly_observed_valid IM _ s).
      - by left.
    }
    assert (Hequivocating_v : v ∈ equivocating_validators sf).
    { apply Heqv. exists im. split; [done |].
      eexists tr, _, [].
      split; [done |].
      split; [done |].
      intros Him_output.
      elim n.
      apply composite_has_been_directly_observed_sent_received_iff.
      left.
      specialize (proper_sent Free _ Hpre_s im) as Hsent_s.
      apply proj2 in Hsent_s. apply Hsent_s. clear Hsent_s.
      apply (has_been_sent_consistency Free _ Hpre_s im).
      by exists si, tr, Hpre_tr.
    }
    specialize (equivocators_can_emit_free _ Hiom _ Hsender _ Hequivocating_v  _ _ Hv) as Hemit_im.
    repeat split
    ; [done |  | done | by right | done].
    apply emitted_messages_are_valid.
    specialize
      (EquivPreloadedBase_Fixed_weak_full_projection IM _ _ Hs') as Hproj.
    spec Hproj.
    { intros.  apply no_initial_messages_in_IM. }
    apply (VLSM_weak_full_projection_can_emit Hproj).
    by apply (VLSM_incl_can_emit (Equivocators_Fixed_Strong_incl IM _  _ Hs')).
Qed.

(**
As a corollary of the above, every valid state for the free composition is
also a valid state for the composition with the
[equivocating_validators_fixed_equivocation_constraint] induced by it.
*)
Lemma equivocating_validators_fixed_equivocation_characterization
  : forall s,
    valid_state_prop Free s ->
    valid_state_prop
      (composite_vlsm IM (equivocating_validators_fixed_equivocation_constraint s)) s.
Proof.
  intros s Hs.
  destruct
    (free_has_strong_trace_witnessing_equivocation_prop IM id sender _ s Hs)
    as [is [tr [Htr Heqv]]].
  cut (finite_valid_trace_from_to (composite_vlsm IM (equivocating_validators_fixed_equivocation_constraint s)) is s tr).
  { by intro Htr'; apply finite_valid_trace_from_to_last_pstate in Htr'. }
  by apply strong_witness_has_fixed_equivocation.
Qed.

End witnessed_equivocation_fixed_set.
