From VLSM.Lib Require Import Itauto.
From Coq Require Import FunctionalExtensionality.
From stdpp Require Import prelude.
From VLSM.Lib Require Import Preamble ListExtras.
From VLSM.Core Require Import VLSM PreloadedVLSM Composition.

(** * HistoryVLSMs *)

Class HistoryVLSM `(X : VLSM message) : Prop :=
{
  not_valid_transition_next_initial :
    forall s2, initial_state_prop X s2 ->
    forall s1, ~ valid_transition_next X s1 s2;
  unique_transition_to_state :
    forall [s : state X],
    forall [l1 s1 iom1 oom1], valid_transition X l1 s1 iom1 s oom1 ->
    forall [l2 s2 iom2 oom2], valid_transition X l2 s2 iom2 s oom2 ->
    l1 = l2 /\ s1 = s2 /\ iom1 = iom2 /\ oom1 = oom2;
}.

#[global] Hint Mode HistoryVLSM - ! : typeclass_instances.

Section sec_history_vlsm_pre_loaded.

Context
  `{HistoryVLSM message X}
  .

#[export] Instance preloaded_history_vlsm :
  HistoryVLSM (pre_loaded_with_all_messages_vlsm X).
Proof.
  split; intros.
  - rewrite <- valid_transition_next_preloaded_iff.
    by apply not_valid_transition_next_initial.
  - by eapply (@unique_transition_to_state _ X);
      [| apply valid_transition_preloaded_iff..].
Qed.

Lemma history_unique_trace_to_reachable :
  forall is s tr,
    finite_valid_trace_init_to (pre_loaded_with_all_messages_vlsm X) is s tr ->
  forall is' tr',
    finite_valid_trace_init_to (pre_loaded_with_all_messages_vlsm X) is' s tr' ->
      is' = is /\ tr' = tr.
Proof.
  intros is s tr Htr; induction Htr using finite_valid_trace_init_to_rev_ind;
    intros is' tr' [Htr' His'].
  - destruct_list_last tr' tr'' item Heqtr'; [by inversion Htr' | subst].
    apply finite_valid_trace_from_to_app_split in Htr' as [_ Hitem].
    inversion Hitem; inversion Htl; subst.
    destruct Ht as [(_ & _ & Hv) Ht].
    exfalso; clear His'; eapply @not_valid_transition_next_initial;
      [| done | by esplit].
    by typeclasses eauto.
  - destruct_list_last tr' tr'' item Heqtr'; subst tr'.
    + inversion Htr'; subst; clear Htr'.
      destruct Ht as [(_ & _ & Hv) Ht].
      exfalso; eapply @not_valid_transition_next_initial; [| done | by esplit].
      by typeclasses eauto.
    + apply finite_valid_trace_from_to_app_split in Htr' as [Htr' Hitem].
      inversion Hitem; inversion Htl; subst; clear Hitem Htl.
      apply input_valid_transition_forget_input in Ht, Ht0.
      specialize (unique_transition_to_state Ht Ht0) as Heqs.
      destruct_and! Heqs; subst.
      specialize (IHHtr _ _  (conj Htr' His')).
      by destruct_and! IHHtr; subst.
Qed.

End sec_history_vlsm_pre_loaded.

Section sec_history_vlsm_composite.

Context
  {message : Type}
  `{EqDecision index}
  (IM : index -> VLSM message)
  `{forall i : index, HistoryVLSM (IM i)}
  (Free := free_composite_vlsm IM)
  (RFree := pre_loaded_with_all_messages_vlsm Free)
  .

Lemma not_composite_valid_transition_next_initial :
  forall s2, composite_initial_state_prop IM s2 ->
  forall s1, ~ composite_valid_transition_next IM s1 s2.
Proof.
  intros s2 Hs2 s1 [* Hs1].
  apply composite_valid_transition_projection, proj1, transition_next in Hs1; cbn in Hs1.
  by contradict Hs1; apply not_valid_transition_next_initial, Hs2.
Qed.

Lemma composite_quasi_unique_transition_to_state :
  forall [s],
  forall [l1 s1 iom1 oom1], composite_valid_transition IM l1 s1 iom1 s oom1 ->
  forall [l2 s2 iom2 oom2], composite_valid_transition IM l2 s2 iom2 s oom2 ->
  projT1 l1 = projT1 l2 ->
  l1 = l2 /\ s1 = s2 /\ iom1 = iom2 /\ oom1 = oom2.
Proof.
  intros ? [i li1] * Ht1 [_i li2] * Ht2 [=]; subst _i.
  apply composite_valid_transition_projection in Ht1, Ht2; cbn in Ht1, Ht2.
  destruct Ht1 as [Ht1 Heq_s], Ht2 as [Ht2 Heqs].
  rewrite Heq_s in Heqs at 1; clear Heq_s.
  specialize (unique_transition_to_state Ht1 Ht2) as Heq;
    destruct_and! Heq; subst; repeat split.
  extensionality j.
  destruct (decide (i = j)); subst; [done |].
  apply f_equal with (f := fun s => s j) in Heqs.
  by state_update_simpl.
Qed.

Lemma composite_valid_transition_reflects_rechability :
  forall l s1 iom s2 oom,
  composite_valid_transition IM l s1 iom s2 oom ->
  valid_state_prop RFree s2 ->
  input_valid_transition RFree l (s1, iom) (s2, oom).
Proof.
  intros * Hnext Hs2; revert l s1 iom oom Hnext.
  induction Hs2 using valid_state_prop_ind; intros * Hnext.
  - apply transition_next in Hnext.
    by contradict Hnext; apply not_composite_valid_transition_next_initial.
  - destruct l as [i li], l0 as [j lj].
    destruct (decide (i = j)).
    + subst; apply input_valid_transition_forget_input in Ht as Hvt.
      apply composite_valid_transition_reachable_iff in Hvt.
      specialize (composite_quasi_unique_transition_to_state Hnext Hvt eq_refl) as Heq.
      by destruct_and! Heq; simplify_eq.
    + apply input_valid_transition_forget_input in Ht as Hti.
      apply composite_valid_transition_reachable_iff,
        composite_valid_transition_projection in Hti;
        cbn in Hti; destruct Hti as [[Hvi Hti] Heqs'].
      apply composite_valid_transition_projection in Hnext;
        cbn in Hnext; destruct Hnext as [[Hvj Htj] Heq_s'].
      rewrite Heq_s' in Heqs'; state_update_simpl.
      specialize (IHHs2 (existT j lj) (state_update IM s j (s1 j)) iom oom).
      spec IHHs2.
      {
        apply composite_valid_transition_projection_inv with (s1 j) (s' j); [done | |].
        - by state_update_simpl.
        - rewrite state_update_twice.
          symmetry; apply state_update_id.
          apply f_equal with (f := fun s => s j) in Heqs'.
          by state_update_simpl.
      }
      assert (Hss1 : input_valid_transition RFree (existT i li)
                  (state_update IM s j (s1 j), om) (s1, om')).
      {
        repeat split; [by apply IHHs2 | by apply any_message_is_valid_in_preloaded | ..]
        ; cbn; state_update_simpl; [done |].
        replace (transition _ _ _) with (s' i, om').
        f_equal; extensionality k; apply f_equal with (f := fun s => s k) in Heqs'.
        rewrite Heq_s'.
        by destruct (decide (i = k)), (decide (j = k)); subst; state_update_simpl.
      }
      repeat split; cbn.
      * by eapply input_valid_transition_destination.
      * by apply any_message_is_valid_in_preloaded.
      * done.
      * by replace (transition _ _ _) with (s' j, oom); f_equal.
Qed.

Lemma composite_valid_transition_next_reflects_rechability :
  forall s1 s2, composite_valid_transition_next IM s1 s2 ->
    valid_state_prop RFree s2 -> valid_state_prop RFree s1.
Proof.
  by intros s1 s2 []; eapply composite_valid_transition_reflects_rechability.
Qed.

Lemma composite_valid_transition_future_reflects_rechability :
  forall s1 s2, composite_valid_transition_future IM s1 s2 ->
    valid_state_prop RFree s2 -> valid_state_prop RFree s1.
Proof. by apply tc_reflect, composite_valid_transition_next_reflects_rechability. Qed.

Lemma composite_valid_transitions_from_to_reflects_reachability :
  forall s s' tr,
  composite_valid_transitions_from_to IM s s' tr ->
  valid_state_prop RFree s' -> finite_valid_trace_from_to RFree s s' tr.
Proof.
  induction 1; intros; [by constructor |].
  assert (Hitem : input_valid_transition RFree (l item) (s', input item)
                          (destination item, output item))
    by (apply composite_valid_transition_reflects_rechability; done).
  eapply finite_valid_trace_from_to_app.
  - apply IHcomposite_valid_transitions_from_to.
    by eapply input_valid_transition_origin.
  - by destruct item; apply finite_valid_trace_from_to_singleton.
Qed.

End sec_history_vlsm_composite.
