From stdpp Require Import prelude.
From Coq Require Import Reals Lra.
From VLSM.Lib Require Import Preamble ListExtras StdppListSet ListSetExtras StdppListFinSet.

(** * Measure-related definitions and lemmas *)

Definition pos_R := {r : R | (r > 0)%R}.

Class Measurable (V : Type) : Type :=
{
  weight : V -> pos_R;
}.

#[global] Hint Mode Measurable ! : typeclass_instances.

Section sec_measurable_props.

Context
  `{Measurable V}
  `{FinSet V Cv}
  .

Definition sum_weights (l : Cv) : R :=
  set_fold (fun v r => (proj1_sig (weight v) + r)%R) 0%R l.

Definition sum_weights_list (vs : list V) :=
  fold_right (fun v r => (proj1_sig (weight v) + r)%R) 0%R vs.

Lemma sum_weights_list_rew (l : Cv) :
  sum_weights l = sum_weights_list (elements l).
Proof. done. Qed.

Lemma sum_weights_empty :
  forall (l : Cv), l ≡ ∅ -> sum_weights l = 0%R.
Proof.
  intros l Hl.
  unfold sum_weights, set_fold; cbn.
  by apply elements_empty_iff in Hl as ->.
Qed.

Lemma sum_weights_positive_list (l : list V) :
  (0 <= sum_weights_list l)%R.
Proof.
  induction l; try apply Rle_refl.
  simpl. apply Rplus_le_le_0_compat; [| done].
  destruct (weight a); cbn.
  by apply Rlt_le.
Qed.

Lemma sum_weights_positive (l : Cv) :
  (0 <= sum_weights l)%R.
Proof.
  rewrite sum_weights_list_rew.
  by apply sum_weights_positive_list.
Qed.

Definition weight_proj1_sig (w : pos_R) : R := proj1_sig w.

Coercion weight_proj1_sig : pos_R >-> R.

Lemma sum_weights_in_list
  : forall (v : V) (vs : list V),
  NoDup vs ->
  v ∈ vs ->
  sum_weights_list vs
  = (proj1_sig (weight v) +
  sum_weights_list (StdppListSet.set_remove v vs))%R.
Proof.
  induction vs; cbn; intros Hnodup Hv **; inversion Hv as [| ? ? ? Hv']; subst; clear Hv.
  - inversion Hnodup; subst; clear Hnodup.
    apply Rplus_eq_compat_l.
    by rewrite decide_True.
  - inversion Hnodup as [|? ? Ha Hnodup']; subst; clear Hnodup.
    pose proof (in_not_in _ _ _ _ Hv' Ha).
    rewrite decide_False; cbn; [| done].
    rewrite <- Rplus_assoc, (Rplus_comm (proj1_sig (weight v))), Rplus_assoc.
    by apply Rplus_eq_compat_l, IHvs.
Qed.

Lemma sum_weights_subseteq_list
  : forall (vs vs' : list V),
  NoDup vs ->
  NoDup vs' ->
  vs ⊆ vs' ->
  (sum_weights_list vs <= sum_weights_list vs')%R.
Proof.
  induction vs; intros vs' Hnodup_vs Hnodup_vs' Hincl;
    [by apply sum_weights_positive_list |].
  pose proof (Hvs' := sum_weights_in_list a vs' Hnodup_vs').
  spec Hvs'; [by apply Hincl; left |].
  rewrite Hvs'; cbn.
  apply Rplus_le_compat_l.
  inversion Hnodup_vs; subst; clear Hnodup_vs.
  apply IHvs; [done | by apply set_remove_nodup |].
  intros v Hv.
  apply StdppListSet.set_remove_iff; [done |].
  split.
  + by apply Hincl; right.
  + by intros ->.
Qed.

Lemma sum_weights_subseteq
  : forall (vs vs' : Cv),
  vs ⊆ vs' ->
  (sum_weights vs <= sum_weights vs')%R.
Proof.
  intros vs vs' Hincl.
  rewrite !sum_weights_list_rew.
  apply sum_weights_subseteq_list.
  - by apply NoDup_elements.
  - by apply NoDup_elements.
  - by intro v; rewrite !elem_of_elements; apply Hincl.
Qed.

Lemma sum_weights_proper : Proper (equiv ==> eq) sum_weights.
Proof.
  intros x y Hequiv.
  by apply Rle_antisym; apply sum_weights_subseteq; intro a; apply Hequiv.
Qed.

Lemma sum_weights_in :
  forall v (vs : Cv),
    v ∈ vs -> sum_weights vs = (proj1_sig (weight v) + sum_weights (set_remove v vs))%R.
Proof.
  intros v vs Hv.
  rewrite sum_weights_list_rew, sum_weights_in_list with (v := v); cycle 1.
  - by apply NoDup_elements.
  - by apply elem_of_elements.
  - apply Rplus_eq_compat_l, Rle_antisym; apply sum_weights_subseteq_list.
    + by apply set_remove_nodup, NoDup_elements.
    + by apply NoDup_elements.
    + intros x Hx.
      rewrite elem_of_elements.
      apply set_remove_iff.
      apply StdppListSet.set_remove_iff in Hx; [| by apply NoDup_elements].
      by rewrite elem_of_elements in Hx.
    + by apply NoDup_elements.
    + by apply set_remove_nodup, NoDup_elements.
    + intros x Hx.
      rewrite elem_of_elements in Hx.
      apply StdppListSet.set_remove_iff; [by apply NoDup_elements |].
      apply set_remove_iff in Hx.
      by rewrite elem_of_elements.
Qed.

Lemma sum_weights_app_list
  : forall (vs vs' : list V),
  sum_weights_list (vs ++ vs') = (sum_weights_list vs + sum_weights_list vs')%R.
Proof. by induction vs; intros; simpl; [| rewrite IHvs]; lra. Qed.

#[export] Instance sum_weights_list_permutation_proper :
  Proper ((≡ₚ) ==> (=)) sum_weights_list.
Proof.
  intros l1 l2 Hl.
  apply foldr_permutation_proper with (=) (λ (v : V) (r : R), (`(weight v) + r)%R) 0%R in Hl;
    [done | typeclasses eauto | by intros v x y -> |].
  by intros; lra.
Qed.

Lemma sum_weights_disj_union :
  forall (vs vs' : Cv),
    vs ## vs' ->
    sum_weights (vs ∪ vs') = (sum_weights vs + sum_weights vs')%R.
Proof.
  intros vs vs' Hdisj.
  apply elements_disj_union, sum_weights_list_permutation_proper in Hdisj.
  setoid_rewrite Hdisj.
  by apply sum_weights_app_list.
Qed.

Lemma sum_weights_union_empty (vs : Cv) :
  sum_weights (vs ∪ ∅) = sum_weights vs.
Proof.
  rewrite sum_weights_disj_union by apply disjoint_empty_r.
  by rewrite (sum_weights_empty ∅); [lra |].
Qed.

End sec_measurable_props.
