From stdpp Require Import prelude.
From Coq Require Import Reals.
From VLSM.Lib Require Import Preamble ListExtras StdppListSet ListSetExtras.

(** * Measure-related definitions and lemmas *)

Definition pos_R := {r : R | (r > 0)%R}.

Class Measurable V := { weight : V -> pos_R}.
#[global] Hint Mode Measurable ! : typeclass_instances.

Definition sum_weights `{Measurable V} (l : list V) : R :=
  fold_right (fun v r => (proj1_sig (weight v) + r)%R) 0%R l.

Lemma sum_weights_positive
  `{Measurable V} (l : list V)
  : (0 <= sum_weights l)%R.
Proof.
  induction l; try apply Rle_refl.
  simpl. apply Rplus_le_le_0_compat; [| done].
  destruct (weight a); cbn.
  by apply Rlt_le.
Qed.

Definition weight_proj1_sig (w : pos_R) : R := proj1_sig w.

Coercion weight_proj1_sig : pos_R >-> R.

Lemma sum_weights_in
  `{EqDecision V} `{Hm : Measurable V}
  : forall v (vs:list V),
  NoDup vs ->
  v ∈ vs ->
  sum_weights vs = (proj1_sig (weight v) + sum_weights (set_remove v vs))%R.
Proof.
  induction vs; intros; inversion H0; subst; clear H0.
  - inversion H; subst; clear H. simpl. apply Rplus_eq_compat_l.
    by rewrite decide_True.
  - inversion H; subst; clear H. simpl.
    pose proof (in_not_in _ _ _ _ H3 H2).
    rewrite decide_False; [| done]. simpl.
    rewrite <- Rplus_assoc. rewrite (Rplus_comm (proj1_sig (weight v)) (proj1_sig (weight a))). rewrite Rplus_assoc.
    by apply Rplus_eq_compat_l, IHvs.
Qed.

Lemma sum_weights_subseteq
  `{EqDecision V} `{Hm : Measurable V}
  : forall (vs vs':list V),
  NoDup vs ->
  NoDup vs' ->
  vs ⊆ vs' ->
  (sum_weights vs <= sum_weights vs')%R.
Proof.
  induction vs; intros; try apply sum_weights_positive.
  specialize (sum_weights_in a vs' H0) as Hvs'.
  spec Hvs'; [by apply H1; left |].
  rewrite Hvs'. simpl.
  apply Rplus_le_compat_l.
  inversion H. subst.  clear H.
  apply IHvs; [done | |].
  - by apply set_remove_nodup.
  - intros v Hv. apply set_remove_iff; [done |].
    split.
    + by apply H1; right.
    + by intros ->.
Qed.

Lemma set_eq_nodup_sum_weight_eq
  `{EqDecision V} `{Hm : Measurable V}
  : forall (lv1 lv2 : list V),
    NoDup lv1 ->
    NoDup lv2 ->
    set_eq lv1 lv2 ->
    sum_weights lv1 = sum_weights lv2.
Proof.
  intros lv1 lv2 H_nodup1 H_nodup2 [H_eq_l H_eq_r].
  by apply Rle_antisym; apply sum_weights_subseteq.
Qed.

Lemma sum_weights_app
  `{Hm : Measurable V}
  : forall (vs vs':list V),
  sum_weights (vs ++ vs') = (sum_weights vs + sum_weights vs')%R.
Proof.
  induction vs; intros; simpl.
  - by rewrite Rplus_0_l.
  - by rewrite IHvs, Rplus_assoc.
Qed.
