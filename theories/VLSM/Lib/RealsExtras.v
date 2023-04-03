From Coq Require Import Reals.
From stdpp Require Import prelude.

Set Default Proof Using "Type".

(** * Real number utility definitions and lemmas *)

(** Sum a list of real numbers. *)
Definition list_sum_R : list R -> R :=
  foldr Rplus 0%R.

Lemma Rplusminus_assoc : forall r1 r2 r3,
  (r1 + r2 - r3)%R = (r1 + (r2 - r3))%R.
Proof.
  by intros; unfold Rminus; apply Rplus_assoc.
Qed.

Lemma Rplusminus_assoc_r : forall r1 r2 r3,
  (r1 - r2 + r3)%R = (r1 + (- r2 + r3))%R.
Proof.
  by intros; unfold Rminus; apply Rplus_assoc.
Qed.

Lemma Rplus_opp_l : forall r, (Ropp r + r)%R = 0%R.
Proof.
  by intros; rewrite Rplus_comm, Rplus_opp_r.
Qed.

Lemma Rplus_ge_reg_neg_r : forall r1 r2 r3,
  (r2 <= 0)%R -> (r3 <= r1 + r2)%R -> (r3 <= r1)%R.
Proof.
  intros.
  apply Rge_le.
  eapply Rplus_ge_reg_neg_r.
  - by apply Rle_ge in H.
  - by apply Rle_ge in H0.
Qed.

Lemma Rminus_lt_r : forall r1 r2,
  (0 <= r2)%R -> (r1 - r2 <= r1)%R.
Proof.
  intros.
  rewrite <- Rplus_0_r.
  unfold Rminus.
  by apply Rplus_le_compat_l, Rge_le, Ropp_0_le_ge_contravar.
Qed.

Lemma Rminus_lt_r_strict : forall r1 r2,
  (0 < r2)%R -> (r1 - r2 <= r1)%R.
Proof.
  intros.
  rewrite <- Rplus_0_r.
  unfold Rminus.
  by apply Rplus_le_compat_l, Rge_le, Ropp_0_le_ge_contravar, Rlt_le.
Qed.

Lemma Rtotal_le_gt : forall x y,
  (x <= y)%R \/ (x > y)%R.
Proof.
  unfold Rle. intros x y.
  by destruct (Rtotal_order x y) as [Hlt | [Heq | Hgt]]; auto.
Qed.

#[export] Instance Rle_transitive : Transitive Rle.
Proof.
  by intros x y z; apply Rle_trans.
Qed.
