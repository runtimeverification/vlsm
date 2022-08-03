From Coq Require Import Reals RelationClasses.
From stdpp Require Import prelude.

(** * Real number utility lemmas *)

(** This lemma is needed in fault_weight_state_sorted_subset **)
Lemma Rplus_opp_l : forall r, (Ropp r + r)%R = 0%R.
Proof.
  intros.
  rewrite Rplus_comm.
  apply Rplus_opp_r.
Qed.

Lemma Rtotal_le_gt : forall x y,
  (x <= y)%R \/ (x > y)%R.
Proof.
  unfold Rle. intros x y.
  destruct (Rtotal_order x y) as [Hlt | [Heq | Hgt]]; auto.
Qed.

#[global] Instance Rle_transitive : Transitive Rle.
Proof.
  intros x y z.
  apply Rle_trans.
Qed.
