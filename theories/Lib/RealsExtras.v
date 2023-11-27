From Coq Require Import Reals.
From stdpp Require Import prelude.

(** * Utility: Real Number Definitions and Results *)

#[export] Instance Rle_transitive : Transitive Rle.
Proof.
  by intros x y z; apply Rle_trans.
Qed.
