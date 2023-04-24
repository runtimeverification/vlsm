From Coq Require Import Reals.
From stdpp Require Import prelude.

(** * Real number utility definitions and lemmas *)

#[export] Instance Rle_transitive : Transitive Rle.
Proof.
  by intros x y z; apply Rle_trans.
Qed.
