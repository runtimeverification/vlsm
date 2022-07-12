From stdpp Require Import prelude.

(** * Finite type utility definitions and lemmas *)

Fixpoint up_to_n_listing
  (n : nat)
  : list nat
  :=
  match n with
  | 0 => []
  | S n' => n' :: up_to_n_listing n'
  end.

Lemma up_to_n_listing_length
  (n : nat)
  : length (up_to_n_listing n) = n.
Proof.
  induction n; simpl; congruence.
Qed.

Lemma up_to_n_full
  (n : nat)
  : forall i, i < n <-> i ∈ up_to_n_listing n.
Proof.
  induction n; intro i; split; intro Hi; [inversion Hi | inversion Hi |..].
  - destruct (decide (n <= i)).
    + by replace n with i by lia; left.
    + right; apply IHn; lia.
  - inversion Hi; subst; [lia |].
    transitivity n; [by apply IHn | lia].
Qed.
