Require Import stdpp.prelude.

(** * Finite type utility definitions and lemmas *)

Fixpoint up_to_n_listing
  (n : nat)
  : list nat
  :=
  match n with
  | 0 => []
  | S n' => n' :: up_to_n_listing n'
  end.

Lemma up_to_n_full
  (n : nat)
  : forall i, i < n <-> i ∈ up_to_n_listing n.
Proof.
  induction n; split; inversion 1; subst; cbn; [left | | lia |].
  - by right; apply IHn.
  - by transitivity n; [apply IHn | lia].
Qed.
