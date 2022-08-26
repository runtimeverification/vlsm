From stdpp Require Import prelude finite.
From Coq Require Import FinFun.
From VLSM.Lib Require Import Preamble ListExtras StdppExtras.

(** * Finite function utility definitions and lemmas *)

Lemma listing_from_finite (A : Type) `{finite.Finite A} : Listing (enum A).
Proof.
  constructor.
  - apply NoDup_ListNoDup, NoDup_enum.
  - intro a. apply elem_of_list_In, elem_of_enum.
Qed.

Lemma map_option_listing
      {A B : Type} (f: A -> option B) (g: B -> A)
      (f_proj_inj: forall a b, f a = Some b -> a = g b)
      (f_surj: forall b, f (g b) = Some b)
      (A_listing: list A) (A_finite : Listing A_listing) : Listing (map_option f A_listing).
Proof.
  destruct A_finite as [Hnodup Hfull].
  split.
  - clear Hfull.
    induction A_listing as [|a l IHl].
    + constructor.
    + inversion_clear Hnodup as [| ? ? H1 H2]; cbn.
      destruct (f a) eqn: Hfa; [| by apply IHl].
      apply f_proj_inj in Hfa; subst a.
      constructor; [| by apply IHl].
      contradict H1.
      apply in_map_option in H1.
      destruct H1 as [a [Ha Hfa]].
      apply f_proj_inj in Hfa.
      by subst a.
  - intro b.
    apply in_map_option.
    exists (g b).
    split; [done |].
    apply f_surj.
Qed.

Section sum_listing.
(** 'Listing' for the sum type implies 'Listing' for each projection *)

Context
  {Left Right : Type}
  {sum_listing : list (Left + Right)}
  .

Definition left_listing
  (sum_finite : Listing sum_listing)
  : list Left
  := list_sum_project_left sum_listing.

Definition right_listing
  (sum_finite : Listing sum_listing)
  : list Right
  := list_sum_project_right sum_listing.

Lemma left_finite
  (sum_finite : Listing sum_listing)
  : Listing (left_listing sum_finite).
Proof.
  revert sum_finite.
  apply map_option_listing with (g:=inl); [| done].
  by destruct a;simpl;congruence.
Qed.

Lemma right_finite
  (sum_finite : Listing sum_listing)
  : Listing (right_listing sum_finite).
Proof.
  revert sum_finite.
  apply map_option_listing with (g:=inr); [| done].
  by destruct a;simpl;congruence.
Qed.

End sum_listing.
