From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From VLSM.Lib Require Import Preamble.

(** * Finite set utility definitions and lemmas *)

Section fin_set.

Context
  `{FinSet A C}.

Section general.

Lemma union_size_ge_size1
  (X Y : C) :
  size (X ∪ Y) >= size X.
Proof.
  apply subseteq_size.
  apply subseteq_union.
  set_solver.
Qed.

Lemma union_size_ge_size2
  (X Y : C) :
  size (X ∪ Y) >= size Y.
Proof.
  apply subseteq_size.
  apply subseteq_union.
  set_solver.
Qed.

Lemma union_size_ge_average
  (X Y : C) :
  2 * size (X ∪ Y) >= size X + size Y.
Proof.
  pose (union_size_ge_size1 X Y) as Hx.
  pose (union_size_ge_size2 X Y) as Hy.
  lia.
Qed.

Lemma difference_size_le_self
  (X Y : C) :
  size (X ∖  Y) <= size X.
Proof.
  apply subseteq_size.
  apply elem_of_subseteq.
  intros x Hx.
  apply elem_of_difference in Hx. itauto.
Qed.

Lemma union_size_le_sum
  (X Y : C) :
  size (X ∪ Y) <= size X + size Y.
Proof.
  rewrite (size_union_alt X Y).
  pose (difference_size_le_self Y X).
  lia.
Qed.

Lemma intersection_size1
  (X Y : C) :
  size (X ∩ Y) <= size X.
Proof.
  apply (subseteq_size (X ∩ Y) X).
  set_solver.
Qed.

Lemma intersection_size2
  (X Y : C) :
  size (X ∩ Y) <= size Y.
Proof.
  apply (subseteq_size (X ∩ Y) Y).
  set_solver.
Qed.

Lemma union_difference_r_sub :
  forall X Y : C,
    Y ⊆ X -> Y ∪ (X ∖ Y) ≡ X.
Proof.
  intros; apply set_equiv_equivalence; intros a.
  split; intros Ha; [set_solver |].
  destruct (@decide (a ∈ Y)).
  - apply elem_of_dec_slow.
  - apply elem_of_union. left. itauto.
  - apply elem_of_union. right. set_solver.
Qed.

Lemma size_difference_sub :
  forall X Y : C,
    Y ⊆ X -> size Y + size (X ∖ Y) = size X.
Proof.
  intros X Y Hsub.
  pose (size_union Y (X ∖ Y)) as Hun.
  rewrite (union_difference_r_sub X Y Hsub) in Hun.
  symmetry; apply Hun.
  rewrite elem_of_disjoint; setoid_rewrite elem_of_difference.
  itauto.
Qed.

Lemma difference_size_subset
  (X Y : C)
  (Hsub : Y ⊆ X) :
  (Z.of_nat (size (X ∖ Y)) = Z.of_nat (size X) - Z.of_nat (size Y))%Z.
Proof.
  pose (size_difference_sub X Y Hsub).
  lia.
Qed.

Lemma difference_with_intersection
  (X Y : C) :
  X ∖ Y ≡ X ∖ (X ∩ Y).
Proof.
  set_solver.
Qed.

Lemma difference_size
  (X Y : C) :
  (Z.of_nat (size (X ∖ Y)) = Z.of_nat (size X) - Z.of_nat (size (X ∩ Y)))%Z.
Proof.
  by rewrite difference_with_intersection, (difference_size_subset X (X ∩ Y)); [| set_solver].
Qed.

Lemma difference_size_ge_disjoint_case
  (X Y : C) :
  size (X ∖ Y) >= size X - size Y.
Proof.
  pose (difference_size X Y).
  pose (intersection_size2 X Y).
  lia.
Qed.

Lemma list_to_set_size
  (l : list A) :
  size (list_to_set l (C := C)) <= length l.
Proof.
  induction l; cbn.
  - by rewrite size_empty.
  - etransitivity.
    + apply union_size_le_sum.
    + by rewrite size_singleton; lia.
Qed.

End general.

Section filter.

Context
  (P P2 : A → Prop)
  `{!∀ x, Decision (P x)}
  `{!∀ x, Decision (P2 x)}
  (X Y : C).

Lemma filter_subset
  (Hsub : X ⊆ Y) :
  filter P X ⊆ filter P Y.
Proof.
  intros a HaX.
  apply elem_of_filter in HaX.
  apply elem_of_filter.
  set_solver.
Qed.

Lemma filter_subprop
  (Hsub : forall a, (P a -> P2 a)) :
  filter P X ⊆ filter P2 X.
Proof.
  intros a HaP.
  apply elem_of_filter in HaP.
  apply elem_of_filter.
  itauto.
Qed.

End filter.

End fin_set.

Section map.

Context
  `{FinSet A C}
  `{FinSet B D}.

Lemma set_map_subset
  (f : A -> B)
  (X Y : C)
  (Hsub : X ⊆ Y) :
  set_map (D := D) f X ⊆ set_map (D := D) f Y.
Proof.
  intros a Ha.
  apply elem_of_map in Ha.
  apply elem_of_map.
  firstorder.
Qed.

Lemma set_map_size_upper_bound
  (f : A -> B)
  (X : C) :
  size (set_map (D := D) f X) <= size X.
Proof.
  unfold set_map.
  remember (f <$> elements X) as fX.
  set (x := size (list_to_set _)).
  cut (x <= length fX); [|by apply list_to_set_size].
  enough (length fX = size X) by lia.
  unfold size, set_size.
  simpl; subst fX.
  by apply fmap_length.
Qed.

End map.
