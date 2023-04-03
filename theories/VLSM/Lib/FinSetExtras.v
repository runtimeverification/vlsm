From VLSM.Lib Require Import Itauto.
From stdpp Require Import prelude.
From VLSM.Lib Require Import Preamble.

Set Default Proof Using "Type".

(** * Finite set utility definitions and lemmas *)

Section sec_fin_set.

Context
  `{FinSet A C}.

Section sec_general.

Lemma elements_subseteq (X Y : C) :
  X ⊆ Y -> elements X ⊆ elements Y.
Proof using H6 H4 H3 H2 H1 H0 EqDecision0. by set_solver. Qed.

Lemma union_size_ge_size1
  (X Y : C) :
  size (X ∪ Y) >= size X.
Proof using H6 H4 H3 H1 H0 H EqDecision0.
  apply subseteq_size.
  apply subseteq_union.
  by set_solver.
Qed.

Lemma union_size_ge_size2
  (X Y : C) :
  size (X ∪ Y) >= size Y.
Proof using H6 H4 H3 H1 H0 H EqDecision0.
  apply subseteq_size.
  apply subseteq_union.
  by set_solver.
Qed.

Lemma union_size_ge_average
  (X Y : C) :
  2 * size (X ∪ Y) >= size X + size Y.
Proof using H6 H4 H3 H1 H0 H EqDecision0.
  specialize (union_size_ge_size1 X Y) as Hx.
  specialize (union_size_ge_size2 X Y) as Hy.
  by lia.
Qed.

Lemma difference_size_le_self
  (X Y : C) :
  size (X ∖  Y) <= size X.
Proof using H6 H3 H2 H1 H0 H EqDecision0.
  apply subseteq_size.
  apply elem_of_subseteq.
  intros x Hx.
  apply elem_of_difference in Hx.
  by itauto.
Qed.

Lemma union_size_le_sum
  (X Y : C) :
  size (X ∪ Y) <= size X + size Y.
Proof using H6 H4 H3 H1 H0 H EqDecision0.
  specialize (size_union_alt X Y) as Halt.
  rewrite Halt.
  specialize (difference_size_le_self Y X).
  by lia.
Qed.

Lemma intersection_size1
  (X Y : C) :
  size (X ∩ Y) <= size X.
Proof using H6 H4 H2 H1 H0 H EqDecision0.
  apply (subseteq_size (X ∩ Y) X).
  by set_solver.
Qed.

Lemma intersection_size2
  (X Y : C) :
  size (X ∩ Y) <= size Y.
Proof using H6 H4 H2 H1 H0 H EqDecision0.
  apply (subseteq_size (X ∩ Y) Y).
  by set_solver.
Qed.

Lemma difference_size_subset
  (X Y : C)
  (Hsub : Y ⊆ X) :
  (Z.of_nat (size (X ∖ Y)) = Z.of_nat (size X) - Z.of_nat (size Y))%Z.
Proof using H6 H3 H2 H1 H0 EqDecision0.
  assert (Htemp : Y ∪ (X ∖ Y) ≡ X).
  {
    apply set_equiv_equivalence.
    intros a.
    split; intros Ha.
    - by set_solver.
    - destruct (@decide (a ∈ Y)).
      apply elem_of_dec_slow.
      + by apply elem_of_union; left; itauto.
      + by apply elem_of_union; right; set_solver.
  }
  assert (Htemp2 : size Y + size (X ∖ Y) = size X).
  {
    specialize (size_union Y (X ∖ Y)) as Hun.
    spec Hun.
    {
      apply elem_of_disjoint.
      intros a Ha Ha2.
      apply elem_of_difference in Ha2.
      by itauto.
    }
    rewrite Htemp in Hun.
    by itauto.
  }
  by lia.
Qed.

Lemma difference_with_intersection
  (X Y : C) :
  X ∖ Y ≡ X ∖ (X ∩ Y).
Proof using H6 H5 H2 H1 H0 EqDecision0.
  by set_solver.
Qed.

Lemma difference_size
  (X Y : C) :
  (Z.of_nat (size (X ∖ Y)) = Z.of_nat (size X) - Z.of_nat (size (X ∩ Y)))%Z.
Proof using H6 H2 H1 H0 H EqDecision0.
  rewrite difference_with_intersection.
  specialize (difference_size_subset X (X ∩ Y)) as Hdif.
  by set_solver.
Qed.

Lemma difference_size_ge_disjoint_case
  (X Y : C) :
  size (X ∖ Y) >= size X - size Y.
Proof using H6 H3 H2 H1 H0 H EqDecision0.
  specialize (difference_size X Y).
  specialize (intersection_size2 X Y).
  by lia.
Qed.

Lemma list_to_set_size
  (l : list A) :
  size (list_to_set l (C := C)) <= length l.
Proof using H6 H4 H3 H EqDecision0.
  induction l; cbn.
  - by rewrite size_empty; lia.
  - specialize (union_size_le_sum ({[ a ]}) (list_to_set l)) as Hun_size.
    by rewrite size_singleton in Hun_size; lia.
Qed.

End sec_general.

Section sec_filter.

Context
  (P P2 : A -> Prop)
  `{!forall x, Decision (P x)}
  `{!forall x, Decision (P2 x)}
  (X Y : C).

Lemma filter_subset
  (Hsub : X ⊆ Y) :
  filter P X ⊆ filter P Y.
Proof using H6 H4 H3 EqDecision0.
  intros a HaX.
  apply elem_of_filter in HaX.
  apply elem_of_filter.
  by set_solver.
Qed.

Lemma filter_subprop
  (Hsub : forall a, (P a -> P2 a)) :
  filter P X ⊆ filter P2 X.
Proof using H6 H4 H3 EqDecision0.
  intros a HaP.
  apply elem_of_filter in HaP.
  apply elem_of_filter.
  by itauto.
Qed.

End sec_filter.

End sec_fin_set.

Section sec_map.

Context
  `{FinSet A C}
  `{FinSet B D}.

Lemma set_map_subset
  (f : A -> B)
  (X Y : C)
  (Hsub : X ⊆ Y) :
  set_map (D := D) f X ⊆ set_map (D := D) f Y.
Proof using H6 H4 H3 H2 H14 H13 H12 H11 H1 H0 EqDecision1 EqDecision0.
  intros a Ha.
  apply elem_of_map in Ha.
  apply elem_of_map.
  by firstorder.
Qed.

Lemma set_map_size_upper_bound
  (f : A -> B)
  (X : C) :
  size (set_map (D := D) f X) <= size X.
Proof using H7 H14 H12 H11 EqDecision1.
  unfold set_map.
  remember (f <$> elements X) as fX.
  set (x := size (list_to_set _)).
  cut (x <= length fX); [| by apply list_to_set_size].
  enough (length fX = size X) by lia.
  unfold size, set_size.
  simpl; subst fX.
  by apply fmap_length.
Qed.

Lemma elem_of_set_map_inj (f : A -> B) `{!Inj (=) (=) f} (a : A) (X : C) :
  f a ∈@{D} fin_sets.set_map f X <-> a ∈ X.
Proof using H6 H4 H3 H2 H14 H13 H12 H11 H1 H0 EqDecision1 EqDecision0.
  intros; rewrite elem_of_map.
  split; [| by eexists].
  intros (_v & HeqAv & H_v).
  eapply inj in HeqAv; [| done].
  by subst.
Qed.

Lemma set_map_id (X : C) : X ≡ set_map id X.
Proof using H9 H8 H7 H6 H4 H3 H14 H13 H12 H11 H10 EqDecision1 EqDecision0 D B. by set_solver. Qed.

End sec_map.
