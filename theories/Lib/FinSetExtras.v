From VLSM.Lib Require Import Itauto.
From stdpp Require Import prelude fin_maps.
From VLSM.Lib Require Import Preamble.

(** * Finite set utility definitions and lemmas *)

Section sec_fin_set.

Context
  `{FinSet A C}.

Section sec_general.

(**
  If <<X>> is a subset of <<Y>>, then the elements of <<X>> are a sublist
  of the elements of <<Y>>.
*)
Lemma elements_subseteq (X Y : C) :
  X ⊆ Y -> elements X ⊆ elements Y.
Proof. by set_solver. Qed.

Lemma union_size_ge_size1
  (X Y : C) :
  size (X ∪ Y) >= size X.
Proof.
  apply subseteq_size.
  apply subseteq_union.
  by set_solver.
Qed.

Lemma union_size_ge_size2
  (X Y : C) :
  size (X ∪ Y) >= size Y.
Proof.
  apply subseteq_size.
  apply subseteq_union.
  by set_solver.
Qed.

Lemma union_size_ge_average
  (X Y : C) :
  2 * size (X ∪ Y) >= size X + size Y.
Proof.
  specialize (union_size_ge_size1 X Y) as Hx.
  specialize (union_size_ge_size2 X Y) as Hy.
  by lia.
Qed.

Lemma difference_size_le_self
  (X Y : C) :
  size (X ∖  Y) <= size X.
Proof.
  apply subseteq_size.
  apply elem_of_subseteq.
  intros x Hx.
  apply elem_of_difference in Hx.
  by itauto.
Qed.

Lemma union_size_le_sum
  (X Y : C) :
  size (X ∪ Y) <= size X + size Y.
Proof.
  specialize (size_union_alt X Y) as Halt.
  rewrite Halt.
  specialize (difference_size_le_self Y X).
  by lia.
Qed.

Lemma intersection_size1
  (X Y : C) :
  size (X ∩ Y) <= size X.
Proof.
  apply (subseteq_size (X ∩ Y) X).
  by set_solver.
Qed.

Lemma intersection_size2
  (X Y : C) :
  size (X ∩ Y) <= size Y.
Proof.
  apply (subseteq_size (X ∩ Y) Y).
  by set_solver.
Qed.

Lemma difference_size_subset
  (X Y : C)
  (Hsub : Y ⊆ X) :
  (Z.of_nat (size (X ∖ Y)) = Z.of_nat (size X) - Z.of_nat (size Y))%Z.
Proof.
  assert (Htemp : Y ∪ (X ∖ Y) ≡ X).
  {
    apply set_equiv_equivalence.
    intros a.
    split; intros Ha.
    - by set_solver.
    - destruct (decide (a ∈ Y)).
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
Proof.
  by set_solver.
Qed.

Lemma difference_size
  (X Y : C) :
  (Z.of_nat (size (X ∖ Y)) = Z.of_nat (size X) - Z.of_nat (size (X ∩ Y)))%Z.
Proof.
  rewrite difference_with_intersection.
  specialize (difference_size_subset X (X ∩ Y)) as Hdif.
  by set_solver.
Qed.

Lemma difference_size_ge_disjoint_case
  (X Y : C) :
  size (X ∖ Y) >= size X - size Y.
Proof.
  specialize (difference_size X Y).
  specialize (intersection_size2 X Y).
  by lia.
Qed.

Lemma list_to_set_size
  (l : list A) :
  size (list_to_set l (C := C)) <= length l.
Proof.
  induction l; cbn.
  - by rewrite size_empty; lia.
  - specialize (union_size_le_sum ({[ a ]}) (list_to_set l)) as Hun_size.
    by rewrite size_singleton in Hun_size; lia.
Qed.

#[export] Instance fin_set_subseteq_dec : RelDecision (⊆@{C}).
Proof.
  intros X Y.
  eapply @Decision_iff with (P := set_Forall (fun a => a ∈ Y) X).
  - by set_solver.
  - by typeclasses eauto.
Qed.

#[export] Instance fin_set_empty_eq_dec :
  forall (X : C), Decision (X ≡ ∅).
Proof.
  intros.
  destruct (decide (elements X = [])).
  - by left; rewrite <- elements_empty_iff.
  - by right; rewrite <- elements_empty_iff.
Qed.

#[export] Instance fin_set_singleton_eq_dec :
  forall (X : C) (x : A), Decision (X ≡ {[x]}).
Proof.
  intros X x.
  destruct (decide (elements X = [x])) as [Heq|Heq].
  - left; intro i.
    rewrite elem_of_singleton, <- elem_of_elements.
    by rewrite Heq, elem_of_list_singleton.
  - right; contradict Heq.
    apply Permutation_singleton_r.
    by rewrite Heq, elements_singleton.
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
Proof.
  intros a HaX.
  apply elem_of_filter in HaX.
  apply elem_of_filter.
  by set_solver.
Qed.

Lemma filter_subprop
  (Hsub : forall a, (P a -> P2 a)) :
  filter P X ⊆ filter P2 X.
Proof.
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
Proof.
  intros a Ha.
  apply elem_of_map in Ha.
  apply elem_of_map.
  by firstorder.
Qed.

Lemma set_map_size_upper_bound
  (f : A -> B)
  (X : C) :
  size (set_map (D := D) f X) <= size X.
Proof.
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
Proof.
  intros; rewrite elem_of_map.
  split; [| by eexists].
  intros (_v & HeqAv & H_v).
  eapply inj in HeqAv; [| done].
  by subst.
Qed.

Lemma set_map_id (X : C) : X ≡ set_map id X.
Proof. by set_solver. Qed.

End sec_map.

Definition mmap_insert
  {I A SA : Type} {MI : Type -> Type}
  `{FinMap I MI} `{FinSet A SA} (i : I) (a : A) (m : MI SA) :=
  <[ i := {[ a ]} ∪ m !!! i ]> m.

Lemma elem_of_mmap_insert
  {I A SA : Type} {MI : Type -> Type}
  `{FinMap I MI} `{FinSet A SA} (m : MI SA) (i j : I) (a b : A) :
    b ∈ mmap_insert i a m !!! j <-> (a = b /\ i = j) \/ (b ∈ m !!! j).
Proof.
  unfold mmap_insert.
  destruct (decide (i = j)) as [<- | Hij].
  - rewrite lookup_total_insert.
    by destruct (decide (a = b)); set_solver.
  - rewrite lookup_total_insert_ne by done.
    by set_solver.
Qed.
