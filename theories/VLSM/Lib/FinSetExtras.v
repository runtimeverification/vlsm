From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From VLSM.Lib Require Import Preamble.

(** * Finite set utility definitions and lemmas *)

Definition set_prod_type A C D : Type := C * (A -> D).

Inductive SetProd A C `{ElemOf A C} D `{Equiv D} `{Empty D} : Type :=
| set_prod_ctor : forall (X : C) (fAD : A -> D)
    (Hmostly_empty : forall a, a ∉ X → fAD a ≡ ∅),
    SetProd A C D.

Definition sp_1 {A C} `{ElemOf A C} {D} `{Equiv D} `{Empty D} (X : SetProd A C D) : C :=
  match X with
    set_prod_ctor _ _ _ X _ _ => X
  end.

Definition sp_2 {A C} `{ElemOf A C} {D} `{Equiv D} `{Empty D} (X : SetProd A C D) : A -> D :=
  match X with
    set_prod_ctor _ _ _ _ fAD _ => fAD
  end.

Section set_prod_type_props.

#[local] Instance set_prod_elem_of
  `{ElemOf A C}
  `{ElemOf B D}
  : ElemOf (A * B) (set_prod_type A C D) :=
  fun a_b Xa_HXb => a_b.1 ∈ Xa_HXb.1 /\ a_b.2 ∈ Xa_HXb.2 a_b.1.

#[local] Instance SetProd_elem_of
  `{ElemOf A C}
  `{ElemOf B D}
  `{Empty D}
  : ElemOf (A * B) (SetProd A C D).
Proof.
  intros (a, b) [].
  exact (a ∈ X ∧ b ∈ fAD a).
Defined.

#[local] Program Instance SetProd_empty `{ElemOf A C} `{ElemOf B D} `{Empty C} `{Empty D}: Empty (SetProd A C D) :=
  set_prod_ctor A C D ∅ (λ _, ∅) _.
Next Obligation.
  done.
Qed.

#[local] Instance set_prod_empty A `{Empty C} `{Empty D}: Empty (set_prod_type A C D)
  := (∅, (λ _, ∅)).

#[local] Program Instance SetProd_singleton
  `{SemiSet A C} `{EqDecision A} `{ElemOf B D} `{Empty D} `{Singleton B D}
  : Singleton (A * B) (SetProd A C D) :=
  λ a_b, set_prod_ctor A C D {[a_b.1]} (λ a, if (decide (a = a_b.1)) then {[a_b.2]} else ∅) _.
Next Obligation.
  intros A C ? ? ? ? ? ? B D ? ? ? (a, b) a' Ha'; cbn in *.
  by rewrite decide_False; [| rewrite <- @not_elem_of_singleton with (C := C)].
Qed.

#[local] Instance set_prod_singleton
  `{Singleton A C} `{Singleton B D} : Singleton (A * B) (set_prod_type A C D)
  := λ a_b, ({[a_b.1]}, (λ _, {[a_b.2]})).

#[local] Program Instance SetProd_union
  `{SemiSet A C} `{SemiSet B D}
  : Union (SetProd A C D) :=
  λ X Y, set_prod_ctor A C D (sp_1 X ∪ sp_1 Y) (λ a, sp_2 X a ∪ sp_2 Y a) _.
Next Obligation.
  intros A C ? ? ? ? ? B D ? ? ? ? ? [X fXD HmeX] [Y fYD HmeY] a Ha; cbn in *.
  apply not_elem_of_union in Ha as [HnaX HnaY].
  by apply empty_union; rewrite HmeX, HmeY.
Qed.

#[local] Instance set_prod_union
  `{ElemOf A C} `{!RelDecision (∈@{C})} `{Union C} `{Union D} : Union (set_prod_type A C D) :=
  λ X Y,
    ( X.1 ∪ Y.1,
      λ a,
      if decide (a ∈ X.1)
        then if decide (a ∈ Y.1) then X.2 a ∪ Y.2 a else X.2 a
        else if decide (a ∈ Y.1) then Y.2 a else X.2 a ∪ Y.2 a).

Lemma semiset_elem_dec_eq `{SemiSet A C} `{!RelDecision (∈@{C})} : EqDecision A.
Proof.
  intros a b.
  by destruct (decide (a ∈@{C} {[b]})) as [Ha | Ha];
    rewrite elem_of_singleton in Ha; [left | right].
Qed.

Lemma SetProd_semiset_alt `{SemiSet A C} `{SemiSet B D} `{!RelDecision (∈@{C})} `{EqDecision A}
   : SemiSet (A * B) (SetProd A C D).
Proof.
  constructor.
  - intros (a, b) [Ha]; revert Ha; apply not_elem_of_empty.
  - intros (a, b) (c, d); split.
    + intros [Ha Hb]; cbn in *.
      apply elem_of_singleton in Ha.
      by rewrite decide_True, elem_of_singleton in Hb; subst.
    + by intros [= -> ->]; split; [| rewrite decide_True by done]; apply elem_of_singleton.
  - intros [X fXD HmeX] [Y fYD HmeY] (a, b); cbn; rewrite !elem_of_union; split;
      [intros [Ha [HbX | HbY]] | intros [[HaX HbX] | [HaY HbY]]];
      [.. | by split; left | by split; right].
    + left; split; [| done].
      destruct (decide (a ∈ X)); [done |].
      rewrite HmeX in HbX by done; contradict HbX; apply not_elem_of_empty.
    + right; split; [| done].
      destruct (decide (a ∈ Y)); [done |].
      rewrite HmeY in HbY by done; contradict HbY; apply not_elem_of_empty.
Qed.

#[local] Instance SetProd_semiset `{SemiSet A C} `{SemiSet B D} `{!RelDecision (∈@{C})}
  (Hsingl := SetProd_singleton (EqDecision0 := semiset_elem_dec_eq (C := C)))
   : SemiSet (A * B) (SetProd A C D).
Proof. by apply SetProd_semiset_alt. Qed.

#[local] Instance set_prod_semiset `{SemiSet A C} `{SemiSet B D} `{!RelDecision (∈@{C})} : SemiSet (A * B) (set_prod_type A C D).
Proof.
  constructor.
  - intros (a, b) [Ha Hb]; revert Ha; apply not_elem_of_empty.
  - intros (a, b) (c, d); split.
    + intros [Ha Hb]; cbn in *; apply elem_of_singleton in Ha, Hb; congruence.
    + by inversion 1; split; cbn; apply elem_of_singleton.
  - intros (X, fXD) (Y, fYD) (a, b); split.
    + intros [Ha Hb]; cbn in *; apply elem_of_union in Ha.
      destruct (decide (a ∈ X)); [destruct (decide (a ∈ Y)) |];
        [apply elem_of_union in Hb as [] |..].
      * by left; split.
      * by right; split.
      * by left; split.
      * destruct Ha as [|Ha]; [done |].
        rewrite decide_True in Hb by done.
        by right; split.
    + intros [[HaX HbX] | [HaY HbY]]; unfold union, set_prod_union; cbn in *;
        (split; [apply elem_of_union|]); [by left | | by right |]; cbn.
      * rewrite decide_True by done.
        by case_decide; [apply elem_of_union; left |].
      * by case_decide; rewrite decide_True; [apply elem_of_union; right |..].
Qed.

#[local] Program Instance SetProd_intersection
  `{Set_ A C} `{!RelDecision (∈@{C})} `{Set_ B D}
  : Intersection (SetProd A C D) :=
  λ X Y, set_prod_ctor A C D (sp_1 X ∩ sp_1 Y) (λ a, sp_2 X a ∩ sp_2 Y a) _.
Next Obligation.
  intros A C ? ? ? ? ? ? ? ? B D ? ? ? ? ? ? ? [X fXD HmeX] [Y fYD HmeY] a Ha; cbn in *.
  apply not_elem_of_intersection in Ha as [HaX | HaY].
  - by rewrite HmeX; [apply intersection_empty_l |].
  - by rewrite HmeY; [apply intersection_empty_r |].
Qed.

#[local] Instance set_prod_intersection A `{Intersection C} `{Intersection D}
  : Intersection (set_prod_type A C D) :=
  λ X Y, ( X.1 ∩ Y.1, (λ a, X.2 a ∩ Y.2 a)).

#[local] Program Instance SetProd_difference
  `{Set_ A C} `{Set_ B D}
  : Difference (SetProd A C D) :=
  λ X Y, set_prod_ctor A C D (sp_1 X) (λ a, sp_2 X a ∖ sp_2 Y a) _.
Next Obligation.
  intros A C ? ? ? ? ? ? ? B D ? ? ? ? ? ? ? [X fXD HmeX] [Y fYD HmeY] a Ha; cbn in *.
  by apply subseteq_empty_difference; rewrite HmeX; [apply empty_subseteq |].
Qed.

#[local] Instance set_prod_difference
  `{ElemOf A C} `{!RelDecision (∈@{C})} `{Difference C} `{Difference D} : Difference (set_prod_type A C D) :=
  λ X Y, ( X.1, (λ a, if (decide (a ∈ Y.1)) then X.2 a ∖ Y.2 a else X.2 a)).

Lemma SetProd_set_alt  `{Set_ A C} `{Set_ B D} `{!RelDecision (∈@{C})} `{EqDecision A}
  : Set_ (A * B) (SetProd A C D).
Proof.
  constructor.
  - apply SetProd_semiset_alt.
  - intros [X fXD HmeX] [Y fYD HmeY] (a, b); cbn; rewrite !elem_of_intersection; itauto.
  - intros [X fXD HmeX] [Y fYD HmeY] (a, b); cbn; rewrite !elem_of_difference; split.
    + by intros (HaX & HbX & HnbY); split; [| intros []].
    + intros [[HaX HbX] HnabY]; split_and!; [done.. |].
      contradict HnabY; split; [| done].
      destruct (decide (a ∈ Y)); [done |].
      rewrite HmeY in HnabY by done; contradict HnabY; apply not_elem_of_empty.
Qed.

#[local] Instance SetProd_set `{Set_ A C} `{Set_ B D} `{!RelDecision (∈@{C})}
  (Hsingl := SetProd_singleton (EqDecision0 := semiset_elem_dec_eq (C := C)))
  : Set_ (A * B) (SetProd A C D).
Proof.  apply SetProd_set_alt. Qed.

#[local] Instance set_prod_set `{Set_ A C} `{Set_ B D} `{!RelDecision (∈@{C})} : Set_ (A * B) (set_prod_type A C D).
Proof.
  constructor.
  - typeclasses eauto.
  - intros (X, fXD) (Y, fYD) (a, b); split.
    + by intros [Ha Hb]; cbn in *; apply elem_of_intersection in Ha as [], Hb as [].
    + by intros [[HaX HbX] [HaY HbY]]; split; cbn in *; apply elem_of_intersection.
  - intros (X, fXD) (Y, fYD) (a, b); split.
    + intros [Ha Hb]; cbn in *; case_decide as Hy.
      * apply elem_of_difference in Hb as [? Hnb].
        by split; [| contradict Hnb; destruct Hnb].
      * by split; [| contradict Hy; destruct Hy].
    + intros [[HaX HbX] Hnab]; unfold difference, set_prod_difference; cbn in *.
      split; [done |]; cbn.
      case_decide; [| done].
      apply elem_of_difference; split; [done |].
      by contradict Hnab.
Qed.

#[local] Program Instance SetProd_elements `{ElemOf A C} `{Equiv D} `{Empty D}
  `{Elements A C} `{Elements B D} : Elements (A * B) (SetProd A C D) :=
  λ X, mjoin (fmap (λ a, fmap (λ b, (a, b)) (elements (sp_2 X a))) (elements (sp_1 X))).

#[local] Instance set_prod_elements `{Elements A C} `{Elements B D} : Elements (A * B) (set_prod_type A C D) :=
  λ X, mjoin (fmap (λ a, fmap (λ b, (a, b)) (elements (X.2 a))) (elements X.1)).

#[local] Instance fin_set_elem_of_dec `{FinSet A C} : RelDecision (∈@{C}).
Proof. by apply elem_of_dec_slow. Qed.

#[local] Instance SetProd_fin_set `{FinSet A C} `{FinSet B D} : FinSet (A * B) (SetProd A C D).
Proof.
  constructor.
  - apply SetProd_set_alt.
  - intros [X fXD ?] (a, b); unfold elements, SetProd_elements; cbn.
    rewrite elem_of_list_join; setoid_rewrite elem_of_list_fmap; cbn.
    clear Hmostly_empty.
    split.
    + intros (l & Hab & _a & -> & Ha).
      apply elem_of_list_fmap in Hab as (_b & [= <- <-] & Hb).
      by apply elem_of_elements in Ha, Hb.
    + intros [Ha Hb]; cbn in *.
      eexists; split; [| by exists a; split; [|apply elem_of_elements]].
      apply elem_of_list_fmap.
      by eexists; split; [| apply elem_of_elements].
  - intros [X fXD ?]; unfold elements, SetProd_elements; cbn.
    generalize (list_to_set_elements X), (NoDup_elements X).
    generalize (elements X) as lA; intros lA; clear Hmostly_empty; revert X.
    induction lA; [by constructor |]; intros X Hequiv Hnodup; cbn.
    generalize (NoDup_elements (fXD a)).
    generalize (elements (fXD a)) as lB; induction lB; intros HnodupB;
      [by eapply IHlA; [| inversion Hnodup] |]; cbn.
    constructor; [| by apply IHlB; inversion HnodupB].
    rewrite elem_of_app; intros [HB | HA].
    + apply elem_of_list_fmap in HB as (b & [= ->] & Hb).
      by inversion HnodupB.
    + apply elem_of_list_join in HA as (l & Haa0 & Hl).
      apply elem_of_list_fmap in Hl as (_a & -> & Ha).
      apply elem_of_list_fmap in Haa0 as (b & [= <- ->] & Hb).
      by inversion Hnodup.
Qed.

#[local] Instance set_prod_fin_set `{FinSet A C} `{FinSet B D} : FinSet (A * B) (set_prod_type A C D).
Proof.
  constructor.
  - typeclasses eauto.
  - intros (X, fXD) (a, b).
    unfold elements, set_prod_elements; rewrite elem_of_list_join.
    setoid_rewrite elem_of_list_fmap; cbn.
    split.
    + intros (l & Hab & _a & -> & Ha).
      apply elem_of_list_fmap in Hab as (_b & [= <- <-] & Hb).
      by apply elem_of_elements in Ha, Hb.
    + intros [Ha Hb]; cbn in *.
      eexists; split; [| by exists a; split; [|apply elem_of_elements]].
      apply elem_of_list_fmap.
      by eexists; split; [| apply elem_of_elements].
  - intros (X, fXD); unfold elements, set_prod_elements; cbn.
    generalize (list_to_set_elements X), (NoDup_elements X).
    generalize (elements X) as lA; intros lA; revert X.
    induction lA; [by constructor |]; intros X Hequiv Hnodup; cbn.
    generalize (NoDup_elements (fXD a)).
    generalize (elements (fXD a)) as lB; induction lB; intros HnodupB;
      [by eapply IHlA; [| inversion Hnodup] |]; cbn.
    constructor; [| by apply IHlB; inversion HnodupB].
    rewrite elem_of_app; intros [HB | HA].
    + apply elem_of_list_fmap in HB as (b & [= ->] & Hb).
      by inversion HnodupB.
    + apply elem_of_list_join in HA as (l & Haa0 & Hl).
      apply elem_of_list_fmap in Hl as (_a & -> & Ha).
      apply elem_of_list_fmap in Haa0 as (b & [= <- ->] & Hb).
      by inversion Hnodup.
Qed.

End set_prod_type_props.

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
  specialize (union_size_ge_size1 X Y) as Hx.
  specialize (union_size_ge_size2 X Y) as Hy.
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
  specialize (size_union_alt X Y) as Halt.
  rewrite Halt.
  specialize (difference_size_le_self Y X).
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

Lemma difference_size_subset
  (X Y : C)
  (Hsub : Y ⊆ X) :
  (Z.of_nat (size (X ∖ Y)) = Z.of_nat (size X) - Z.of_nat (size Y))%Z.
Proof.
  assert (Htemp : Y ∪ (X ∖ Y) ≡ X). {
    apply set_equiv_equivalence.
    intros a.
    split; intros Ha.
    - set_solver.
    - destruct (@decide (a ∈ Y)).
      apply elem_of_dec_slow.
      + apply elem_of_union. left. itauto.
      + apply elem_of_union. right. set_solver.
  }
  assert (Htemp2 : size Y + size (X ∖ Y) = size X). {
    specialize (size_union Y (X ∖ Y)) as Hun.
    spec Hun. {
      apply elem_of_disjoint.
      intros a Ha Ha2.
      apply elem_of_difference in Ha2.
      itauto.
    }
    rewrite Htemp in Hun.
    itauto.
  }
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
  rewrite difference_with_intersection.
  specialize (difference_size_subset X (X ∩ Y)) as Hdif.
  set_solver.
Qed.

Lemma difference_size_ge_disjoint_case
  (X Y : C) :
  size (X ∖ Y) >= size X - size Y.
Proof.
  specialize (difference_size X Y).
  specialize (intersection_size2 X Y).
  lia.
Qed.

Lemma list_to_set_size
  (l : list A) :
  size (list_to_set l (C := C)) <= length l.
Proof.
  induction l.
  - simpl.
    rewrite size_empty. lia.
  - simpl.
    specialize (union_size_le_sum ({[a]}) (list_to_set l)) as Hun_size.
    rewrite size_singleton in Hun_size.
    lia.
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
