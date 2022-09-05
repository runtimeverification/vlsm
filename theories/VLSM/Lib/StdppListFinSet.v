From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.

Section fst_defs.

Context `{FinSet A C}.

Definition set := C.

Definition empty_set : set := ∅.

Definition set_add (a : A) (x : set) : set := {[a]} ∪ x.

Definition set_remove (a : A) (x : set) : set := x ∖ {[ a ]}.

Definition set_union (x y : set) : set := x ∪ y.

Definition set_diff (x y : set) : set := x ∖ y.

Lemma set_add_intro1 :
  forall (a b : A) (x : set), a ∈ x -> a ∈ set_add b x.
Proof.
  unfold set_add; intros a b x Hab.
  by apply elem_of_union; right.
Qed.

Lemma set_add_intro2 :
  forall (a b : A) (x : set), a = b -> a ∈ set_add b x.
Proof.
  unfold set_add; intros a b x Hab.
  by rewrite elem_of_union, elem_of_singleton; left.
Qed.

#[local] Hint Resolve set_add_intro1 set_add_intro2 : core.

Lemma set_add_intro :
  forall (a b : A) (x : set), a = b \/ a ∈ x -> a ∈ set_add b x.
Proof.
  unfold set_add; intros a b x Hab.
  by rewrite elem_of_union, elem_of_singleton.
Qed.

Lemma set_add_elim :
  forall (a b : A) (x : set), a ∈ set_add b x -> a = b \/ a ∈ x.
Proof.
  unfold set_add; intros a b x Hab.
  by rewrite elem_of_union, elem_of_singleton in Hab.
Qed.

Lemma set_add_not_empty :
  forall (a : A) (x : set), ¬ set_add a x ≡ ∅.
Proof.
  unfold set_add; intros a x Hcontra.
  cut (a ∈@{C} ∅); [by apply not_elem_of_empty |].
  by rewrite <- Hcontra, elem_of_union, elem_of_singleton; left.
Qed.

Lemma set_add_iff a b l :
  a ∈ set_add b l <-> a = b \/ a ∈ l.
Proof.
  split.
  - by apply set_add_elim.
  - by apply set_add_intro.
Qed.

Lemma set_remove_1 (a b : A) (l : set) :
  a ∈ set_remove b l -> a ∈ l.
Proof.
  unfold set_remove; intros Habl.
  by apply elem_of_difference in Habl as [Hl Hnb].
Qed.

Lemma set_remove_2 (a b : A) (l : set) :
  NoDup (elements l) -> a ∈ set_remove b l -> a <> b.
Proof.
  unfold set_remove; intros Hnd Habl.
  rewrite elem_of_difference, elem_of_singleton in Habl.
  by destruct Habl.
Qed.

Lemma set_remove_3 (a b : A) (l : set) :
  a ∈ l -> a <> b -> a ∈ set_remove b l.
Proof.
  intros Hl Hnb; unfold set_remove.
  by rewrite elem_of_difference, elem_of_singleton.
Qed.

Lemma set_remove_iff (a b : A) (l : set) :
  NoDup (elements l) -> a ∈ set_remove b l <-> a ∈ l /\ a <> b.
Proof.
  split; [split |].
  - by eapply set_remove_1.
  - by eapply set_remove_2.
  - by intros []; apply set_remove_3.
Qed.

Lemma set_union_intro :
  forall (a : A) (x y : set),
    a ∈ x \/ a ∈ y -> a ∈ set_union x y.
Proof.
  by intros; apply elem_of_union.
Qed.

Lemma set_union_elim :
  forall (a : A) (x y : set),
    a ∈ set_union x y -> a ∈ x \/ a ∈ y.
Proof.
  by intros; apply elem_of_union.
Qed.

Lemma set_union_iff a l l' :
  a ∈ set_union l l' <-> a ∈ l \/ a ∈ l'.
Proof.
  split.
  - by apply set_union_elim.
  - by apply set_union_intro.
Qed.

Lemma set_diff_intro :
  forall (a : A) (x y : set),
    a ∈ x -> ~ a ∈ y -> a ∈ set_diff x y.
Proof.
  by intros; apply elem_of_difference.
Qed.

Lemma set_diff_elim1 :
  forall (a : A) (x y : set),
    a ∈ set_diff x y -> a ∈ x.
Proof.
  unfold set_diff; intros a x y Hxy.
  by apply elem_of_difference in Hxy as [Hx _].
Qed.

Lemma set_diff_elim2 :
  forall (a : A) (x y : set), a ∈ set_diff x y -> ~ a ∈ y.
Proof.
  unfold set_diff; intros a x y Hxy.
  by apply elem_of_difference in Hxy as [_ Hny].
Qed.

Lemma set_diff_iff a l l' :
  a ∈ set_diff l l' <-> a ∈ l /\ ~ a ∈ l'.
Proof.
  split.
  - eauto using set_diff_elim1, set_diff_elim2.
  - by intros []; apply set_diff_intro.
Qed.

End fst_defs.

Arguments set : clear implicits.

Section other_defs.

Context 
  `{FinSet A C}
  `{FinSet B D}
  `{FinSet (A * B) CD}
  .

Definition set_prod (X : C) (Y : D) : CD :=
  list_to_set (list_prod (elements X) (elements Y)).

End other_defs.
