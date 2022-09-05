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
  intros. unfold set_add. apply elem_of_union. right. apply H7.
Qed.

Lemma set_add_intro2 :
  forall (a b : A) (x : set), a = b -> a ∈ set_add b x.
Proof.
  intros. unfold set_add. apply elem_of_union. left. apply elem_of_singleton, H7.
Qed.

#[local] Hint Resolve set_add_intro1 set_add_intro2 : core.

Lemma set_add_intro :
  forall (a b : A) (x : set), a = b \/ a ∈ x -> a ∈ set_add b x.
Proof.
  intros. unfold set_add. apply elem_of_union. destruct H7 as [Hb | Hx].
  - left. apply elem_of_singleton, Hb.
  - right. apply Hx.
Qed.

Lemma set_add_elim :
  forall (a b : A) (x : set), a ∈ set_add b x -> a = b \/ a ∈ x.
Proof.
  intros. unfold set_add in H7. apply elem_of_union in H7. destruct H7 as [Hb | Hx].
  - left. apply elem_of_singleton in Hb. apply Hb.
  - right. apply Hx.
Qed.

Lemma set_add_not_empty :
  forall (a : A) (x : set), ¬ set_add a x ≡ ∅.
Proof.
  intros. unfold set_add. intros contra.
  cut (a ∈@{C} ∅); [by apply not_elem_of_empty |].
  apply contra, elem_of_union. left. by apply elem_of_singleton.
Qed.

Lemma set_add_iff a b l :
  a ∈ set_add b l <-> a = b \/ a ∈ l.
Proof.
  split.
  - apply set_add_elim.
  - apply set_add_intro.
Qed.

Lemma set_remove_1 (a b : A) (l : set) :
  a ∈ set_remove b l -> a ∈ l.
Proof.
  intros. unfold set_remove in H7. apply elem_of_difference in H7. 
  destruct H7 as [Hl Hnb]. apply Hl.
Qed.

Lemma set_remove_2 (a b : A) (l : set) :
  NoDup (elements l) -> a ∈ set_remove b l -> a <> b.
Proof.
  intros. unfold set_remove in H8. apply elem_of_difference in H8. destruct H8 as [Hl Hnb].
  unfold "≠". unfold "≠" in Hnb. intros. rewrite elem_of_singleton in Hnb. apply Hnb, H8.
Qed.

Lemma set_remove_3 (a b : A) (l : set) :
  a ∈ l -> a <> b -> a ∈ set_remove b l.
Proof.
  intros. unfold set_remove. apply elem_of_difference. split.
  - apply H7.
  - unfold "≠" in H8. unfold "≠". intros. apply elem_of_singleton in H9. apply H8, H9.
Qed.

Lemma set_remove_iff (a b : A) (l : set) :
  NoDup (elements l) -> a ∈ set_remove b l <-> a ∈ l /\ a <> b.
Proof.
  split; [split |].
  - eapply set_remove_1; eauto.
  - eapply set_remove_2; eauto.
  - destruct 1; apply set_remove_3; auto.
Qed.

Lemma set_union_intro :
  forall (a : A) (x y : set),
    a ∈ x \/ a ∈ y -> a ∈ set_union x y.
Proof.
  intros. apply elem_of_union, H7.
Qed.

Lemma set_union_elim :
  forall (a : A) (x y : set),
    a ∈ set_union x y -> a ∈ x \/ a ∈ y.
Proof.
  intros. unfold set_union in H7. apply elem_of_union in H7. apply H7.
Qed.

Lemma set_union_iff a l l' :
  a ∈ set_union l l' <-> a ∈ l \/ a ∈ l'.
Proof.
  split.
  - apply set_union_elim.
  - apply set_union_intro.
Qed.

Lemma set_diff_intro :
  forall (a : A) (x y : set),
    a ∈ x -> ~ a ∈ y -> a ∈ set_diff x y.
Proof.
  intros. apply elem_of_difference. split.
  - apply H7.
  - apply H8.
Qed.

Lemma set_diff_elim1 :
  forall (a : A) (x y : set),
    a ∈ set_diff x y -> a ∈ x.
Proof.
  intros. unfold set_diff in H7. apply elem_of_difference in H7. destruct H7 as [Hx _]. apply Hx.
Qed.

Lemma set_diff_elim2 :
  forall (a : A) (x y : set), a ∈ set_diff x y -> ~ a ∈ y.
Proof.
  intros. unfold set_diff in H7. apply elem_of_difference in H7. destruct H7 as [_ Hny]. apply Hny.
Qed.

Lemma set_diff_iff a l l' :
  a ∈ set_diff l l' <-> a ∈ l /\ ~ a ∈ l'.
Proof.
  split.
  - eauto using set_diff_elim1, set_diff_elim2.
  - by destruct 1; apply set_diff_intro.
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
