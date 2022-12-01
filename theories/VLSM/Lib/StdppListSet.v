From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.

Section sec_fst_defs.

Context `{EqDecision A}.

Definition set := list A.

Definition empty_set : set := [].

Fixpoint set_add (a : A) (x : set) : set :=
match x with
| [] => [a]
| a1 :: x1 => if decide (a = a1) then a1 :: x1 else a1 :: set_add a x1
end.

Fixpoint set_remove (a : A) (x : set) : set :=
match x with
| [] => empty_set
| a1 :: x1 => if decide (a = a1) then x1 else a1 :: set_remove a x1
end.

Fixpoint set_union (x y : set) : set :=
match y with
| [] => x
| a1 :: y1 => set_add a1 (set_union x y1)
end.

Fixpoint set_diff (x y : set) : set :=
match x with
| [] => []
| a1 :: x1 => if decide (a1 ∈ y) then set_diff x1 y else set_add a1 (set_diff x1 y)
end.

Lemma set_add_intro1 :
  forall (a b : A) (x : set), a ∈ x -> a ∈ set_add b x.
Proof.
  induction x; cbn.
  - by inversion 1.
  - by destruct (decide (b = a0)); rewrite !elem_of_cons; itauto.
Qed.

Lemma set_add_intro2 :
  forall (a b : A) (x : set), a = b -> a ∈ set_add b x.
Proof.
  induction x; cbn.
  - by rewrite elem_of_cons; left.
  - by intros ->; destruct (decide (b = a0)); rewrite !elem_of_cons; itauto.
Qed.

#[local] Hint Resolve set_add_intro1 set_add_intro2 : core.

Lemma set_add_intro :
  forall (a b : A) (x : set), a = b \/ a ∈ x -> a ∈ set_add b x.
Proof.
  by intros a b x [H1| H2]; auto.
Qed.

Lemma set_add_elim :
  forall (a b : A) (x : set), a ∈ set_add b x -> a = b \/ a ∈ x.
Proof.
  induction x; cbn.
  - by rewrite elem_of_cons.
  - by destruct (decide (b = a0)); rewrite !elem_of_cons; itauto.
Qed.

Lemma set_add_not_empty :
  forall (a : A) (x : set), set_add a x <> empty_set.
Proof.
  by induction x as [| a' x']; cbn; [| destruct (decide (a = a'))].
Qed.

Lemma set_add_iff a b l :
  a ∈ set_add b l <-> a = b \/ a ∈ l.
Proof.
  split.
  - by apply set_add_elim.
  - by apply set_add_intro.
Qed.

Lemma set_add_nodup a l :
  NoDup l -> NoDup (set_add a l).
Proof.
  induction 1 as [| x l H H' IH]; cbn.
  - by constructor; [inversion 1| apply NoDup_nil].
  - by destruct (decide (a = x)) as [<- | Hax]; constructor
    ; rewrite ?set_add_iff; itauto.
Qed.

Lemma set_remove_1 (a b : A) (l : set) :
  a ∈ set_remove b l -> a ∈ l.
Proof.
  induction l as [| x xs Hrec]; cbn; [done |].
  by destruct (decide (b = x)); rewrite !elem_of_cons; itauto.
Qed.

Lemma set_remove_2 (a b : A) (l : set) :
  NoDup l -> a ∈ set_remove b l -> a <> b.
Proof.
  induction l as [| x l IH]; intro Hnd; cbn; [by inversion 1 |].
  inversion_clear Hnd.
  destruct (decide (b = x)) as [<- | Hbx].
  - by intros Ha ->.
  - by rewrite elem_of_cons; firstorder subst.
Qed.

Lemma set_remove_3 (a b : A) (l : set) :
  a ∈ l -> a <> b -> a ∈ set_remove b l.
Proof.
  induction l as [| x xs Hrec]; cbn.
  - by inversion 1.
  - by destruct (decide (b = x)) as [<- | Hbx]; rewrite !elem_of_cons; itauto.
Qed.

Lemma set_remove_iff (a b : A) (l : set) :
  NoDup l -> a ∈ set_remove b l <-> a ∈ l /\ a <> b.
Proof.
  repeat split.
  - by eapply set_remove_1.
  - by eapply set_remove_2.
  - by destruct 1; apply set_remove_3.
Qed.

Lemma set_remove_nodup a l
  : NoDup l -> NoDup (set_remove a l).
Proof.
  induction 1 as [| x l H H' IH]; cbn; [by constructor |].
  destruct (decide (a = x)) as [<- | Hax]; [done |].
  constructor; [| done].
  by rewrite set_remove_iff; itauto.
Qed.

Lemma set_union_intro :
  forall (a : A) (x y : set),
    a ∈ x \/ a ∈ y -> a ∈ set_union x y.
Proof.
  induction y; cbn.
  - by rewrite elem_of_nil; itauto.
  - by rewrite elem_of_cons, set_add_iff; itauto.
Qed.

Lemma set_union_elim :
  forall (a : A) (x y : set),
    a ∈ set_union x y -> a ∈ x \/ a ∈ y.
Proof.
  by induction y; cbn; rewrite ?elem_of_cons, ?set_add_iff; itauto.
Qed.

Lemma set_union_iff a l l' :
  a ∈ set_union l l' <-> a ∈ l \/ a ∈ l'.
Proof.
  split.
  - by apply set_union_elim.
  - by apply set_union_intro.
Qed.

Lemma set_union_nodup l l' :
  NoDup l -> NoDup l' -> NoDup (set_union l l').
Proof.
  by induction 2 as [| x' l' ? ? IH]; cbn; [| apply set_add_nodup].
Qed.

Lemma set_diff_intro :
  forall (a : A) (x y : set),
    a ∈ x -> ~ a ∈ y -> a ∈ set_diff x y.
Proof.
  induction x; cbn; [by inversion 1 |].
  by intros y; destruct (decide (a0 ∈ y));
    rewrite elem_of_cons, ?set_add_iff; firstorder congruence.
Qed.

Lemma set_diff_elim1 :
  forall (a : A) (x y : set),
    a ∈ set_diff x y -> a ∈ x.
Proof.
  induction x; cbn; [done |]; intros y.
  by destruct (decide (a0 ∈ y)); rewrite elem_of_cons, ?set_add_iff; firstorder.
Qed.

Lemma set_diff_elim2 :
  forall (a : A) (x y : set), a ∈ set_diff x y -> ~ a ∈ y.
Proof.
  induction x; cbn; [by inversion 1 |].
  by intros y; destruct (decide (a0 ∈ y)); rewrite ?set_add_iff; firstorder congruence.
Qed.

Lemma set_diff_iff a l l' :
  a ∈ set_diff l l' <-> a ∈ l /\ ~ a ∈ l'.
Proof.
  split.
  - by eauto using set_diff_elim1, set_diff_elim2.
  - by destruct 1; apply set_diff_intro.
Qed.

(*
 TODO: change statement when Coq's stdlib drops
 the unnecessary second premise in ListSet
*)
Lemma set_diff_nodup l l' :
  NoDup l -> NoDup l' -> NoDup (set_diff l l').
Proof.
  induction 1 as [| x l H H' IH]; cbn.
  - by constructor.
  - intro Hl'; specialize (IH Hl').
    by case_decide; [| apply set_add_nodup].
Qed.

End sec_fst_defs.

Arguments set : clear implicits.

Section sec_other_defs.

Definition set_prod : forall {A B : Type}, set A -> set B -> set (A * B) :=
  list_prod.

Definition set_fold_right {A B : Type} (f : A -> B -> B) (x : set A) (b : B) : B :=
  fold_right f b x.

Definition set_map {A B : Type} `{EqDecision B} (f : A -> B) (x : set A) : set B :=
  set_fold_right (fun a => set_add (f a)) x empty_set.

End sec_other_defs.
