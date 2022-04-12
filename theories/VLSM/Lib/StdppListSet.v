From Cdcl Require Import Itauto. Local Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.

(* TODO(traiansf): fix indentation for the whole file. *)
Section fst_defs.

Context `{EqDecision A}.

Definition set := list A.

Definition empty_set : set := [].

Fixpoint set_add (a:A) (x:set) : set :=
match x with
| [] => [a]
| a1 :: x1 =>
  if decide (a = a1) then a1 :: x1 else a1 :: set_add a x1
end.

Fixpoint set_remove (a:A) (x:set) : set :=
match x with
| [] => empty_set
| a1 :: x1 =>
  if decide (a = a1) then x1 else a1 :: set_remove a x1
end.

Fixpoint set_union (x y:set) : set :=
match y with
| [] => x
| a1 :: y1 => set_add a1 (set_union x y1)
end.

Fixpoint set_diff (x y:set) : set :=
match x with
| [] => []
| a1 :: x1 =>
  if decide (a1 ∈ y) then set_diff x1 y else set_add a1 (set_diff x1 y)
end.

Lemma set_add_intro1 :
 forall (a b:A) (x:set), a ∈ x -> a ∈ (set_add b x).
Proof.
  simple induction x; simpl.
  - intro Hel; inversion Hel.
  - intros a0 l IH.
    rewrite elem_of_cons.
    intros [Ha0a| Hal].
    * subst; destruct (decide (b = a0)); simpl; left; assumption.
    * specialize (IH Hal).
      destruct (decide (b = a0)); right; [ assumption | auto with datatypes ].
Qed.

Lemma set_add_intro2 :
 forall (a b:A) (x:set), a = b -> a ∈ (set_add b x).
Proof.
simple induction x; simpl.
- intro Hab; rewrite Hab; left.
- intros a0 l H Hab.
  specialize (H Hab).
  subst.
  destruct (decide (b = a0)).
  * subst; left.
  * right; assumption.
Qed.

Local Hint Resolve set_add_intro1 set_add_intro2 : core.

Lemma set_add_intro :
 forall (a b:A) (x:set), a = b \/ a ∈ x -> a ∈ (set_add b x).
Proof.
intros a b x [H1| H2]; auto with datatypes.
Qed.

Lemma set_add_elim :
 forall (a b:A) (x:set), a ∈ (set_add b x) -> a = b \/ a ∈ x.
Proof.
simple induction x.
- simpl. rewrite elem_of_cons; intros [H1| H2]; auto with datatypes.
- simpl; intros a0 l IH.
  destruct (decide (b = a0)).
  * simpl; itauto.
  * rewrite elem_of_cons; intros [Heq|Hin].
    + subst; right; left.
    + specialize (IH Hin).
      destruct IH; [left; assumption|].
      right; rewrite elem_of_cons; right.
      assumption.
Qed.

Lemma set_add_not_empty : forall (a:A) (x:set), set_add a x <> empty_set.
Proof.
  simple induction x; cbn; [done |].
  by intros; destruct (decide (a = a0)).
Qed.

Lemma set_add_iff a b l : a ∈ (set_add b l) <-> a = b \/ a ∈ l.
Proof.
split. apply set_add_elim. apply set_add_intro.
Qed.

Lemma set_add_nodup a l : NoDup l -> NoDup (set_add a l).
Proof.
induction 1 as [|x l H H' IH]; simpl.
- constructor; [|apply NoDup_nil; trivial]; intro Ha; inversion Ha.
- destruct (decide (a = x)) as [<-|Hax]; constructor; trivial.
  rewrite set_add_iff. itauto.
Qed.

Lemma set_remove_1 (a b : A) (l : set) : a ∈ (set_remove b l) -> a ∈ l.
Proof.
induction l as [|x xs Hrec].
- intros. auto.
- simpl; destruct (decide (b = x)); rewrite elem_of_cons.
  * itauto.
  * intro H. destruct H.
    + rewrite H. left.
    + rewrite elem_of_cons.
      right; apply Hrec; assumption.
Qed.

Lemma set_remove_2 (a b:A) (l : set) : NoDup l -> a ∈ (set_remove b l) -> a <> b.
Proof.
induction l as [|x l IH]; intro Hnd; simpl.
- intro Hem; inversion Hem.
- inversion_clear Hnd.
  destruct (decide (b = x)) as [<-|Hbx].
  + intros; intro Ha.
    subst; contradiction.
  + rewrite elem_of_cons.
    intros [Ha|Hset].
    * subst; auto.
    * apply IH; assumption.
Qed.

Lemma set_remove_3 (a b : A) (l : set) : a ∈ l -> a <> b -> a ∈ (set_remove b l).
Proof.
induction l as [|x xs Hrec].
- intro Ha; inversion Ha.
- rewrite elem_of_cons; simpl.
  destruct (decide (b = x)) as [<-|Hbx]; simpl.
  + intros [Ha|Hx] Hab; [contradiction|].
    assumption.
  + intros [Ha|Hx] Hab; subst; [left|].
    right.
    apply Hrec; assumption.
Qed.

Lemma set_remove_iff (a b : A) (l : set) :
 NoDup l -> (a ∈ (set_remove b l) <-> a ∈ l /\ a <> b).
Proof.
split; try split.
- eapply set_remove_1; eauto.
- eapply set_remove_2; eauto.
- destruct 1; apply set_remove_3; auto.
Qed.

Lemma set_remove_nodup a l : NoDup l -> NoDup (set_remove a l).
Proof.
induction 1 as [|x l H H' IH]; simpl.
- constructor.
- destruct (decide (a = x)) as [<-|Hax]; trivial.
  constructor; trivial.
  rewrite set_remove_iff; trivial. itauto.
Qed.

Lemma set_union_intro : forall (a:A) (x y:set),
 a ∈ x \/ a ∈ y -> a ∈ (set_union x y).
Proof.
simple induction y; simpl.
- intros [Ha|Ha]; [assumption|].
  inversion Ha.
- intros a0 l IH; rewrite elem_of_cons.
  intros [Ha|Ha].
  + auto with datatypes.
  + destruct Ha.
    * subst; auto with datatypes.
    * auto with datatypes.
Qed.

Lemma set_union_elim :
 forall (a:A) (x y:set), a ∈ (set_union x y) -> a ∈ x \/ a ∈ y.
Proof.
simple induction y; simpl.
- itauto.
- intros; rewrite elem_of_cons.
  destruct (set_add_elim a a0 _ H0).
  + right; left; assumption.
  + itauto.
Qed.

Lemma set_union_iff a l l': a ∈ (set_union l l') <-> a ∈ l \/ a ∈ l'.
Proof.
split. apply set_union_elim. apply set_union_intro.
Qed.

Lemma set_union_nodup l l' : NoDup l -> NoDup l' -> NoDup (set_union l l').
Proof.
induction 2 as [|x' l' ? ? IH]; simpl; trivial. now apply set_add_nodup.
Qed.

Lemma set_diff_intro :
 forall (a:A) (x y:set), a ∈ x -> ~ a ∈ y -> a ∈ (set_diff x y).
Proof.
simple induction x; simpl.
- intros y Hy; inversion Hy.
- intros a0 l Hrec y.
  rewrite elem_of_cons.
  intros [Ha0a| Hal] Hay.
  + subst; rewrite decide_False by assumption.
    auto with datatypes.
  + destruct (decide (a0 ∈ y)).
    * apply Hrec; assumption.
    * auto with datatypes.
Qed.

Lemma set_diff_elim1 : forall (a:A) (x y:set), a ∈ (set_diff x y) -> a ∈ x.
Proof.
simple induction x; simpl.
- intros a0 Ha; inversion Ha.
- intros a0 l Hrec y.
  destruct (decide (a0 ∈ y)); rewrite elem_of_cons.
  + intros Ha.
    right.
    specialize (Hrec _ Ha).
    assumption.
  + intros Ha.
    apply set_add_elim in Ha.
    destruct Ha.
    * left; assumption.
    * right.
      specialize (Hrec _ H).
      assumption.
Qed.

Lemma set_diff_elim2 : forall (a:A) (x y:set), a ∈ (set_diff x y) -> ~ a ∈ y.
Proof.
simple induction x; simpl.
- intros y Ha; inversion Ha.
- intros a0 l IH y.
  destruct (decide (a0 ∈ y)); intros Ha.
  + apply IH; assumption.
  + apply set_add_elim in Ha.
    destruct Ha.
    * subst; assumption.
    * apply IH; assumption.
Qed.

Lemma set_diff_iff a l l' : a ∈ (set_diff l l') <-> a ∈ l /\ ~a ∈ l'.
Proof.
split.
  - split; [eapply set_diff_elim1 | eapply set_diff_elim2]; eauto.
  - destruct 1. now apply set_diff_intro.
Qed.

Lemma set_diff_nodup l l' : NoDup l -> NoDup (set_diff l l').
Proof.
induction 1 as [|x l H H' IH]; simpl.
- constructor.
- case_decide.
  + apply IH; assumption.
  + apply set_add_nodup.
    apply IH.
Qed.

End fst_defs.

Arguments set : clear implicits.

Section other_defs.

Definition set_prod : forall {A B:Type}, set A -> set B -> set (A * B) :=
 list_prod.

Definition set_fold_right {A B:Type} (f:A -> B -> B) (x:set A)
 (b:B) : B := fold_right f b x.

Definition set_map {A B:Type} `{EqDecision B}
 (f : A -> B) (x : set A) : set B :=
 set_fold_right (fun a => set_add (f a)) x empty_set.

End other_defs.
