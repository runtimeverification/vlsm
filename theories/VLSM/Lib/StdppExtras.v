From Cdcl Require Import Itauto. Local Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From VLSM.Lib Require Import ListExtras.

Lemma elem_of_take {A : Type} (l : list A) (n : nat) (x : A) :
  elem_of x (take n l) -> elem_of x l.
Proof.
  generalize dependent n.
  induction l; intros n H.
  - simpl in H. destruct n; simpl in H; inversion H.
  - simpl in H.
    destruct n.
    { simpl in H. inversion H. }
    simpl in H.
    apply elem_of_cons in H.
    destruct H as [H|H].
    { subst. simpl. left. }
    simpl. right.
    eauto.
Qed.

Lemma map_skipn [A B : Type] (f : A -> B) (l : list A) (n : nat) :
  map f (skipn n l) = skipn n (map f l).
Proof.
  revert n; induction l; intros n.
  - by rewrite !skipn_nil.
  - cbn. destruct n; cbn; auto.
Qed.

Lemma map_firstn [A B : Type] (f : A -> B) (l : list A) (n : nat) :
  map f (firstn n l) = firstn n (map f l).
Proof.
  generalize dependent n.
  induction l; intros n.
  - by cbn; rewrite !firstn_nil.
  - by destruct n; cbn; rewrite ?IHl.
Qed.

Lemma skipn_S_tail {A : Type} (l : list A) (n : nat) :
  skipn (S n) l = (skipn n (tail l)).
Proof.
  by destruct l; cbn; rewrite ?drop_nil.
Qed.

Lemma skipn_tail_comm {A : Type} (l : list A) (n : nat) :
  skipn n (tail l) = tail (skipn n l).
Proof.
  revert l; induction n; intros l.
  - by rewrite !drop_0.
  - by rewrite !skipn_S_tail, IHn.
Qed.

Lemma map_tail [A B : Type] (f : A -> B) (l : list A) :
  map f (tail l) = tail (map f l).
Proof.
  by destruct l.
Qed.

Lemma nth_error_stdpp_last {A : Type} (l : list A) :
  nth_error l (length l - 1) = last l.
Proof.
  induction l; [done |].
  destruct l; [done |]; cbn in *.
  by rewrite <- IHl, Nat.sub_0_r.
Qed.

Lemma last_last_error {A : Type} (l : list A) :
  last_error l = last l.
Proof.
  induction l; [done |].
  rewrite last_cons, <- IHl; clear IHl.
  destruct l; [done |]; cbn; f_equal.
  induction l; [done |]; cbn.
  rewrite <- IHl.
  by destruct l.
Qed.

Lemma existsb_Exists {A} (f : A -> bool):
  forall l, existsb f l = true <-> Exists (fun x => f x = true) l.
Proof.
  intro l.
  rewrite Exists_exists.
  rewrite existsb_exists.
  setoid_rewrite elem_of_list_In.
  auto.
Qed.

Lemma Exists_last
  {A : Type}
  (l : list A)
  (P : A -> Prop)
  (Pdec : forall a, Decision (P a))
  (Hsomething : Exists P l)
  : exists (prefix : list A)
         (suffix : list A)
         (last : A),
         P last /\
         l = prefix ++ [last] ++ suffix /\
         ~Exists P suffix.

Proof.
  induction l using rev_ind;[solve[inversion Hsomething]|].
  destruct (decide (P x)).
  - exists l, nil, x.
    rewrite Exists_nil.
    itauto.
  - apply Exists_app in Hsomething.
    destruct Hsomething.
    2:{ inversion H; [done |]. inversion H1. }
    specialize (IHl H);clear H.
    destruct IHl as [prefix [suffix [last [Hf [-> Hnone_after]]]]].
    exists prefix, (suffix ++ [x]), last.
    simpl. rewrite app_assoc_reverse. simpl.
    rewrite Exists_app. rewrite Exists_cons. rewrite Exists_nil.
    itauto.
Qed.

Lemma existsb_last
  {A : Type}
  (l : list A)
  (f : A -> bool)
  (Hsomething : existsb f l = true) :
  exists (prefix : list A)
         (suffix : list A)
         (last : A),
         (f last = true) /\
         l = prefix ++ [last] ++ suffix /\
         (existsb f suffix = false).
Proof.
  setoid_rewrite <-not_true_iff_false.
  setoid_rewrite existsb_Exists.
  apply Exists_last.
  { intro a; solve_decision. }
  apply existsb_Exists;assumption.
Qed.

Lemma existsb_forall {A} (f : A -> bool):
  forall l, existsb f l = false <-> forall x, In x l -> f x = false.
Proof.
  intro l.
  setoid_rewrite <- not_true_iff_false.
  setoid_rewrite <- elem_of_list_In.
  by rewrite existsb_Exists, <- Forall_Exists_neg, Forall_forall.
Qed.

Lemma existsb_first
  {A : Type}
  (l : list A)
  (f : A -> bool)
  (Hsomething : existsb f l = true) :
  exists (prefix : list A)
         (suffix : list A)
         (first : A),
         (f first = true) /\
         l = prefix ++ [first] ++ suffix /\
         (existsb f prefix = false).
Proof.
  setoid_rewrite <-not_true_iff_false.
  setoid_rewrite existsb_Exists.
  apply Exists_first.
  { intro a. solve_decision. }
  apply existsb_Exists;assumption.
Qed.

(* Returns all elements X of l such that X does not compare less
   than any other element w.r.t to the precedes relation *)

Definition maximal_elements_list
  {A} (precedes: relation A) `{!RelDecision precedes} (l : list A)
  : list A :=
  filter (fun a => Forall (fun b => (~ precedes a b)) l) l.

Example maximal_elements_list1: maximal_elements_list Nat.lt [1; 4; 2; 4] = [4;4].
Proof. itauto. Qed.

Example maximal_elements_list2 : maximal_elements_list Nat.le [1; 4; 2; 4] = [].
Proof. itauto. Qed.

(**
Returns all elements <<x>> of a set <<S>> such that <<x>> does not compare less
than any other element in <<S>> w.r.t to a given precedes relation.
*)
Definition maximal_elements_set
  `{HfinSetMessage : FinSet A SetA}
   (precedes: relation A) `{!RelDecision precedes} (s : SetA)
   : SetA :=
    filter (fun a => set_Forall (fun b => ~ precedes a b) s) s.

Lemma filter_ext_elem_of {A} P Q
 `{∀ (x:A), Decision (P x)} `{∀ (x:A), Decision (Q x)} (l:list A) :
 (forall a, a ∈ l -> (P a <-> Q a)) ->
 filter P l = filter Q l.
Proof.
  induction l; intros.
  - by rewrite 2 filter_nil.
  - rewrite 2 filter_cons.
    destruct (decide (P a)); destruct (decide (Q a)).
    + rewrite IHl; [done |].
      intros.
      apply H1.
      right; assumption.
    + contradict n.
      by apply H1; [left |].
    + contradict n.
      by apply H1; [left |].
    + apply IHl.
      intros.
      apply H1.
      right; assumption.
Qed.

Lemma ext_elem_of_filter {A} P Q
 `{∀ (x:A), Decision (P x)} `{∀ (x:A), Decision (Q x)}
 (l : list A) :
 filter P l = filter Q l -> forall a, a ∈ l -> (P a <-> Q a).
Proof.
  intros.
  split; intros.
  - assert (a ∈ filter P l). {
      apply elem_of_list_filter.
      split; assumption.
    }
    rewrite H1 in H4.
    apply elem_of_list_filter in H4.
    destruct H4; assumption.
  - assert (a ∈ filter Q l). {
      apply elem_of_list_filter.
      split; assumption.
    }
    rewrite <- H1 in H4.
    apply elem_of_list_filter in H4.
    destruct H4; assumption.
Qed.

Lemma filter_complement {X} P Q
 `{∀ (x:X), Decision (P x)} `{∀ (x:X), Decision (Q x)}
 (l : list X) :
 filter P l = filter Q l <->
 filter (fun x => ~ P x) l = filter (fun x => ~ Q x) l.
Proof.
   split; intros.
   - specialize (ext_elem_of_filter P Q l H1) as Hext.
     apply filter_ext_elem_of.
     intros.
     specialize (Hext a H2).
     rewrite Hext. itauto.
   - specialize (ext_elem_of_filter _ _ l H1) as Hext.
     apply filter_ext_elem_of. intros.
     specialize (Hext a H2).
     destruct (decide (P a)); destruct (decide (Q a)).
     * itauto.
     * apply Hext in n.
       contradict n; assumption.
     * apply Hext in n.
       contradict n; assumption.
     * itauto.
Qed.

Lemma NoDup_elem_of_remove A (l l' : list A) a :
  NoDup (l ++ a :: l') -> NoDup (l ++ l') /\ a ∉ (l ++ l').
Proof.
  intros Hnda.
  apply NoDup_app in Hnda.
  destruct Hnda as [Hnd [Ha Hnda]].
  apply NoDup_cons in Hnda.
  destruct Hnda as [Ha' Hnd']; split.
  - apply NoDup_app; split; [assumption|split;[|assumption]].
    intros x Hxl.
    specialize (Ha x Hxl).
    intro Hxl'; contradict Ha; right; assumption.
  - rewrite elem_of_app.
    intro Hal.
    destruct Hal as [Hal|Hal]; [| done].
    specialize (Ha a Hal).
    contradict Ha; left.
Qed.
