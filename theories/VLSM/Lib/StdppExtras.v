From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From VLSM.Lib Require Import Preamble ListExtras.

(** * Std++ Related Results **)

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
  - by destruct n; cbn; auto.
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
  - by typeclasses eauto.
  - by apply existsb_Exists.
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
  - typeclasses eauto.
  - by apply existsb_Exists.
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
    setoid_rewrite elem_of_cons in H1.
    destruct (decide (P a)); destruct (decide (Q a)); [|firstorder ..].
    rewrite IHl; [done |]. firstorder.
Qed.

Lemma ext_elem_of_filter {A} P Q
 `{∀ (x:A), Decision (P x)} `{∀ (x:A), Decision (Q x)}
 (l : list A) :
 filter P l = filter Q l -> forall a, a ∈ l -> (P a <-> Q a).
Proof.
  intros.
  split; intros.
  - by eapply elem_of_list_filter; rewrite <- H1; apply elem_of_list_filter.
  - by eapply elem_of_list_filter; rewrite H1; apply elem_of_list_filter.
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
  - apply filter_ext_elem_of. intros.
    specialize (ext_elem_of_filter _ _ l H1 a H2) as Hext; cbn in Hext.
    destruct (decide (P a)); destruct (decide (Q a)); itauto.
Qed.

Lemma NoDup_elem_of_remove A (l l' : list A) a :
  NoDup (l ++ a :: l') -> NoDup (l ++ l') /\ a ∉ (l ++ l').
Proof.
  intros Hnda.
  apply NoDup_app in Hnda.
  destruct Hnda as [Hnd [Ha Hnda]].
  apply NoDup_cons in Hnda.
  setoid_rewrite elem_of_cons in Ha.
  destruct Hnda as [Ha' Hnd']; split.
  - by apply NoDup_app; firstorder.
  - by rewrite elem_of_app; firstorder.
Qed.

Lemma list_lookup_lt [A] (is : list A) :
  forall i, is_Some (is !! i) ->
  forall j, j < i -> is_Some (is !! j).
Proof.
  intros; apply lookup_lt_is_Some.
  by etransitivity; [| apply lookup_lt_is_Some].
Qed.

Lemma list_suffix_lookup
  {A : Type}
  (s : list A)
  (n : nat)
  (i : nat)
  (Hi : n <= i)
  : list_suffix s n !! (i - n) = s !! i.
Proof.
  revert s n Hi; induction i; intros [| a s] [| n] Hi; cbn; try done; [| apply IHi]; lia.
Qed.

Lemma longer_subseteq_has_dups `{EqDecision A} :
  forall l1 l2 : list A, l1 ⊆ l2 -> length l1 > length l2 ->
  exists (i1 i2 : nat) (a : A), i1 ≠ i2 ∧ l1 !! i1 = Some a /\ l1 !! i2 = Some a.
Proof.
  induction l1; [inversion 2 |].
  intros l2 Hl12 Hlen12.
  destruct (decide (a ∈ l1)).
  - exists 0.
    apply elem_of_list_lookup_1 in e as [i2 Hi2].
    by exists (S i2), a.
  - edestruct (IHl1 (list_difference l2 [a]))
           as (i1 & i2 & a' & Hi12 & Hli1 & Hli2); cycle 2.
    + exists (S i1), (S i2), a'; cbn; itauto.
    + intros x Hx.
      rewrite elem_of_list_difference, elem_of_list_singleton.
      by split; [apply Hl12; right | by contradict n; subst].
    + cbn in Hlen12.
      assert (Ha : a ∈ l2) by (apply Hl12; left).
      specialize (list_difference_singleton_length_in _ _ Ha) as Hlen'; lia.
Qed.

Lemma ForAllSuffix2_lookup [A : Type] (R : A -> A -> Prop) l
  : ForAllSuffix2 R l <-> forall n a b, l !! n = Some a -> l !! (S n) = Some b -> R a b.
Proof.
  split.
  - induction 1; cbn; [inversion 2 |].
    destruct n as [| n']; cbn.
    + by destruct l; do 2 inversion 1; subst.
    + by intros; eapply IHForAllSuffix.
  - induction l as [| a [| b l']]; cbn.
    + by constructor.
    + by repeat constructor.
    + constructor.
      * by apply (H 0).
      * by apply IHl; intro n; apply (H (S n)).
Qed.

Lemma ForAllSuffix2_transitive_lookup
  [A : Type] (R : A -> A -> Prop) {HT : Transitive R} (l : list A)
  : ForAllSuffix2 R l <-> forall m n a b, m < n -> l !! m = Some a -> l !! n = Some b -> R a b.
Proof.
  rewrite ForAllSuffix2_lookup.
  split; intro Hall; [| by intros n a b; apply Hall; lia].
  intros m n a b Hlt.
  apply le_plus_dec in Hlt as [k Hlt]; subst n.
  revert a b; induction k; cbn; [apply Hall |].
  intros a b Ha Hb.
  assert (Hlt : k + S m < length l) by (apply lookup_lt_Some in Hb; lia).
  apply lookup_lt_is_Some in Hlt as [c Hc].
  by transitivity c; [apply IHk | eapply Hall].
Qed.
