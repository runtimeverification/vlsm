From VLSM.Lib Require Import Itauto.
From stdpp Require Import prelude.
From VLSM.Lib Require Import Preamble ListExtras.

(** * Std++ Related Results *)

Lemma elem_of_take {A : Type} (l : list A) (n : nat) (x : A) :
  elem_of x (take n l) -> elem_of x l.
Proof.
  generalize dependent n.
  induction l; intros n H.
  - by simpl in H; destruct n; simpl in H; inversion H.
  - destruct n; [by inversion H |].
    simpl in H.
    apply elem_of_cons in H as [-> | H].
    + by left.
    + by right; eapply IHl.
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

Lemma existsb_Exists {A} (f : A -> bool) :
  forall l, existsb f l = true <-> Exists (fun x => f x = true) l.
Proof.
  intro l.
  rewrite Exists_exists, existsb_exists.
  by setoid_rewrite elem_of_list_In.
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
         ~ Exists P suffix.

Proof.
  induction l using rev_ind; [by inversion Hsomething |].
  destruct (decide (P x)).
  - exists l, nil, x.
    rewrite Exists_nil.
    by itauto.
  - apply Exists_app in Hsomething.
    destruct Hsomething; [| by inversion H; [| inversion H1]].
    specialize (IHl H); clear H.
    destruct IHl as [prefix [suffix [last [Hf [-> Hnone_after]]]]].
    exists prefix, (suffix ++ [x]), last.
    simpl. rewrite app_assoc_reverse. simpl.
    rewrite Exists_app. rewrite Exists_cons. rewrite Exists_nil.
    by itauto.
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

Lemma existsb_forall {A} (f : A -> bool) :
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
  - by typeclasses eauto.
  - by apply existsb_Exists.
Qed.

(*
  Returns all elements <<X>> of <<l>> such that <<X>> does not compare less
  than any other element w.r.t to the precedes relation.
*)

Definition maximal_elements_list
  {A} (precedes : relation A) `{!RelDecision precedes} (l : list A)
  : list A :=
  filter (fun a => Forall (fun b => ~ precedes a b) l) l.

Example maximal_elements_list1 : maximal_elements_list Nat.lt [1; 4; 2; 4] = [4; 4].
Proof. by itauto. Qed.

Example maximal_elements_list2 : maximal_elements_list Nat.le [1; 4; 2; 4] = [].
Proof. by itauto. Qed.

(**
  Returns all elements <<x>> of a set <<S>> such that <<x>> does not compare less
  than any other element in <<S>> w.r.t to a given precedes relation.
*)
Definition maximal_elements_set
  `{HfinSetMessage : FinSet A SetA}
   (precedes : relation A) `{!RelDecision precedes} (s : SetA)
   : SetA :=
    filter (fun a => set_Forall (fun b => ~ precedes a b) s) s.

Lemma filter_ext_elem_of {A} P Q
 `{forall (x : A), Decision (P x)} `{forall (x : A), Decision (Q x)} (l : list A) :
 (forall a, a ∈ l -> (P a <-> Q a)) ->
 filter P l = filter Q l.
Proof.
  induction l; intros.
  - by rewrite 2 filter_nil.
  - rewrite 2 filter_cons.
    setoid_rewrite elem_of_cons in H1.
    by destruct (decide (P a)), (decide (Q a)); [rewrite IHl | ..]; firstorder.
Qed.

Lemma ext_elem_of_filter {A} P Q
 `{forall (x : A), Decision (P x)} `{forall (x : A), Decision (Q x)}
 (l : list A) :
 filter P l = filter Q l -> forall a, a ∈ l -> (P a <-> Q a).
Proof.
  intros.
  split; intros.
  - by eapply elem_of_list_filter; rewrite <- H1; apply elem_of_list_filter.
  - by eapply elem_of_list_filter; rewrite H1; apply elem_of_list_filter.
Qed.

Lemma filter_complement {X} P Q
 `{forall (x : X), Decision (P x)} `{forall (x : X), Decision (Q x)}
 (l : list X) :
 filter P l = filter Q l <->
 filter (fun x => ~ P x) l = filter (fun x => ~ Q x) l.
Proof.
  split; intros.
  - specialize (ext_elem_of_filter P Q l H1) as Hext.
    apply filter_ext_elem_of.
    intros.
    specialize (Hext a H2).
    by rewrite Hext; itauto.
  - apply filter_ext_elem_of. intros.
    specialize (ext_elem_of_filter _ _ l H1 a H2) as Hext; cbn in Hext.
    by destruct (decide (P a)), (decide (Q a)); itauto.
Qed.

Lemma NoDup_elem_of_remove A (l l' : list A) a :
  NoDup (l ++ a :: l') -> NoDup (l ++ l') /\ a ∉ l ++ l'.
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
  by revert s n Hi; induction i; intros [| a s] [| n] Hi; cbn; try done; [| apply IHi]; lia.
Qed.

Lemma list_difference_singleton_not_in `{EqDecision A} :
  forall (l : list A) (a : A), a ∉ l ->
    list_difference l [a] = l.
Proof.
  intros l a; induction l; [done |].
  rewrite not_elem_of_cons; intros [Hna0 Hnal]; cbn.
  case_decide as Ha0; [by apply elem_of_list_singleton in Ha0 |].
  by rewrite IHl.
Qed.

Lemma list_difference_singleton_length_in `{EqDecision A} :
  forall (l : list A) (a : A), a ∈ l ->
    length (list_difference l [a]) < length l.
Proof.
  intros l a; induction l; cbn; [by inversion 1 |].
  case_decide as Ha0; rewrite elem_of_list_singleton in Ha0.
  - subst; intros _.
    destruct (decide (a ∈ l)).
    + by etransitivity; [apply IHl | lia].
    + by rewrite list_difference_singleton_not_in; [lia |].
  - by inversion 1; subst; [done |]; cbn; spec IHl; [| lia].
Qed.

Lemma longer_subseteq_has_dups `{EqDecision A} :
  forall l1 l2 : list A, l1 ⊆ l2 -> length l1 > length l2 ->
  exists (i1 i2 : nat) (a : A), i1 <> i2 /\ l1 !! i1 = Some a /\ l1 !! i2 = Some a.
Proof.
  induction l1; [by inversion 2 |].
  intros l2 Hl12 Hlen12.
  destruct (decide (a ∈ l1)).
  - exists 0.
    apply elem_of_list_lookup_1 in e as [i2 Hi2].
    by exists (S i2), a.
  - edestruct (IHl1 (list_difference l2 [a]))
           as (i1 & i2 & a' & Hi12 & Hli1 & Hli2); cycle 2.
    + by exists (S i1), (S i2), a'; cbn; itauto.
    + intros x Hx.
      rewrite elem_of_list_difference, elem_of_list_singleton.
      by split; [apply Hl12; right | by contradict n; subst].
    + cbn in Hlen12.
      assert (Ha : a ∈ l2) by (apply Hl12; left).
      by specialize (list_difference_singleton_length_in _ _ Ha) as Hlen'; lia.
Qed.

Lemma ForAllSuffix2_lookup [A : Type] (R : A -> A -> Prop) l
  : ForAllSuffix2 R l <-> forall n a b, l !! n = Some a -> l !! (S n) = Some b -> R a b.
Proof.
  split.
  - induction 1; cbn; [by inversion 2 |].
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

Lemma stdpp_nat_le_sum (x y : nat) : x <= y <-> exists z, y = x + z.
Proof.
  split.
  - by exists (y - x); lia.
  - by intros [z ->]; lia.
Qed.

Lemma ForAllSuffix2_transitive_lookup
  [A : Type] (R : A -> A -> Prop) {HT : Transitive R} (l : list A)
  : ForAllSuffix2 R l <-> forall m n a b, m < n -> l !! m = Some a -> l !! n = Some b -> R a b.
Proof.
  rewrite ForAllSuffix2_lookup.
  split; intro Hall; [| by intros n a b; apply Hall; lia].
  intros m n a b Hlt.
  apply stdpp_nat_le_sum in Hlt as [k ->]; rewrite Nat.add_comm.
  revert a b; induction k; cbn; [by apply Hall |].
  intros a b Ha Hb.
  assert (Hlt : k + S m < length l) by (apply lookup_lt_Some in Hb; lia).
  apply lookup_lt_is_Some in Hlt as [c Hc].
  by transitivity c; [apply IHk | eapply Hall].
Qed.

(**
  If the <<n>>-th element of <<l>> is <<x>>, then we can decompose long enough
  suffixes of <<l>> into <<x>> and a suffix shorter by 1.
*)
Lemma lastn_length_cons :
  forall {A : Type} (n : nat) (l : list A) (x : A),
    l !! n = Some x -> lastn (length l - n) l = x :: lastn (length l - S n) l.
Proof.
  intros A n l x H.
  unfold lastn.
  rewrite <- rev_length, <- !skipn_rev, rev_involutive.
  by apply drop_S.
Qed.

Lemma filter_in {A} P `{forall (x : A), Decision (P x)} x s :
  In x s ->
  P x ->
  In x (filter P s).
Proof.
  intros.
  apply elem_of_list_In.
  apply elem_of_list_In in H0.
  by apply elem_of_list_filter.
Qed.

Lemma list_subseteq_filter {A} P Q
  `{forall (x : A), Decision (P x)} `{forall (x : A), Decision (Q x)} :
  (forall a, P a -> Q a) ->
  forall s : list A, filter P s ⊆ filter Q s.
Proof.
  induction s; cbn; intros x Hin; [done |].
  by destruct (decide (P a)), (decide (Q a)); cbn in *; rewrite ?elem_of_cons in *; itauto.
Qed.

Lemma filter_length_fn {A} P Q
  `{forall (x : A), Decision (P x)} `{forall (x : A), Decision (Q x)}
  s (Hfg : Forall (fun a => P a -> Q a) s) :
  length (filter P s) <= length (filter Q s).
Proof.
  induction s; simpl; [lia |].
  inversion Hfg; subst. specialize (IHs H4).
  rewrite 2 filter_cons.
  by destruct (decide (P a)), (decide (Q a)); cbn; itauto lia.
Qed.

Lemma filter_eq_fn {A} P Q
 `{forall (x : A), Decision (P x)} `{forall (x : A), Decision (Q x)} s :
  (forall a, In a s -> P a <-> Q a) ->
  filter P s = filter Q s.
Proof.
  induction s; intros; [done |].
  assert (IHs' : forall a : A, In a s -> P a <-> Q a) by (intros; apply H1; right; done).
  apply IHs in IHs'.
  erewrite !filter_cons, decide_ext.
  - by rewrite IHs'.
  - by apply H1; left.
Qed.

Lemma nth_error_filter
  {A} P `{forall (x : A), Decision (P x)}
  (l : list A)
  (n : nat)
  (a : A)
  (Hnth : nth_error (filter P l) n = Some a)
  : exists (nth : nat),
    nth_error_filter_index P l n = Some nth
    /\ nth_error l nth = Some a.
Proof.
  generalize dependent a. generalize dependent n.
  induction l.
  - by intros []; cbn; inversion 1.
  - intros. rewrite filter_cons in Hnth. simpl. destruct (decide (P a)).
    + destruct n.
      * by inversion Hnth; subst; exists 0.
      * simpl in Hnth.
        specialize (IHl n a0 Hnth).
        destruct IHl as [nth [Hnth' Ha0]].
        exists (S nth).
        by rewrite Hnth'.
    + specialize (IHl n a0 Hnth).
      destruct IHl as [nth [Hnth' Ha0]].
      exists (S nth).
      by rewrite Hnth'.
Qed.

Lemma filter_subseteq {A} P `{forall (x : A), Decision (P x)} (s1 s2 : list A) :
  s1 ⊆ s2 ->
  filter P s1 ⊆ filter P s2.
Proof.
  induction s1; intros; intro x; intros.
  - by apply not_elem_of_nil in H1.
  - rewrite filter_cons in H1.
    destruct (decide (P a)).
    + rewrite elem_of_cons in H1.
      destruct H1.
      * subst; apply elem_of_list_filter.
        by split; [| apply H0; left].
      * apply IHs1; [| done].
        by intros y Hel; apply H0; right.
    + apply IHs1; [| done].
      by intros y Hel; apply H0; right.
Qed.

Lemma filter_subseteq_fn {A} P Q
  `{forall (x : A), Decision (P x)} `{forall (x : A), Decision (Q x)} :
  (forall a, P a -> Q a) ->
  forall (s : list A), filter P s ⊆ filter Q s.
Proof.
  induction s; cbn; intros x H2; [by inversion H2 |].
  destruct (decide (P a)), (decide (Q a)); rewrite ?elem_of_cons in H2.
  - by destruct H2 as [-> |]; [left | right; apply IHs].
  - by itauto.
  - by right; apply IHs.
  - by itauto.
Qed.

Lemma Forall_filter_nil {A} P `{forall (x : A), Decision (P x)} l :
  Forall (fun a : A => ~ P a) l <-> filter P l = [].
Proof.
  rewrite Forall_forall.
  split; intro Hnone.
  - induction l; cbn; [done |].
    setoid_rewrite elem_of_cons in Hnone.
    by rewrite decide_False; auto.
  - intros x Hel Px.
    by eapply filter_nil_not_elem_of in Px.
Qed.

Lemma elem_of_list_annotate_forget
  {A : Type}
  (P : A -> Prop)
  {Pdec : forall a, Decision (P a)}
  (l : list A)
  (Hs : Forall P l)
  (xP : dsig P)
  (Hin : xP ∈ list_annotate P l Hs)
  : proj1_sig xP ∈ l.
Proof.
  induction l.
  - by inversion Hin.
  - rewrite list_annotate_unroll, elem_of_cons in Hin.
    destruct Hin as [-> | Hin].
    + by left.
    + by right; apply (IHl (Forall_tl Hs)).
Qed.

Lemma elem_of_list_annotate
  `{EqDecision A}
  (P : A -> Prop)
  {Pdec : forall a, Decision (P a)}
  (l : list A)
  (Hs : Forall P l)
  (xP : dsig P)
  : xP ∈ list_annotate P l Hs <-> (` xP) ∈ l.
Proof.
  split; [by apply elem_of_list_annotate_forget |].
  destruct xP as [x Hpx]; cbn.
  by induction 1; cbn; rewrite elem_of_cons, dsig_eq; cbn; auto.
Qed.

Lemma occurrences_ordering
  {A : Type}
  (a b : A)
  (la1 la2 lb1 lb2 : list A)
  (Heq : la1 ++ a :: la2 = lb1 ++ b :: lb2)
  (Ha : a ∉ b :: lb2)
  : exists lab : list A, lb1 = la1 ++ a :: lab.
Proof.
  generalize dependent lb2. generalize dependent la2.
  generalize dependent b. generalize dependent lb1.
  generalize dependent a.
  induction la1; intros; destruct lb1 as [| b0 lb1]; simpl in *
  ; inversion Heq; subst.
  - by contradict Ha; left.
  - by exists lb1.
  - by contradict Ha; rewrite elem_of_cons, elem_of_app, elem_of_cons; auto.
  - specialize (IHla1 a0 lb1 b la2 lb2 H1 Ha).
    destruct IHla1 as [la0b Hla0b].
    by exists la0b; subst.
Qed.

Lemma list_max_elem_of_exists
   (l : list nat)
   (nz : list_max l > 0) :
   list_max l ∈ l.
Proof.
  induction l; simpl in *; [lia |].
  rewrite elem_of_cons.
  by destruct (Nat.max_spec_le a (list_max l)) as [[H ->] | [H ->]]; itauto lia.
Qed.

Lemma map_option_subseteq
  {A B : Type}
  (f : A -> option B)
  (l1 l2 : list A)
  (Hincl : l1 ⊆ l2)
  : map_option f l1 ⊆ map_option f l2.
Proof.
  by intros b; rewrite !elem_of_map_option; firstorder.
Qed.

Lemma elem_of_cat_option
  {A : Type}
  (l : list (option A))
  (a : A)
  : a ∈ cat_option l <-> exists b : option A, b ∈ l /\ b = Some a.
Proof.
  by apply elem_of_map_option.
Qed.

Lemma list_max_elem_of_exists2
   (l : list nat)
   (Hne : l <> []) :
   list_max l ∈ l.
Proof.
  destruct (list_max l) eqn: eq_max.
  - destruct l; [by itauto congruence |].
    specialize (list_max_le (n :: l) 0) as Hle.
    destruct Hle as [Hle _].
    rewrite eq_max in Hle. spec Hle. apply Nat.le_refl.
    rewrite Forall_forall in Hle.
    specialize (Hle n). spec Hle. left.
    assert (Hn0 : n = 0) by lia.
    by rewrite Hn0; left.
  - specialize (list_max_elem_of_exists l) as Hmax.
    by rewrite <- eq_max; itauto lia.
Qed.

Lemma mode_not_empty
  `{EqDecision A}
  (l : list A)
  (Hne : l <> []) :
  mode l <> [].
Proof.
  destruct l; [done |].
  remember (a :: l) as l'.
  remember (List.map (count_occ decide_eq l') l') as occurrences.

  assert (Hmaxp : list_max occurrences > 0). {
    rewrite Heqoccurrences, Heql'; cbn.
    by rewrite decide_True; [lia |].
  }

  assert (exists a, (count_occ decide_eq l' a) = list_max occurrences). {
    assert (In (list_max occurrences) occurrences) by (apply list_max_exists; done).
    rewrite Heqoccurrences, in_map_iff in H.
    destruct H as (x & Heq & Hin).
    by rewrite Heqoccurrences; eauto.
  }

  assert (exists a, In a (mode l')). {
    destruct H.
    exists x.
    specialize (count_occ_In decide_eq l' x).
    intros.
    destruct H0 as [_ H1].
    rewrite H in H1.
    specialize (H1 Hmaxp).
    unfold mode.
    apply filter_in; [done |].
    by rewrite H, Heqoccurrences.
  }
  intros contra; rewrite contra in H0.
  by destruct H0 as [? []].
Qed.

(**
  When a list contains two elements, either they are equal or we can split
  the list into three parts separated by the elements (and this can be done
  in two ways, depending on the order of the elements).
*)
Lemma elem_of_list_split_2 :
  forall {A : Type} (l : list A) (x y : A),
    x ∈ l -> y ∈ l ->
      x = y \/ exists l1 l2 l3 : list A,
        l = l1 ++ x :: l2 ++ y :: l3 \/ l = l1 ++ y :: l2 ++ x :: l3.
Proof.
  intros A x y l Hx Hy.
  apply elem_of_list_split in Hx as (l1 & l2 & ->).
  rewrite elem_of_app, elem_of_cons in Hy.
  destruct Hy as [Hy | [-> | Hy]]; [| by left |].
  - apply elem_of_list_split in Hy as (l11 & l12 & ->).
    right; exists l11, l12, l2; right; cbn.
    by rewrite <- app_assoc.
  - apply elem_of_list_split in Hy as (l21 & l22 & ->).
    by right; exists l1, l21, l22; left; cbn.
Qed.

Lemma mjoin_app {A} (l1 l2 : list (list A)) :
  mjoin (l1 ++ l2) = mjoin l1 ++ mjoin l2.
Proof.
  induction l1; cbn; [done |].
  replace (mjoin (l1 ++ l2)) with (mjoin l1 ++ mjoin l2).
  by rewrite app_assoc.
Qed.

Lemma mbind_app `(f : A -> list B) (l1 l2 : list A) :
  mbind f (l1 ++ l2) = mbind f l1 ++ mbind f l2.
Proof. by induction l1; [| cbn; rewrite IHl1, app_assoc]. Qed.

Lemma mbind_nils :
  forall {A B : Type} (f : A -> list B) (l : list A),
    Forall (fun x : A => f x = []) l ->
      mbind f l = [].
Proof.
  induction 1; cbn; [done |].
  by rewrite H, IHForall; cbn.
Qed.

Lemma list_subseteq_inv_app :
  forall {A : Type} (l1 l2 l3 : list A),
    l1 ++ l2 ⊆ l3 -> l1 ⊆ l3 /\ l2 ⊆ l3.
Proof.
  unfold subseteq, list_subseteq.
  intros A l1 l2 l3 Hsub.
  split; intros x Hin.
  - by apply Hsub, elem_of_app; left.
  - by apply Hsub, elem_of_app; right.
Qed.
