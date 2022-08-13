From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From Coq Require Import Sorting.
From VLSM.Lib Require Import Preamble ListExtras ListSetExtras.

(** * Sorted list utility functions and lemmas **)

Fixpoint list_compare {A} (compare : A -> A -> comparison)
    (l1 l2 : list A) : comparison :=
  match l1,l2 with
  | [], [] => Eq
  | [], _ => Lt
  | _, [] => Gt
  | (h1 :: t1), (h2 :: t2) =>
    match compare h1 h2 with
    | Eq => @list_compare A compare t1 t2
    | cmp => cmp
    end
  end.

#[export] Instance list_compare_strict_order {A} {compare : A -> A -> comparison} `{CompareStrictOrder A compare} :
  CompareStrictOrder (@list_compare A compare).
Proof.
  intros. destruct H as [R T].
  split.
  - intro x. induction x; intros; destruct y; split; intros; try done.
    + simpl in H. destruct (compare a a0) eqn: Hcmp; try done.
      apply compare_eq in Hcmp as ->. by apply IHx in H as ->.
    + inversion H; subst; cbn. by rewrite compare_eq_refl, IHx.
  - intros x y. generalize dependent x.
    induction y; intros; destruct x; destruct z; try done
    ; destruct comp; try done
    ; inversion H; clear H; destruct (compare a0 a) eqn:Ha0; try done
    ; inversion H0; clear H0; destruct (compare a a1) eqn:Ha1; try done
    ; try apply (IHy _ _ _ H2) in H1; try apply (T _ _ _ _ Ha0) in Ha1
    ; try apply R in Ha0; subst
    ; try (by simpl; rewrite Ha1; try rewrite H1, H2)
    ; try (by simpl; rewrite Ha1; rewrite H2)
    ; try (by apply R in Ha1; subst; simpl;  rewrite Ha0; rewrite H1)
    .
Defined.

Lemma list_compare_eq_dec {A} {compare : A -> A -> comparison} `{CompareStrictOrder A compare} :
  (forall x y : list A, {x = y} + {x <> y}).
Proof.
  intros.
  apply compare_eq_dec.
Qed.

Fixpoint add_in_sorted_list_fn {A} (compare : A -> A -> comparison) (x : A) (l : list A) : list A :=
  match l with
  | [] => [x]
  | h :: t =>
    match compare x h with
    | Lt => x :: h :: t
    | Eq => h :: t
    | Gt => h :: @add_in_sorted_list_fn A compare x t
    end
  end.

Lemma add_in_sorted_list_in {A} {compare : A -> A -> comparison} `{CompareStrictOrder A compare} : forall msg msg' sigma,
  msg' ∈ (add_in_sorted_list_fn compare msg sigma) ->
  msg = msg' \/ msg' ∈ sigma.
Proof.
  intros. induction sigma; simpl in H0.
  - rewrite elem_of_cons in H0.
    by destruct H0 as [H0 | H0]; subst; try inversion H0; left.
  - destruct (compare msg a) eqn:Hcmp.
    + rewrite compare_eq in Hcmp; subst. by right.
    + rewrite elem_of_cons in H0.
      by destruct H0 as [Heq | Hin]; subst; [left | right].
    + rewrite elem_of_cons in H0.
      destruct H0 as [Heq | Hin]; subst.
      * by right; left.
      * rewrite elem_of_cons. apply IHsigma in Hin as []; itauto.
Qed.

Lemma add_in_sorted_list_in_rev {A} {compare : A -> A -> comparison} `{CompareStrictOrder A compare} : forall msg msg' sigma,
  msg = msg' \/ msg' ∈ sigma ->
  msg' ∈ (add_in_sorted_list_fn compare msg sigma).
Proof.
  intros. induction sigma; simpl in H0.
  - destruct H0 as [H0 | H0]; subst; [left | inversion H0].
  - rewrite elem_of_cons in H0; cbn.
    destruct H0 as [Heq | Heq], (compare msg a) eqn: Hcmp
    ; rewrite !elem_of_cons; rewrite ?compare_eq in Hcmp; subst; itauto.
Qed.

Lemma add_in_sorted_list_iff {A} {compare : A -> A -> comparison} `{CompareStrictOrder A compare} : forall msg msg' sigma,
  msg' ∈ (add_in_sorted_list_fn compare msg sigma) <->
  msg = msg' \/ msg' ∈ sigma.
Proof.
  intros; split.
  - by apply add_in_sorted_list_in.
  - by apply add_in_sorted_list_in_rev.
Qed.

Lemma add_in_sorted_list_head {A} {compare : A -> A -> comparison} `{CompareStrictOrder A compare} : forall msg sigma,
  msg ∈ (add_in_sorted_list_fn compare msg sigma).
Proof.
  by intros; apply add_in_sorted_list_iff; left.
Qed.

Lemma add_in_sorted_list_tail {A} {compare : A -> A -> comparison} `{CompareStrictOrder A compare} : forall msg sigma,
  sigma ⊆ (add_in_sorted_list_fn compare msg sigma).
Proof.
  intros msg sigma x Hin.
  by apply add_in_sorted_list_iff; right.
Qed.

Lemma LocallySorted_ForAll2 [A : Type] (R : A -> A -> Prop)
  : forall l, LocallySorted R l <-> ForAllSuffix2 R l.
Proof.
  induction l; split; intro Hl.
  - by constructor.
  - constructor.
  - inversion Hl; subst.
    + by repeat constructor.
    + apply IHl in H1. by constructor.
  - apply proj2 in IHl. inversion Hl; subst.
    destruct l; constructor; auto.
Qed.

Lemma LocallySorted_filter [A : Type] (R : A -> A -> Prop) {HT : Transitive R}
  (P : A -> Prop) (Pdec : forall a, Decision (P a))
  : forall l, LocallySorted R l -> LocallySorted R (filter P l).
Proof.
  setoid_rewrite LocallySorted_ForAll2.
  by apply ForAllSuffix2_filter.
Qed.

Lemma LocallySorted_tl {A} {compare : A -> A -> comparison} `{CompareStrictOrder A compare} : forall msg sigma,
    LocallySorted (compare_lt compare) (msg :: sigma) ->
    LocallySorted (compare_lt compare) sigma.
Proof.
  intros. apply Sorted_LocallySorted_iff in H0.
  inversion H0; subst; clear H0. by apply Sorted_LocallySorted_iff.
Qed.

Lemma add_in_sorted_list_sorted {A} {compare : A -> A -> comparison} `{CompareStrictOrder A compare} : forall msg sigma,
    LocallySorted (compare_lt compare) sigma ->
  LocallySorted (compare_lt compare) (add_in_sorted_list_fn compare msg sigma).
Proof.
  intros. apply (@compare_asymmetric_intro _) in H as Hasymm.
  induction H0; simpl; try constructor; destruct (compare msg a) eqn:Hcmpa.
  - constructor.
  - constructor; [| done]. constructor.
  - apply Hasymm in Hcmpa. constructor; [| done]. constructor.
  - by constructor.
  - constructor; [| done]. by constructor.
  - apply Hasymm in Hcmpa.
    simpl in IHLocallySorted. destruct (compare msg b) eqn:Hcmpb.
    + apply StrictOrder_Reflexive in Hcmpb. subst. by constructor.
    + by constructor.
    + apply Hasymm in Hcmpb. by constructor.
Qed.

(** Sorted lists as sets **)
Lemma LocallySorted_elem_of_lt {A} {lt : relation A} `{StrictOrder A lt} :
  forall x y s,
  LocallySorted lt (y :: s) ->
  x ∈ s ->
  lt y x.
Proof.
  intros x y s LS IN. revert y x LS IN.
  induction s.
  - inversion 2.
  - do 2 inversion 1; subst; firstorder.
Qed.

Lemma set_eq_first_equal {A}  {lt : relation A} `{StrictOrder A lt} :
  forall x1 x2 s1 s2,
  LocallySorted lt (x1 :: s1) ->
  LocallySorted lt (x2 :: s2) ->
  set_eq (x1 :: s1) (x2 :: s2) ->
  x1 = x2 /\ set_eq s1 s2.
Proof.
  intros x1 x2 s1 s2 LS1 LS2 [IN1 IN2].
  assert (x12 : x1 = x2).
  {
    specialize (IN1 x1).
    rewrite 2 elem_of_cons in IN1.
    specialize (IN1 (or_introl (eq_refl x1))).
    destruct IN1; [done |].
    specialize (IN2 x2).
    rewrite 2 elem_of_cons in IN2.
    specialize (IN2 (or_introl (eq_refl x2))).
    destruct IN2; [by subst |].
    pose proof (LocallySorted_elem_of_lt x2 x1 s1 LS1 H1).
    pose proof (LocallySorted_elem_of_lt x1 x2 s2 LS2 H0).
    pose proof (StrictOrder_Irreflexive x1) as ltIrr.
    destruct H as [Hirr Htr].
    pose proof (Htr x1 x2 x1 H2 H3) as Hlt.
    unfold complement in ltIrr.
    itauto.
  }
  subst.
  split; [done |].
  split.
  - intros x Hx.
    pose proof (LocallySorted_elem_of_lt x _ _ LS1 Hx).
    specialize (IN1 x).
    rewrite elem_of_cons in IN1.
    specialize (IN1 (or_intror Hx)).
    rewrite elem_of_cons in IN1.
    destruct IN1; [| done].
    subst.
    by apply StrictOrder_Irreflexive in H0.
  - intros x Hx.
    pose proof (LocallySorted_elem_of_lt x _ _ LS2 Hx).
    specialize (IN2 x).
    rewrite elem_of_cons in IN2.
    specialize (IN2 (or_intror Hx)).
    rewrite elem_of_cons in IN2.
    destruct IN2; [| done].
    subst.
    by apply StrictOrder_Irreflexive in H0.
Qed.

Lemma set_equality_predicate {A}  {lt : relation A} `{StrictOrder A lt} :
  forall s1 s2,
  LocallySorted lt s1 ->
  LocallySorted lt s2 ->
  set_eq s1 s2 <-> s1 = s2.
Proof.
  intros s1 s2 LS1 LS2 . rename H into SO.
  assert (SO' := SO). destruct SO' as [IR TR].
  split.
  - generalize dependent s2. induction s1; destruct s2.
    + by intros.
    + intros. destruct H. exfalso. pose proof (H0 a).
      rewrite elem_of_cons in H1.
      specialize (H1 (or_introl (eq_refl a))).
      inversion H1.
    + intros. destruct H. exfalso. pose proof (H a).
      rewrite elem_of_cons in H1.
      specialize (H1 (or_introl (eq_refl a))).
      inversion H1.
    + intros. apply (set_eq_first_equal a a0 s1 s2 LS1 LS2) in H. destruct H; subst.
      apply Sorted_LocallySorted_iff in LS1. apply Sorted_inv in LS1. destruct LS1 as [LS1 _]. apply Sorted_LocallySorted_iff in LS1.
      apply Sorted_LocallySorted_iff in LS2. apply Sorted_inv in LS2. destruct LS2 as [LS2 _]. apply Sorted_LocallySorted_iff in LS2.
      by apply (IHs1 LS1 s2 LS2) in H0; subst.
  - intros. subst. easy.
Qed.

(* Transitive isn't necessary but makes the proof simpler. *)

Lemma lsorted_app
  {A : Type}
  (l : list A)
  (R : A -> A -> Prop)
  (Hsorted : LocallySorted R l)
  (Htransitive : Transitive R)
  (alfa beta : list A)
  (Hconcat : l = alfa ++ beta) :
  LocallySorted R alfa /\ LocallySorted R beta.
Proof.
  generalize dependent l.
  generalize dependent beta.
  induction alfa.
  - intros.
    split.
    apply LSorted_nil.
    simpl in *.
    by rewrite Hconcat in Hsorted.
  - intros.
    apply Sorted_LocallySorted_iff in Hsorted.
    apply Sorted_StronglySorted in Hsorted; [| done].
    rewrite Hconcat in Hsorted.
    simpl in Hsorted.
    apply StronglySorted_inv in Hsorted.
    destruct Hsorted.
    specialize (IHalfa beta (alfa ++ beta)).
    spec IHalfa.
    apply Sorted_LocallySorted_iff.
    by apply StronglySorted_Sorted.
    specialize (IHalfa eq_refl).
    destruct IHalfa.
    split; [| done].
    destruct alfa; constructor; [done |].
    rewrite Forall_forall in H0.
    apply H0; left.
Qed.

Lemma lsorted_pairwise_ordered
  {A : Type}
  (l : list A)
  (R : A -> A -> Prop)
  (Hsorted : LocallySorted R l)
  (Htransitive : Transitive R)
  (x y : A)
  (alfa beta gamma : list A)
  (Hconcat : l = alfa ++ [x] ++ beta ++ [y] ++ gamma) :
  R x y.
Proof.
  apply (lsorted_app _ _ Hsorted _ alfa) in Hconcat.
  destruct Hconcat as [_ Hneed].
  simpl in Hneed.
  rewrite <- Sorted_LocallySorted_iff in Hneed.
  apply Sorted_extends in Hneed; [| done].
  rewrite Forall_forall in Hneed.
  specialize (Hneed y).
  spec Hneed; [| done].
  apply elem_of_app; right; left.
Qed.
