From Cdcl Require Import Itauto. Local Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From Coq Require Import Sorting RelationClasses Relations Orders.
From VLSM Require Import Lib.Preamble Lib.ListExtras Lib.StdppListSet Lib.ListSetExtras.

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

Instance list_compare_strict_order {A} {compare : A -> A -> comparison} `{CompareStrictOrder A compare} :
  CompareStrictOrder (@list_compare A compare).
Proof.
  intros. destruct H as [R T].
  split.
  - intro x. induction x; intros; destruct y; split; intros; try discriminate; try reflexivity.
    + simpl in H. destruct (compare a a0) eqn:Hcmp; try discriminate H.
      apply R in Hcmp; subst. apply IHx in H; subst.
      reflexivity.
    + inversion H; subst. simpl. rewrite compare_eq_refl; try assumption.
      apply IHx. reflexivity.
  - intros x y. generalize dependent x.
    induction y; intros; destruct x; destruct z; try assumption
    ; destruct comp; try discriminate
    ; inversion H; clear H; destruct (compare a0 a) eqn:Ha0; try discriminate
    ; inversion H0; clear H0; destruct (compare a a1) eqn:Ha1; try discriminate
    ; try apply (IHy _ _ _ H2) in H1; try apply (T _ _ _ _ Ha0) in Ha1
    ; try apply R in Ha0; subst
    ; try (simpl; rewrite Ha1; try rewrite H1, H2; reflexivity)
    ; try (simpl; rewrite Ha1; rewrite H2; reflexivity)
    ; try (apply R in Ha1; subst; simpl;  rewrite Ha0; rewrite H1; reflexivity)
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

Lemma add_in_sorted_list_no_empty {A} (compare : A -> A -> comparison) : forall msg sigma,
  add_in_sorted_list_fn compare msg sigma <> [].
Proof.
  unfold not. intros. destruct sigma; simpl in H.
  - inversion H.
  - destruct (compare msg a); inversion H.
Qed.

Lemma add_in_sorted_list_in {A} {compare : A -> A -> comparison} `{CompareStrictOrder A compare} : forall msg msg' sigma,
  msg' ∈ (add_in_sorted_list_fn compare msg sigma) ->
  msg = msg' \/ msg' ∈ sigma.
Proof.
  intros. induction sigma; simpl in H0.
  - rewrite elem_of_cons in H0.
    destruct H0 as [H0 | H0]; subst; try inversion H0; left; reflexivity.
  - destruct (compare msg a) eqn:Hcmp.
    + apply StrictOrder_Reflexive in Hcmp; subst. right. assumption.
    + rewrite elem_of_cons in H0.
      destruct H0 as [Heq | Hin]; subst.
      * left; reflexivity.
      * right; assumption.
    + rewrite elem_of_cons in H0.
      destruct H0 as [Heq | Hin]; subst.
      * right; left; reflexivity.
      * apply IHsigma in Hin. destruct Hin; try (left; assumption).
        right. right. assumption.
Qed.

Lemma add_in_sorted_list_in_rev {A} {compare : A -> A -> comparison} `{CompareStrictOrder A compare} : forall msg msg' sigma,
  msg = msg' \/ msg' ∈ sigma ->
  msg' ∈ (add_in_sorted_list_fn compare msg sigma).
Proof.
  intros. induction sigma; simpl in H0.
  - destruct H0 as [H0 | H0]; subst; try inversion H0; left; reflexivity.
  - rewrite elem_of_cons in H0.
    simpl.
    destruct H0 as [Heq|Heq];destruct (compare msg a) eqn:Hcmp.
    + apply StrictOrder_Reflexive in Hcmp; subst; left.
    + subst; left.
    + subst; right; apply IHsigma; left; reflexivity.
    + apply StrictOrder_Reflexive in Hcmp; subst.
      destruct Heq as [Heq|Heq].
      * subst; left.
      * right; assumption.
    + destruct Heq as [Heq|Heq].
      * subst; right; left.
      * right; right; assumption.
    + destruct Heq as [Heq|Heq].
      * subst; left.
      * right; apply IHsigma; right; assumption.
Qed.

Lemma add_in_sorted_list_iff {A} {compare : A -> A -> comparison} `{CompareStrictOrder A compare} : forall msg msg' sigma,
  msg' ∈ (add_in_sorted_list_fn compare msg sigma) <->
  msg = msg' \/ msg' ∈ sigma.
Proof.
  intros; split.
  - apply add_in_sorted_list_in; assumption.
  - apply add_in_sorted_list_in_rev; assumption.
Qed.

Lemma add_in_sorted_list_head {A} {compare : A -> A -> comparison} `{CompareStrictOrder A compare} : forall msg sigma,
  msg ∈ (add_in_sorted_list_fn compare msg sigma).
Proof.
  intros.
  apply add_in_sorted_list_iff; try assumption. left; reflexivity.
Qed.

Lemma add_in_sorted_list_tail {A} {compare : A -> A -> comparison} `{CompareStrictOrder A compare} : forall msg sigma,
  sigma ⊆ (add_in_sorted_list_fn compare msg sigma).
Proof.
  intros. intros x Hin.
  apply add_in_sorted_list_iff; try assumption. right. assumption.
Qed.

Lemma LocallySorted_ForAll2 [A : Type] (R : A -> A -> Prop)
  : forall l, LocallySorted R l <-> ForAllSuffix2 R l.
Proof.
  induction l; split; intro Hl.
  - constructor. exact I.
  - constructor.
  - inversion Hl; subst.
    + constructor; [exact I|]. constructor. exact I.
    + apply IHl in H1. constructor; assumption.
  - apply proj2 in IHl.
    spec IHl. { apply fsFurther in Hl; assumption. }
    destruct l; constructor; [assumption|].
    inversion Hl. assumption.
Qed.

Lemma LocallySorted_filter [A : Type] (R : A -> A -> Prop) {HT : Transitive R}
  (P : A -> Prop) (Pdec : forall a, Decision (P a))
  : forall l, LocallySorted R l -> LocallySorted R (filter P l).
Proof.
  setoid_rewrite LocallySorted_ForAll2.
  apply ForAllSuffix2_filter.
  assumption.
Qed.

Lemma LocallySorted_tl {A} {compare : A -> A -> comparison} `{CompareStrictOrder A compare} : forall msg sigma,
    LocallySorted (compare_lt compare) (msg :: sigma) ->
    LocallySorted (compare_lt compare) sigma.
Proof.
  intros. apply Sorted_LocallySorted_iff in H0.
  inversion H0; subst; clear H0. apply Sorted_LocallySorted_iff. assumption.
Qed.

Lemma add_in_sorted_list_sorted {A} {compare : A -> A -> comparison} `{CompareStrictOrder A compare} : forall msg sigma,
    LocallySorted (compare_lt compare) sigma ->
  LocallySorted (compare_lt compare) (add_in_sorted_list_fn compare msg sigma).
Proof.
  intros. apply (@compare_asymmetric_intro _) in H as Hasymm.
  induction H0; simpl; try constructor; destruct (compare msg a) eqn:Hcmpa.
  - constructor.
  - constructor; try assumption. constructor.
  - apply Hasymm in Hcmpa. constructor; try assumption. constructor.
  - constructor; assumption.
  - constructor; try assumption. constructor; assumption.
  - apply Hasymm in Hcmpa.
    simpl in IHLocallySorted. destruct (compare msg b) eqn:Hcmpb.
    + apply StrictOrder_Reflexive in Hcmpb. subst. constructor; assumption.
    + constructor; assumption.
    + apply Hasymm in Hcmpb. constructor; assumption.
Qed.

(** Sorted lists as sets **)
Lemma LocallySorted_elem_of_lt {A} {lt : relation A} `{StrictOrder A lt} :
  forall x y s,
  LocallySorted lt (y :: s) ->
  x ∈ s ->
  lt y x.
Proof.
  intros x y s LS IN. generalize dependent x. generalize dependent y.
  induction s.
  - intros y LS x IN. inversion IN.
  - intros y LS x IN.
    inversion LS; subst.
    inversion IN; subst.
    + assumption.
    + spec IHs a H2 x H3.
      destruct H as [_ H]; red in H.
      apply (H y a x H4 IHs).
Qed.

Lemma add_in_sorted_list_existing {A} {compare : A -> A -> comparison} `{CompareStrictOrder A compare} : forall msg sigma,
  LocallySorted (compare_lt compare) sigma ->
  msg ∈ sigma ->
  add_in_sorted_list_fn compare msg sigma = sigma.
Proof.
  induction sigma; intros.
  - inversion H1.
  - rewrite elem_of_cons in H1.
    destruct H1 as [Heq | Hin].
    + subst. simpl. rewrite compare_eq_refl. reflexivity.
    + apply LocallySorted_tl in H0 as LS.
      spec IHsigma LS Hin. simpl.
      destruct (compare msg a) eqn:Hcmp; try rewrite IHsigma; try reflexivity.
      apply (@LocallySorted_elem_of_lt _ _ compare_lt_strict_order msg a sigma H0) in Hin.
      unfold compare_lt in Hin. apply compare_asymmetric in Hin.
      rewrite Hin in Hcmp. inversion Hcmp.
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
    destruct IN1; [assumption|].
    specialize (IN2 x2).
    rewrite 2 elem_of_cons in IN2.
    specialize (IN2 (or_introl (eq_refl x2))).
    destruct IN2; [subst; reflexivity|].
    pose proof (LocallySorted_elem_of_lt x2 x1 s1 LS1 H1).
    pose proof (LocallySorted_elem_of_lt x1 x2 s2 LS2 H0).
    pose proof (StrictOrder_Irreflexive x1) as ltIrr.
    destruct H as [Hirr Htr].
    pose proof (Htr x1 x2 x1 H2 H3) as Hlt.
    unfold complement in ltIrr.
    itauto.
  }
  subst.
  split. reflexivity.
  split.
  - intros x Hx.
    pose proof (LocallySorted_elem_of_lt x _ _ LS1 Hx).
    specialize (IN1 x).
    rewrite elem_of_cons in IN1.
    specialize (IN1 (or_intror Hx)).
    rewrite elem_of_cons in IN1.
    destruct IN1; [|assumption].
    subst.
    apply StrictOrder_Irreflexive in H0.
    contradiction.
  - intros x Hx.
    pose proof (LocallySorted_elem_of_lt x _ _ LS2 Hx).
    specialize (IN2 x).
    rewrite elem_of_cons in IN2.
    specialize (IN2 (or_intror Hx)).
    rewrite elem_of_cons in IN2.
    destruct IN2; [|assumption].
    subst.
    apply StrictOrder_Irreflexive in H0.
    contradiction.
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
    + intros. reflexivity.
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
      apply (IHs1 LS1 s2 LS2) in H0. subst. reflexivity.
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
    rewrite Hconcat in Hsorted.
    assumption.
  - intros.
    apply Sorted_LocallySorted_iff in Hsorted.
    apply Sorted_StronglySorted in Hsorted.
    rewrite Hconcat in Hsorted.
    simpl in Hsorted.
    apply StronglySorted_inv in Hsorted.
    destruct Hsorted.
    specialize (IHalfa beta (alfa ++ beta)).
    spec IHalfa.
    apply Sorted_LocallySorted_iff.
    apply StronglySorted_Sorted.
    assumption.
    specialize (IHalfa eq_refl).
    destruct IHalfa.
    split.
    + destruct alfa.
      * apply LSorted_cons1.
      * apply LSorted_consn.
        assumption.
        rewrite Forall_forall in H0.
        specialize (H0 a0).
        spec H0.
        left.
        assumption.
    + assumption.
    + assumption.
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
  apply Sorted_extends in Hneed.
  rewrite Forall_forall in Hneed.
  specialize (Hneed y).
  spec Hneed.
  apply elem_of_app.
  right; left.
  assumption.
  assumption.
Qed.

Lemma lsorted_pair_wise_unordered
  {A : Type}
  (l : list A)
  (R : A -> A -> Prop)
  (Hsorted : LocallySorted R l)
  (Htransitive : Transitive R)
  (x y : A)
  (Hin_x : x ∈ l)
  (Hin_y : y ∈ l) :
  x = y \/ R x y \/ R y x.
Proof.
  apply elem_of_list_split in Hin_x.
  destruct Hin_x as [pref1 [suf1 Hconcat1]].
  rewrite Hconcat1 in Hin_y.
  apply elem_of_app in Hin_y.
  rewrite elem_of_cons in Hin_y.
  assert (y =x \/ y ∈ (pref1 ++ suf1)). {
    destruct Hin_y as [Hin_y|Hin_y]; [|destruct Hin_y].
    - right; apply elem_of_app; left; assumption.
    - left; assumption.
    - right; apply elem_of_app; right; assumption.
  }
  clear Hin_y.
  rename H into Hin_y.
  destruct Hin_y as [Hin_y|Hin_y].
  - symmetry in Hin_y.
    itauto.
  - apply elem_of_app in Hin_y; destruct Hin_y.
    * apply elem_of_list_split in H.
      destruct H as [pref2 [suf2 Hconcat2]].
      rewrite Hconcat2 in Hconcat1.
      rewrite <- app_assoc in Hconcat1.
      specialize (lsorted_pairwise_ordered l R Hsorted Htransitive y x pref2 suf2 suf1 Hconcat1).
      intros; right; right; assumption.
    * apply elem_of_list_split in H.
      destruct H as [pref2 [suf2 Hconcat2]].
      rewrite Hconcat2 in Hconcat1.
      specialize (lsorted_pairwise_ordered l R Hsorted Htransitive x y pref1 pref2 suf2 Hconcat1).
      intros; right; left; assumption.
Qed.
