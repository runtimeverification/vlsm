From VLSM.Lib Require Import Itauto.
From stdpp Require Import prelude.
From Coq Require Import Sorting.
From VLSM.Lib Require Import Preamble ListExtras ListSetExtras.

(** * Utility: Sorted List Functions and Results *)

(** Insert an element into a sorted list. *)
Fixpoint add_in_sorted_list_fn
  {A} (compare : A -> A -> comparison) (x : A) (l : list A) : list A :=
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
  - by inversion H.
  - by destruct (compare msg a); inversion H.
Qed.

Lemma add_in_sorted_list_in
  {A} {compare : A -> A -> comparison} `{CompareStrictOrder A compare} :
  forall msg msg' sigma,
    msg' ∈ add_in_sorted_list_fn compare msg sigma ->
    msg = msg' \/ msg' ∈ sigma.
Proof.
  intros. induction sigma; simpl in H0.
  - rewrite elem_of_cons in H0.
    by destruct H0 as [H0 | H0]; subst; try inversion H0; left.
  - destruct (compare msg a) eqn: Hcmp.
    + by rewrite compare_eq in Hcmp; subst; right.
    + rewrite elem_of_cons in H0.
      by destruct H0 as [Heq | Hin]; subst; [left | right].
    + rewrite elem_of_cons in H0.
      destruct H0 as [Heq | Hin]; subst.
      * by right; left.
      * rewrite elem_of_cons.
        by apply IHsigma in Hin as []; itauto.
Qed.

Lemma add_in_sorted_list_in_rev
  {A} {compare : A -> A -> comparison} `{CompareStrictOrder A compare} :
  forall msg msg' sigma,
    msg = msg' \/ msg' ∈ sigma ->
    msg' ∈ add_in_sorted_list_fn compare msg sigma.
Proof.
  intros. induction sigma; simpl in H0.
  - by destruct H0 as [H0 | H0]; subst; [left | inversion H0].
  - rewrite elem_of_cons in H0; cbn.
    by destruct H0 as [Heq | Heq], (compare msg a) eqn: Hcmp
    ; rewrite !elem_of_cons; rewrite ?compare_eq in Hcmp; subst; itauto.
Qed.

Lemma add_in_sorted_list_iff
  {A} {compare : A -> A -> comparison} `{CompareStrictOrder A compare} :
  forall msg msg' sigma,
    msg' ∈ add_in_sorted_list_fn compare msg sigma <->
    msg = msg' \/ msg' ∈ sigma.
Proof.
  intros; split.
  - by apply add_in_sorted_list_in.
  - by apply add_in_sorted_list_in_rev.
Qed.

Lemma add_in_sorted_list_head
  {A} {compare : A -> A -> comparison} `{CompareStrictOrder A compare} :
  forall msg sigma,
    msg ∈ add_in_sorted_list_fn compare msg sigma.
Proof.
  by intros; apply add_in_sorted_list_iff; left.
Qed.

Lemma add_in_sorted_list_tail
  {A} {compare : A -> A -> comparison} `{CompareStrictOrder A compare} :
  forall msg sigma,
    sigma ⊆ add_in_sorted_list_fn compare msg sigma.
Proof.
  intros msg sigma x Hin.
  by apply add_in_sorted_list_iff; right.
Qed.

Lemma LocallySorted_ForAll2 [A : Type] (R : A -> A -> Prop)
  : forall l, LocallySorted R l <-> ForAllSuffix2 R l.
Proof.
  induction l; split; intro Hl.
  - by constructor.
  - by constructor.
  - inversion Hl; subst.
    + by repeat constructor.
    + by apply IHl in H1; constructor.
  - apply proj2 in IHl; inversion Hl; subst.
    by destruct l; constructor; auto.
Qed.

Lemma LocallySorted_filter [A : Type] (R : A -> A -> Prop) {HT : Transitive R}
  (P : A -> Prop) (Pdec : forall a, Decision (P a))
  : forall l, LocallySorted R l -> LocallySorted R (filter P l).
Proof.
  setoid_rewrite LocallySorted_ForAll2.
  by apply ForAllSuffix2_filter.
Qed.

Lemma LocallySorted_tl
  {A} {compare : A -> A -> comparison} `{CompareStrictOrder A compare} :
  forall msg sigma,
    LocallySorted (compare_lt compare) (msg :: sigma) ->
    LocallySorted (compare_lt compare) sigma.
Proof.
  intros. apply Sorted_LocallySorted_iff in H0.
  inversion H0; subst; clear H0.
  by apply Sorted_LocallySorted_iff.
Qed.

Lemma add_in_sorted_list_sorted
  {A} {compare : A -> A -> comparison} `{CompareStrictOrder A compare} :
  forall msg sigma,
    LocallySorted (compare_lt compare) sigma ->
    LocallySorted (compare_lt compare) (add_in_sorted_list_fn compare msg sigma).
Proof.
  induction 1; cbn; try constructor; destruct (compare msg a) eqn: Hcmpa.
  - by constructor.
  - by constructor; [constructor |].
  - constructor; [constructor |].
    by red; rewrite compare_asymmetric, Hcmpa.
  - by constructor.
  - by constructor; [constructor |].
  - cbn in IHLocallySorted.
    destruct (compare msg b) eqn: Hcmpb.
    + by rewrite compare_eq in Hcmpb; constructor.
    + constructor; [done |].
      by red; rewrite compare_asymmetric, Hcmpa.
    + by constructor.
Qed.

(** ** Sorted lists as sets *)

Lemma LocallySorted_elem_of_lt {A} {lt : relation A} `{StrictOrder A lt} :
  forall x y s,
  LocallySorted lt (y :: s) ->
  x ∈ s ->
  lt y x.
Proof.
  intros x y s LS IN. revert y x LS IN.
  induction s.
  - by inversion 2.
  - by do 2 inversion 1; subst; firstorder.
Qed.

Lemma add_in_sorted_list_existing
  {A} {compare : A -> A -> comparison} `{CompareStrictOrder A compare} :
  forall msg sigma,
    LocallySorted (compare_lt compare) sigma ->
    msg ∈ sigma ->
    add_in_sorted_list_fn compare msg sigma = sigma.
Proof.
  induction sigma; intros; [by inversion H1 |].
  rewrite elem_of_cons in H1.
  destruct H1 as [Heq | Hin].
  - by subst; simpl; rewrite compare_eq_refl.
  - apply LocallySorted_tl in H0 as LS.
    specialize (IHsigma LS Hin). simpl.
    destruct (compare msg a) eqn: Hcmp; try rewrite IHsigma; [done | | done].
    apply (@LocallySorted_elem_of_lt _ _ compare_lt_strict_order msg a sigma H0) in Hin.
    unfold compare_lt in Hin.
    by rewrite compare_asymmetric, Hcmp in Hin; inversion Hin.
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
    by pose proof (Htr x1 x2 x1 H2 H3) as Hlt.
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
  split; [| by intros ->].
  generalize dependent s2.
  induction s1; destruct s2; intros; [done | | |].
  - by destruct H as [_ H]; apply list_nil_subseteq in H.
  - by destruct H as [H _]; apply list_nil_subseteq in H.
  - apply (set_eq_first_equal a a0 s1 s2 LS1 LS2) in H. destruct H; subst.
    apply Sorted_LocallySorted_iff, Sorted_inv in LS1 as [LS1 _].
    apply Sorted_LocallySorted_iff in LS1.
    apply Sorted_LocallySorted_iff, Sorted_inv in LS2 as [LS2 _].
    apply Sorted_LocallySorted_iff in LS2.
    by apply (IHs1 LS1 s2 LS2) in H0; subst.
Qed.

(* [Transitive] isn't necessary but makes the proof simpler. *)

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
    + by apply LSorted_nil.
    + by simpl in *; rewrite Hconcat in Hsorted.
  - intros.
    apply Sorted_LocallySorted_iff in Hsorted.
    apply Sorted_StronglySorted in Hsorted; [| done].
    rewrite Hconcat in Hsorted.
    simpl in Hsorted.
    apply StronglySorted_inv in Hsorted.
    destruct Hsorted.
    specialize (IHalfa beta (alfa ++ beta)).
    spec IHalfa; [by apply Sorted_LocallySorted_iff, StronglySorted_Sorted |].
    destruct (IHalfa eq_refl).
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
  by apply elem_of_app; right; left.
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
  assert (y =x \/ y ∈ pref1 ++ suf1). {
    destruct Hin_y as [Hin_y | Hin_y]; [| destruct Hin_y].
    - by right; apply elem_of_app; left.
    - by left.
    - by right; apply elem_of_app; right.
  }
  clear Hin_y.
  rename H into Hin_y.
  destruct Hin_y as [Hin_y | Hin_y]; [by left |].
  apply elem_of_app in Hin_y; destruct Hin_y.
  - apply elem_of_list_split in H.
    destruct H as [pref2 [suf2 Hconcat2]].
    rewrite Hconcat2 in Hconcat1.
    rewrite <- app_assoc in Hconcat1.
    specialize (lsorted_pairwise_ordered l R Hsorted Htransitive y x pref2 suf2 suf1 Hconcat1).
    by intros; right; right.
  - apply elem_of_list_split in H.
    destruct H as [pref2 [suf2 Hconcat2]].
    rewrite Hconcat2 in Hconcat1.
    specialize (lsorted_pairwise_ordered l R Hsorted Htransitive x y pref1 pref2 suf2 Hconcat1).
    by intros; right; left.
Qed.
