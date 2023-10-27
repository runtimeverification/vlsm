From VLSM.Lib Require Import Itauto.
From Coq Require Import FunctionalExtensionality.
From stdpp Require Import prelude finite.
From VLSM.Lib Require Import Preamble StdppExtras ListExtras.

(** * Finitely supported functions *)

(**
  The support of a function (w.r.t. a specified codomain value) is the type of
  elements of its domain that are not mapped to the specified value.

  Note that we require the codomain to have decidable equality, because it
  allows for a straight-forward approach to proving equality of elements
  of the support.
*)
Definition support {A B : Type} (s : B) (f : A -> B) `{EqDecision B} : Type :=
  dsig (fun a => f a <> s).


(**
  A function is finitely supported if its [support] is [Finite].
  We define a type to encapsulate functions of finite support.
*)
Definition fsfun (A : Type) `(s : B) `{EqDecision A, EqDecision B} : Type :=
  sigT (fun (f : A -> B) => Finite (support s f)).

Definition fsfun_project
  {A B : Type} {b : B} `{EqDecision A, EqDecision B} : fsfun A b -> A -> B :=
  projT1.

Coercion fsfun_project : fsfun >-> Funclass.

#[global] Arguments fsfun_project : simpl never.

Section sec_fsfun_fixed_domain.

Context
  `{EqDecision A}
  .

Section sec_fsfun_fixed_supp_value.

Context
  `{EqDecision B}
  {b : B}
  .

#[export] Instance fsfun_equiv : Equiv (fsfun A b) :=
  (fun f g => fsfun_project f = fsfun_project g).

#[export] Instance fsfun_equivalence :
  Equivalence (≡@{fsfun A b}).
Proof.
  unfold equiv, fsfun_equiv.
  constructor.
  - done.
  - by intros f g; apply symmetry.
  - by intros f g h; apply transitivity.
Qed.

#[export] Instance fsfun_project_proper :
  Proper ((≡) ==> (=)) fsfun_project.
Proof. by intros f g Heqv; inversion Heqv. Qed.

#[export] Instance projT1_proper :
  Proper ((≡@{fsfun A b}) ==> (=)) projT1.
Proof. by apply fsfun_project_proper. Qed.

Lemma fsfun_equiv_unfold (f g : fsfun A b) :
  f ≡ g <-> fsfun_project f = fsfun_project g.
Proof. done. Qed.

#[export] Instance fsfun_has_fin_supp
  (f : fsfun A b) : Finite (support b (f)) :=
    projT2 f.

Definition fin_supp (f : fsfun A b) : list A :=
  map proj1_sig (enum (support b (f))).

Lemma elem_of_fin_supp (f : fsfun A b) :
  forall (a : A), a ∈ fin_supp f <-> f a <> b.
Proof.
  unfold fin_supp.
  split; rewrite elem_of_list_fmap.
  - intros (asupp & -> & _).
    by destruct_dec_sig asupp _a H_a Heq; subst.
  - intros Ha.
    by exists (dexist a Ha); split; [| apply elem_of_enum].
Qed.

Lemma not_elem_of_fin_supp (f : fsfun A b) :
  forall (a : A), a ∉ fin_supp f <-> f a = b.
Proof.
  intros a; rewrite elem_of_fin_supp.
  by destruct (decide (f a = b)); itauto.
Qed.

Lemma fin_supp_NoDup (f : fsfun A b) : NoDup (fin_supp f).
Proof. by apply dsig_NoDup_map, NoDup_enum. Qed.

#[export] Instance fin_supp_proper : Proper ((≡) ==> (≡ₚ)) fin_supp.
Proof.
  intros f g Heq.
  apply NoDup_Permutation; [by apply fin_supp_NoDup.. |].
  by intro; rewrite !elem_of_fin_supp, Heq.
Qed.

#[export] Instance fsfun_eq_dec : RelDecision (≡@{fsfun A b}).
Proof.
  intros f g.
  destruct (@finset_equiv_dec A (listset A) _ _ _ _ _ _ _ _ _
    (list_to_set (fin_supp f)) (list_to_set (fin_supp g))) as [Heqv | Hneqv]; cycle 1.
  - right; intros Heqv.
    by rewrite Heqv in Hneqv.
  - destruct (decide (set_Forall (fun a => fsfun_project f a = fsfun_project g a) (list_to_set (C := listset A) (fin_supp f))))
      as [Hall | Hall]; [| by right; contradict Hall; rewrite Hall].
    left; apply fsfun_equiv_unfold; extensionality a.
    destruct (decide (a ∈ fin_supp f)) as [| Hf]; [by apply Hall, elem_of_list_to_set |].
    destruct (decide (a ∈ fin_supp g)) as [| Hg]; [by apply Hall; rewrite Heqv, elem_of_list_to_set |].
    apply not_elem_of_fin_supp in Hf, Hg.
    by (transitivity b).
Qed.

Program Definition empty_fsfun : fsfun A b :=
  existT (const b) {| enum := [] |}.
Next Obligation.
Proof. by constructor. Qed.
Next Obligation.
Proof. by intros; destruct_dec_sig x a Ha Heq; contradiction Ha. Qed.

Lemma empty_fsfun_supp : fin_supp empty_fsfun = [].
Proof. done. Qed.

Lemma empty_fsfun_supp_inv (f : fsfun A b) :
  fin_supp f = [] -> f ≡ empty_fsfun.
Proof.
  intros Hf; apply fsfun_equiv_unfold; extensionality a; cbn.
  eapply not_elem_of_fin_supp.
  rewrite Hf.
  by apply not_elem_of_nil.
Qed.

Definition update_supp (f : fsfun A b) (n : A) (b' : B) : listset A :=
  if decide (b' = b)
  then list_to_set (fin_supp f) ∖ {[n]}
  else {[n]} ∪ list_to_set (fin_supp f).

Lemma update_supp_all (f : fsfun A b) (n : A) (b' : B) :
  Forall (fun a => update (f) n b' a <> b) (elements (update_supp f n b')).
Proof.
  unfold update_supp.
  apply Forall_forall; intros a.
  rewrite elem_of_elements.
  case_decide.
  - rewrite elem_of_difference, elem_of_singleton, elem_of_list_to_set,
      elem_of_fin_supp.
    by intros []; rewrite update_neq.
  - rewrite elem_of_union, elem_of_singleton, elem_of_list_to_set,
      elem_of_fin_supp.
    by unfold update; case_decide; cbn; intros [].
Qed.

Program Definition update_fsfun
  (f : fsfun A b) (n : A) (b' : B) : fsfun A b :=
  existT (update (f) n b')
    {| enum := list_annotate (update_supp_all f n b') |}.
Next Obligation.
Proof. by intros; apply list_annotate_NoDup, NoDup_elements. Qed.
Next Obligation.
Proof.
  intros; destruct_dec_sig x a Ha Heq; subst.
  apply elem_of_list_annotate, elem_of_elements.
  unfold update_supp; case_decide.
  - rewrite elem_of_difference, elem_of_list_to_set, elem_of_fin_supp,
      elem_of_singleton; cbn.
    by unfold update in Ha; case_decide; split; congruence.
  - rewrite elem_of_union, elem_of_list_to_set, elem_of_fin_supp,
      elem_of_singleton; cbn.
    by unfold update in Ha; case_decide; [left | right].
Qed.

Lemma update_fsfun_eq (f : fsfun A b) (n : A) (b' : B) :
  update_fsfun f n b' n = b'.
Proof. by setoid_rewrite update_eq. Qed.

Lemma update_fsfun_neq (f : fsfun A b) (n : A) (b' : B):
  forall (m : A), m <> n -> update_fsfun f n b' m = f m.
Proof. by intros; setoid_rewrite update_neq. Qed.

#[export] Instance update_fsfun_proper :
  Proper ((≡) ==> (=) ==> (=) ==> (≡)) update_fsfun.
Proof.
  intros f g Heqv _n n -> _b' b' ->.
  apply fsfun_equiv_unfold; extensionality a; cbn.
  destruct (decide (n = a)) as [-> |].
  - by rewrite !update_fsfun_eq.
  - by rewrite !update_fsfun_neq, Heqv.
Qed.

Lemma elem_of_update_fsfun (f : fsfun A b) (n : A) (b' : B) :
  forall (a : A),
    a ∈ fin_supp (update_fsfun f n b')
      <->
    b' = b /\ a ∈ fin_supp f /\ a <> n \/
    b' <> b /\ (a ∈ fin_supp f \/ a = n).
Proof.
  intro; unfold fin_supp at 1; cbn.
  rewrite list_annotate_forget, elem_of_elements.
  unfold update_supp; case_decide.
  - by rewrite elem_of_difference, elem_of_list_to_set, elem_of_singleton; split; itauto.
  - by rewrite elem_of_union, elem_of_list_to_set, elem_of_singleton; split; itauto.
Qed.

End sec_fsfun_fixed_supp_value.

(** ** Finitely supported functions on naturals *)

Definition zero_fsfun : fsfun A 0 := empty_fsfun.

Lemma zero_fsfun_rew : forall (n : A), zero_fsfun n = 0.
Proof. done. Qed.

Definition succ_fsfun (f : fsfun A 0) (n : A) : fsfun A 0 :=
  update_fsfun f n (S (f n)).

Lemma succ_fsfun_eq (f : fsfun A 0) (n : A) :
  succ_fsfun f n n = S (f n).
Proof. by apply update_fsfun_eq. Qed.

Lemma succ_fsfun_neq (f : fsfun A 0) (n : A) :
  forall (m : A), m <> n -> succ_fsfun f n m = f m.
Proof. by apply update_fsfun_neq. Qed.

#[export] Instance succ_fsfun_proper :
  Proper ((≡) ==> (=) ==> (≡)) succ_fsfun.
Proof.
  intros f g Heqv _n n ->.
  by apply update_fsfun_proper; [.. | rewrite Heqv].
Qed.

Lemma elem_of_succ_fsfun (f : fsfun A 0) (n : A) :
  forall (a : A),
    a ∈ fin_supp (succ_fsfun f n) <-> a = n \/ a ∈ fin_supp f.
Proof.
  intros a; unfold succ_fsfun.
  rewrite elem_of_update_fsfun.
  by split; itauto lia.
Qed.

Lemma succ_fsfun_supp_in (f : fsfun A 0) (n : A) :
  n ∈ fin_supp f -> fin_supp (succ_fsfun f n) ≡ₚ fin_supp f.
Proof.
  intros.
  apply NoDup_Permutation; intros; [by apply fin_supp_NoDup.. |].
  rewrite elem_of_succ_fsfun.
  by set_solver.
Qed.

Lemma succ_fsfun_supp_not_in (f : fsfun A 0) (n : A) :
  n ∉ fin_supp f -> fin_supp (succ_fsfun f n) ≡ₚ n :: fin_supp f.
Proof.
  intros; cbn; rewrite list_annotate_forget.
  unfold update_supp; rewrite decide_False by lia.
  rewrite @elements_union_singleton;
    [| by typeclasses eauto | by rewrite elem_of_list_to_set].
  by constructor; eapply @elements_list_to_set;
    [typeclasses eauto | apply fin_supp_NoDup].
Qed.

Definition delta_nat_fsfun (n : A) : fsfun A 0 :=
  succ_fsfun zero_fsfun n.

Lemma delta_nat_fsfun_eq (n : A) :
  delta_nat_fsfun n n = 1.
Proof. by apply succ_fsfun_eq. Qed.

Lemma delta_nat_fsfun_neq (n : A) :
  forall (m : A), m <> n -> delta_nat_fsfun n m = 0.
Proof. by apply succ_fsfun_neq. Qed.

Lemma elem_of_delta_nat_fsfun (n : A) :
  forall (a : A),
    a ∈ fin_supp (delta_nat_fsfun n) <-> a = n.
Proof.
  intros a.
  unfold delta_nat_fsfun.
  rewrite elem_of_succ_fsfun; cbn; rewrite elem_of_nil.
  by itauto.
Qed.

Definition fsfun_sum (f : fsfun A 0) : nat :=
  sum_list_with (f) (fin_supp f).

Lemma fsfun_sum_proper : Proper ((≡) ==> (=)) fsfun_sum.
Proof.
  intros f g Heqv.
  unfold fsfun_sum.
  rewrite (sum_list_with_proper (f) (fin_supp f) (fin_supp g)).
  - by apply sum_list_with_ext_forall; intros; rewrite Heqv.
  - by apply fin_supp_proper.
Qed.

Lemma fsfun_sum_zero_inv (f : fsfun A 0) :
  fsfun_sum f = 0 -> f ≡ zero_fsfun.
Proof.
  setoid_rewrite sum_list_with_zero; intros Hall.
  apply fsfun_equiv_unfold; extensionality a; cbn.
  apply dec_stable; intro Ha.
  apply elem_of_fin_supp in Ha as Ha'.
  by apply Hall in Ha'.
Qed.

Lemma fsfun_sum_succ (f : fsfun A 0) (n : A) :
  fsfun_sum (succ_fsfun f n) = S (fsfun_sum f).
Proof.
  unfold fsfun_sum.
  destruct (decide (n ∈ fin_supp f)).
  - rewrite succ_fsfun_supp_in by done.
    pose proof (Hnodup := fin_supp_NoDup f).
    revert Hnodup e; cbn.
    generalize (fin_supp f) as l; induction l; [by inversion 2 |].
    rewrite list.NoDup_cons, elem_of_cons; cbn.
    intros [Ha Hnodup] [<- | Hn].
    + rewrite succ_fsfun_eq; cbn.
      do 2 f_equal.
      apply sum_list_with_ext_forall.
      by intros; rewrite succ_fsfun_neq by set_solver.
    + rewrite succ_fsfun_neq by set_solver.
      by rewrite IHl.
  - rewrite succ_fsfun_supp_not_in by done.
    cbn; rewrite succ_fsfun_eq.
    replace (f n) with 0 by (rewrite elem_of_fin_supp in n0; cbn in n0; lia).
    cbn; f_equal.
    apply sum_list_with_ext_forall.
    by intros; rewrite succ_fsfun_neq; [| set_solver].
Qed.

(** The component-wise sum of two functions *)
Definition add_fsfun_supp (f1 f2 : fsfun A 0) : listset A :=
  list_to_set (fin_supp f1) ∪ list_to_set (fin_supp f2).

Lemma add_fsfun_supp_all (f1 f2 : fsfun A 0) :
  Forall (fun a => f1 a + f2 a <> 0)
    (elements (add_fsfun_supp f1 f2)).
Proof.
  unfold add_fsfun_supp; apply Forall_forall; intros a.
  rewrite elem_of_elements, elem_of_union, !elem_of_list_to_set,
    !elem_of_fin_supp.
  by lia.
Qed.

Program Definition add_fsfun (f1 f2 : fsfun A 0) : fsfun A 0 :=
  existT (fun a => f1 a + f2 a)
    {| enum := list_annotate (add_fsfun_supp_all f1 f2) |}.
Next Obligation.
Proof. by intros; apply list_annotate_NoDup, NoDup_elements. Qed.
Next Obligation.
Proof.
  intros; destruct_dec_sig x a Ha Heq; subst.
  apply elem_of_list_annotate; unfold add_fsfun_supp.
  rewrite elem_of_elements, !elem_of_union, !elem_of_list_to_set, !elem_of_fin_supp.
  by cbn; lia.
Qed.

Lemma add_fsfun_rew (f1 f2 : fsfun A 0) (a : A) :
  add_fsfun f1 f2 a = f1 a + f2 a.
Proof. done. Qed.

#[export] Instance add_fsfun_proper :
  Proper ((≡) ==> (≡) ==> (≡)) add_fsfun.
Proof.
  intros f1 g1 Heqv1 f2 g2 Heqv2.
  apply fsfun_equiv_unfold; extensionality a.
  by rewrite !add_fsfun_rew, Heqv1, Heqv2.
Qed.

Lemma elem_of_add_fsfun (f1 f2 : fsfun A 0) :
  forall (a : A),
    a ∈ fin_supp (add_fsfun f1 f2) <->
    a ∈ fin_supp f1 \/ a ∈ fin_supp f2.
Proof.
  intro; unfold fin_supp at 1; cbn.
  rewrite list_annotate_forget, elem_of_elements.
  unfold add_fsfun_supp.
  by rewrite elem_of_union, !elem_of_list_to_set.
Qed.

#[export] Instance add_fsfun_comm : Comm (≡) add_fsfun.
Proof.
  intros f1 f2; apply fsfun_equiv_unfold; extensionality a.
  by rewrite !add_fsfun_rew; lia.
Qed.

#[export] Instance add_fsfun_left_id :
  LeftId (≡) zero_fsfun add_fsfun.
Proof. by intro; apply fsfun_equiv_unfold; extensionality a. Qed.

#[export] Instance add_fsfun_right_id :
  RightId (≡) zero_fsfun add_fsfun.
Proof.
  intro; apply fsfun_equiv_unfold; extensionality a.
  by rewrite add_fsfun_rew, zero_fsfun_rew; lia.
Qed.

#[export] Instance add_fsfun_assoc : Assoc (≡) add_fsfun.
Proof.
  intros f g h; rewrite !fsfun_equiv_unfold; extensionality a.
  by rewrite !add_fsfun_rew; lia.
Qed.

Lemma add_fsfun_succ_l (f1 f2 : fsfun A 0) :
  forall (a : A),
    add_fsfun (succ_fsfun f1 a) f2
      ≡
    succ_fsfun (add_fsfun f1 f2) a.
Proof.
  intros a; apply fsfun_equiv_unfold; extensionality a'.
  rewrite add_fsfun_rew.
  destruct (decide (a = a')) as [-> |].
  - by rewrite !succ_fsfun_eq.
  - by rewrite !succ_fsfun_neq.
Qed.

Lemma add_fsfun_succ_r (f1 f2 : fsfun A 0) :
  forall (a : A),
    add_fsfun f2 (succ_fsfun f1 a)
      ≡
    succ_fsfun (add_fsfun f2 f1) a.
Proof.
  by intros; rewrite (comm add_fsfun), add_fsfun_succ_l,
    (comm add_fsfun).
Qed.

(**
  To be able to prove things by induction on finitely supported functions on
  naturals we define the following inductive property and then we show that it
  holds for all such functions.
*)
Inductive NatFSFun : fsfun A 0 -> Prop :=
| P_zero :
    forall (f' : fsfun A 0), f' ≡ zero_fsfun ->
    NatFSFun f'
| P_succ :
    forall (f : fsfun A 0), NatFSFun f ->
    forall (f' : fsfun A 0) (i : A), f' ≡ succ_fsfun f i ->
    NatFSFun f'.

Lemma NatFSFun_complete (f : fsfun A 0) :  NatFSFun f.
Proof.
  remember (fsfun_sum f) as n.
  symmetry in Heqn.
  revert f Heqn; induction n; intros;
    [by apply fsfun_sum_zero_inv in Heqn; constructor |].
  assert (Hex : Exists (fun (i : A) => f i <> 0) (fin_supp f)).
  {
    apply dec_stable; intros Hex.
    apply not_Exists_Forall in Hex; [| by typeclasses eauto].
    replace (fsfun_sum f) with 0 in Heqn; [done |].
    symmetry.
    apply sum_list_with_zero.
    intros a Ha.
    by rewrite Forall_forall in Hex; apply Hex in Ha; cbn in Ha; lia.
  }
  pose proof (Hx := Exists_choose_first_good _ _ Hex); cbn in Hx.
  pose (x := Exists_choose_first Hex).
  destruct (f x) as [| px] eqn: Heqx; [done |]; clear Hx.
  pose (f' := update_fsfun f x px).
  assert (Heq : f ≡ succ_fsfun f' x).
  {
    subst f'; apply fsfun_equiv_unfold; extensionality a.
    destruct (decide (x = a)) as [-> |].
    - by rewrite succ_fsfun_eq, update_fsfun_eq.
    - by rewrite succ_fsfun_neq, update_fsfun_neq.
  }
  constructor 2 with f' x; [| done].
  apply IHn; subst f'.
  rewrite fsfun_sum_proper in Heqn by done.
  rewrite fsfun_sum_succ in Heqn.
  by congruence.
Qed.

Lemma nat_fsfun_inv (f : fsfun A 0) :
  f ≡ zero_fsfun
    \/
  exists (a : A) (f' : fsfun A 0), f ≡ succ_fsfun f' a.
Proof.
  pose proof (Hcomplete := NatFSFun_complete f).
  by inversion Hcomplete; subst; [left | right; eexists _,_].
Qed.

Lemma nat_fsfun_ind (P : (fsfun A 0) -> Prop)
  (Hproper : Proper ((≡) ==> impl) P)
  (Hzero : P zero_fsfun)
  (Hsucc : forall (i : A) (f : fsfun A 0),
    P f -> P (succ_fsfun f i)) :
  forall (f : fsfun A 0), P f.
Proof.
  intros.
  pose proof (Hcomplete := NatFSFun_complete f).
  by induction Hcomplete as [| ? ? ? ? ? ->];
    [eapply Hproper | apply Hsucc].
Qed.

End sec_fsfun_fixed_domain.

