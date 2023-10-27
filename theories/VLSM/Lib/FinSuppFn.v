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

(** A function is finitely supported if its [support] is [Finite]. *)
Class FinSupp {A B : Type} (s : B) (f : A -> B) `{EqDecision A} `{EqDecision B} :=
  finite_supp :> Finite (support s f).

Global Hint Mode FinSupp - - ! - - - : typeclass_instances.

(**
  We define a type to encapsulate functions of finite support.
*)
Record FinSuppFn {A : Type} `{s : B} `{EqDecision A} `{EqDecision B} : Type := fin_supp_fn
{
  fin_supp_fn_project :> A -> B;
  fin_supp_fn_has_fin_supp : FinSupp s fin_supp_fn_project;
}.

Arguments fin_supp_fn {_ _ s _ _} _ _.
Arguments FinSuppFn _ {_} s {_ _}.

Section sec_fin_supp_fn_fixed_domain.

Context
  `{EqDecision A}
  .

Section sec_fin_supp_fn_fixed_supp_value.

Context
  `{EqDecision B}
  {b : B}
  .

#[export] Instance fin_supp_fn_equiv : Equiv (FinSuppFn A b) :=
  (fun f g => fin_supp_fn_project f = fin_supp_fn_project g).

#[export] Instance fin_supp_fn_equivalence :
  Equivalence (≡@{FinSuppFn A b}).
Proof.
  unfold equiv, fin_supp_fn_equiv.
  constructor.
  - done.
  - by intros f g; apply symmetry.
  - by intros f g h; apply transitivity.
Qed.

#[export] Instance fin_supp_fn_project_proper :
  Proper ((≡) ==> (=)) (@fin_supp_fn_project A B b _ _).
Proof. by intros f g Heqv; inversion Heqv. Qed.

Lemma fin_supp_fn_equiv_unfold (f g : FinSuppFn A b) :
  f ≡ g <-> fin_supp_fn_project f = fin_supp_fn_project g.
Proof. done. Qed.

#[export] Instance fin_supp_fn_has_fin_supp_instance
  (f : FinSuppFn A b) : @FinSupp _ _ b f _ _ :=
    fin_supp_fn_has_fin_supp f.

Definition fin_supp (f : FinSuppFn A b) : list A :=
  map proj1_sig (enum (support b f)).

Lemma elem_of_fin_supp (f : FinSuppFn A b) :
  forall (a : A), a ∈ fin_supp f <-> f a <> b.
Proof.
  unfold fin_supp.
  split; rewrite elem_of_list_fmap.
  - intros (asupp & -> & _).
    by destruct_dec_sig asupp _a H_a Heq; subst.
  - intros Ha.
    by exists (dexist a Ha); split; [| apply elem_of_enum].
Qed.

Lemma not_elem_of_fin_supp (f : FinSuppFn A b) :
  forall (a : A), a ∉ fin_supp f <-> f a = b.
Proof.
  intros a; rewrite elem_of_fin_supp.
  by destruct (decide (f a = b)); itauto.
Qed.

Lemma fin_supp_NoDup (f : FinSuppFn A b) : NoDup (fin_supp f).
Proof. by apply dsig_NoDup, NoDup_enum. Qed.

#[export] Instance fin_supp_proper : Proper ((≡) ==> (≡ₚ)) fin_supp.
Proof.
  intros f g Heq.
  apply NoDup_Permutation; [by apply fin_supp_NoDup.. |].
  by intro; rewrite !elem_of_fin_supp, Heq.
Qed.

#[export] Instance fin_supp_fn_eq_dec : RelDecision (≡@{FinSuppFn A b}).
Proof.
  intros f g.
  destruct (@finset_equiv_dec A (listset A) _ _ _ _ _ _ _ _ _
    (list_to_set (fin_supp f)) (list_to_set (fin_supp g))) as [Heqv | Hneqv]; cycle 1.
  - right; intros Heqv.
    by rewrite Heqv in Hneqv.
  - destruct (decide (set_Forall (fun a => f a = g a) (list_to_set (C := listset A) (fin_supp f))))
      as [Hall | Hall]; [| by right; contradict Hall; rewrite Hall].
    left; apply fin_supp_fn_equiv_unfold; extensionality a.
    destruct (decide (a ∈ fin_supp f)) as [| Hf]; [by apply Hall, elem_of_list_to_set |].
    destruct (decide (a ∈ fin_supp g)) as [| Hg]; [by apply Hall; rewrite Heqv, elem_of_list_to_set |].
    apply not_elem_of_fin_supp in Hf, Hg.
    by congruence.
Qed.

Program Definition empty_supp_fn : FinSuppFn A b :=
  fin_supp_fn (const b) {| enum := [] |}.
Next Obligation.
Proof. by constructor. Qed.
Next Obligation.
Proof. by intros; destruct_dec_sig x a Ha Heq; contradiction Ha. Qed.

Lemma empty_supp_fn_supp : fin_supp empty_supp_fn = [].
Proof. done. Qed.

Lemma empty_supp_fn_supp_inv (f : FinSuppFn A b) :
  fin_supp f = [] -> f ≡ empty_supp_fn.
Proof.
  intros Hf; apply fin_supp_fn_equiv_unfold; extensionality a; cbn.
  eapply not_elem_of_fin_supp.
  rewrite Hf.
  by apply not_elem_of_nil.
Qed.

Definition update_fn_supp (f : FinSuppFn A b) (n : A) (b' : B) : listset A :=
  if decide (b' = b)
  then list_to_set (fin_supp f) ∖ {[n]}
  else {[n]} ∪ list_to_set (fin_supp f).

Lemma update_fn_supp_all (f : FinSuppFn A b) (n : A) (b' : B) :
  Forall (fun a => update_fn f n b' a <> b) (elements (update_fn_supp f n b')).
Proof.
  unfold update_fn_supp.
  apply Forall_forall; intros a.
  rewrite elem_of_elements.
  case_decide.
  - rewrite elem_of_difference, elem_of_singleton, elem_of_list_to_set,
      elem_of_fin_supp.
    by intros []; rewrite update_fn_neq.
  - rewrite elem_of_union, elem_of_singleton, elem_of_list_to_set,
      elem_of_fin_supp.
    by unfold update_fn; case_decide; cbn; intros [].
Qed.

Program Definition update_fn_fin_supp
  (f : FinSuppFn A b) (n : A) (b' : B) : FinSuppFn A b :=
  fin_supp_fn (update_fn f n b')
    {| enum := list_annotate (update_fn_supp_all f n b') |}.
Next Obligation.
Proof. by intros; apply list_annotate_NoDup, NoDup_elements. Qed.
Next Obligation.
Proof.
  intros; destruct_dec_sig x a Ha Heq; subst.
  apply elem_of_list_annotate, elem_of_elements.
  unfold update_fn_supp; case_decide.
  - rewrite elem_of_difference, elem_of_list_to_set, elem_of_fin_supp,
      elem_of_singleton; cbn.
    by unfold update_fn in Ha; case_decide; split; congruence.
  - rewrite elem_of_union, elem_of_list_to_set, elem_of_fin_supp,
      elem_of_singleton; cbn.
    by unfold update_fn in Ha; case_decide; [left | right].
Qed.

#[export] Instance update_fn_fin_supp_proper :
  Proper ((≡) ==> (=) ==> (=) ==> (≡)) update_fn_fin_supp.
Proof.
  intros f g Heqv _n n -> _b' b' ->.
  apply fin_supp_fn_equiv_unfold; extensionality a; cbn.
  by unfold update_fn; case_decide; cbn; congruence.
Qed.

Lemma elem_of_update_fn_fin_supp (f : FinSuppFn A b) (n : A) (b' : B) :
  forall (a : A),
    a ∈ fin_supp (update_fn_fin_supp f n b')
      <->
    b' = b /\ a ∈ fin_supp f /\ a <> n \/
    b' <> b /\ (a ∈ fin_supp f \/ a = n).
Proof.
  intro; unfold fin_supp at 1; cbn.
  rewrite list_annotate_forget, elem_of_elements.
  unfold update_fn_supp; case_decide.
  - by rewrite elem_of_difference, elem_of_list_to_set, elem_of_singleton; split; itauto.
  - by rewrite elem_of_union, elem_of_list_to_set, elem_of_singleton; split; itauto.
Qed.

End sec_fin_supp_fn_fixed_supp_value.

(** ** Finitely supported functions on naturals *)

Definition zero_fin_supp_nat_fn : FinSuppFn A 0 := empty_supp_fn.

Definition succ_fin_supp_nat_fn (f : FinSuppFn A 0) (n : A) : FinSuppFn A 0 :=
  update_fn_fin_supp f n (S (f n)).

#[export] Instance succ_fin_supp_nat_fn_proper :
  Proper ((≡) ==> (=) ==> (≡)) succ_fin_supp_nat_fn.
Proof.
  intros f g Heqv _n n ->.
  by apply update_fn_fin_supp_proper; [.. | rewrite Heqv].
Qed.

Lemma elem_of_succ_fin_supp_nat_fn_fin_supp (f : FinSuppFn A 0) (n : A) :
  forall (a : A),
    a ∈ fin_supp (succ_fin_supp_nat_fn f n) <-> a = n \/ a ∈ fin_supp f.
Proof.
  intros a; unfold succ_fin_supp_nat_fn.
  rewrite elem_of_update_fn_fin_supp.
  by split; itauto lia.
Qed.

Lemma succ_fin_supp_nat_fn_supp_in (f : FinSuppFn A 0) (n : A) :
  n ∈ fin_supp f -> fin_supp (succ_fin_supp_nat_fn f n) ≡ₚ fin_supp f.
Proof.
  intros.
  apply NoDup_Permutation; intros; [by apply fin_supp_NoDup.. |].
  rewrite elem_of_succ_fin_supp_nat_fn_fin_supp.
  by set_solver.
Qed.

Lemma succ_fin_supp_nat_fn_supp_not_in (f : FinSuppFn A 0) (n : A) :
  n ∉ fin_supp f -> fin_supp (succ_fin_supp_nat_fn f n) ≡ₚ n :: fin_supp f.
Proof.
  intros; cbn; rewrite list_annotate_forget.
  unfold update_fn_supp; rewrite decide_False by lia.
  rewrite @elements_union_singleton;
    [| by typeclasses eauto | by rewrite elem_of_list_to_set].
  by constructor; eapply @elements_list_to_set;
    [typeclasses eauto | apply fin_supp_NoDup].
Qed.

Definition delta_fin_supp_nat_fn (n : A) : FinSuppFn A 0 :=
  succ_fin_supp_nat_fn zero_fin_supp_nat_fn n.

Lemma elem_of_delta_fin_supp_nat_fn_fin_supp (n : A) :
  forall (a : A),
    a ∈ fin_supp (delta_fin_supp_nat_fn n) <-> a = n.
Proof.
  intros a.
  unfold delta_fin_supp_nat_fn.
  rewrite elem_of_succ_fin_supp_nat_fn_fin_supp; cbn; rewrite elem_of_nil.
  by itauto.
Qed.

Definition sum_fin_supp_nat_fn (f : FinSuppFn A 0) : nat :=
  sum_list_with f (fin_supp f).

Lemma sum_fin_supp_nat_fn_proper : Proper ((≡) ==> (=)) sum_fin_supp_nat_fn.
Proof.
  intros f g Heqv.
  unfold sum_fin_supp_nat_fn.
  rewrite (sum_list_with_proper f (fin_supp f) (fin_supp g)).
  - by apply sum_list_with_ext_forall; intros; rewrite Heqv.
  - by apply fin_supp_proper.
Qed.

Lemma sum_fin_supp_nat_fn_zero_inv (f : FinSuppFn A 0) :
  sum_fin_supp_nat_fn f = 0 -> f ≡ zero_fin_supp_nat_fn.
Proof.
  setoid_rewrite sum_list_with_zero; intros Hall.
  apply fin_supp_fn_equiv_unfold; extensionality a; cbn.
  destruct (decide (a ∈ fin_supp f)); [by apply Hall |].
  by rewrite elem_of_fin_supp in n; cbn in n; lia.
Qed.

Lemma sum_fin_supp_nat_fn_succ (f : FinSuppFn A 0) (n : A) :
  sum_fin_supp_nat_fn (succ_fin_supp_nat_fn f n) = S (sum_fin_supp_nat_fn f).
Proof.
  unfold sum_fin_supp_nat_fn.
  destruct (decide (n ∈ fin_supp f)).
  - rewrite succ_fin_supp_nat_fn_supp_in by done.
    pose proof (Hnodup := fin_supp_NoDup f).
    revert Hnodup e; cbn.
    generalize (fin_supp f) as l; induction l; [by inversion 2 |].
    rewrite list.NoDup_cons, elem_of_cons; cbn.
    intros [Ha Hnodup] [<- | Hn].
    + rewrite update_fn_eq; cbn.
      do 2 f_equal.
      apply sum_list_with_ext_forall.
      by intros; rewrite update_fn_neq by set_solver.
    + rewrite update_fn_neq by set_solver.
      by rewrite IHl.
  - rewrite succ_fin_supp_nat_fn_supp_not_in by done.
    cbn; rewrite update_fn_eq.
    replace (f n) with 0 by (rewrite elem_of_fin_supp in n0; cbn in n0; lia).
    cbn; f_equal.
    apply sum_list_with_ext_forall.
    by intros; rewrite update_fn_neq; [| set_solver].
Qed.

(** The component-wise sum of two functions *)
Definition fin_supp_nat_fn_add_supp (f1 f2 : FinSuppFn A 0) : listset A :=
  list_to_set (fin_supp f1) ∪ list_to_set (fin_supp f2).

Lemma fin_supp_nat_fn_add_supp_all (f1 f2 : FinSuppFn A 0) :
  Forall (fun a => f1 a + f2 a <> 0)
    (elements (fin_supp_nat_fn_add_supp f1 f2)).
Proof.
  unfold fin_supp_nat_fn_add_supp; apply Forall_forall; intros a.
  rewrite elem_of_elements, elem_of_union, !elem_of_list_to_set,
    !elem_of_fin_supp.
  by lia.
Qed.

Program Definition fin_supp_nat_fn_add (f1 f2 : FinSuppFn A 0) : FinSuppFn A 0 :=
  fin_supp_fn (fun a => f1 a + f2 a)
    {| enum := list_annotate (fin_supp_nat_fn_add_supp_all f1 f2) |}.
Next Obligation.
Proof. by intros; apply list_annotate_NoDup, NoDup_elements. Qed.
Next Obligation.
Proof.
  intros; destruct_dec_sig x a Ha Heq; subst.
  apply elem_of_list_annotate; unfold fin_supp_nat_fn_add_supp.
  rewrite elem_of_elements, !elem_of_union, !elem_of_list_to_set, !elem_of_fin_supp.
  by cbn; lia.
Qed.

#[export] Instance fin_supp_nat_fn_add_proper :
  Proper ((≡) ==> (≡) ==> (≡)) fin_supp_nat_fn_add.
Proof.
  intros f1 g1 Heqv1 f2 g2 Heqv2.
  apply fin_supp_fn_equiv_unfold; extensionality a; cbn.
  by rewrite Heqv1, Heqv2.
Qed.

Lemma elem_of_fin_supp_nat_fn_add_fin_supp (f1 f2 : FinSuppFn A 0) :
  forall (a : A),
    a ∈ fin_supp (fin_supp_nat_fn_add f1 f2) <->
    a ∈ fin_supp f1 \/ a ∈ fin_supp f2.
Proof.
  intro; unfold fin_supp at 1; cbn.
  rewrite list_annotate_forget, elem_of_elements.
  unfold fin_supp_nat_fn_add_supp.
  by rewrite elem_of_union, !elem_of_list_to_set.
Qed.

#[export] Instance fin_supp_nat_fn_add_comm : Comm (≡) fin_supp_nat_fn_add.
Proof.
  intros f1 f2; apply fin_supp_fn_equiv_unfold.
  by extensionality a; cbn; lia.
Qed.

#[export] Instance fin_supp_nat_fn_add_left_id :
  LeftId (≡) zero_fin_supp_nat_fn fin_supp_nat_fn_add.
Proof. by intro; apply fin_supp_fn_equiv_unfold; extensionality a. Qed.

#[export] Instance fin_supp_nat_fn_add_right_id :
  RightId (≡) zero_fin_supp_nat_fn fin_supp_nat_fn_add.
Proof. by intro; apply fin_supp_fn_equiv_unfold; extensionality a; cbn; lia. Qed.

#[export] Instance fin_supp_nat_fn_add_assoc : Assoc (≡) fin_supp_nat_fn_add.
Proof.
  by intros f g h; rewrite !fin_supp_fn_equiv_unfold; extensionality a; cbn; lia.
Qed.

Lemma fin_supp_nat_fn_add_succ_l (f1 f2 : FinSuppFn A 0) :
  forall (a : A),
    fin_supp_nat_fn_add (succ_fin_supp_nat_fn f1 a) f2
      ≡
    succ_fin_supp_nat_fn (fin_supp_nat_fn_add f1 f2) a.
Proof.
  intros a; apply fin_supp_fn_equiv_unfold.
  extensionality a'; cbn.
  by unfold update_fn; case_decide; cbn; congruence.
Qed.

Lemma fin_supp_nat_fn_add_succ_r (f1 f2 : FinSuppFn A 0) :
  forall (a : A),
    fin_supp_nat_fn_add f2 (succ_fin_supp_nat_fn f1 a)
      ≡
    succ_fin_supp_nat_fn (fin_supp_nat_fn_add f2 f1) a.
Proof.
  by intros; rewrite (comm fin_supp_nat_fn_add), fin_supp_nat_fn_add_succ_l,
    (comm fin_supp_nat_fn_add).
Qed.

(**
  To be able to prove things by induction on finitely supported functions on
  naturals we define the following inductive property and then we show that it
  holds for all such functions.
*)
Inductive FinSuppNatFn : FinSuppFn A 0 -> Prop :=
| P_zero :
    forall (f' : FinSuppFn A 0), f' ≡ zero_fin_supp_nat_fn ->
    FinSuppNatFn f'
| P_succ :
    forall (f : FinSuppFn A 0), FinSuppNatFn f ->
    forall (f' : FinSuppFn A 0) (i : A), f' ≡ succ_fin_supp_nat_fn f i ->
    FinSuppNatFn f'.

Lemma FinSuppNatFn_complete (f : FinSuppFn A 0) :  FinSuppNatFn f.
Proof.
  remember (sum_fin_supp_nat_fn f) as n.
  symmetry in Heqn.
  revert f Heqn; induction n; intros;
    [by apply sum_fin_supp_nat_fn_zero_inv in Heqn; constructor |].
  assert (Hex : Exists (fun (i : A) => f i <> 0) (fin_supp f)).
  {
    apply dec_stable; intros Hex.
    apply not_Exists_Forall in Hex; [| by typeclasses eauto].
    replace (sum_fin_supp_nat_fn f) with 0 in Heqn; [done |].
    symmetry.
    apply sum_list_with_zero.
    intros a Ha.
    by rewrite Forall_forall in Hex; apply Hex in Ha; cbn in Ha; lia.
  }
  pose proof (Hx := Exists_choose_first_good _ _ Hex); cbn in Hx.
  pose (x := Exists_choose_first Hex).
  destruct (f x) as [| px] eqn: Heqx; [done |]; clear Hx.
  pose (f' := update_fn_fin_supp f x px).
  assert (Heq : f ≡ succ_fin_supp_nat_fn f' x).
  {
    subst f'; apply fin_supp_fn_equiv_unfold; extensionality a; cbn.
    by unfold update_fn; repeat case_decide; congruence.
  }
  constructor 2 with f' x; [| done].
  apply IHn; subst f'.
  rewrite sum_fin_supp_nat_fn_proper in Heqn by done.
  rewrite sum_fin_supp_nat_fn_succ in Heqn.
  by congruence.
Qed.

Lemma fin_supp_nat_fn_inv (f : FinSuppFn A 0) :
  f ≡ zero_fin_supp_nat_fn
    \/
  exists (a : A) (f' : FinSuppFn A 0), f ≡ succ_fin_supp_nat_fn f' a.
Proof.
  pose proof (Hcomplete := FinSuppNatFn_complete f).
  by inversion Hcomplete; subst; [left | right; eexists _,_].
Qed.

Lemma fin_supp_nat_fn_ind (P : (FinSuppFn A 0) -> Prop)
  (Hproper : Proper ((≡) ==> impl) P)
  (Hzero : P zero_fin_supp_nat_fn)
  (Hsucc : forall (i : A) (f : FinSuppFn A 0),
    P f -> P (succ_fin_supp_nat_fn f i)) :
  forall (f : FinSuppFn A 0), P f.
Proof.
  intros.
  pose proof (Hcomplete := FinSuppNatFn_complete f).
  by induction Hcomplete as [| ? ? ? ? ? ->];
    [eapply Hproper | apply Hsucc].
Qed.

End sec_fin_supp_fn_fixed_domain.
