From VLSM.Lib Require Import Itauto.
From Coq Require Import FunctionalExtensionality.
From stdpp Require Import prelude finite.
From VLSM.Lib Require Import Preamble StdppExtras ListExtras.


(** * Finitely supported functions *)

(**
  A function is finitely supported if the subtype of its elements whose image
  through the function is different from the [inhabitant] is [Finite].

  Note that for [nat] and [Z] the [inhabitant] is <<0>>.
*)

(**
  Given a function, we define its support as the subtype of elements from
  its domain whose image through the function is different from the [inhabitant].
*)
Definition supp `(f : A -> B) `{Inhabited B} `{EqDecision B} : Type :=
  dsig (fun a => f a <> inhabitant).

(** ** Functions with a finite domain *)

(**
  We model functions with a finite domain of interest as
  consisting of a function over a (possibly) infinite type and a finite
  set of elements of that type representing the domain of interest associated
  to that function.
*)
Section sec_fin_supp_fn.

Context
  `{EqDecision A}
  `{EqDecision B}
  `{Inhabited B}
  .

Definition fin_supp `(f : A -> B) `{!Finite (supp f)} : list A :=
  map proj1_sig (enum (supp f)).

Lemma elem_of_fin_supp (f : A -> B) `{!Finite (supp f)} :
  forall a : A, a ∈ fin_supp f <-> f a <> inhabitant.
Proof.
  intro a. unfold fin_supp; rewrite elem_of_list_fmap; split.
  - intros (asupp & -> & _).
    by destruct_dec_sig asupp _a H_a Heq; subst.
  - intro Ha.
    by exists (dexist a Ha); split; [| apply elem_of_enum].
Qed.

Lemma fin_supp_NoDup `(f : A -> B) `{!Finite (supp f)} : NoDup (fin_supp f).
Proof. by apply dsig_NoDup, NoDup_enum. Qed.

Lemma fin_supp_proper (f g : A -> B) `{!Finite (supp f)} `{!Finite (supp g)} :
  f = g -> fin_supp f ≡ₚ fin_supp g.
Proof.
  intro Heq.
  apply NoDup_Permutation; [by apply fin_supp_NoDup.. |].
  by intro; rewrite !elem_of_fin_supp; subst.
Qed.

#[export] Instance fin_supp_fn_eq_dec (f g : A -> B) `{!Finite (supp f)} `{!Finite (supp g)} :
  Decision (f = g).
Proof.
  destruct
    (@finset_equiv_dec A (listset A) _ _ _ _ _ _ _ _ _
      (list_to_set (fin_supp f)) (list_to_set (fin_supp g))).
  - destruct (decide (set_Forall (fun a => f a = g a) (list_to_set (C := listset A) (fin_supp f)))).
    + left; extensionality a.
      destruct (decide (a ∈ fin_supp f)).
      * by apply s, elem_of_list_to_set.
      * assert (f a = inhabitant) as ->.
        {
          destruct (decide (f a = inhabitant)); [done |].
          by contradict n; apply elem_of_fin_supp.
        }
        symmetry; destruct (decide (g a = inhabitant)); [done |].
        contradict n.
        rewrite <- (elem_of_list_to_set (C := listset A)).
        by apply e, elem_of_list_to_set, elem_of_fin_supp.
    + by right; contradict n; subst.
  - right; contradict n; subst.
    by intro a; rewrite !elem_of_list_to_set, !elem_of_fin_supp.
Qed.

Definition empty_supp_fn : A -> B := const inhabitant.

#[export] Program Instance empty_supp_fn_has_fin_supp : Finite (supp empty_supp_fn) :=
{
  enum := []
}.
Next Obligation.
Proof. by constructor. Qed.
Next Obligation.
Proof. by intro x; destruct_dec_sig x a Ha Heq; contradiction Ha. Defined.

Lemma empty_supp_fn_supp : fin_supp empty_supp_fn = [].
Proof. done. Qed.

Lemma empty_supp_fn_supp_inv (f : A -> B) `{!Finite (supp f)} :
  fin_supp f = [] -> f = empty_supp_fn.
Proof.
  intro Hf; extensionality a.
  destruct (decide (f a = inhabitant)); [done |].
  contradict Hf.
  eapply elem_of_not_nil, elem_of_list_fmap.
  by exists (dexist a n); split; [| apply elem_of_enum].
Qed.

Definition update_fn_supp (f : A -> B) (n : A) (b : B) `{!Finite (supp f)} :
  listset A :=
  if (decide (b = inhabitant)) then list_to_set (fin_supp f) ∖ {[n]} else
  {[n]} ∪ list_to_set (fin_supp f).

Lemma update_fn_supp_all (f : A -> B) (n : A) (b : B) `{!Finite (supp f)} :
  Forall (fun a => update_fn f n b a <> inhabitant)
    (elements (update_fn_supp f n b)).
Proof.
  unfold update_fn_supp; apply Forall_forall; intro a.
  rewrite elem_of_elements.
  case_decide.
  - rewrite elem_of_difference, elem_of_singleton, elem_of_list_to_set,
      elem_of_fin_supp.
    by intros []; rewrite update_fn_neq.
  - rewrite elem_of_union, elem_of_singleton, elem_of_list_to_set,
      elem_of_fin_supp.
    destruct (decide (a = n)).
    + by subst; rewrite update_fn_eq.
    + rewrite update_fn_neq by done.
      by intros [].
Qed.

Program Definition update_fn_has_fin_supp
  (f : A -> B) (n : A) (b : B) `{!Finite (supp f)} :
  Finite (supp (update_fn f n b)) :=
{|
  enum := list_annotate (update_fn_supp_all f n b)
|}.
Next Obligation.
Proof. intros; apply list_annotate_NoDup, NoDup_elements. Qed.
Next Obligation.
Proof.
  intros; destruct_dec_sig x a Ha Heq; subst.
  apply elem_of_list_annotate, elem_of_elements.
  unfold update_fn_supp; case_decide.
  - rewrite elem_of_difference, elem_of_list_to_set, elem_of_fin_supp,
      elem_of_singleton; cbn.
    destruct (decide (a = n)); [by subst; rewrite update_fn_eq in Ha |].
    by rewrite update_fn_neq in Ha.
  - rewrite elem_of_union, elem_of_list_to_set, elem_of_fin_supp,
      elem_of_singleton; cbn.
    destruct (decide (a = n)); [by left |].
    by right; rewrite update_fn_neq in Ha.
Qed.

Lemma elem_of_update_fn_fin_supp
  (f : A -> B) (n : A) (b : B) `{!Finite (supp f)} :
  forall a : A, a ∈ fin_supp (update_fn f n b) (Finite0 := update_fn_has_fin_supp f n b)
    <->
  b = inhabitant /\ a ∈ fin_supp f /\ a <> n \/
  b <> inhabitant /\ (a ∈ fin_supp f \/ a = n).
Proof.
  intro; unfold fin_supp at 1; cbn.
  rewrite list_annotate_forget, elem_of_elements.
  unfold update_fn_supp; case_decide.
  - by rewrite elem_of_difference, elem_of_list_to_set, elem_of_singleton; split; itauto.
  - by rewrite elem_of_union, elem_of_list_to_set, elem_of_singleton; split; itauto.
Qed.

End sec_fin_supp_fn.
Arguments empty_supp_fn (A B)%type_scope {H} _ : assert.

(** ** Finitely supported functions on naturals *)

Section sec_fin_supp_nat_fn_prop.

Context
  `{EqDecision A}
  .

Definition zero_fin_supp_nat_fn : A -> nat := empty_supp_fn A nat.

Definition succ_fin_supp_nat_fn (f : A -> nat) (n : A) : A -> nat :=
    update_fn f n (S (f n)).

Definition succ_fin_supp_nat_fn_supp (f : A -> nat) (n : A) `{!Finite (supp f)} :
  listset A :=
  {[n]} ∪ list_to_set (fin_supp f).

Lemma succ_fin_supp_nat_fn_supp_all (f : A -> nat) (n : A) `{!Finite (supp f)} :
  Forall (fun a => succ_fin_supp_nat_fn f n a <> inhabitant)
    (elements (succ_fin_supp_nat_fn_supp f n)).
Proof.
  unfold succ_fin_supp_nat_fn_supp; apply Forall_forall; intro a.
  rewrite elem_of_elements, elem_of_union, elem_of_singleton, elem_of_list_to_set,
    elem_of_fin_supp.
  unfold succ_fin_supp_nat_fn; cbn.
  destruct (decide (a = n)).
  - by subst; rewrite update_fn_eq; lia.
  - rewrite update_fn_neq by done.
    by intros [].
Qed.

#[export] Program Instance succ_fin_supp_nat_fn_has_fin_supp
  (f : A -> nat) (n : A) `{!Finite (supp f)} :
  Finite (supp (succ_fin_supp_nat_fn f n)) :=
{
  enum := list_annotate (succ_fin_supp_nat_fn_supp_all f n)
}.
Next Obligation.
Proof. intros; apply list_annotate_NoDup, NoDup_elements. Qed.
Next Obligation.
Proof.
  intros; destruct_dec_sig x a Ha Heq; subst.
  apply elem_of_list_annotate, elem_of_elements, elem_of_union; cbn.
  rewrite elem_of_singleton, elem_of_list_to_set, elem_of_fin_supp.
  destruct (decide (a = n)); [by left |].
  unfold succ_fin_supp_nat_fn in Ha; rewrite update_fn_neq in Ha by done.
  by right.
Qed.

Lemma elem_of_succ_fin_supp_nat_fn_fin_supp
  (f : A -> nat) (n : A) `{!Finite (supp f)} :
  forall a : A, a ∈ fin_supp (succ_fin_supp_nat_fn f n) <-> a = n \/ a ∈ fin_supp f.
Proof.
  intro; unfold fin_supp at 1; cbn.
  rewrite list_annotate_forget, elem_of_elements.
  unfold succ_fin_supp_nat_fn_supp.
  by rewrite elem_of_union, elem_of_list_to_set, elem_of_singleton.
Qed.

Definition delta_fin_supp_nat_fn (n : A) : A -> nat :=
  succ_fin_supp_nat_fn zero_fin_supp_nat_fn n.

Lemma elem_of_delta_fin_supp_nat_fn_fin_supp (n : A) :
  forall a, a ∈ fin_supp (delta_fin_supp_nat_fn n) <-> a = n.
Proof.
  intro; unfold delta_fin_supp_nat_fn; rewrite elem_of_succ_fin_supp_nat_fn_fin_supp; cbn.
  split; [| by left].
  by intros [| Ha]; [| inversion Ha].
Qed.

Definition sum_fin_supp_nat_fn (f : A -> nat) `{!Finite (supp f)} : nat :=
  sum_list_with f (fin_supp f).

Lemma sum_fin_supp_nat_fn_proper
  (f g : A -> nat) `{!Finite (supp f)} `{!Finite (supp g)} :
  f = g -> sum_fin_supp_nat_fn f = sum_fin_supp_nat_fn g.
Proof.
  intros.
  unfold sum_fin_supp_nat_fn; rewrite (sum_list_with_proper f (fin_supp f) (fin_supp g));
    [by apply sum_list_with_ext_forall; subst |].
  by apply fin_supp_proper.
Qed.

Lemma sum_fin_supp_nat_fn_zero_inv (f : A -> nat) `{!Finite (supp f)} :
  sum_fin_supp_nat_fn f = 0 -> f = zero_fin_supp_nat_fn.
Proof.
  setoid_rewrite sum_list_with_zero; intros Hall.
  extensionality a; cbn.
  destruct (decide (a ∈ fin_supp f)); [by apply Hall |].
  by rewrite elem_of_fin_supp in n; cbn in n; lia.
Qed.

Lemma sum_fin_supp_nat_fn_succ
  (f : A -> nat) (n : A) `{!Finite (supp f)}:
  sum_fin_supp_nat_fn (succ_fin_supp_nat_fn f n) = S (sum_fin_supp_nat_fn f).
Proof.
  unfold sum_fin_supp_nat_fn, succ_fin_supp_nat_fn; cbn.
  rewrite list_annotate_forget.
  unfold succ_fin_supp_nat_fn_supp.
  destruct (decide (n ∈ fin_supp f)).
  - assert ({[n]} ∪ list_to_set (C := listset A) (fin_supp f) ≡ list_to_set (fin_supp f)) as ->
      by set_solver.
    rewrite elements_list_to_set by apply fin_supp_NoDup.
    revert e; specialize (fin_supp_NoDup f).
    generalize (fin_supp f) as l; clear; induction l; [by inversion 2 |].
    rewrite list.NoDup_cons, elem_of_cons; cbn.
    intros [Ha Hnodup] [<- | Hn].
    + rewrite update_fn_eq; cbn.
      do 2 f_equal.
      apply sum_list_with_ext_forall.
      by intros; rewrite update_fn_neq by  set_solver.
    + rewrite update_fn_neq by set_solver.
      rewrite IHl by done.
      by lia.
  - rewrite elements_union_singleton by (rewrite elem_of_list_to_set; done).
    rewrite elements_list_to_set by apply fin_supp_NoDup.
    cbn; rewrite update_fn_eq.
    assert (f n = 0) as -> by (rewrite elem_of_fin_supp in n0; cbn in n0; lia).
    cbn; f_equal.
    apply sum_list_with_ext_forall.
    by intros; rewrite update_fn_neq; [| set_solver].
Qed.

(** The component-wise sum of two functions *)
Definition fin_supp_nat_fn_add (f1 f2 : A -> nat) (a : A) : nat := f1 a + f2 a.

Definition fin_supp_nat_fn_add_supp
  (f1 f2 : A -> nat) `{!Finite (supp f1)} `{!Finite (supp f2)} : listset A :=
  list_to_set (fin_supp f1) ∪ list_to_set (fin_supp f2).

Lemma fin_supp_nat_fn_add_supp_all
  (f1 f2 : A -> nat) `{!Finite (supp f1)} `{!Finite (supp f2)}:
  Forall (fun a => fin_supp_nat_fn_add f1 f2 a <> inhabitant)
    (elements (fin_supp_nat_fn_add_supp f1 f2)).
Proof.
  unfold fin_supp_nat_fn_add_supp; apply Forall_forall; intro a.
  rewrite elem_of_elements, elem_of_union, !elem_of_list_to_set,
    !elem_of_fin_supp.
  by unfold fin_supp_nat_fn_add; cbn; lia.
Qed.

#[export] Program Instance fin_supp_nat_fn_add_has_finn_supp
  (f1 f2 : A -> nat) `{!Finite (supp f1)} `{!Finite (supp f2)}
  : Finite (supp (fin_supp_nat_fn_add f1 f2)) :=
{
  enum := list_annotate (fin_supp_nat_fn_add_supp_all f1 f2)
}.
Next Obligation.
Proof. intros; apply list_annotate_NoDup, NoDup_elements. Qed.
Next Obligation.
Proof.
  intros; destruct_dec_sig x a Ha Heq; subst.
  apply elem_of_list_annotate, elem_of_elements, elem_of_union; cbn.
  rewrite !elem_of_list_to_set, !elem_of_fin_supp.
  by unfold fin_supp_nat_fn_add in Ha; cbn in *; lia.
Qed.

Lemma elem_of_fin_supp_nat_fn_add_fin_supp
  (f1 f2 : A -> nat) `{!Finite (supp f1)} `{!Finite (supp f2)} :
  forall a : A, a ∈ fin_supp (fin_supp_nat_fn_add f1 f2) <->
    a ∈ fin_supp f1 \/ a ∈ fin_supp f2.
Proof.
  intro; unfold fin_supp at 1; cbn.
  rewrite list_annotate_forget, elem_of_elements.
  unfold fin_supp_nat_fn_add_supp.
  by rewrite elem_of_union, !elem_of_list_to_set.
Qed.

#[export] Instance fin_supp_nat_fn_add_comm : Comm (=) fin_supp_nat_fn_add.
Proof.
  by intros f1 f2; extensionality a; unfold fin_supp_nat_fn_add; lia.
Qed.

#[export] Instance fin_supp_nat_fn_add_left_id :
  LeftId (=) zero_fin_supp_nat_fn fin_supp_nat_fn_add.
Proof. by intro; extensionality a. Qed.

#[export] Instance fin_supp_nat_fn_add_right_id :
  RightId (=) zero_fin_supp_nat_fn fin_supp_nat_fn_add.
Proof. by unfold fin_supp_nat_fn_add; intro; extensionality a; cbn; lia. Qed.

#[export] Instance fin_supp_nat_fn_add_assoc : Assoc (=) fin_supp_nat_fn_add.
Proof.
  by intros f g h; extensionality a; unfold fin_supp_nat_fn_add; lia.
Qed.

Lemma fin_supp_nat_fn_add_succ_l (f1 f2 : A -> nat) :
  forall a : A,
  fin_supp_nat_fn_add (succ_fin_supp_nat_fn f1 a) f2
    =
  succ_fin_supp_nat_fn (fin_supp_nat_fn_add f1 f2) a.
Proof.
  intro n; extensionality a; unfold fin_supp_nat_fn_add, succ_fin_supp_nat_fn.
  destruct (decide (n = a)).
  - by subst; rewrite !update_fn_eq; lia.
  - by rewrite !update_fn_neq.
Qed.

Lemma fin_supp_nat_fn_add_succ_r (f1 f2 : A -> nat) :
  forall a : A,
  fin_supp_nat_fn_add f2 (succ_fin_supp_nat_fn f1 a)
    =
  succ_fin_supp_nat_fn (fin_supp_nat_fn_add f2 f1) a.
Proof.
  etransitivity; [by apply comm; typeclasses eauto |].
  rewrite fin_supp_nat_fn_add_succ_l.
  by f_equal; apply comm; typeclasses eauto.
Qed.

(**
  To be able to prove things by induction on finitely supported functions on
  naturals we define the following inductive property and we then show it
  holds for all such functions.
*)
Inductive FinSuppNatFn : (A -> nat) -> Type :=
| P_zero : FinSuppNatFn zero_fin_supp_nat_fn
| P_succ : forall (i : A) (f : A -> nat),
   FinSuppNatFn f -> FinSuppNatFn (succ_fin_supp_nat_fn f i).


Lemma FinSuppNatFn_has_fin_supp (f : A -> nat) (Hf : FinSuppNatFn f) :
  Finite (supp f).
Proof.
  by induction Hf; typeclasses eauto.
Defined.

Lemma FinSuppNatFn_complete
  (f : A -> nat) `{Hf : !Finite (supp f)} : FinSuppNatFn f.
Proof.
  remember (sum_fin_supp_nat_fn f) as n.
  symmetry in Heqn.
  revert f Hf Heqn.
  induction n; intros;
    [by apply sum_fin_supp_nat_fn_zero_inv in Heqn as ->; constructor |].
  assert (Hex : Exists (fun (i : A) => f i <> 0) (fin_supp f)).
  {
    destruct (decide (Exists (fun (i : A) => f i <> 0) (fin_supp f))); [done |].
    apply not_Exists_Forall in n0; [| by typeclasses eauto].
    replace (sum_fin_supp_nat_fn f) with 0 in Heqn; [done |].
    symmetry.
    apply sum_list_with_zero.
    intros a Ha.
    by rewrite Forall_forall in n0; apply n0 in Ha; cbn in Ha; lia.
  }
  pose proof (Hx := Exists_choose_first_good _ _ Hex); cbn in Hx.
  pose (x := Exists_choose_first Hex).
  destruct (f x) as [| px] eqn: Heqx; [done |]; clear Hx.
  pose (f' := update_fn f x px).
  assert (Heq : f = succ_fin_supp_nat_fn f' x).
  {
    subst f'; unfold succ_fin_supp_nat_fn.
    extensionality a.
    destruct (decide (a = x)); [by subst; rewrite !update_fn_eq |].
    by rewrite !update_fn_neq.
  }
  rewrite Heq.
  constructor.
  unshelve eapply IHn; [by apply update_fn_has_fin_supp |].
  unshelve erewrite sum_fin_supp_nat_fn_proper with (g := succ_fin_supp_nat_fn f' x) in Heqn;
    [by apply succ_fin_supp_nat_fn_has_fin_supp, update_fn_has_fin_supp | | done].
  rewrite sum_fin_supp_nat_fn_succ in Heqn.
  by congruence.
Qed.

Lemma fin_supp_nat_fn_ind
  (P : forall (f : A -> nat) `{!Finite (supp f)}, Prop)
  (Hproper : forall (f g : A -> nat) `{!Finite (supp f)} `{!Finite (supp g)},
    f = g -> P f -> P g)
  (Hzero : P zero_fin_supp_nat_fn)
  (Hsucc : forall (i : A) (f : A -> nat) `{Hf : !Finite (supp f)},
    P f -> P (succ_fin_supp_nat_fn f i)) :
  forall (f : A -> nat) `{Hf : !Finite (supp f)}, P f.
Proof.
  intros.
  pose proof (Hcomplete := FinSuppNatFn_complete f).
  induction Hcomplete; [by eapply Hproper in Hzero |].
  apply FinSuppNatFn_has_fin_supp in Hcomplete.
  specialize (IHHcomplete Hcomplete).
  specialize (Hsucc i _ _ IHHcomplete).
  by eapply Hproper in Hsucc.
Qed.

End sec_fin_supp_nat_fn_prop.
