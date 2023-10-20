From VLSM.Lib Require Import Itauto.
From Coq Require Import FunctionalExtensionality.
From stdpp Require Import prelude.
From VLSM.Lib Require Import Preamble StdppExtras.


(** * Finitely supported functions *)

(**
  We model finitely supported functions as consisting of a total function
  and a finite set of elements from the function's source type (called the domain),
  satisfying that an element is in the domain iff its image through the
  function is different than the [inhabitant].
  Note that for [nat] and [Z] the [inhabitant] is <<0>>.

  We will split that into two definitions: a record [fin_dom_fn] encapsulating
  functions fith a finite domain functions and a class [FinSuppFn] encapsulating
  the finite support property.
*)

(** ** Functions with a finite domain *)

(**
  We model functions with a finite domain of interest as
  consisting of a function over a (possibly) infinite type and a finite
  set of elements of that type representing the domain of interest associated
  to that function.
*)
Record fin_dom_fn (A B Supp : Type) := mk_fin_dom_fn
{
  fin_dom_f : A -> B ;
  fin_dom : Supp ;
}.
Arguments fin_dom {A B Supp}%type_scope  f : assert.
Arguments fin_dom_f {A B Supp}%type_scope f _ : assert.
Arguments mk_fin_dom_fn {A B Supp}%type_scope fin_dom_f%function_scope fin_dom : assert.

Section sec_fin_dom_fn_prop.

Context
  `{FinSet A Supp}
  {B : Type}
  .

Record fin_dom_fn_subseteq (fp1 fp2 : fin_dom_fn A B Supp) : Prop :=
{
  fp_sub_dom : fin_dom fp1 ⊆ fin_dom fp2;
  fp_sub_fn : forall (a : A), a ∈ fin_dom fp1 -> fin_dom_f fp1 a = fin_dom_f fp2 a
}.

#[export] Instance fin_dom_fn_subseteq_instance
  : SubsetEq (fin_dom_fn A B Supp) := fin_dom_fn_subseteq.

Record fin_dom_fn_equiv (fp1 fp2 : fin_dom_fn A B Supp) : Prop :=
{
  fp_eqv_dom : fin_dom fp1 ≡ fin_dom fp2;
  fp_eqv_fn : forall (a : A), a ∈ fin_dom fp1 -> fin_dom_f fp1 a = fin_dom_f fp2 a
}.

#[export] Instance fin_dom_fn_equivalence : Equivalence fin_dom_fn_equiv.
Proof.
  split.
  - by intro fp; split; intros.
  - intros fp1 fp2 []; split; symmetry; [done |].
    by apply fp_eqv_fn0, fp_eqv_dom0.
  - intros fp1 fp2 fp3 [] []; split; [by etransitivity |].
    intros a Ha; etransitivity.
    + by apply fp_eqv_fn0.
    + by apply fp_eqv_fn1, fp_eqv_dom0.
Qed.

#[export] Instance fin_dom_fn_eqv : Equiv (fin_dom_fn A B Supp) := fin_dom_fn_equiv.

#[export] Instance fin_dom_fn_equiv_dec `{EqDecision B} : RelDecision fin_dom_fn_equiv.
Proof.
  intros fp1 fp2.
  destruct (decide (fin_dom fp1 ≡ fin_dom fp2)); [| by right; inversion 1].
  destruct (decide (set_Forall (fun i => fin_dom_f fp1 i = fin_dom_f fp2 i) (fin_dom fp1)));
    [by left |].
  by right; contradict n; destruct n.
Qed.

#[export] Instance dom_proper : Proper ((≡) ==> (≡)) fin_dom.
Proof. by intros ? ? []. Qed.

#[export] Instance fin_dom_fn_subseteq_proper :
  Proper ((≡) ==> (≡) ==> iff) fin_dom_fn_subseteq.
Proof.
  intros fn1 fn1' Heqv1 fn2 fn2' Heqv2.
  split; intros []; split.
  - by rewrite <- Heqv1, <- Heqv2.
  - intros a Ha.
    etransitivity; [by symmetry; apply fp_eqv_fn, Heqv1 |].
    etransitivity; [| apply fp_eqv_fn; [done |]].
    + by eapply fp_sub_fn0, fp_eqv_dom.
    + by eapply fp_eqv_dom, fp_sub_dom0 in Ha.
  - by rewrite Heqv1, Heqv2.
  - intros a Ha.
    etransitivity; [by apply fp_eqv_fn |].
    transitivity (fin_dom_f fn2' a ).
    + by apply fp_sub_fn0; rewrite fp_eqv_dom.
    + symmetry; eapply fp_eqv_fn; [done |].
      rewrite fp_eqv_dom by done.
      apply fp_sub_dom0.
      by rewrite <- fp_eqv_dom.
Qed.

Lemma fin_dom_fn_equiv_subseteq (fn1 fn2 : fin_dom_fn A B Supp) :
  fn1 ≡ fn2 <-> fn1 ⊆ fn2 /\ fn2 ⊆ fn1.
Proof.
  split; [by intros -> |].
  by intros [[] []]; split; [set_solver |].
Qed.

#[export] Instance fin_dom_fn_subseteq_antisymm :
  AntiSymm fin_dom_fn_equiv fin_dom_fn_subseteq.
Proof.
  by intros fn1 fn2 H12 H21; apply fin_dom_fn_equiv_subseteq; split.
Qed.

#[export] Instance fin_dom_fn_subseteq_preorder :
  PreOrder fin_dom_fn_subseteq.
Proof.
  constructor.
  - by intro fp; split; intros.
  - intros fp1 fp2 fp3 [] []; split; [by etransitivity |].
    intros a Ha; etransitivity.
    + by apply fp_sub_fn0.
    + by apply fp_sub_fn1, fp_sub_dom0.
Qed.

Definition empty_dom_fn `{Inhabited B} : fin_dom_fn A B Supp :=
{|
  fin_dom_f := const inhabitant;
  fin_dom := ∅;
|}.

Lemma empty_dom_fn_dom `{Inhabited B} (fp : fin_dom_fn A B Supp) :
  fp ≡ empty_dom_fn <-> fin_dom fp ≡ ∅.
Proof.
  split; [by intros -> |].
  intros Hdom; split; [done |].
  by intros; exfalso; set_solver.
Qed.

End sec_fin_dom_fn_prop.

(** ** Finitely supported functions *)

(**
  A function with a finite domain is finitely supported if its domain is also
  its support, i.e., containing exactly the elements for which the image of the
  function is different from the codomain's [inhabitant].
*)
Class FinSuppFn `{FinSet A Supp} `{Inhabited B} (fn : fin_dom_fn A B Supp) :=
  Hdom : forall i : A, fin_dom_f fn i <> inhabitant <-> i ∈ fin_dom fn.

Section sec_fin_supp_fn.

Context
  `{FinSet A Supp}
  `{EqDecision B}
  `{Inhabited B}
  .

(**
  Given a finite domain function, [mkFinSuppFn] extracts the maximal finite
  domain function (w.r.t. [fin_dom_fn_subseteq]) which satisfies [FinSuppFn].
*)
Definition mkFinSuppFn (f : A -> B) (dom : Supp) : fin_dom_fn A B Supp :=
{|
  fin_dom_f :=
    fun (a : A) => if decide (a ∈ dom) then f a else inhabitant ;
  fin_dom := filter (fun a => f a <> inhabitant) dom ;
|}.

#[export] Instance mkFinSuppFn_proper : Proper ((=) ==> (≡) ==> (≡)) mkFinSuppFn.
Proof.
  intros ? f -> _dom dom Hdom; split; cbn; intro a; rewrite !elem_of_filter.
  - by rewrite <- Hdom.
  - by intros []; rewrite !decide_True by set_solver.
Qed.

Lemma mkFinSuppFn_subseteq (f : A -> B) (dom : Supp) :
  mkFinSuppFn f dom ⊆ mk_fin_dom_fn f dom.
Proof.
  split; cbn; intros a Ha; apply elem_of_filter in Ha as [Ha Hdoma]; [done |].
  by rewrite decide_True.
Qed.

#[export] Instance mkFinSuppFn_is_fin_supp (f : A -> B) (dom : Supp) :
  FinSuppFn (mkFinSuppFn f dom).
Proof.
  intro a; cbn; rewrite elem_of_filter; split.
  - by case_decide; [intro | done].
  - by intros []; rewrite decide_True.
Qed.

Lemma mkFinSuppFn_subseteq_maximal (f : A -> B) (dom : Supp) :
  forall fp', FinSuppFn fp' -> fp' ⊆ mk_fin_dom_fn f dom -> fp' ⊆ mkFinSuppFn f dom.
Proof.
  intros fp' ? []; split; cbn.
  - intro a; rewrite elem_of_filter.
    intro Ha; split; [| by set_solver].
    rewrite <- fp_sub_fn0 by done.
    by apply Hdom.
  - intros a Hdoma.
    rewrite decide_True by set_solver.
    by apply fp_sub_fn0.
Qed.

#[export] Instance empty_dom_fn_is_fin_supp :
  FinSuppFn (empty_dom_fn (B := B) (Supp := Supp)).
Proof. by intro; cbn; set_solver. Qed.

End sec_fin_supp_fn.

(** ** Finitely supported functions on naturals *)

Definition fin_supp_nat_fn (A Supp : Type) `{FinSet A Supp} :=
  fin_dom_fn A nat Supp.

Section sec_fin_supp_nat_fn_prop.

Context
  `{FinSet A Supp}
  .

Definition zero_fin_supp_nat_fn : fin_supp_nat_fn A Supp := empty_dom_fn.

Definition succ_fin_supp_nat_fn
  (fp : fin_supp_nat_fn A Supp) (n : A) : fin_supp_nat_fn A Supp :=
{|
  fin_dom_f :=
    update_fn (fin_dom_f fp) n
      (if (decide (n ∈ fin_dom fp)) then (1 + fin_dom_f fp n) else 1) ;
  fin_dom := {[n]} ∪ fin_dom fp
|}.

#[export] Instance succ_fin_supp_nat_fn_is_fin_supp
  (fp : fin_supp_nat_fn A Supp) `{!FinSuppFn fp} (n : A) :
  FinSuppFn (succ_fin_supp_nat_fn fp n).
Proof.
  intro; cbn.
  pose proof (Hdom := Hdom (fn := fp)).
  destruct (decide (n = i)).
  - subst; rewrite update_fn_eq.
    case_decide; [| by set_solver].
    by split; [set_solver | lia].
  - rewrite update_fn_neq, Hdom by done.
    by set_solver.
Qed.

Definition delta_fin_supp_nat_fn (n : A) : fin_supp_nat_fn A Supp :=
  succ_fin_supp_nat_fn zero_fin_supp_nat_fn n.

#[export] Instance succ_fin_supp_nat_fn_proper :
  Proper ((≡) ==> (=) ==> (≡)) succ_fin_supp_nat_fn.
Proof.
  intros [] [] [] _n n ->; split; cbn in *; [by set_solver |].
  intro i; rewrite elem_of_union, elem_of_singleton; intro Ha.
  destruct (decide (n = i)).
  - subst; rewrite !update_fn_eq.
    case_decide.
    + by rewrite decide_True, fp_eqv_fn0 by set_solver.
    + by rewrite decide_False by set_solver.
  - rewrite !update_fn_neq by done.
    by apply fp_eqv_fn0; set_solver.
Qed.

Definition sum_fin_supp_nat_fn (fp : fin_supp_nat_fn A Supp) : nat :=
  sum_list_with (fin_dom_f fp) (elements (fin_dom fp)).

#[export] Instance sum_fin_supp_nat_fn_proper :
  Proper ((≡) ==> (=)) sum_fin_supp_nat_fn.
Proof.
  intros [] [] []; unfold sum_fin_supp_nat_fn; cbn in *.
  rewrite <- fp_eqv_dom0.
  apply sum_list_with_fn_dom.
  by intros; apply fp_eqv_fn0, elem_of_elements.
Qed.

Lemma sum_fin_supp_nat_fn_zero (fp : fin_supp_nat_fn A Supp) `{!FinSuppFn fp} :
  sum_fin_supp_nat_fn fp = 0 <-> fp ≡ zero_fin_supp_nat_fn.
Proof.
  split.
  - setoid_rewrite sum_list_with_zero; intros Hall.
    pose proof (Hdom := Hdom (fn := fp)).
    split; cbn; [| by intros; apply Hall, elem_of_elements].
    by set_solver.
  - intros ->.
    unfold sum_fin_supp_nat_fn; cbn.
    by rewrite elements_empty.
Qed.

Lemma sum_fin_supp_nat_fn_succ
  (fp : fin_supp_nat_fn A Supp) (n : A) :
  sum_fin_supp_nat_fn (succ_fin_supp_nat_fn fp n) = S (sum_fin_supp_nat_fn fp).
Proof.
  unfold sum_fin_supp_nat_fn, succ_fin_supp_nat_fn; cbn.
  destruct (decide (n ∈ fin_dom fp)).
  - assert ({[n]} ∪ fin_dom fp ≡ fin_dom fp) as -> by set_solver.
    apply elem_of_elements in e; revert e.
    specialize (NoDup_elements (fin_dom fp)).
    generalize (elements (fin_dom fp)) as l; clear; induction l; [by inversion 2 |].
    rewrite list.NoDup_cons, elem_of_cons; cbn.
    intros [Ha Hnodup] [<- | Hn].
    + rewrite update_fn_eq; cbn.
      do 2 f_equal.
      apply sum_list_with_fn_dom.
      by intros; rewrite update_fn_neq by  set_solver.
    + rewrite update_fn_neq by set_solver.
      rewrite IHl by done.
      by lia.
  - rewrite elements_union_singleton by done; cbn.
    rewrite update_fn_eq; cbn.
    f_equal; apply sum_list_with_fn_dom.
    by intros; rewrite update_fn_neq; [| set_solver].
Qed.

(** The component-wise sum of two functions *)
Definition fin_supp_nat_fn_add
  (fn1 fn2 : fin_supp_nat_fn A Supp) : fin_supp_nat_fn A Supp :=
{|
  fin_dom := fin_dom fn1 ∪ fin_dom fn2 ;
  fin_dom_f := fun a =>
    if decide (a ∈ fin_dom fn1) then
      if decide (a ∈ fin_dom fn2) then
        fin_dom_f fn1 a + fin_dom_f fn2 a
      else fin_dom_f fn1 a
    else fin_dom_f fn2 a
|}.

#[export] Instance fin_supp_nat_fn_add_is_finn_supp
  (fn1 fn2 : fin_supp_nat_fn A Supp) `{!FinSuppFn fn1} `{!FinSuppFn fn2}
  : FinSuppFn (fin_supp_nat_fn_add fn1 fn2).
Proof.
  intro i; cbn.
  rewrite elem_of_union;  split.
  - case_decide; [by left |].
    by intros Hi; right; apply Hdom.
  - intros [Hi | Hi]; apply Hdom in Hi as Hnz; cbn in Hnz.
    + rewrite decide_True by done.
      by case_decide; lia.
    + case_decide; [| done].
      by rewrite decide_True; [lia |].
Qed.

#[export] Instance fin_supp_nat_fn_add_proper :
  Proper ((≡) ==> (≡) ==> (≡)) fin_supp_nat_fn_add.
Proof.
  intros [] [] [] [] [] []; split; cbn in *; [by set_solver |].
  intros a Ha; do 2 case_decide;
    [| | by set_solver..].
  - by rewrite !decide_True, fp_eqv_fn0, fp_eqv_fn1 by set_solver.
  - by rewrite decide_True, decide_False, fp_eqv_fn0 by set_solver.
Qed.

#[export] Instance fin_supp_nat_fn_add_comm : Comm (≡) fin_supp_nat_fn_add.
Proof.
  intros [] []; split; cbn; [by set_solver |].
  intros a Ha; do 2 case_decide; [| by set_solver..].
  by apply Nat.add_comm.
Qed.

#[export] Instance fin_supp_nat_fn_add_left_id :
  LeftId (≡) zero_fin_supp_nat_fn fin_supp_nat_fn_add.
Proof.
  intros []; split; cbn; [by set_solver |].
  intros a Ha.
  by rewrite decide_False by set_solver.
Qed.

#[export] Instance fin_supp_nat_fn_add_right_id :
  RightId (≡) zero_fin_supp_nat_fn fin_supp_nat_fn_add.
Proof.
  intros []; split; cbn; [by set_solver |].
  intros a Ha.
  by rewrite decide_True, decide_False by set_solver.
Qed.

#[export] Instance fin_supp_nat_fn_add_assoc : Assoc (≡) fin_supp_nat_fn_add.
Proof.
  split; cbn; [by set_solver |].
  intros a Ha.
  destruct (decide (a ∈ fin_dom x)), (decide (a ∈ fin_dom y)), (decide (a ∈ fin_dom z)).
  - by rewrite !decide_True by set_solver; lia.
  - by rewrite !decide_True by set_solver; lia.
  - by rewrite !decide_True by set_solver; lia.
  - by rewrite decide_False, decide_True by set_solver.
  - by rewrite decide_True by set_solver.
  - by rewrite decide_True by set_solver.
  - by rewrite decide_False by set_solver.
  - by set_solver.
Qed.

Lemma fin_supp_nat_fn_add_succ_l (fn1 fn2 : fin_supp_nat_fn A Supp) :
  forall a : A,
  fin_supp_nat_fn_add (succ_fin_supp_nat_fn fn1 a) fn2
    ≡
  succ_fin_supp_nat_fn (fin_supp_nat_fn_add fn1 fn2) a.
Proof.
  intro a; split; cbn; [by set_solver |].
  intros b Hb; cbn.
  destruct (decide (b = a)); [subst; destruct (decide (a ∈ fin_dom fn1)), (decide (a ∈ fin_dom fn2)) |].
  - rewrite !decide_True by set_solver.
    by rewrite !update_fn_eq; lia.
  - rewrite !decide_True by set_solver.
    by rewrite !update_fn_eq.
  - rewrite !decide_True by set_solver.
    by rewrite !update_fn_eq.
  - rewrite decide_True, !decide_False by set_solver.
    by rewrite !update_fn_eq.
  - destruct (decide (b ∈ fin_dom fn1));
      [rewrite decide_True by set_solver; destruct (decide (b ∈ fin_dom fn2));
        (destruct (decide (a ∈ fin_dom fn1)); [| destruct (decide (a ∈ fin_dom fn2))]) |].
    + rewrite decide_True by set_solver.
      rewrite !update_fn_neq by done.
      by rewrite !decide_True by set_solver.
    + rewrite decide_True by set_solver.
      rewrite !update_fn_neq by done.
      by rewrite !decide_True by set_solver.
    + rewrite decide_False by set_solver.
      rewrite !update_fn_neq by done.
      by rewrite !decide_True by set_solver.
    + rewrite decide_True by set_solver.
      rewrite !update_fn_neq by done.
      by rewrite decide_True, decide_False by set_solver.
    + rewrite decide_True by set_solver.
      rewrite !update_fn_neq by done.
      by rewrite decide_True, decide_False by set_solver.
    + rewrite decide_False by set_solver.
      rewrite !update_fn_neq by done.
      by rewrite decide_True, decide_False by set_solver.
    + rewrite decide_False by set_solver.
      destruct (decide (a ∈ fin_dom fn1)); [| destruct (decide (a ∈ fin_dom fn2))].
      * rewrite decide_True by set_solver.
        rewrite update_fn_neq by done.
        by rewrite decide_False by set_solver.
      * rewrite decide_True by set_solver.
        rewrite update_fn_neq by done.
        by rewrite decide_False by set_solver.
      * rewrite decide_False by set_solver.
        rewrite update_fn_neq by done.
        by rewrite decide_False by set_solver.
Qed.

Lemma fin_supp_nat_fn_add_succ_r (fn1 fn2 : fin_supp_nat_fn A Supp) :
  forall a : A,
  fin_supp_nat_fn_add fn2 (succ_fin_supp_nat_fn fn1 a)
    ≡
  succ_fin_supp_nat_fn (fin_supp_nat_fn_add fn2 fn1) a.
Proof.
  etransitivity; [by apply comm; typeclasses eauto |].
  rewrite fin_supp_nat_fn_add_succ_l.
  apply succ_fin_supp_nat_fn_proper; [| done].
  by apply comm; typeclasses eauto.
Qed.

(**
  To be able to prove things by induction on finitely supported functions on
  naturals we define the following inductive property and we then show it
  holds for all such functions.
*)
Inductive FinSuppNatFn : fin_supp_nat_fn A Supp -> Prop :=
| P_zero : forall fp : fin_supp_nat_fn A Supp,
    FinSuppFn fp -> fp ≡ zero_fin_supp_nat_fn -> FinSuppNatFn fp
| P_succ : forall (i : A) (fp0 fp1 : fin_supp_nat_fn A Supp),
   FinSuppNatFn fp0 -> FinSuppFn fp1 ->
   fp1 ≡ succ_fin_supp_nat_fn fp0 i -> FinSuppNatFn fp1.

Lemma FinSuppNatFn_is_fin_supp (fp : fin_supp_nat_fn A Supp) :
  FinSuppNatFn fp -> FinSuppFn fp.
Proof. by inversion 1. Qed.

Lemma FinSuppNatFn_complete
  (fp : fin_supp_nat_fn A Supp) `{Hfp : !FinSuppFn fp} : FinSuppNatFn fp.
Proof.
  remember (sum_fin_supp_nat_fn fp) as n.
  revert fp Hfp Heqn.
  induction n; intros;
    [by constructor; [| apply sum_fin_supp_nat_fn_zero] |].
  assert (exists (i : A), i ∈ fin_dom fp /\ fin_dom_f fp i <> 0) as (x & Hdomx & Hx).
  {
    destruct (decide (exists (i : A), i ∈ fin_dom fp /\ fin_dom_f fp i <> 0)); [done |].
    apply not_set_Exists_Forall in n0; [| by typeclasses eauto].
    replace (sum_fin_supp_nat_fn fp) with 0 in Heqn; [done |].
    symmetry.
    apply sum_list_with_zero.
    intros a Ha.
    apply elem_of_elements in Ha.
    by specialize (n0 a Ha); cbn in n0; lia.
  }
  destruct (fin_dom_f fp x) as [| px] eqn: Heqx; [done |]; clear Hx.
  pose (fp' := mkFinSuppFn (update_fn (fin_dom_f fp) x px) (fin_dom fp)).
  assert (Heq : fp ≡ succ_fin_supp_nat_fn fp' x).
  {
    subst fp'; split; cbn.
    - intro a; rewrite elem_of_union, elem_of_filter, elem_of_singleton.
      specialize (Hdom a) as Hdoma.
      destruct (decide (a = x)); [by subst; set_solver |].
      rewrite update_fn_neq, Hdoma by done.
      by set_solver.
    - intros a Ha.
      case_decide as Hin; destruct (decide (x = a)); subst.
      + by rewrite !update_fn_eq, decide_True by set_solver.
      + rewrite !update_fn_neq by done.
        by rewrite decide_True by set_solver.
      + rewrite update_fn_eq, Heqx.
        destruct (decide (px = 0)); [by lia |].
        contradict Hin; rewrite elem_of_filter, update_fn_eq.
        by split; [lia | set_solver].
      + rewrite !update_fn_neq by done.
        by rewrite decide_True by set_solver.
  }
  econstructor 2 with (fp0 := fp') (i := x); [| done..].
  apply IHn; cycle 1.
  - rewrite Heq, sum_fin_supp_nat_fn_succ in Heqn by typeclasses eauto.
    by congruence.
  - by typeclasses eauto.
Qed.

Lemma fin_supp_nat_fn_ind
  (P : fin_supp_nat_fn A Supp -> Prop)
  (Pproper : Proper ((≡) ==> (impl)) P)
  (Hzero : P zero_fin_supp_nat_fn)
  (Hsucc : forall (i : A) (fp : fin_supp_nat_fn A Supp) `{Hfp : !FinSuppFn fp},
    P fp -> P (succ_fin_supp_nat_fn fp i)) :
  forall (fp : fin_supp_nat_fn A Supp) `{Hfp : !FinSuppFn fp}, P fp.
Proof.
  intros.
  pose proof (Hcomplete := FinSuppNatFn_complete fp).
  clear Hfp.
  induction Hcomplete as [fp ? Heqv | i fp0 fp1 Hfp0 HPfp0 ? Heqv];
    rewrite Heqv; [done |].
  apply Hsucc; [by apply FinSuppNatFn_is_fin_supp |].
  by apply HPfp0.
Qed.

End sec_fin_supp_nat_fn_prop.

