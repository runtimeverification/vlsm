From Coq Require Import FunctionalExtensionality.
From stdpp Require Import prelude.
From VLSM.Lib Require Import Preamble StdppExtras.

Record fin_supp_fn (A B Supp : Type) `{FinSet A Supp} `{Inhabited B} := mk_fin_supp_fn
{
  fin_supp_f : A -> B ;
  dom : Supp ;
  Hdom : forall i : A, fin_supp_f i <> inhabitant <-> i ∈ dom
}.

Arguments dom {A B Supp}%type_scope {H H0 H1 H2 H3 H4 H5 EqDecision0 H6 H7} f : assert.
Arguments fin_supp_f {A B Supp}%type_scope {H H0 H1 H2 H3 H4 H5 EqDecision0 H6 H7} f _ : assert.

Section sec_fin_supp_fn_prop.

Context
  `{FinSet A Supp}
  `{Inhabited B}
  `{EqDecision B}
  .

Record fin_supp_fn_equiv (fp1 fp2 : fin_supp_fn A B Supp) : Prop :=
{
  fp_eqv_dom : dom fp1 ≡ dom fp2;
  fp_eqv_fn : fin_supp_f fp1 = fin_supp_f fp2
}.

#[export] Instance fin_supp_nat_fn_equivalence : Equivalence fin_supp_fn_equiv.
Proof.
  split.
  - by intro fp; split; intros.
  - by intros fp1 fp2 []; split; symmetry.
  - by intros fp1 fp2 fp3 [] []; split; etransitivity.
Qed.

#[export] Instance fin_supp_nat_fn_equiv_dec : RelDecision fin_supp_fn_equiv.
Proof.
  intros [] [].
  destruct (decide (dom0 ≡ dom1)); [| by right; inversion 1].
  destruct (decide (set_Forall (fun i => fin_supp_f0 i = fin_supp_f1 i) dom0)).
  - left; split; cbn; [done |].
    extensionality i.
    destruct (decide (i ∈ dom0)); [by apply s |].
    destruct (decide (fin_supp_f0 i = inhabitant)); [| by contradict n; apply Hdom0].
    destruct (decide (fin_supp_f1 i = inhabitant)); [| by contradict n; rewrite e; apply Hdom1].
    by congruence.
  - right. contradict n; intros i _.
    destruct n as [_ Hrew]; cbn in Hrew.
    by congruence.
Qed.

#[export] Instance fin_supp_fn_eqv : Equiv (fin_supp_fn A B Supp) := fin_supp_fn_equiv.

#[export] Instance dom_proper : Proper ((≡) ==> (≡)) dom.
Proof. by intros ? ? []. Qed.

#[export] Instance fin_supp_f_proper : Proper ((≡) ==> (=)) fin_supp_f.
Proof. by intros ? ? []. Qed.

Program Definition update_fin_supp_fn (fp : fin_supp_fn A B Supp) (a : A) (b : B)
  : fin_supp_fn A B Supp :=
{|
  fin_supp_f := update_fn (fin_supp_f fp) a b;
  dom := if decide (b = inhabitant) then dom fp ∖ {[a]} else {[a]} ∪ dom fp ;
|}.
Next Obligation.
Proof.
  intros [] *; cbn.
  by unfold update_fn; do 2 case_decide; subst; set_solver.
Qed.

Lemma update_fin_supp_fn_proper : Proper ((≡) ==> (=) ==> (=) ==> (≡)) update_fin_supp_fn.
Proof.
  intros fp1 fp2 [] _n n -> _nr nr ->; split; cbn; [by case_decide; set_solver |].
  extensionality i.
  destruct (decide (n = i)).
  - by subst; rewrite !update_fn_eq.
  - by rewrite !update_fn_neq, fp_eqv_fn0.
Qed.

Program Definition zero_fin_supp_fn : fin_supp_fn A B Supp :=
{|
  fin_supp_f := const inhabitant;
  dom := ∅;
|}.
Next Obligation.
Proof. by cbn; set_solver. Qed.

Lemma empty_dom_zero_f : forall fp : fin_supp_fn A B Supp,
  dom fp ≡ ∅ -> fin_supp_f fp = const inhabitant.
Proof.
  intros [] Hdom; extensionality i; cbn in *.
  destruct (decide (fin_supp_f0 i = inhabitant)); [done |].
  rewrite Hdom0, Hdom in n.
  by contradict n; apply not_elem_of_empty.
Qed.

Lemma zero_fin_supp_fn_dom : forall fp : fin_supp_fn A B Supp,
  fp ≡ zero_fin_supp_fn <-> dom fp ≡ ∅.
Proof.
  intros []; split; [by intros -> |].
  intros Hdom; split; [done |].
  by apply empty_dom_zero_f.
Qed.

Lemma zero_fin_supp_nat_fn_f : forall fp,
  fp ≡ zero_fin_supp_fn <-> fin_supp_f fp = const inhabitant.
Proof.
  intros []; split; [by intros []; apply empty_dom_zero_f |].
  intros Hpow; split; [| done]; cbn in *.
  by set_solver.
Qed.

End sec_fin_supp_fn_prop.

Definition fin_supp_nat_fn (A Supp : Type) `{FinSet A Supp} :=
  fin_supp_fn A nat Supp.

Section sec_fin_supp_nat_fn_prop.

Context
  `{FinSet A Supp}
  .

Definition increment_fn (f : A -> nat) (n : A) :=
  update_fn f n (S (f n)).

Lemma increment_fn_eq (f : A -> nat) (n : A) :
  increment_fn f n n = S (f n).
Proof.
  by apply update_fn_eq.
Qed.

Lemma increment_fn_neq (f : A -> nat) (n : A) (x : A) :
  n <> x -> increment_fn f n x = f x.
Proof.
  by apply update_fn_neq.
Qed.

Program Definition increment_fin_supp_nat_fn
  (fp : fin_supp_nat_fn A Supp) (n : A) : fin_supp_nat_fn A Supp :=
{|
  fin_supp_f := increment_fn (fin_supp_f fp) n;
  dom := {[n]} ∪ dom fp
|}.
Next Obligation.
Proof.
  intros [] *; cbn.
  unfold increment_fn.
  destruct (decide (n = i)); subst.
  - by rewrite update_fn_eq; set_solver.
  - by rewrite update_fn_neq; set_solver.
Qed.

#[export] Instance increment_fin_supp_nat_fn_proper :
  Proper ((≡) ==> (=) ==> (≡)) increment_fin_supp_nat_fn.
Proof.
  intros [] [] [] _n n ->; split; cbn in *; [by set_solver |].
  extensionality i.
  destruct (decide (n = i)).
  - by subst; rewrite increment_fn_eq.
  - by rewrite !increment_fn_neq, fp_eqv_fn0.
Qed.

Definition sum_fin_supp_nat_fn (fp : fin_supp_nat_fn A Supp) : nat :=
  sum_list_with (fin_supp_f fp) (elements (dom fp)).

#[export] Instance sum_fin_supp_nat_fn_proper :
  Proper ((≡) ==> (=)) sum_fin_supp_nat_fn.
Proof.
  intros [] [] []; unfold sum_fin_supp_nat_fn; cbn in *; subst.
  by rewrite fp_eqv_dom0.
Qed.

Lemma sum_fin_supp_nat_fn_zero :
  forall fp, sum_fin_supp_nat_fn fp = 0 <-> fp ≡ zero_fin_supp_fn.
Proof.
  split.
  - destruct fp; unfold sum_fin_supp_nat_fn; cbn.
    intros Hsum.
    apply zero_fin_supp_fn_dom; cbn.
    cut (forall i, i ∈ dom0 -> fin_supp_f0 i = 0). { by set_solver. }
    intros i Hi; apply elem_of_elements in Hi.
    by eapply sum_list_with_in in Hi; rewrite Hsum in Hi; lia.
  - intros ->.
    unfold sum_fin_supp_nat_fn; cbn.
    by rewrite elements_empty.
Qed.

Lemma sum_fin_supp_nat_fn_increment (fp : fin_supp_nat_fn A Supp) (n : A) :
  sum_fin_supp_nat_fn (increment_fin_supp_nat_fn fp n) = S (sum_fin_supp_nat_fn fp).
Proof.
  destruct fp; unfold sum_fin_supp_nat_fn, increment_fin_supp_nat_fn; cbn.
  destruct (decide (n ∈ dom0)).
  - assert ({[n]} ∪ dom0 ≡ dom0) as -> by set_solver.
    apply elem_of_elements in e; revert e.
    specialize (NoDup_elements dom0).
    generalize (elements dom0) as l; clear; induction l; [by inversion 2 |].
    rewrite NoDup_cons, elem_of_cons; cbn.
    intros [Ha Hnodup] [<- | Hn].
    + rewrite increment_fn_eq; cbn.
      do 2 f_equal.
      apply sum_list_with_fn_dom.
      by intros; rewrite increment_fn_neq; [| set_solver].
    + rewrite increment_fn_neq by set_solver.
      rewrite IHl by done.
      by lia.
  - rewrite elements_union_singleton by done; cbn.
    rewrite increment_fn_eq; cbn.
    destruct (decide (fin_supp_f0 n = 0)) as [-> | Hn]; cbn.
    + f_equal; apply sum_list_with_fn_dom.
      by intros; apply increment_fn_neq; set_solver.
    + by contradict n0; apply Hdom0.
Qed.

Inductive FinSuppNatFn : fin_supp_nat_fn A Supp -> Prop :=
| P_zero : forall fp : fin_supp_nat_fn A Supp, fp ≡ zero_fin_supp_fn -> FinSuppNatFn fp
| P_succ : forall (i : A) (fp0 fp1 : fin_supp_nat_fn A Supp),
   FinSuppNatFn fp0 -> fp1 ≡ increment_fin_supp_nat_fn fp0 i -> FinSuppNatFn fp1.

Lemma FinSuppNatFn_proper_impl : Proper ((≡) ==> (impl)) FinSuppNatFn.
Proof.
  intros fp1 fp2 Heqv Hfp1.
  revert fp2 Heqv; induction Hfp1;
    [by intros; constructor 1; rewrite <- Heqv |].
  intros fp2 Heqfp2.
  rewrite Heqfp2 in *.
  by econstructor 2.
Qed.

#[export] Instance FinSuppNatFn_proper : Proper ((≡) ==> (iff)) FinSuppNatFn.
Proof.
  intros fp1 fp2 Heqv.
  by split; apply FinSuppNatFn_proper_impl.
Qed.

Lemma FinSuppNatFn_complete (fp : fin_supp_nat_fn A Supp) : FinSuppNatFn fp.
Proof.
  remember (sum_fin_supp_nat_fn fp) as n.
  revert fp Heqn.
  induction n; intros.
  - symmetry in Heqn.
    apply sum_fin_supp_nat_fn_zero in Heqn.
    by constructor.
  - assert (exists (i : A), fin_supp_f fp i <> 0) as [x Hx].
    {
      destruct (decide (fp ≡ zero_fin_supp_fn));
        [by apply sum_fin_supp_nat_fn_zero in e; congruence |].
      assert (Hdomfp : dom fp ≢ ∅)
        by (contradict n0; apply zero_fin_supp_fn_dom; done).
      apply set_choose in Hdomfp as [i Hi].
      by exists i; apply Hdom.
    }
    destruct (fin_supp_f fp x) as [| px] eqn: Heqx; [done |]; clear Hx.
    pose (fp' := update_fin_supp_fn fp x px).
    assert (Heq : fp ≡ increment_fin_supp_nat_fn fp' x).
    {
      subst fp'; split; cbn.
      - assert (x ∈ dom fp) by (apply Hdom; cbn; lia).
        intros; case_decide; [| by set_solver].
        intro y; rewrite elem_of_union, elem_of_difference, elem_of_singleton.
        by destruct (decide (x = y)); set_solver.
      - extensionality y.
        destruct (decide (x = y)); subst.
        + by rewrite increment_fn_eq, update_fn_eq.
        + by rewrite increment_fn_neq, update_fn_neq.
    }
    econstructor 2; [| done].
    apply IHn.
    rewrite Heq, sum_fin_supp_nat_fn_increment in Heqn.
    by congruence.
Qed.

Lemma fin_supp_nat_fn_ind
  (P : fin_supp_nat_fn A Supp -> Prop)
  (Pproper : Proper ((≡) ==> (impl)) P)
  (Hzero : P zero_fin_supp_fn)
  (Hsucc : forall (i : A) (fp : fin_supp_nat_fn A Supp),
    P fp -> P (increment_fin_supp_nat_fn fp i)) :
  forall (fp : fin_supp_nat_fn A Supp), P fp.
Proof.
  intro f.
  pose proof (Hcomplete := FinSuppNatFn_complete f).
  induction Hcomplete as [fp -> | i fp0 fp1 Hfp0 HPfp0 ->]; [done |].
  by apply Hsucc.
Qed.

Program Definition fin_supp_nat_fn_add
  (fn1 fn2 : fin_supp_nat_fn A Supp) : fin_supp_nat_fn A Supp :=
{|
  dom := dom fn1 ∪ dom fn2 ;
  fin_supp_f := fun a => fin_supp_f fn1 a + fin_supp_f fn2 a ;
|}.
Next Obligation.
Proof. intros [] [] i; cbn.
rewrite elem_of_union, <- Hdom0, <- Hdom1; cbn.
by lia.
Qed.

End sec_fin_supp_nat_fn_prop.
