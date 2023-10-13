From Coq Require Import ZArith.Znumtheory.
From stdpp Require Import prelude.
From VLSM.Lib Require Import Preamble FinSuppFn.

#[export] Instance prime_dec : forall n, Decision (prime n).
Proof.
  apply prime_dec.
Qed.

Definition primes : Type := dsig prime.

#[export] Instance primes_inhabited : Inhabited primes :=
  populate (dexist 2%Z prime_2).

Section sec_prod_powers.

Context
  `{FinSet index indexSet}
  `(multipliers : index -> Z)
  .


Definition prod_powers_aux (powers : index -> nat) (l : list index) : Z :=
  foldr Z.mul 1%Z (zip_with Z.pow (map multipliers l) (map (Z.of_nat ∘ powers) l)).

#[export] Instance prod_powers_aux_proper :
  Proper ((=) ==> (≡ₚ) ==> (=)) prod_powers_aux.
Proof.
  intros _f f ->; induction 1; cbn.
  - done.
  - by setoid_rewrite IHPermutation.
  - by lia.
  - by congruence.
Qed.

Lemma prod_powers_aux_fn_dom (powers1 powers2 : index -> nat) (l : list index) :
  (forall i, i ∈ l -> powers1 i = powers2 i) ->
  prod_powers_aux powers1 l = prod_powers_aux powers2 l.
Proof.
  induction l; cbn; intros Heq; [done |].
  rewrite Heq by left.
  f_equal; apply IHl.
  by intros; apply Heq; right.
Qed.

Definition prod_fin_supp_nat_fn (fp : fin_supp_nat_fn index indexSet) : Z :=
  prod_powers_aux (fin_supp_f fp) (elements (dom fp)).

#[export] Instance prod_fin_supp_nat_fn_proper :
  Proper ((≡) ==> (=)) prod_fin_supp_nat_fn.
Proof.
  intros fp1 fp2 []; unfold prod_fin_supp_nat_fn; cbn.
  by rewrite fp_eqv_fn, fp_eqv_dom.
Qed.

Lemma prod_fin_supp_nat_fn_zero : prod_fin_supp_nat_fn zero_fin_supp_fn = 1%Z.
Proof.
  unfold prod_fin_supp_nat_fn; cbn.
  by rewrite elements_empty.
Qed.

Lemma prod_fin_supp_nat_fn_increment (fp : fin_supp_nat_fn index indexSet) (n : index) :
  prod_fin_supp_nat_fn (increment_fin_supp_nat_fn fp n)
    =
  (multipliers n * prod_fin_supp_nat_fn fp)%Z.
Proof.
  destruct fp; unfold prod_fin_supp_nat_fn, increment_fin_supp_nat_fn; cbn.
  destruct (decide (n ∈ dom)).
  - assert ({[n]} ∪ dom ≡ dom) as -> by set_solver.
    apply elem_of_elements in e; revert e.
    specialize (NoDup_elements dom).
    generalize (elements dom) as l; clear; induction l; [by inversion 2 |].
    rewrite NoDup_cons, elem_of_cons; cbn.
    intros [Ha Hnodup] [<- | Hn].
    + rewrite increment_fn_eq; cbn.
      setoid_rewrite (prod_powers_aux_fn_dom (increment_fn fin_supp_f n) fin_supp_f).
      * rewrite Z.mul_assoc; f_equal.
        by rewrite <- Z.pow_succ_r; lia.
      * by intros; rewrite increment_fn_neq; [| set_solver].
    + rewrite increment_fn_neq by set_solver.
      setoid_rewrite IHl; [| done..].
      by unfold prod_powers_aux; lia.
  - rewrite elements_union_singleton by done; cbn.
    rewrite increment_fn_eq; cbn.
    destruct (decide (fin_supp_f n = 0%nat)) as [-> | Hn]; cbn.
    + f_equal; [by lia |].
      apply prod_powers_aux_fn_dom.
      by intros; apply increment_fn_neq; set_solver.
    + by contradict n0; apply Hdom.
Qed.

Definition delta_fin_supp_nat_fn (n : index) : fin_supp_nat_fn index indexSet :=
  increment_fin_supp_nat_fn zero_fin_supp_fn n.

Lemma prod_powers_delta (n : index) :
  prod_fin_supp_nat_fn (delta_fin_supp_nat_fn n) = multipliers n.
Proof.
  intros; unfold delta_fin_supp_nat_fn.
  rewrite prod_fin_supp_nat_fn_increment, prod_fin_supp_nat_fn_zero by done.
  by lia.
Qed.

Lemma prod_powers_pos (Hmpos : forall (i : index), (multipliers i > 0)%Z) :
  forall (fp : fin_supp_nat_fn index indexSet), (prod_fin_supp_nat_fn fp > 0)%Z.
Proof.
  apply fin_supp_nat_fn_ind.
  - by intros _fp fp ->.
  - by rewrite prod_fin_supp_nat_fn_zero.
  - intros; rewrite prod_fin_supp_nat_fn_increment.
    by specialize (Hmpos i); lia.
Qed.

Lemma prod_powers_add (fp1 fp2 :  fin_supp_nat_fn index indexSet) :
  prod_fin_supp_nat_fn (fin_supp_nat_fn_add fp1 fp2)
    =
  (prod_fin_supp_nat_fn fp1 * prod_fin_supp_nat_fn fp2)%Z.
Proof.
  revert fp2.
  pose (P := fun fp1 => forall fp2,
    prod_fin_supp_nat_fn (fin_supp_nat_fn_add fp1 fp2)
      =
    (prod_fin_supp_nat_fn fp1 * prod_fin_supp_nat_fn fp2)%Z).
  cut (P fp1); [done |].
  revert fp1.
  apply fin_supp_nat_fn_ind; subst P; cbn.
  - intros fp1 fp1' Heqv Hall fp2.


End sec_prod_powers.


Fixpoint prod_primes (l : list primes) : Z :=
  match l with
  | [] => 1%Z
  | p :: ps => Z.mul (` p) (prod_primes ps)
  end.

Lemma prod_primes_app (l1 l2 : list primes) :
  prod_primes (l1 ++ l2) = (prod_primes l1 * prod_primes l2)%Z.
Proof.
  by induction l1; cbn; [lia | rewrite IHl1; lia].
Qed.

Lemma primes_decomposition : forall (n : Z), (n > 1)%Z ->
  exists (ps : list primes),  n = prod_primes ps.
Proof.
  pose (P := fun n : Z => (n > 1)%Z → ∃ ps : list primes, n = prod_primes ps).
  cut (forall n : Z, (0 <= n)%Z -> P n).
  {
    by intros HP n Hn; apply HP; lia.
  }
  apply Zlt_0_ind; subst P; cbn; intros n Hind _ Hn1.
  destruct (decide (prime n)) as [| Hnp].
  - by exists [dexist n p]; cbn; lia.
  - apply not_prime_divide in Hnp as (p & [Hp1 Hpn] & q & ->); [| lia].
    assert (Hq1 : (1 < q)%Z) by nia.
    assert (Hqn : (q < q * p)%Z) by nia.
    destruct (Hind p) as [ps ->]; [by split; lia | by lia |..].
    destruct (Hind q) as [qs ->]; [by split; lia | by lia |..].
    by eexists; symmetry; apply prod_primes_app.
Qed.
