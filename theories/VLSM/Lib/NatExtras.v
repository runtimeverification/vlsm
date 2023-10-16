From Coq Require Import ZArith.Znumtheory.
From stdpp Require Import prelude.
From VLSM.Lib Require Import EquationsExtras.
From VLSM.Lib Require Import Preamble FinSuppFn StdppExtras.

(** * Natural number utility definitions and lemmas *)

Fixpoint up_to_n_listing (n : nat) : list nat :=
  match n with
  | 0 => []
  | S n' => n' :: up_to_n_listing n'
  end.

Lemma up_to_n_listing_length :
  forall (n : nat),
    length (up_to_n_listing n) = n.
Proof.
  by induction n; simpl; congruence.
Qed.

Lemma up_to_n_full :
  forall (n i : nat),
    i < n <-> i ∈ up_to_n_listing n.
Proof.
  induction n; split; inversion 1; subst; cbn; [left | | lia |].
  - by right; apply IHn.
  - by transitivity n; [apply IHn | lia].
Qed.

(**
  Given a decidable property on naturals and a bound, finds the
  largest natural (not larger the than bound) for which the property holds.
*)
Equations find_largest_nat_with_property_bounded
  (P : nat -> Prop) `{forall n, Decision (P n)}
  (bound : nat)
  : option nat :=
| P, 0 => None
| P, S n => if decide (P n) then Some n else find_largest_nat_with_property_bounded P n.

Lemma find_largest_nat_with_property_bounded_Some
  (P : nat -> Prop) `{forall n, Decision (P n)}
  (bound : nat)
  : forall n,
      find_largest_nat_with_property_bounded P bound = Some n
        <->
      maximal_among lt (fun n => n < bound /\ P n) n.
Proof.
  induction bound; simp find_largest_nat_with_property_bounded.
  - by split; [| intros []; lia].
  - case_decide as HP; split.
    + by intros [= ->]; repeat split; cbn; [lia | | lia].
    + intros [[Hn HPn] Hmax]; f_equal; cbn in Hmax.
      destruct (decide (n < bound)); [| lia].
      cut (bound < n); [lia |].
      by apply Hmax; [split; [lia |] |].
    + rewrite IHbound.
      intros [[] Hmax]; split; [by split; [lia |] |].
      intros m [] ?.
      apply Hmax; [split; [| done] | done].
      by destruct (decide (m = bound)); [subst | lia].
    + intros [[] Hmax]; apply IHbound; repeat split; [| done |].
      * by destruct (decide (n = bound)); [subst | lia].
      * by intros m [] ?; apply Hmax; [split; [lia |] |].
Qed.

Lemma find_largest_nat_with_property_bounded_None
  (P : nat -> Prop) `{forall n, Decision (P n)}
  (bound : nat)
  : find_largest_nat_with_property_bounded P bound = None
      <->
    forall n, n < bound -> ~ P n.
Proof.
  induction bound; simp find_largest_nat_with_property_bounded; [by split; [lia |] |].
  case_decide as HP; split; [done | | |].
  - by intro Hmax; contradict HP; apply Hmax; lia.
  - intros.
    destruct (decide (n < bound)); [by eapply IHbound |].
    by replace n with bound; [| lia].
  - intros Hmax; apply IHbound.
    by intros; apply Hmax; lia.
Qed.

(**
  Given a predicate on indices and naturals, a bound for each index, and a
  list of indices, finds first index in the list and largest natural (less than
  bound) corresponding to it for which the predicate holds.
*)
Equations find_first_indexed_largest_nat_with_propery_bounded {index}
  (P : index -> nat -> Prop) `{!RelDecision P}
  (bound : index -> nat)
  (indices : list index)
  : option (index * nat) :=
| _, _, [] => None
| P, bound, i :: indices' with inspect (find_largest_nat_with_property_bounded (P i) (bound i)) =>
  | None eq: Hdec => find_first_indexed_largest_nat_with_propery_bounded P bound indices';
  | (Some n) eq: Hdec => Some (i, n).

Lemma find_first_indexed_largest_nat_with_propery_bounded_Some {index}
  (P : index -> nat -> Prop) `{!RelDecision P}
  (bound : index -> nat)
  (indices : list index) (Hindices : NoDup indices)
  : forall (i : index) (n : nat),
      find_first_indexed_largest_nat_with_propery_bounded P bound indices = Some (i, n)
        <->
      i ∈ indices /\
      find_largest_nat_with_property_bounded (P i) (bound i) = Some n /\
      forall (prefix suffix : list index),
        indices = prefix ++ [i] ++ suffix ->
        forall (j : index), j ∈ prefix ->
        find_largest_nat_with_property_bounded (P j) (bound j) = None.
Proof.
  induction indices; simp find_first_indexed_largest_nat_with_propery_bounded.
  - by split; [inversion 1 | intros [Hcontra]; inversion Hcontra].
  - apply NoDup_cons in Hindices as [Ha Hindices].
    cbn; split;
      destruct (find_largest_nat_with_property_bounded  (P a) (bound a)) as [_n |] eqn: Hpos.
    + inversion 1; subst a _n; split_and!; [by left | done |].
      intros [| _i prefix] ? Heq; [by inversion 1 |].
      contradict Ha; simplify_list_eq.
      by apply elem_of_app; right; left.
    + rewrite IHindices by done.
      intros (Hi & Hposition & Hfirst).
      split_and!; [by right | done |].
      intros [| _a prefix] ? Heq; [by inversion 1 |].
      simplify_list_eq.
      by inversion 1; [| eapply Hfirst].
    + intros (Hi & Hposi & Hfirst).
      apply elem_of_cons in Hi as [<- | Hi]; [by congruence |].
      apply elem_of_list_split in Hi as (prefix' & suffix & ->).
      by erewrite Hfirst in Hpos; [| rewrite app_comm_cons | left].
    + intros (Hi & Hposi & Hfirst).
      apply elem_of_cons in Hi as [<- | Hi]; [by congruence |].
      apply IHindices; [done |].
      split_and!; [done.. |].
      intros prefix suffix -> j Hj.
      eapply Hfirst; [| by right].
      by rewrite app_comm_cons.
Qed.

Lemma find_first_indexed_largest_nat_with_propery_bounded_None {index}
  (P : index -> nat -> Prop) `{!RelDecision P}
  (bound : index -> nat)
  (indices : list index) (Hindices : NoDup indices)
  : find_first_indexed_largest_nat_with_propery_bounded P bound indices = None
      <->
    forall (i : index), i ∈ indices ->
      find_largest_nat_with_property_bounded (P i) (bound i) = None.
Proof.
  induction indices; simp find_first_indexed_largest_nat_with_propery_bounded;
    [by split; [inversion 2 |] |].
  apply NoDup_cons in Hindices as [Ha Hindices].
  cbn; split; destruct find_largest_nat_with_property_bounded eqn: Hp; [done | | |].
  - by intros Hnone i Hi; apply elem_of_cons in Hi as  [-> | Hi]; [| eapply IHindices].
  - intro Hmin.
    replace (find_largest_nat_with_property_bounded (P a) (bound a))
      with (@None nat) in Hp; [done |].
    by symmetry; apply Hmin; left.
  - intros Hmin.
    apply IHindices; [done |].
    by intros; apply Hmin; right.
Qed.

(** ** Products of (natural) powers of integers *)

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

Lemma prod_powers_delta (n : index) :
  prod_fin_supp_nat_fn (delta_fin_supp_nat_fn n) = multipliers n.
Proof.
  intros; unfold delta_fin_supp_nat_fn.
  rewrite prod_fin_supp_nat_fn_increment, prod_fin_supp_nat_fn_zero by done.
  by lia.
Qed.

Lemma prod_powers_gt (n : Z) (Hn : (n >= 0)%Z)
  (Hmpos : forall (i : index), (multipliers i > n)%Z) :
  forall (fp : fin_supp_nat_fn index indexSet),
    dom fp ≢ ∅ -> (prod_fin_supp_nat_fn fp > n)%Z.
Proof.
  intro fp.
  pose (P := fun fp => dom fp ≢ ∅ -> (prod_fin_supp_nat_fn fp > n)%Z).
  cut (P fp); [done |].
  revert fp; apply fin_supp_nat_fn_ind; subst P; cbn.
  - by intros _fp fp ->.
  - by rewrite prod_fin_supp_nat_fn_zero.
  - intros * IH _; rewrite prod_fin_supp_nat_fn_increment.
    specialize (Hmpos i).
    destruct (decide (dom fp ≡ ∅)) as [Hdom | Hndom].
    + apply zero_fin_supp_fn_dom in Hdom as ->.
      by rewrite prod_fin_supp_nat_fn_zero; lia.
    + by specialize (IH Hndom); nia.
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
  - by intros fp1 fp1' Heqv Hall fp2; rewrite <- Heqv; apply Hall.
  - intros; rewrite left_id, prod_fin_supp_nat_fn_zero by typeclasses eauto.
    by lia.
  - intros i fp1 Hall fp2.
    rewrite fin_sup_nat_fn_add_increment_l, !prod_fin_supp_nat_fn_increment, Hall.
    by lia.
Qed.

End sec_prod_powers.

(** ** A Prime Factorization Result *)

#[export] Instance prime_dec : forall n, Decision (prime n).
Proof.
  apply prime_dec.
Qed.

Definition primes : Type := dsig prime.

#[export] Instance primes_inhabited : Inhabited primes :=
  populate (dexist 2%Z prime_2).

Definition primes_powers : Type := fin_supp_nat_fn primes (listset primes).
Definition prod_primes_powers : primes_powers -> Z :=
  prod_fin_supp_nat_fn (fun p : primes => ` p).


Lemma primes_factorization : forall (n : Z), (n > 1)%Z ->
  exists (ps : primes_powers), dom ps ≢ ∅ /\ n = prod_primes_powers ps.
Proof.
  pose (P := fun n : Z => (n > 1)%Z →
    exists (ps : primes_powers), dom ps ≢ ∅ /\ n = prod_primes_powers ps).
  cut (forall n : Z, (0 <= n)%Z -> P n).
  {
    by intros HP n Hn; apply HP; lia.
  }
  apply Zlt_0_ind; subst P; cbn; intros n Hind _ Hn1.
  destruct (decide (prime n)) as [| Hnp].
  - exists (delta_fin_supp_nat_fn (dexist n p)); split; [by cbn; set_solver |].
    by unfold prod_primes_powers; rewrite prod_powers_delta.
  - apply not_prime_divide in Hnp as (p & [Hp1 Hpn] & q & ->); [| lia].
    assert (Hq1 : (1 < q)%Z) by nia.
    assert (Hqn : (q < q * p)%Z) by nia.
    destruct (Hind p) as (ps & Hdomps & ->); [by split; lia | by lia |..].
    destruct (Hind q) as (qs & Hdomqs & ->); [by split; lia | by lia |..].
    eexists; split; [| by symmetry; apply prod_powers_add].
    by cbn; set_solver.
Qed.
