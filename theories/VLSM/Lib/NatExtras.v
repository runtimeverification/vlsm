From Coq Require Import ZArith.Znumtheory.
From stdpp Require Import prelude finite.
From VLSM.Lib Require Import EquationsExtras.
From VLSM.Lib Require Import Preamble FinSuppFn StdppExtras ListExtras.

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
  `{EqDecision index}
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

Lemma prod_powers_aux_ext_forall (powers1 powers2 : index -> nat) (l : list index) :
  (forall i, i ∈ l -> powers1 i = powers2 i) ->
  prod_powers_aux powers1 l = prod_powers_aux powers2 l.
Proof.
  intros Hall; unfold prod_powers_aux; do 2 f_equal.
  apply map_ext_Forall, Forall_forall.
  by intros; cbn; f_equal; apply Hall.
Qed.

Lemma prod_powers_aux_ge_1 (powers : index -> nat) (l : list index)
  (Hmpos : Forall (fun i => (multipliers i > 0)%Z) l) :
  (prod_powers_aux powers l >= 1)%Z.
Proof.
  revert Hmpos; induction l; [by cbn; lia |].
  rewrite Forall_cons; intros [Hma Hmpos].
  change (prod_powers_aux powers (a :: l))
    with (multipliers a ^ Z.of_nat (powers a) * prod_powers_aux powers l)%Z.
  by specialize (IHl Hmpos); lia.
Qed.

Lemma prod_powers_aux_gt (powers : index -> nat) (l : list index)
  (n : Z) (Hn : (n >= 0)%Z)
  (Hmpos : Forall (fun i => (multipliers i > n)%Z) l) :
  Exists (fun i => powers i <> 0) l -> (prod_powers_aux powers l > n)%Z.
Proof.
  revert Hmpos; induction l; [by inversion 2 |].
  change (prod_powers_aux powers (a :: l))
    with (multipliers a ^ Z.of_nat (powers a) * prod_powers_aux powers l)%Z.
  rewrite Forall_cons, Exists_cons; intros [Hma Hmpos] Hppos.
  destruct (decide (powers a = 0)); cycle 1.
  - destruct (powers a) as [| pa]; [done |].
    replace (Z.of_nat (S pa)) with (Z.succ (Z.of_nat pa)) by lia.
    rewrite Z.pow_succ_r by lia.
    cut (multipliers a ^ Z.of_nat pa * prod_powers_aux powers l >= 1)%Z; [by nia |].
    cut (prod_powers_aux powers l >= 1)%Z; [by nia |].
    apply prod_powers_aux_ge_1.
    rewrite Forall_forall in Hmpos |- *.
    by intros x Hx; specialize (Hmpos x Hx); lia.
  - cut (prod_powers_aux powers l > n)%Z; [by nia |].
    apply IHl; [done |].
    by destruct Hppos.
Qed.

Definition prod_fin_supp_nat_fn (f : index -> nat) `{!Finite (supp f)} : Z :=
  prod_powers_aux f (fin_supp f).

Lemma prod_fin_supp_nat_fn_proper
  (f : index -> nat) `{!Finite (supp f)}
  (g : index -> nat) `{!Finite (supp g)} :
  f = g -> prod_fin_supp_nat_fn f = prod_fin_supp_nat_fn g.
Proof.
  by intros Heq; apply prod_powers_aux_proper, fin_supp_proper.
Qed.

Lemma prod_fin_supp_nat_fn_zero : prod_fin_supp_nat_fn zero_fin_supp_nat_fn = 1%Z.
Proof. done. Qed.

Lemma prod_fin_supp_nat_fn_succ
  (f : index -> nat) `{!Finite (supp f)} (n : index) :
  prod_fin_supp_nat_fn (succ_fin_supp_nat_fn f n)
    =
  (multipliers n * prod_fin_supp_nat_fn f)%Z.
Proof.
  unfold prod_fin_supp_nat_fn, succ_fin_supp_nat_fn.
  unfold fin_supp at 1, enum, succ_fin_supp_nat_fn_has_fin_supp.
  rewrite list_annotate_forget.
  unfold succ_fin_supp_nat_fn_supp.
  destruct (decide (n ∈ fin_supp f)).
  - assert (Heqv : {[n]} ∪ list_to_set (C := listset index) (fin_supp f) ≡ list_to_set (fin_supp f))
      by set_solver.
    apply elements_proper in Heqv.
    rewrite elements_list_to_set in Heqv by apply fin_supp_NoDup.
    rewrite prod_powers_aux_proper at 1 by done.
    revert e; specialize (fin_supp_NoDup f).
    generalize (fin_supp f) as l; clear; induction l; [by inversion 2 |].
    rewrite list.NoDup_cons, elem_of_cons; cbn.
    intros [Ha Hnodup] [<- | Hn].
    + rewrite update_fn_eq, assoc by typeclasses eauto; cbn.
      f_equal; [by rewrite <- Z.pow_succ_r; lia |].
      apply prod_powers_aux_ext_forall.
      intros; cbn; f_equal.
      by apply update_fn_neq; set_solver.
    + rewrite update_fn_neq by set_solver.
      setoid_rewrite IHl; [| done..].
      by unfold prod_powers_aux; lia.
  - rewrite elements_union_singleton by (rewrite elem_of_list_to_set; done).
    rewrite elements_list_to_set by apply fin_supp_NoDup.
    cbn; rewrite update_fn_eq.
    assert (f n = 0) as -> by (rewrite elem_of_fin_supp in n0; cbn in n0; lia).
    cbn; f_equal; [by lia |].
    apply prod_powers_aux_ext_forall.
    by intros; apply update_fn_neq; set_solver.
Qed.

Lemma prod_powers_delta (n : index) :
  prod_fin_supp_nat_fn (delta_fin_supp_nat_fn n) = multipliers n.
Proof.
  intros; unfold delta_fin_supp_nat_fn.
  rewrite prod_fin_supp_nat_fn_succ, prod_fin_supp_nat_fn_zero
    by typeclasses eauto.
  by lia.
Qed.

Lemma prod_powers_gt (n : Z) (Hn : (n >= 0)%Z)
  (Hmpos : forall (i : index), (multipliers i > n)%Z) :
  forall (f : index -> nat) `{!Finite (supp f)},
    fin_supp f <> [] -> (prod_fin_supp_nat_fn f > n)%Z.
Proof.
  intros; apply prod_powers_aux_gt; [done |..].
  by apply Forall_forall; intros; apply Hmpos.
  apply Exists_exists.
  unfold fin_supp; setoid_rewrite elem_of_list_fmap.
  destruct (fin_supp f) eqn : Heq; [done |].
  assert (Hi : i ∈ fin_supp f) by (rewrite Heq; left).
  apply elem_of_list_fmap in Hi as [inh]; clear -inh.
  destruct_dec_sig inh i Hi Heq.
  exists i; split; [| done].
  by exists inh; split; [rewrite Heq | apply elem_of_enum].
Qed.

Lemma prod_powers_elem_of_dom
  (f : index -> nat) `{!Finite (supp f)} :
  forall i : index, i ∈ fin_supp f -> (multipliers i | prod_fin_supp_nat_fn f)%Z.
Proof.
  pose (P := fun f `{!Finite (supp f)} => forall i : index, i ∈ fin_supp f ->
    (multipliers i | prod_fin_supp_nat_fn f)%Z).
  cut (P f _); [done |].
  apply fin_supp_nat_fn_ind; clear; subst P; cbn.
  - intros f g ? ? Heq Hall i Hi.
    rewrite <- (fin_supp_proper f) in Hi by done.
    apply Hall in Hi as [x Hx].
    exists x.
    by rewrite <- (prod_fin_supp_nat_fn_proper f).
  - by inversion 1.
  - intros j f ? IHf i.
    intros Hi.
    setoid_rewrite prod_fin_supp_nat_fn_succ.
    apply elem_of_succ_fin_supp_nat_fn_fin_supp in Hi as [<- | Hi];
      [by exists (prod_fin_supp_nat_fn f); lia |].
    edestruct IHf as [x ->]; [done |].
    by exists (multipliers j * x)%Z; lia.
Qed.

Lemma prod_powers_add
  (f1 f2 :  index -> nat)
  `{Hf1 : !Finite (supp f1)} `{Hf2 : !Finite (supp f2)} :
  prod_fin_supp_nat_fn (fin_supp_nat_fn_add f1 f2)
    =
  (prod_fin_supp_nat_fn f1 * prod_fin_supp_nat_fn f2)%Z.
Proof.
  revert f2 Hf2.
  pose (P := fun f1 `{!Finite (supp f1)} => forall f2 `(!Finite (supp f2)),
    prod_fin_supp_nat_fn (fin_supp_nat_fn_add f1 f2)
      =
    (prod_fin_supp_nat_fn f1 * prod_fin_supp_nat_fn f2)%Z).
  cut (P f1 _); [done |].
  apply fin_supp_nat_fn_ind; clear; subst P.
  - intros * Heq Hall ? ?.
    rewrite <- (prod_fin_supp_nat_fn_proper (fin_supp_nat_fn_add f f2)), Hall
      by (subst; done).
    by f_equal; apply prod_fin_supp_nat_fn_proper.
  - intros f2 ?.
    rewrite prod_fin_supp_nat_fn_zero.
    rewrite <- (prod_fin_supp_nat_fn_proper f2); [by lia |].
    by symmetry; apply left_id; typeclasses eauto.
  - intros i f1 ? Hall f2 ?.
    rewrite <- (prod_fin_supp_nat_fn_proper (succ_fin_supp_nat_fn (fin_supp_nat_fn_add f1 f2) i)),
      !prod_fin_supp_nat_fn_succ, Hall; [by lia |].
    by rewrite fin_supp_nat_fn_add_succ_l.
Qed.

End sec_prod_powers.

(** ** A Prime Factorization Result *)

#[export] Instance prime_decision : forall n, Decision (prime n) := prime_dec.

Definition primes : Type := dsig prime.

#[export] Instance primes_inhabited : Inhabited primes :=
  populate (dexist 2%Z prime_2).

Definition prod_primes_powers (powers : primes -> nat) `{!Finite (supp powers)} : Z :=
  prod_fin_supp_nat_fn (fun p : primes => ` p) powers.

Lemma not_prime_divide_prime : forall (n : Z), (n > 1)%Z -> ~ prime n ->
  exists (m : Z), prime m /\ exists (q : Z), (2 <= q < n)%Z /\ n = (q * m)%Z.
Proof.
  pose (P := fun n =>  ~ prime n ->
    exists (m : Z), prime m /\ exists (q : Z), (2 <= q < n)%Z /\ n = (q * m)%Z).
  cut (forall n : Z, (2 <= n)%Z -> P n).
  {
    by intros HP n Hn1 Hnp; apply HP; [lia |].
  }
  apply Zlt_lower_bound_ind; subst P; cbn; intros n Hind Hn2 Hnp.
  apply not_prime_divide in Hnp as (p & [Hp1 Hpn] & q & ->); [| lia].
  destruct (decide (prime p)) as [| Hnp].
  - exists p; split; [done |].
    eexists; split; [| done].
    by nia.
  - apply Hind in Hnp as (m & Hmprime & q' & Hq' & ->); [| by lia].
    exists m; split; [done |].
    by exists (q * q')%Z; split; nia.
Qed.

Lemma primes_factorization : forall (n : Z), (n > 1)%Z ->
  exists (ps : primes -> nat) (Hps : Finite (supp ps)),
    fin_supp ps <> [] /\ n = prod_primes_powers ps.
Proof.
  intros n H_n; assert (Hn : (2 <= n)%Z) by lia; clear H_n.
  revert n Hn; apply Zlt_lower_bound_ind.
  intros n Hind Hn2.
  destruct (decide (prime n)) as [| Hnp].
  - eexists (delta_fin_supp_nat_fn (dexist n p)), _.
    split; [| by unfold prod_primes_powers; rewrite prod_powers_delta].
    by eapply elem_of_not_nil, elem_of_delta_fin_supp_nat_fn_fin_supp.
  - apply not_prime_divide in Hnp as (p & [Hp1 Hpn] & q & ->); [| lia].
    assert (Hq1 : (1 < q)%Z) by nia.
    assert (Hqn : (q < q * p)%Z) by nia.
    destruct (Hind p) as (ps & ? & Hdomps & ->); [by lia |].
    destruct (Hind q) as (qs & ? & Hdomqs & ->); [by lia |].
    exists (fin_supp_nat_fn_add qs ps), _.
    split.
    + apply not_null_element in Hdomps.
      destruct_dec_sig Hdomps i Hi Heq.
      by eapply elem_of_not_nil, elem_of_fin_supp_nat_fn_add_fin_supp; right.
    + by symmetry; apply prod_powers_add.
Qed.
