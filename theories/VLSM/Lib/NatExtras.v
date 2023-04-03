From stdpp Require Import prelude.
From VLSM.Lib Require Import EquationsExtras.
From VLSM.Lib Require Import Preamble.

Set Default Proof Using "Type".

(** * Natural number utility definitions and lemmas

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
