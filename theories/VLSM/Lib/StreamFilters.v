From stdpp Require Import prelude.
From Coq Require Import Streams Sorted.
From VLSM.Lib Require Import Preamble StreamExtras SortedLists ListExtras.

(**
Given a predicate <<P>> and a stream <<s>>, a stream of naturals <<ns>>
determines a [filtering_subsequence] for <<P>> on <<s>> if it corresponds to
the list of positions in <<ss>> where <<P>> holds, increasingly ordered.
*)
Definition filtering_subsequence
  {A : Type}
  (P : A -> Prop)
  (s : Stream A)
  (ns : Stream nat)
  : Prop
  := (forall i, i < hd ns -> ~P (Str_nth i s)) /\
     ForAll2 (fun m n => P (Str_nth m s) /\ m < n /\ forall i, m < i < n -> ~ P (Str_nth i s)) ns.

Lemma filtering_subsequence_sorted
  {A : Type}
  (P : A -> Prop)
  (s : Stream A)
  (ns : Stream nat)
  (Hfs : filtering_subsequence P s ns)
  : ForAll2 lt ns.
Proof.
  apply proj2 in Hfs. revert Hfs. apply ForAll2_subsumption.
  intros. apply H.
Qed.

Lemma filtering_subsequence_prefix_sorted
  {A : Type}
  (P : A -> Prop)
  (s : Stream A)
  (ns : Stream nat)
  (Hfs : filtering_subsequence P s ns)
  : forall n, LocallySorted lt (stream_prefix ns n).
Proof.
  intro n. apply LocallySorted_ForAll2.
  apply stream_prefix_ForAll2.
  by apply filtering_subsequence_sorted in Hfs.
Qed.

Lemma filtering_subsequence_iff
  {A : Type}
  (P Q : A -> Prop)
  (HPQ : forall a, P a <-> Q a)
  (s : Stream A)
  (ss : Stream nat)
  : filtering_subsequence P s ss <-> filtering_subsequence Q s ss.
Proof.
  unfold filtering_subsequence.
  rewrite !ForAll2_forall.
  by setoid_rewrite <- HPQ.
Qed.

(** Each element in a [filtering_subsequence] is a position in the base
stream for which the predicate holds.
*)
Lemma filtering_subsequence_witness
  {A : Type}
  (P : A -> Prop)
  (s : Stream A)
  (ss : Stream nat)
  (Hfs : filtering_subsequence P s ss)
  (k : nat)
  : P (Str_nth (Str_nth k ss) s).
Proof.
  apply proj2 in Hfs. rewrite ForAll2_forall in Hfs.
  apply Hfs.
Qed.

(** For each position in the base stream for which the predicate holds is
present in the [filtering_subsequence].
*)
Lemma filtering_subsequence_witness_rev
  {A : Type}
  (P : A -> Prop)
  (s : Stream A)
  (ss : Stream nat)
  (Hfs : filtering_subsequence P s ss)
  (n : nat)
  (Hn : P (Str_nth n s))
  : exists k, n = Str_nth k ss.
Proof.
  apply filtering_subsequence_sorted in Hfs as Hss_sorted.
  apply monotone_nat_stream_prop_from_successor in Hss_sorted.
  apply monotone_nat_stream_find with (n := n) in Hss_sorted.
  destruct Hss_sorted  as [Hlt | [k Hk]].
  - destruct Hfs as [Hfs _]. by elim (Hfs n).
  - destruct Hk as [Heq | Hk]; subst; [by exists k |].
    exfalso. apply proj2 in Hfs.
    rewrite ForAll2_forall in Hfs.
    specialize (Hfs k) as [_ [_ Hfs]].
    by elim (Hfs n).
Qed.

(** Prefixes of the filtering subsequence expressed as filters.
*)
Lemma filtering_subsequence_prefix_is_filter
  {A : Type}
  (P : A -> Prop)
  {Pdec : forall a, Decision (P a)}
  (s : Stream A)
  (ss : Stream nat)
  (Hfs : filtering_subsequence P s ss)
  : forall (k : nat),
    stream_prefix ss (S k) =
    filter (fun i => P (Str_nth i s)) (stream_prefix nat_sequence (S (Str_nth k ss))).
Proof.
  intro k.
  apply (@set_equality_predicate _ lt _).
  - by apply filtering_subsequence_prefix_sorted with P s.
  - apply LocallySorted_filter.
    + unfold Transitive. lia.
    + apply nat_sequence_prefix_sorted.
  - unfold ListSetExtras.set_eq, subseteq, list_subseteq.
    setoid_rewrite elem_of_list_filter.
    setoid_rewrite elem_of_stream_prefix.
    setoid_rewrite nat_sequence_nth.
    split; intros.
    + destruct H as [i [Hi Ha]].
      subst.
      split; [by apply filtering_subsequence_witness |].
      eexists; split; [| done].
      destruct (decide (i = k)); [subst; lia|].
      cut (Str_nth i ss < Str_nth k ss); [lia|].
      apply ForAll2_transitive_lookup; [unfold Transitive; lia| | lia].
      by apply filtering_subsequence_sorted in Hfs.
    + destruct H as [Hpa [_a [Hlt H_a]]].
      subst _a.
      specialize (filtering_subsequence_witness_rev _ _ _ Hfs _ Hpa)
        as [k' Hk'].
      subst.
      exists k'.
      split; [| done].
      apply filtering_subsequence_sorted in Hfs.
      apply monotone_nat_stream_prop_from_successor in Hfs.
      specialize (monotone_nat_stream_rev _ Hfs k' k) as Hle.
      feed specialize Hle; lia.
Qed.

Lemma filtering_subsequence_prefix_length
  {A : Type}
  (P : A -> Prop)
  {Pdec : forall a, Decision (P a)}
  (s : Stream A)
  (ss : Stream nat)
  (Hfs : filtering_subsequence P s ss)
  (m : nat)
  : length (filter P (stream_prefix s (S (Str_nth m ss)))) = S m.
Proof.
  specialize (filtering_subsequence_prefix_is_filter _ _ _ Hfs m) as Hfilter.
  apply f_equal with (f := length) in Hfilter.
  rewrite stream_prefix_length in Hfilter.
  rewrite! stream_prefix_S, filter_app in Hfilter.
  unfold filter at 2 in Hfilter. simpl in Hfilter.
  rewrite nat_sequence_nth in Hfilter.
  rewrite stream_prefix_S, filter_app.
  unfold filter at 2. simpl.
  specialize (filtering_subsequence_witness _ _ _ Hfs m) as Hm.
  rewrite decide_True in Hfilter by done.
  rewrite decide_True by done.
  rewrite app_length, Nat.add_comm in Hfilter. simpl in Hfilter.
  rewrite app_length, Nat.add_comm. simpl.
  rewrite Hfilter.
  f_equal.
  clear -Hfs.
  generalize (Str_nth m ss).
  induction n; [done |].
  rewrite !stream_prefix_S, !filter_app, !app_length, IHn.
  f_equal. rewrite nat_sequence_nth.
  by cbn; case_decide.
Qed.

Lemma filtering_subsequence_prefix_is_filter_last
  {A : Type}
  (P : A -> Prop)
  {Pdec : forall a, Decision (P a)}
  (s : Stream A)
  (ss : Stream nat)
  (Hfs : filtering_subsequence P s ss)
  (n : nat)
  (Hn : P (Str_nth n s))
  : Str_nth (length (filter P (stream_prefix s n))) ss = n.
Proof.
  specialize (filtering_subsequence_witness_rev _ _ _ Hfs _ Hn) as [k Heqn].
  replace (length _) with k; [by subst |].
  specialize (filtering_subsequence_prefix_length _ _ _ Hfs k) as Hlength.
  rewrite! stream_prefix_S, filter_app in Hlength.
  unfold filter at 2 in Hlength. simpl in Hlength.
  rewrite decide_True in Hlength by (subst; done).
  rewrite app_length, Nat.add_comm in Hlength. simpl in Hlength.
  by inversion Hlength; subst.
Qed.

(** Given a [filtering_subsequence] for property <<P>> over a stream <<s>> and
a function <<f>> transforming elements with property <<P>>, we can define the
filtering of <<s>> by <<P>> mapped through the function <<f>>.
*)
Definition filtering_subsequence_stream_filter_map
  {A B : Type}
  (P : A -> Prop)
  {Pdec : forall a, Decision (P a)}
  (f : dsig P -> B)
  (s : Stream A)
  (ss : Stream nat)
  (Hfs : filtering_subsequence P s ss)
  : Stream B
  := map (fun k => f (dexist _ (filtering_subsequence_witness P s ss Hfs k))) nat_sequence.

(** Connecting prefixes of [filtering_subsequence_stream_filter_map] with [list_filter_map]s on
prefixes.
*)
Lemma fitering_subsequence_stream_filter_map_prefix
  {A B : Type}
  (P : A -> Prop)
  {Pdec : forall a, Decision (P a)}
  (f : dsig P -> B)
  (s : Stream A)
  (ss : Stream nat)
  (Hfs : filtering_subsequence P s ss)
  (n : nat)
  (pre_filter_map := list_filter_map P f (stream_prefix s n))
  (m := length pre_filter_map)
  : stream_prefix (filtering_subsequence_stream_filter_map P f s ss Hfs) m = pre_filter_map.
Proof.
  subst m pre_filter_map.
  induction n; [done |].
  rewrite stream_prefix_S, list_filter_map_app, app_length.
  remember (list_filter_map P f [Str_nth n s]) as lst.
  unfold list_filter_map in Heqlst.
  rewrite filter_annotate_unroll in Heqlst. simpl in Heqlst.
  case_decide; subst lst; simpl; [| by rewrite Nat.add_comm, app_nil_r].
  replace (length (list_filter_map P f (stream_prefix s n)) + 1)
    with (S (length (list_filter_map P f (stream_prefix s n))))
    by lia.
  rewrite stream_prefix_S.
  rewrite IHn.
  f_equal. f_equal.
  unfold filtering_subsequence_stream_filter_map.
  rewrite Str_nth_map.
  f_equal. apply dsig_eq.
  simpl. rewrite nat_sequence_nth.
  f_equal.
  unfold list_filter_map.
  rewrite map_length. rewrite filter_annotate_length.
  by apply filtering_subsequence_prefix_is_filter_last.
Qed.

Program Definition fitering_subsequence_stream_filter_map_prefix_ex
  {A B : Type}
  (P : A -> Prop)
  {Pdec : forall a, Decision (P a)}
  (f : dsig P -> B)
  (s : Stream A)
  (ss : Stream nat)
  (Hfs : filtering_subsequence P s ss)
  (m : nat)
  : { n : nat | stream_prefix (filtering_subsequence_stream_filter_map P f s ss Hfs) m = list_filter_map P f (stream_prefix s n) } :=
  match m with
  | 0 => exist _ 0 _
  | S m => exist _ (S (Str_nth m ss)) _
  end.
Next Obligation. done. Qed.
Next Obligation.
  intros. subst.
  specialize (fitering_subsequence_stream_filter_map_prefix P f _ _ Hfs (S (Str_nth m ss))) as Heq.
  remember (S m) as Sm.
  simpl in *.
  rewrite <- Heq.
  f_equal.
  unfold list_filter_map.
  rewrite map_length. rewrite filter_annotate_length.
  symmetry. subst.
  by apply filtering_subsequence_prefix_length.
Qed.

Lemma stream_filter_Forall
  {A : Type}
  (P : A -> Prop)
  (s : Stream A)
  (ss : Stream nat)
  (s' := stream_subsequence s ss)
  (Hfs : filtering_subsequence P s ss)
  : ForAll1 P s'.
Proof.
  apply ForAll1_forall.
  intro n.
  unfold s'.
  unfold stream_subsequence.
  rewrite Str_nth_map.
  by apply filtering_subsequence_witness.
Qed.

(** ** Obtaining [filtering_sequences] for streams

Given a stream, a decidable predicate on its elements, and a guarantee that the
predicates holds [InfinitelyOften] on the elements of the stream, we can
(coinductively) obtain a [filtering_sequence].

The approach below follows closely the one proposed by the following paper,
except that instead of obtaining the filtered sequence itself we obtain the
stream of all positions corresponding to the filtered sequence.

Yves Bertot. Filters on Co-Inductive streams: an application to Eratosthenes’ sieve. RR-5343, INRIA.
2004, pp.21. ffinria-00070658 https://hal.inria.fr/inria-00070658/document
*)

Section stream_filter_positions.

Context
  [A : Type]
  (P : A -> Prop)
  {Pdec : forall a, Decision (P a)}
  .

(** Given a stream <<s>> and a proof that there exists an element of <<s>> for
which <<P>> holds, computes the first position of <<s>> in which <<P>> holds
(shifted by the given argument <<n>>) and the remainder of <<s>> after that
position.

The definition iterates looking for the first position in which <<P>> holds,
termination being ensured by the fact that [Exists1] is inductive.
*)
Fixpoint stream_filter_fst_pos
  (s : Stream A)
  (Hev : Exists1 P s)
  (n : nat)
  {struct Hev}
  : nat * Stream A.
Proof.
  refine
    (match decide (P (hd s)) with
      | left p => (n, tl s)
      | right _ =>
        stream_filter_fst_pos (tl s) _ (S n)
     end).
  by destruct Hev.
Defined.

Lemma stream_filter_fst_pos_characterization
  (s : Stream A)
  (Hev : Exists1 P s)
  (n : nat)
  : exists k,
    stream_filter_fst_pos s Hev n = (n + k, Str_nth_tl (S k) s) /\
    P (Str_nth k s) /\ (forall i, i < k -> ~ P (Str_nth i s)).
Proof.
  revert s Hev n.
  fix H 2.
  intros.
  destruct Hev; simpl.
  - destruct (decide _); [| done].
    exists 0. split_and!; f_equal; [lia | done | lia].
  - destruct (decide _); simpl.
    + exists 0. split_and!; f_equal; [lia | done | lia].
    + specialize (H (tl s) Hev (S n)) as (k & Heq & Hp & Hnp).
      exists (S k). rewrite Heq.
      split; [f_equal; lia|].
      split; [done |].
      intros. destruct i; [done |].
      apply Hnp. lia.
Qed.

Lemma stream_filter_fst_pos_infinitely_often
  (s : Stream A)
  (Hev : Exists1 P s)
  (n : nat)
  : InfinitelyOften P s -> InfinitelyOften P (stream_filter_fst_pos s Hev n).2.
Proof.
  destruct (stream_filter_fst_pos_characterization s Hev n) as [k [Heq _]].
  rewrite Heq. apply InfinitelyOften_nth_tl.
Qed.

Lemma stream_filter_fst_pos_le
  (s : Stream A)
  (Hev : Exists1 P s)
  (n : nat)
  : n <= (stream_filter_fst_pos s Hev n).1.
Proof.
  destruct (stream_filter_fst_pos_characterization s Hev n) as [k [Heq _]].
  rewrite Heq. simpl. lia.
Qed.

Lemma stream_filter_fst_pos_nth_tl_has_property
  (s : Stream A)
  (n : nat)
  (sn := Str_nth_tl n s)
  (Hev : Exists1 P sn)
  (fpair := stream_filter_fst_pos (Str_nth_tl n s) Hev n)
  : P (Str_nth fpair.1 s) /\
    forall i, n <= i < fpair.1 -> ~ P (Str_nth i s).
Proof.
  specialize (stream_filter_fst_pos_characterization sn Hev n)
    as [k [Heq [Hp Hnp]]].
  subst sn fpair.
  rewrite Heq.
  clear -Hp Hnp. rewrite Str_nth_plus, Nat.add_comm in Hp.
  split; [done |].
  intros i [Hlt_i Hilt].
  apply nat_le_sum in Hlt_i as [i' ->].
  rewrite Nat.add_comm, <- Str_nth_plus.
  apply Hnp. simpl in *. lia.
Qed.

(** Given as stream <<s>> for which predicate <<P>> holds [InfinitelyOften]
produces the streams of all its position at which <<P>> holds in a strictly
increasing order (shifted by the given argument <<n>>).
*)
CoFixpoint stream_filter_positions (s : Stream A) (Hinf : InfinitelyOften P s) (n : nat) : Stream nat :=
  let fpair := stream_filter_fst_pos _ (fHere _ _ Hinf) n in
  Cons fpair.1 (stream_filter_positions fpair.2 (stream_filter_fst_pos_infinitely_often _ (fHere _ _ Hinf) n Hinf)  (S fpair.1)).

Lemma stream_filter_positions_unroll (s : Stream A) (Hinf : InfinitelyOften P s) (n : nat)
  (fpair := stream_filter_fst_pos _ (fHere _ _ Hinf) n)
  : stream_filter_positions s Hinf n =
    Cons fpair.1 (stream_filter_positions fpair.2 (stream_filter_fst_pos_infinitely_often _ (fHere _ _ Hinf) n Hinf)  (S fpair.1)).
Proof.
  by rewrite <- recons at 1.
Qed.

Lemma stream_filter_positions_Str_nth_tl
  (s : Stream A) (Hinf : InfinitelyOften P s) (n0 : nat) (n : nat)
  : exists kn (Hinf' : InfinitelyOften P (Str_nth_tl (S kn) s)),
    Str_nth_tl n (stream_filter_positions s Hinf n0) = Cons (n0 + kn) (stream_filter_positions (Str_nth_tl (S kn) s) Hinf' (S (n0 + kn)))
    /\ P (Str_nth kn s).
Proof.
  induction n.
  - simpl. rewrite (stream_filter_positions_unroll s Hinf n0).
    specialize
      (stream_filter_fst_pos_characterization s (fHere _ s Hinf) n0)
        as [k [Heq [Hp _]]].
    assert (Hk : (stream_filter_fst_pos s (fHere (Exists1 P) s Hinf) n0).1 = n0 + k).
    { by rewrite Heq. }
    assert (Htl : (stream_filter_fst_pos s (fHere (Exists1 P) s Hinf) n0).2 = Str_nth_tl (S k) s).
    { by rewrite Heq. }
    exists k.
    rewrite Hk. simpl. simpl in Htl. rewrite <- Htl. eauto.
  - replace
      (Str_nth_tl (S n) (stream_filter_positions s Hinf n0))
      with (tl (Str_nth_tl n (stream_filter_positions s Hinf n0)))
      by apply tl_nth_tl.
    destruct IHn as [kn [Hinfn [Hsn Hpn]]].
    rewrite Hsn.
    simpl. rewrite (stream_filter_positions_unroll (Str_nth_tl kn (tl s)) Hinfn (S (n0 + kn))).
    specialize
      (stream_filter_fst_pos_characterization (Str_nth_tl kn (tl s)) (fHere _ _ Hinfn) (S (n0 + kn)))
        as [k [Heq [Hp _]]].
    match type of Heq with
    | ?pair = (?f, ?s) =>
      assert (Hk : pair.1 = f) by (rewrite Heq; done);
      assert (Htl : pair.2 = s) by (rewrite Heq; done)
    end.
    simpl in Hk.  rewrite Hk.
    simpl in Htl.
    exists (S (k + kn)).
    simpl.
    rewrite tl_nth_tl, Str_nth_tl_plus in Htl.
    rewrite Str_nth_plus in Hp.
    rewrite <- Htl.
    replace (n0 + S (k + kn)) with (S (n0 + kn + k)) by lia. eauto.
Qed.

Lemma stream_filter_positions_monotone
  (s : Stream A) (Hinf : InfinitelyOften P s) (n : nat)
  : monotone_nat_stream_prop (stream_filter_positions s Hinf n).
Proof.
  apply monotone_nat_stream_prop_from_successor.
  revert s Hinf n.
  cofix H.
  intros.
  constructor; simpl; [|apply H].
  apply stream_filter_fst_pos_le.
Qed.

(** [stream_filter_positions] produces a [filtering_sequence].
*)
Lemma stream_filter_positions_filtering_subsequence
  (s : Stream A) (Hinf : InfinitelyOften P s)
  : filtering_subsequence P s (stream_filter_positions s Hinf 0).
Proof.
  split.
  - specialize (stream_filter_fst_pos_characterization s (fHere (Exists1 P) s Hinf) 0)
      as [k [Heq [Hpk Hnp]]].
    simpl in Heq.
    by rewrite stream_filter_positions_unroll; cbn; rewrite Heq.
  - apply ForAll2_forall.
    intro n.
    specialize (stream_filter_positions_Str_nth_tl s Hinf 0 n) as Hnth_tl.
    simpl in Hnth_tl.
    remember (stream_filter_positions s Hinf 0).
    destruct Hnth_tl as [kn [Hnth_inf [Hnth Hnth_p]]].
    unfold Str_nth. simpl. rewrite <- tl_nth_tl.
    rewrite stream_filter_positions_unroll in Hnth.
    specialize (stream_filter_fst_pos_characterization (Str_nth_tl kn (tl s)) (fHere _ _ Hnth_inf) (S kn))
      as [k [Heq [Hpk Hnp]]].
    rewrite Hnth; simpl.
    split; [done |].
    rewrite Heq. simpl.
    split; [lia|].
    intros i [Hle Hlt].
    apply nat_le_sum in Hle as [k' ->].
    rewrite Nat.add_comm, <- Str_nth_tl_plus. simpl.
    apply Hnp. lia.
Qed.

(** A restatement of [filtering_subsequence_stream_filter_map] based on the
[InfinitelyOften] predicate, using the [stream_filter_positions_filtering_subsequence].
*)
Definition stream_filter_map
  [B : Type]
  (f : dsig P -> B)
  (s : Stream A)
  (Hinf : InfinitelyOften P s)
  : Stream B :=
  filtering_subsequence_stream_filter_map P f _ _ (stream_filter_positions_filtering_subsequence s Hinf).

(** Stream filtering is obtained as a specialization of [stream_filter_map].
*)
Definition stream_filter
  (s : Stream A)
  (Hinf : InfinitelyOften P s)
  : Stream A :=
  stream_filter_map proj1_sig s Hinf.

End stream_filter_positions.

Section stream_map_option.

(** ** Mapping a partial function on a stream

Given a partial function <<f>> which is [InfinitelyOften] defined on the
elements of a stream <<s>>, we can define the stream of the defined mapped
values of <<s>> through <<f>> as a particular [stream_filter_map].
*)
Context
  [A B : Type]
  (f : A -> option B)
  (P : A -> Prop := is_Some ∘ f)
  (s : Stream A)
  .

Definition stream_map_option
  (Hinf : InfinitelyOften P s)
  : Stream B :=
  stream_filter_map P (fun k : dsig P => is_Some_proj (proj2_dsig k)) s Hinf.

Lemma stream_map_option_prefix
  (Hinf : InfinitelyOften P s)
  (n : nat)
  (map_opt_pre := map_option f (stream_prefix s n))
  (m := length map_opt_pre)
  : stream_prefix (stream_map_option Hinf) m = map_opt_pre.
Proof.
  subst map_opt_pre m.
  rewrite !(map_option_as_filter f (stream_prefix s n)).
  apply fitering_subsequence_stream_filter_map_prefix.
Qed.

Program Definition stream_map_option_prefix_ex
  (Hinf : InfinitelyOften P s)
  (Hfs := stream_filter_positions_filtering_subsequence _ _ Hinf)
  (k : nat)
  : { n | stream_prefix (stream_map_option Hinf) k = map_option f (stream_prefix s n)} :=
  let (n, Heq) := (fitering_subsequence_stream_filter_map_prefix_ex P (fun k => is_Some_proj (proj2_dsig k)) _ _ Hfs k) in
  exist _ n _.
Next Obligation.
  by intros; cbn; rewrite !map_option_as_filter.
Qed.

Definition bounded_stream_map_option
  (Hfin : FinitelyManyBound P s)
  : list B :=
  map_option f (stream_prefix s (` Hfin)).

End stream_map_option.

(** For a totally defined function, [stream_map_option] corresponds to the
regular [map] on streams.
*)
Lemma stream_map_option_EqSt [A B : Type] (f : A -> B)
  : forall s (Hinf : InfinitelyOften (is_Some ∘ (Some ∘ f)) s),
  EqSt (map f s) (stream_map_option (Some ∘ f) s Hinf).
Proof.
  intros. apply EqSt_stream_prefix. intro n.
  destruct n; [done |].
  rewrite <- stream_prefix_map.

  pose (stream_map_option_prefix_ex (Some ∘ f) s Hinf (S n)) as Hrew.
  rewrite (proj2_sig Hrew).
  replace (` Hrew) with (S n); [done |].
  simpl. f_equal. clear.
  cut
    (forall k, Streams.Str_nth n
      (stream_filter_positions (is_Some ∘ (Some ∘ f)) s Hinf k) = k + n).
  { intros Hk. specialize (Hk 0). simpl in Hk. congruence.  }
  revert s Hinf.
  assert (Hfirst : forall s Hinf k,
    (stream_filter_fst_pos (is_Some ∘ (Some ∘ f)) s (fHere _ _ Hinf) k).1 = k).
  { intros.
    match goal with
    |- fst (stream_filter_fst_pos ?P s ?Hex k) = k =>
      specialize (stream_filter_fst_pos_characterization P s Hex k)
        as [_k [Heq1 [_ H_k]]]
    end.
    rewrite Heq1.
    simpl.
    destruct _k; [lia|].
    exfalso. apply (H_k 0); [lia | by eexists].
  }
  induction n; intros; rewrite stream_filter_positions_unroll; unfold Streams.Str_nth; simpl.
  - replace (k + 0) with k by lia.
    apply Hfirst.
  - unfold Streams.Str_nth in IHn.
    rewrite IHn.
    simpl. replace (k + S n) with (S (k + n)) by lia.
    f_equal. f_equal.
    apply Hfirst.
Qed.
