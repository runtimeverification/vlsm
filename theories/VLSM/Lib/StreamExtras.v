From stdpp Require Import prelude.
From Coq Require Import Streams Sorted.
From VLSM.Lib Require Import Preamble ListExtras StdppExtras SortedLists NeList.

Set Default Proof Using "Type".

(** * Stream utility definitions and lemmas *)

Lemma stream_eq_hd_tl {A} (s s' : Stream A) :
  hd s = hd s' -> tl s = tl s' -> s = s'.
Proof. by destruct s, s'; cbn; intros -> ->. Qed.

Lemma fHere [A : Type] (P : Stream A -> Prop) : forall s, ForAll P s -> P s.
Proof. by intros s []. Qed.

Lemma fFurther [A : Type] (P : Stream A -> Prop) : forall s, ForAll P s -> ForAll P (tl s).
Proof. by intros s []. Qed.

Lemma ForAll_subsumption [A : Type] (P Q : Stream A -> Prop)
  (HPQ : forall s, P s -> Q s)
  : forall s, ForAll P s -> ForAll Q s.
Proof.
  apply ForAll_coind.
  - by intros s Hp; apply fHere in Hp; apply HPQ.
  - by apply fFurther.
Qed.

Lemma Exists_Str_nth_tl [A : Type] (P : Stream A -> Prop)
  : forall s, Exists P s <-> exists n, P (Str_nth_tl n s).
Proof.
  intros s; split.
  - induction 1; [by exists 0 |].
    destruct IHExists as [n Hn].
    by exists (S n).
  - intros [n Hn]. revert s Hn.
    induction n; [by apply Here |].
    intros s Hs. specialize (IHn (tl s) Hs).
    by apply Further.
Qed.

Definition Exists1 [A : Type] (P : A -> Prop) := Exists (fun s => P (hd s)).

Lemma Exists1_exists [A : Type] (P : A -> Prop) s
  : Exists1 P s <-> exists n, P (Str_nth n s).
Proof.
  split.
  - induction 1.
    + by exists 0.
    + destruct IHExists as [n Hp].
      by exists (S n).
  - intros [n Hp]. revert s Hp. induction n; intros.
    + by constructor.
    + by apply Further, IHn.
Qed.

Definition ForAll1 [A : Type] (P : A -> Prop) := ForAll (fun s => P (hd s)).

Lemma ForAll1_subsumption [A : Type] (P Q : A -> Prop)
  (HPQ : forall a, P a -> Q a)
  : forall s, ForAll1 P s -> ForAll1 Q s.
Proof.
  by apply ForAll_subsumption; intro s; apply HPQ.
Qed.

Lemma ForAll1_forall [A : Type] (P : A -> Prop) s
  : ForAll1 P s <-> forall n, P (Str_nth n s).
Proof.
  split; intros.
  - by apply ForAll_Str_nth_tl with (m := n) in H; apply H.
  - apply ForAll_coind with (fun s : Stream A => forall n : nat, P (Str_nth n s))
    ; intros.
    + by specialize (H0 0).
    + by specialize (H0 (S n)).
    + by apply H.
Qed.

Definition ForAll2 [A : Type] (R : A -> A -> Prop) := ForAll (fun s => R (hd s) (hd (tl s))).

Lemma ForAll2_subsumption [A : Type] (R1 R2 : A -> A -> Prop)
  (HR : forall a b, R1 a b -> R2 a b)
  : forall s, ForAll2 R1 s -> ForAll2 R2 s.
Proof.
  by apply ForAll_subsumption; intro s; apply HR.
Qed.

Lemma ForAll2_forall [A : Type] (R : A -> A -> Prop) s
  : ForAll2 R s <-> forall n, R (Str_nth n s) (Str_nth (S n) s).
Proof.
  split; intros.
  - apply ForAll_Str_nth_tl with (m := n), fHere in H.
    by rewrite tl_nth_tl in H.
  - apply ForAll_coind with (fun s : Stream A => forall n : nat, R (Str_nth n s) (Str_nth (S n) s))
    ; intros.
    + by apply (H0 0).
    + by apply (H0 (S n)).
    + by apply H.
Qed.

Lemma recons
  {A : Type}
  (s : Stream A)
  : Cons (hd s) (tl s) = s.
Proof.
  by case s.
Qed.

Definition stream_app
  {A : Type}
  (prefix : list A)
  (suffix : Stream A)
  : Stream A
  :=
  fold_right (@Cons A) suffix prefix.

Definition stream_app_cons {A}
  (a : A)
  (l : Stream A)
  : stream_app [a] l = Cons a l
  := eq_refl.

Lemma stream_app_assoc
  {A : Type}
  (l m : list A)
  (n : Stream A)
  : stream_app l (stream_app m n) = stream_app (l ++ m) n.
Proof.
  by induction l; cbn; f_equal.
Qed.

Lemma stream_app_f_equal
  {A : Type}
  (l1 l2 : list A)
  (s1 s2 : Stream A)
  (Hl : l1 = l2)
  (Hs : EqSt s1 s2)
  : EqSt (stream_app l1 s1) (stream_app l2 s2).
Proof.
  by subst; induction l2; [| constructor].
Qed.

Lemma stream_app_inj_l
  {A : Type}
  (l1 l2 : list A)
  (s : Stream A)
  (Heq : stream_app l1 s = stream_app l2 s)
  (Heq_len : length l1 = length l2)
  : l1 = l2.
Proof.
  generalize dependent l2.
  induction l1; intros; destruct l2; try done; try inversion Heq_len.
  inversion Heq.
  by rewrite (IHl1 l2 H2 H0).
Qed.

Fixpoint stream_prefix
  {A : Type}
  (l : Stream A)
  (n : nat)
  : list A
  := match n, l with
  | 0, _ => []
  | S n, Cons a l => a :: stream_prefix l n
  end.

Lemma stream_prefix_nth
  {A : Type}
  (s : Stream A)
  (n : nat)
  (i : nat)
  (Hi : i < n)
  : nth_error (stream_prefix s n) i = Some (Str_nth i s).
Proof.
  revert s n Hi.
  induction i; intros [a s] [| n] Hi; [by inversion Hi .. |].
  by apply IHi; lia.
Qed.

Lemma stream_prefix_lookup
  {A : Type}
  (s : Stream A)
  (n : nat)
  (i : nat)
  (Hi : i < n)
  : stream_prefix s n !! i = Some (Str_nth i s).
Proof.
  revert s n Hi.
  induction i; intros [a s] [| n] Hi; [by inversion Hi .. |].
  by apply IHi; lia.
Qed.

Lemma stream_prefix_S
  {A : Type}
  (s : Stream A)
  (n : nat)
  : stream_prefix s (S n) = stream_prefix s n ++ [Str_nth n s].
Proof.
  revert s.
  by induction n; intros; rewrite <- (recons s); cbn; f_equal; rewrite <- IHn.
Qed.

Lemma stream_prefix_EqSt
  {A : Type}
  (s1 s2 : Stream A)
  (Heq : EqSt s1 s2)
  : forall n : nat, stream_prefix s1 n = stream_prefix s2 n .
Proof.
  intro n; revert s1 s2 Heq.
  induction n; [done |]; intros [a1 s1] [a2 s2] Heq.
  by inversion Heq; cbn in *; subst; erewrite IHn.
Qed.

Lemma EqSt_stream_prefix
  {A : Type}
  (s1 s2 : Stream A)
  (Hpref : forall n : nat, stream_prefix s1 n = stream_prefix s2 n)
  : EqSt s1 s2.
Proof.
  apply ntheq_eqst.
  intro n.
  assert (Hlt : n < S n) by constructor.
  assert (HSome : Some (Str_nth n s1) = Some (Str_nth n s2)).
  {
    rewrite <- (stream_prefix_nth  s1 (S n) n Hlt).
    rewrite <- (stream_prefix_nth  s2 (S n) n Hlt).
    by rewrite (Hpref (S n)).
  }
  by inversion HSome.
Qed.

Lemma elem_of_stream_prefix
  {A : Type}
  (l : Stream A)
  (n : nat)
  (a : A)
  : a ∈ stream_prefix l n <-> exists k : nat, k < n /\ Str_nth k l = a.
Proof.
  revert l a.
  induction n; simpl; split; intros.
  - by inversion H.
  - by destruct H as [k [Hk _]]; lia.
  - destruct l as (b, l).
    inversion H; subst.
    + by exists 0; split; [lia |].
    + apply IHn in H2 as [k [Hlt Heq]].
      by exists (S k); split; [lia |].
  - destruct l as (b, l).
    destruct H as [k [Hlt Heq]].
    destruct k.
    + by unfold Str_nth in Heq; simpl in Heq; subst; left.
    + unfold Str_nth in *; simpl in Heq.
      right; apply IHn.
      by exists k; split; [lia |].
Qed.

Lemma stream_prefix_app_l
  {A : Type}
  (l : list A)
  (s : Stream A)
  (n : nat)
  (Hle : n <= length l)
  : stream_prefix (stream_app l s) n = list_prefix l n.
Proof.
  revert n Hle; induction l; intros [| n] Hle; [by inversion Hle.. |].
  by cbn in *; rewrite IHl; [| lia].
Qed.

Lemma stream_prefix_app_r
  {A : Type}
  (l : list A)
  (s : Stream A)
  (n : nat)
  (Hge : n >= length l)
  : stream_prefix (stream_app l s) n = l ++ stream_prefix s (n - length l).
Proof.
  generalize dependent l.
  generalize dependent s.
  induction n.
  - by intros s [| a l] Hge; cbn in *; [| lia].
  - intros s [| a l] Hge; cbn in *; [done |].
    by rewrite <- IHn; [| lia].
Qed.

Lemma stream_prefix_map
  {A B : Type}
  (f : A -> B)
  (l : Stream A)
  (n : nat)
  : List.map f (stream_prefix l n) = stream_prefix (Streams.map f l) n.
Proof.
  by revert l; induction n; intros [a l]; cbn; rewrite ?IHn.
Qed.

Lemma stream_prefix_length
  {A : Type}
  (l : Stream A)
  (n : nat)
  : length (stream_prefix l n) = n.
Proof.
  by revert l; induction n; intros [a l]; cbn; rewrite ?IHn.
Qed.

(**
  The following two lemmas connect forall quantifiers looking at one
  element or two consecutive elements at a time with corresponding list
  quantifiers applied on their finite prefixes.
*)

Lemma stream_prefix_ForAll
  {A : Type}
  (P : A -> Prop)
  (s : Stream A)
  : ForAll1 P s <-> forall n : nat, Forall P (stream_prefix s n).
Proof.
  rewrite ForAll1_forall.
  setoid_rewrite (Forall_nth P (hd s)).
  setoid_rewrite stream_prefix_length.
  specialize (stream_prefix_nth s) as Hi.
  split.
  - intros Hp n i Hlt.
    specialize (Hi _ _ Hlt).
    by apply nth_error_nth with (d := hd s) in Hi; rewrite Hi.
  - intros Hp n.
    assert (Hn : n < S n) by lia.
    specialize (Hp _ _ Hn).
    specialize (Hi _ _ Hn).
    apply nth_error_nth with (d := hd s) in Hi.
    by rewrite Hi in Hp.
Qed.

Lemma stream_prefix_ForAll2
  {A : Type}
  (R : A -> A -> Prop)
  (s : Stream A)
  : ForAll2 R s <-> forall n : nat, ForAllSuffix2 R (stream_prefix s n).
Proof.
  rewrite ForAll2_forall.
  setoid_rewrite (ForAllSuffix2_lookup R).
  specialize (stream_prefix_lookup s) as Hi.
  split.
  - intros Hp n i.
    destruct (decide (n <= S i)).
    + intros. rewrite lookup_ge_None_2 in H0; [done |].
      by rewrite stream_prefix_length.
    + pose proof (stream_prefix_length s n) as Hlen.
      rewrite (Hi n i), (Hi n (S i)) by lia.
      by do 2 inversion 1; subst.
  - intros Hp n.
    specialize (Hp (S (S n)) n).
    rewrite !Hi in Hp by lia.
    by apply Hp.
Qed.

Lemma ForAll2_transitive_lookup [A : Type] (R : A -> A -> Prop) {HT : Transitive R}
  : forall l, ForAll2 R l <-> forall m n, m < n -> R (Str_nth m l) (Str_nth n l).
Proof.
  setoid_rewrite stream_prefix_ForAll2.
  setoid_rewrite ForAllSuffix2_transitive_lookup; [| done].
  intros s.
  specialize (stream_prefix_lookup s) as Hi.
  split.
  - intros Hp i j Hij.
    specialize (Hp (S j) i j (Str_nth i s) (Str_nth j s) Hij).
    rewrite !Hi in Hp by lia.
    by apply Hp.
  - intros Hp n i j a b Hlt Ha Hb.
    apply lookup_lt_Some in Hb as Hltj.
    rewrite stream_prefix_length in Hltj.
    rewrite Hi in Ha, Hb by lia.
    inversion Ha; inversion Hb.
    by apply Hp.
Qed.

Lemma ForAll2_strict_lookup_rev [A : Type] (R : A -> A -> Prop) {HR : StrictOrder R}
  (l : Stream A) (Hl : ForAll2 R l)
  : forall m n, R (Str_nth m l) (Str_nth n l) -> m < n.
Proof.
  intros m n Hr.
  rewrite ForAll2_transitive_lookup in Hl by typeclasses eauto.
  destruct (Nat.lt_total m n) as [Hlt | [-> | Hgt]]; [done | |].
  - by eapply StrictOrder_Irreflexive in Hr.
  - elim (StrictOrder_Irreflexive (Str_nth n l)).
    transitivity (Str_nth m l); [| done].
    by apply Hl.
Qed.

Lemma ForAll2_strict_lookup [A : Type] (R : A -> A -> Prop) {HR : StrictOrder R}
  : forall l, ForAll2 R l <-> (forall m n, m < n <-> R (Str_nth m l) (Str_nth n l)).
Proof.
  split.
  - intro Hall; split.
    + by apply ForAll2_transitive_lookup; [typeclasses eauto |].
    + by apply ForAll2_strict_lookup_rev.
  - intro Hall.
    apply ForAll2_transitive_lookup; [typeclasses eauto |].
    by intros; apply Hall.
Qed.

Lemma ForAll2_strict_lookup_inj
 [A : Type] (R : A -> A -> Prop) {HR : StrictOrder R}
  (l : Stream A) (Hl : ForAll2 R l)
  : forall m n, Str_nth m l = Str_nth n l -> m = n.
Proof.
  intros m n Hmn.
  destruct HR as [HI HT].
  rewrite ForAll2_transitive_lookup in Hl by done.
  destruct (decide (m = n)); [done |].
  elim (HI (Str_nth n l)).
  by destruct (decide (m < n))
  ; [specialize (Hl m n) | specialize (Hl n m)]; (spec Hl; [lia |])
  ; rewrite Hmn in Hl.
Qed.

Definition stream_suffix
  {A : Type}
  (l : Stream A)
  (n : nat)
  : Stream A
  := Str_nth_tl n l.

Lemma stream_suffix_S
  {A : Type}
  (l : Stream A)
  (n : nat)
  : stream_suffix l n = Cons (Str_nth n l) (stream_suffix l (S n)).
Proof.
  revert l. induction n; intros.
  - by destruct l.
  - by apply IHn.
Qed.

Lemma stream_suffix_nth
  {A : Type}
  (s : Stream A)
  (n : nat)
  (i : nat)
  : Str_nth i (stream_suffix s n) = Str_nth (i + n) s.
Proof.
  by apply Str_nth_plus.
Qed.

Lemma stream_prefix_suffix
  {A : Type}
  (l : Stream A)
  (n : nat)
  : stream_app (stream_prefix l n) (stream_suffix l n) = l.
Proof.
  generalize dependent l. unfold stream_suffix.
  induction n; [done |]; intros [a l]; cbn.
  by f_equal; apply IHn.
Qed.

Lemma stream_prefix_prefix
  {A : Type}
  (l : Stream A)
  (n1 n2 : nat)
  (Hn : n1 <= n2)
  : list_prefix (stream_prefix l n2) n1 = stream_prefix l n1.
Proof.
  revert l n2 Hn.
  induction n1; intros [a l]; intros [| n2] Hn; cbn; [by inversion Hn.. |].
  by rewrite IHn1; [| lia].
Qed.

Lemma stream_prefix_of
  {A : Type}
  (l : Stream A)
  (n1 n2 : nat)
  (Hn : n1 <= n2)
  : stream_prefix l n1 `prefix_of` stream_prefix l n2.
Proof.
  rewrite <- (stream_prefix_prefix l n1 n2 Hn).
  by apply prefix_of_list_prefix.
Qed.

Definition stream_segment
  {A : Type}
  (l : Stream A)
  (n1 n2 : nat)
  : list A
  := list_suffix (stream_prefix l n2) n1.

Lemma stream_segment_nth
  {A : Type}
  (l : Stream A)
  (n1 n2 : nat)
  (Hn : n1 <= n2)
  (i : nat)
  (Hi1 : n1 <= i)
  (Hi2 : i < n2)
  : nth_error (stream_segment l n1 n2) (i - n1) = Some (Str_nth i l).
Proof.
  unfold stream_segment.
  rewrite list_suffix_nth; [| done].
  by apply stream_prefix_nth.
Qed.

Definition stream_segment_alt
  {A : Type}
  (l : Stream A)
  (n1 n2 : nat)
  : list A
  := stream_prefix (stream_suffix l n1) (n2 - n1).

Lemma stream_segment_alt_iff
  {A : Type}
  (l : Stream A)
  (n1 n2 : nat)
  : stream_segment l n1 n2 = stream_segment_alt l n1 n2.
Proof.
  apply nth_error_eq.
  intro k.
  unfold stream_segment_alt. unfold stream_segment.
  destruct (decide (n2 - n1 <= k)).
  - specialize (nth_error_None (list_suffix (stream_prefix l n2) n1) k); intros [_ H].
    specialize (nth_error_None (stream_prefix (stream_suffix l n1) (n2 - n1)) k); intros [_ H_alt].
    rewrite H, H_alt; [done | |].
    + by rewrite stream_prefix_length.
    + by rewrite list_suffix_length, stream_prefix_length.
  - rewrite stream_prefix_nth, stream_suffix_nth by lia.
    assert (Hle : n1 <= n1 + k) by lia.
    specialize (list_suffix_nth (stream_prefix l n2) n1 (n1 + k) Hle)
    ; intro Heq.
    clear Hle.
    assert (Hs : n1 + k - n1 = k) by lia.
    rewrite Hs in Heq.
    by rewrite Heq, stream_prefix_nth; [do 2 f_equal |]; lia.
Qed.

Lemma stream_prefix_segment
  {A : Type}
  (l : Stream A)
  (n1 n2 : nat)
  (Hn : n1 <= n2)
  : stream_prefix l n1 ++ stream_segment l n1 n2 = stream_prefix l n2.
Proof.
  unfold stream_segment.
  rewrite <- (list_prefix_suffix (stream_prefix l n2) n1) at 2.
  by rewrite stream_prefix_prefix.
Qed.

Lemma stream_prefix_segment_suffix
  {A : Type}
  (l : Stream A)
  (n1 n2 : nat)
  (Hn : n1 <= n2)
  : stream_app
      (stream_prefix l n1 ++ stream_segment l n1 n2)
      (stream_suffix l n2)
  = l.
Proof.
  rewrite <- (stream_prefix_suffix l n2) at 4.
  by rewrite stream_prefix_segment.
Qed.

Lemma stream_segment_app
  {A : Type}
  (l : Stream A)
  (n1 n2 n3 : nat)
  (H12 : n1 <= n2)
  (H23 : n2 <= n3)
  : stream_segment l n1 n2 ++ stream_segment l n2 n3 = stream_segment l n1 n3.
Proof.
  assert (Hle : n1 <= n3) by lia.
  specialize (stream_prefix_segment_suffix l n1 n3 Hle); intro Hl1.
  specialize (stream_prefix_segment_suffix l n2 n3 H23); intro Hl2.
  rewrite <- Hl2 in Hl1 at 4. clear Hl2.
  apply stream_app_inj_l in Hl1.
  - specialize (list_prefix_suffix (stream_prefix l n2) n1); intro Hl2.
    specialize (stream_prefix_prefix l n1 n2 H12); intro Hl3.
    rewrite Hl3 in Hl2.
    rewrite <- Hl2, <- app_assoc in Hl1.
    by apply app_inv_head in Hl1.
  - repeat rewrite app_length.
    unfold stream_segment.
    by rewrite !list_suffix_length, !stream_prefix_length; lia.
Qed.

Definition monotone_nat_stream_prop
  (s : Stream nat)
  := forall n1 n2 : nat, n1 < n2 <-> Str_nth n1 s < Str_nth n2 s.

Lemma monotone_nat_stream_prop_from_successor s
  : ForAll2 lt s <-> monotone_nat_stream_prop s.
Proof. by apply ForAll2_strict_lookup; typeclasses eauto. Qed.

Lemma monotone_nat_stream_rev
  (s : Stream nat)
  (Hs : monotone_nat_stream_prop s)
  : forall n1 n2, Str_nth n1  s <= Str_nth n2 s -> n1 <= n2.
Proof.
  intros n1 n2 Hle.
  destruct (decide (n2 < n1)) as [Hlt |]; [| by lia].
  by apply Hs in Hlt; lia.
Qed.

Lemma monotone_nat_stream_find s (Hs : monotone_nat_stream_prop s) (n : nat)
  : n < hd s \/ exists k, Str_nth k s = n \/ Str_nth k s < n < Str_nth (S k) s.
Proof.
  induction n.
  - destruct (hd s) eqn: Hhd.
    + by right; exists 0; left.
    + by left; lia.
  - destruct (decide (hd s <= S n)); [| by left; lia].
    right.
    destruct IHn as [Hlt | [k Hk]]
    ; [by exists 0; left; cbv in *; lia |].
    destruct (decide (Str_nth (S k) s = S n))
    ; [by exists (S k); left |].
    exists k; right.
    cut (Str_nth k s < Str_nth (S k) s); [by lia |].
    by apply (Hs k (S k)); lia.
Qed.

Definition monotone_nat_stream :=
  {s : Stream nat | monotone_nat_stream_prop s}.

Lemma monotone_nat_stream_tl
  (s : Stream nat)
  (Hs : monotone_nat_stream_prop s)
  : monotone_nat_stream_prop (tl s).
Proof.
  by intros n1 n2; etransitivity; [| by apply (Hs (S n1) (S n2))]; lia.
Qed.

CoFixpoint nat_sequence_from (n : nat) : Stream nat
  := Cons n (nat_sequence_from (S n)).

Definition nat_sequence : Stream nat := nat_sequence_from 0.

Lemma nat_sequence_from_nth : forall m n, Str_nth n (nat_sequence_from m) = n + m.
Proof.
  intros m n; revert m.
  induction n; cbn; intros; [done |].
  by unfold Str_nth in IHn |- *; cbn; rewrite IHn; lia.
Qed.

Lemma nat_sequence_nth : forall n, Str_nth n nat_sequence = n.
Proof.
  by intros; unfold nat_sequence; rewrite nat_sequence_from_nth; lia.
Qed.

Lemma nat_sequence_from_sorted : forall n, ForAll2 lt (nat_sequence_from n).
Proof.
  intro n; apply ForAll2_forall; intro m.
  by rewrite !nat_sequence_from_nth; lia.
Qed.

Definition nat_sequence_sorted : ForAll2 lt nat_sequence :=
  nat_sequence_from_sorted 0.

Lemma nat_sequence_from_prefix_sorted
  : forall m n, LocallySorted lt (stream_prefix (nat_sequence_from m) n).
Proof.
  by intros; apply LocallySorted_ForAll2, stream_prefix_ForAll2, nat_sequence_from_sorted.
Qed.

Definition nat_sequence_prefix_sorted
  : forall n, LocallySorted lt (stream_prefix nat_sequence n) :=
  nat_sequence_from_prefix_sorted 0.

Definition stream_subsequence
  {A : Type}
  (s : Stream A)
  (ns : Stream nat)
  : Stream A
  := Streams.map (fun k => Str_nth k s) ns.

Lemma stream_prefix_nth_last
  {A : Type}
  (l : Stream A)
  (n : nat)
  (_last : A)
  : List.last (stream_prefix l (S n)) _last = Str_nth n l.
Proof.
  specialize (nth_error_last (stream_prefix l (S n)) n); intro Hlast.
  specialize (stream_prefix_length l (S n)); intro Hpref_len.
  symmetry in Hpref_len.
  specialize (Hlast Hpref_len _last).
  specialize (stream_prefix_nth l (S n) n); intro Hnth.
  assert (Hlt : n < S n) by constructor.
  specialize (Hnth Hlt).
  rewrite Hnth in Hlast.
  by inversion Hlast.
Qed.

Section sec_infinitely_often.

Context
  [A : Type]
  (P : A -> Prop)
  {Pdec : forall a, Decision (P a)}
  .

Definition InfinitelyOften : Stream A -> Prop :=
  ForAll (Exists1 P).

Definition FinitelyMany : Stream A -> Prop :=
  Exists (ForAll1 (fun a => ~ P a)).

Definition FinitelyManyBound (s : Stream A) : Type :=
  { n : nat | ForAll1 (fun a => ~ P a) (Str_nth_tl n s)}.

Lemma FinitelyMany_from_bound
  : forall s, FinitelyManyBound s -> FinitelyMany s.
Proof.
  intros s [n Hn].
  apply Exists_Str_nth_tl.
  by exists n.
Qed.

Lemma InfinitelyOften_tl s
  : InfinitelyOften s -> InfinitelyOften (tl s).
Proof. by inversion 1. Qed.

Definition InfinitelyOften_nth_tl
  : forall n s, InfinitelyOften s -> InfinitelyOften (Str_nth_tl n s)
  := (@ForAll_Str_nth_tl _ (Exists1 P)).

End sec_infinitely_often.

Lemma InfinitelyOften_impl [A : Type] (P Q : A -> Prop) (HPQ : forall a, P a -> Q a)
  : forall s, InfinitelyOften P s -> InfinitelyOften Q s.
Proof.
  unfold InfinitelyOften.
  cofix IH.
  intros [a s] H.
  inversion H. simpl in H1. apply IH in H1.
  constructor; [| done].
  by rewrite Exists1_exists in *; firstorder.
Qed.

Lemma FinitelyManyBound_impl_rev
 [A : Type] (P Q : A -> Prop) (HPQ : forall a, P a -> Q a)
 : forall s, FinitelyManyBound Q s -> FinitelyManyBound P s.
Proof.
  intros s [n Hn].
  exists n.
  apply ForAll1_forall.
  rewrite ForAll1_forall in Hn.
  by firstorder.
Qed.

Definition stream_prepend {A} (nel : ne_list A) (s : Stream A) : Stream A :=
  (cofix prepend (l : ne_list A) :=
    Cons (ne_list_hd l) (from_option prepend s (ne_list_tl l))) nel.

CoFixpoint stream_concat {A} (s : Stream (ne_list A)) : Stream A :=
  stream_prepend (hd s) (stream_concat (tl s)).

Lemma stream_prepend_prefix {A} (nel : ne_list A) (s : Stream A) :
  stream_prefix (stream_prepend nel s) (ne_list_length nel) = ne_list_to_list nel.
Proof.
  by induction nel; [| cbn; f_equal].
Qed.

Lemma stream_prepend_prefix_l
  {A : Type}
  (l : ne_list A)
  (s : Stream A)
  : forall n : nat, n <= ne_list_length l ->
    stream_prefix (stream_prepend l s) n = list_prefix (ne_list_to_list l) n.
Proof.
  induction l; intros [| n] Hle; cbn; [done | | done |].
  - by cbn in Hle; replace n with 0 by lia.
  - by cbn in *; rewrite IHl; [| cbv in *; lia].
Qed.

Lemma stream_prepend_prefix_r
  {A : Type}
  (n : nat)
  : forall l : ne_list A, n >= ne_list_length l ->
    forall (s : Stream A),
      stream_prefix (stream_prepend l s) n
        =
      ne_list_to_list l ++ stream_prefix s (n - ne_list_length l).
Proof.
  induction n; intros [| a l] Hge s; cbn in *; [by lia.. | |].
  - by rewrite Nat.sub_0_r.
  - by rewrite <- IHn; [| cbv in *; lia].
Qed.

Lemma stream_concat_unroll {A} (a : ne_list A) (s : Stream (ne_list A)) :
  stream_concat (Cons a s) = stream_prepend a (stream_concat s).
Proof. by apply stream_eq_hd_tl. Qed.

Lemma stream_concat_prefix {A} (s : Stream (ne_list A)) n len
  (prefix := mjoin (List.map ne_list_to_list (stream_prefix s n)))
  : len = length prefix ->
    stream_prefix (stream_concat s) len = prefix.
Proof.
  intros ->; revert s prefix.
  induction n; [done |].
  intros [n0 s]; cbn.
  rewrite app_length.
  assert (Hge :
    length (ne_list_to_list n0) + length (mjoin (List.map ne_list_to_list (stream_prefix s n)))
    ≥ length (ne_list_to_list n0)) by lia.
  rewrite stream_concat_unroll, stream_prepend_prefix_r by done.
  rewrite <- IHn at 2.
  do 2 f_equal.
  rewrite Nat.add_comm.
  by apply Nat.add_sub.
Qed.
