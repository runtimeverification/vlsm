From VLSM.Lib Require Import Itauto.
From stdpp Require Import finite.
From Coq Require Import FinFun.
From VLSM.Lib Require Import Preamble.

(** * Utility lemmas about lists *)

(** A list is empty if it has no members. *)
Lemma empty_nil [X : Type] (l : list X) :
  (forall v, ~ In v l) -> l = [].
Proof.
  clear.
  destruct l as [| a]; cbn; [done |].
  by intro H; elim (H a); left.
Qed.

(** It is decidable whether a list is null or not. *)
#[export] Instance null_dec {S} (l : list S) : Decision (l = []).
Proof.
  by destruct l; [left | right].
Qed.

(**
  A list is either null or it can be decomposed into an initial prefix
  and a last element.
*)
Lemma has_last_or_null {S} (l : list S)
  : {l' : list S & {a : S | l = l' ++ (a :: nil)}} + {l = nil} .
Proof.
  destruct (null_dec l).
  - by right.
  - by left; apply exists_last in n.
Qed.

(**
  Destructs a list in <<l>> in either null or a prefix <<l'>> and
  a last element <<a>> with an equation <<Heq>> stating that <<l = l' ++ [a]>>.
*)
Ltac destruct_list_last l l' a Heq :=
 destruct (has_last_or_null l) as [[l' [a Heq]] | Heq]; rewrite Heq in *; swap 1 2.

Lemma last_not_null {S} (l : list S) (a : S)
  : l ++ [a] <> [].
Proof.
  by destruct l.
Qed.

Definition last_error {S} (l : list S) : option S :=
  match l with
  | [] => None
  | a :: t => Some (List.last t a)
  end.

Lemma unfold_last_hd {S} : forall (random a b : S) (l : list S),
  List.last (a :: (b :: l)) random = List.last (b :: l) random.
Proof. done. Qed.

Lemma swap_head_last {S} : forall (random a b c : S) (l : list S),
  List.last (a :: b :: c :: l) random = List.last (b :: a :: c :: l) random.
Proof.
  intros random h1 h2 s tl.
  by induction tl as [| hd tl IHl].
Qed.

Lemma remove_hd_last {X} :
  forall (hd1 hd2 d1 d2 : X) (tl : list X),
    List.last (hd1 :: hd2 :: tl) d1 = List.last (hd2 :: tl) d2.
Proof.
  induction tl; cbn; [done |].
  by destruct tl.
Qed.

Lemma unroll_last {S} : forall (random a : S) (l : list S),
  List.last (a :: l) random = List.last l a.
Proof.
  induction l; [done |].
  destruct l; [done |].
  by rewrite swap_head_last, unfold_last_hd, IHl, unfold_last_hd.
Qed.

Lemma last_app
  {A}
  (l1 l2 : list A)
  (def : A)
  : List.last (l1 ++ l2) def = List.last l2 (List.last l1 def).
Proof.
  generalize dependent def.
  induction l1; [done |].
  by intro def; rewrite <- !app_comm_cons, !unroll_last.
Qed.

Lemma last_map
  {A B}
  (f : A -> B)
  (h : A)
  (t : list A)
  (def : B)
  : List.last (map f (h :: t)) def = f (List.last t h).
Proof.
  revert def h.
  induction t; intros; [done |].
  by rewrite map_cons, !unroll_last.
Qed.

Lemma last_error_some {S}
  (l : list S)
  (s random : S)
  (Herr : last_error l = Some s) :
  List.last l random = s.
Proof.
  by destruct l; [| inversion Herr; apply unroll_last].
Qed.

Lemma incl_empty : forall A (l : list A),
  incl l nil -> l = nil.
Proof.
  intros A [] H; [done |].
  by destruct (H a); left.
Qed.

Lemma incl_singleton {A} : forall (l : list A) (a : A),
  incl l [a] ->
  forall b, In b l -> b = a.
Proof.
  intros. induction l; inversion H0; subst.
  - by destruct (H b); [left | done | inversion H1].
  - apply IHl; [| done].
    apply incl_tran with (a0 :: l); [| done].
    by apply incl_tl, incl_refl.
Qed.

Lemma Exists_first
  {A : Type}
  (l : list A)
  (P : A -> Prop)
  (Pdec : forall a : A, Decision (P a))
  (Hsomething : Exists P l)
  : exists (prefix : list A)
         (suffix : list A)
         (first : A),
         P first /\
         l = prefix ++ [first] ++ suffix /\
         ~ Exists P prefix.
Proof.
  induction l as [| h t]; [by inversion Hsomething |].
  destruct (decide (P h)).
  - exists [], t, h.
    rewrite Exists_nil.
    by itauto.
  - apply Exists_cons in Hsomething as []; [done |].
    destruct (IHt H) as (prefix & suffix & first & p & -> & Hnex).
    exists (h :: prefix), suffix, first.
    rewrite Exists_cons.
    by itauto.
Qed.

Lemma in_not_in : forall A (x y : A) (l : list A),
  x ∈ l ->
  y ∉ l ->
  x <> y.
Proof. by itauto congruence. Qed.

Definition inb {A} (Aeq_dec : forall x y : A, {x = y} + {x <> y}) (x : A) (xs : list A) :=
  if in_dec Aeq_dec x xs then true else false.

Lemma in_correct `{EqDecision X} :
  forall (l : list X) (x : X),
    In x l <-> inb decide_eq x l = true.
Proof.
  intros s msg.
  unfold inb.
  by destruct (in_dec _ _ _); itauto congruence.
Qed.

Lemma in_correct_refl `{EqDecision X} :
  forall (l : list X) (x : X),
    In x l <-> inb decide_eq x l.
Proof.
  intros s msg.
  by rewrite in_correct, Is_true_iff_eq_true.
Qed.

Lemma in_correct' `{EqDecision X} :
  forall (l : list X) (x : X),
    ~ In x l <-> inb decide_eq x l = false.
Proof.
  intros s msg.
  by rewrite in_correct, not_true_iff_false.
Qed.

Definition inclb
  `{EqDecision A}
  (l1 l2 : list A)
  : bool
  := forallb (fun x : A => inb decide_eq x l2) l1.

Lemma incl_correct `{EqDecision A}
  (l1 l2 : list A)
  : incl l1 l2 <-> inclb l1 l2 = true.
Proof.
  unfold inclb.
  rewrite forallb_forall.
  by split; intros Hincl x Hx; apply in_correct; apply Hincl.
Qed.

Lemma map_incl {A B} (f : B -> A) : forall s s',
  incl s s' ->
  incl (map f s) (map f s').
Proof.
  intros s s' Hincl fx Hin.
  apply in_map_iff .
  by apply in_map_iff in Hin as (x & Heq & Hin); eauto.
Qed.

Definition app_cons {A}
  (a : A)
  (l : list A)
  : [a] ++ l = a :: l
  := eq_refl.

Lemma append_nodup_left {A} :
  forall (l1 l2 : list A), List.NoDup (l1 ++ l2) -> List.NoDup l1.
Proof.
  induction l1; intros.
  - by constructor.
  - inversion H. apply IHl1 in H3. constructor; [| done].
    by rewrite in_app_iff in H2; itauto.
Qed.

Lemma append_nodup_right {A} :
  forall (l1 l2 : list A), List.NoDup (l1 ++ l2) -> List.NoDup l2.
Proof.
  by induction l1; cbn; intros; [| inversion H; auto].
Qed.

Lemma last_is_last {A} : forall (l : list A) (x dummy : A),
  List.last (l ++ [x]) dummy = x.
Proof.
  induction l; intros; [done |].
  rewrite <- app_comm_cons. rewrite <- (IHl x dummy) at 2.
  by destruct l.
Qed.

Lemma last_error_is_last {A} : forall (l : list A) (x : A),
  last_error (l ++ [x]) = Some x.
Proof.
  destruct l; cbn; [done |].
  by intros; rewrite last_is_last.
Qed.

(** Polymorphic list library *)

Fixpoint is_member {W} `{StrictlyComparable W} (w : W) (l : list W) : bool :=
  match l with
  | [] => false
  | hd :: tl => match compare w hd with
              | Eq => true
              | _ => is_member w tl
              end
  end.

Definition compareb {A} `{StrictlyComparable A} (a1 a2 : A) : bool :=
  match compare a1 a2 with
  | Eq => true
  | _ => false
  end.

Lemma is_member_correct {W} `{StrictlyComparable W}
  : forall l (w : W), is_member w l = true <-> In w l.
Proof.
  intros l w.
  induction l as [| hd tl IHl]; cbn.
  - by itauto congruence.
  - rewrite compare_asymmetric, <- compare_eq.
    by destruct (compare hd w) eqn: Hcmp; cbn; itauto congruence.
Qed.

Lemma is_member_correct' {W} `{StrictlyComparable W}
  : forall l (w : W), is_member w l = false <-> ~ In w l.
Proof.
  intros.
  rewrite <- is_member_correct.
  split; [by congruence |].
  by apply not_true_is_false.
Qed.

Lemma In_app_comm {X} : forall l1 l2 (x : X), In x (l1 ++ l2) <-> In x (l2 ++ l1).
Proof.
  by intros l1 l2 x; split; intro H_in;
    apply in_or_app; apply in_app_or in H_in as [cat | dog]; itauto.
Qed.

Lemma nth_error_last
  {A : Type}
  (l : list A)
  (n : nat)
  (Hlast : S n = length l)
  (_last : A)
  : nth_error l n = Some (List.last l _last).
Proof.
  generalize dependent _last.
  generalize dependent l.
  induction n; intros.
  - destruct l; inversion Hlast. symmetry in H0.
    by apply length_zero_iff_nil in H0; subst.
  - destruct l; inversion Hlast.
    specialize (IHn l H0 _last). rewrite unroll_last.
    simpl. rewrite IHn. f_equal.
    destruct l; inversion H0.
    by rewrite !unroll_last.
Qed.

Fixpoint list_suffix
  {A : Type}
  (l : list A)
  (n : nat)
  {struct n}
  : list A
  := match n, l with
    | 0, _ => l
    | _, [] => []
    | S n, a :: l => list_suffix l n
    end.

Lemma list_suffix_map
  {A B : Type}
  (f : A -> B)
  (l : list A)
  (n : nat)
  : List.map f (list_suffix l n) = list_suffix (List.map f l) n.
Proof.
  by revert l; induction n; intros [| a l]; [.. | apply IHn].
Qed.

Fixpoint list_prefix
  {A : Type}
  (l : list A)
  (n : nat)
  : list A
  := match n, l with
    | 0, _ => []
    | _, [] => []
    | S n, a :: l => a :: list_prefix l n
    end.

Lemma list_prefix_split
  {A : Type}
  (l left right : list A)
  (left_len : nat)
  (Hlen : left_len = length left)
  (Hsplit : l = left ++ right) :
  list_prefix l left_len = left.
Proof.
  generalize dependent l.
  generalize dependent left.
  generalize dependent right.
  generalize dependent left_len.
  induction left_len.
  - intros.
    symmetry in Hlen.
    rewrite length_zero_iff_nil in Hlen.
    rewrite Hlen.
    unfold list_prefix.
    by destruct l.
  - intros.
    destruct left; [done |].
    assert (left_len = length left).
    {
      simpl in Hlen.
      inversion Hlen.
      itauto.
    }
    specialize (IHleft_len right left H (left ++ right) eq_refl).
    rewrite Hsplit.
    simpl.
    by rewrite IHleft_len.
Qed.

Lemma list_prefix_map
  {A B : Type}
  (f : A -> B)
  (l : list A)
  (n : nat)
  : List.map f (list_prefix l n) = list_prefix (List.map f l) n.
Proof.
  by revert l; induction n; intros [| a l]; cbn; [.. | rewrite IHn].
Qed.

Lemma list_prefix_length
  {A : Type}
  (l : list A)
  (n : nat)
  (Hlen : n <= length l)
  : length (list_prefix l n) = n.
Proof.
  by revert l Hlen; induction n; intros [| a l] Hlen; cbn in *;
    [| | inversion Hlen | rewrite IHn; lia].
Qed.

Lemma list_suffix_length
  {A : Type}
  (l : list A)
  (n : nat)
  : length (list_suffix l n) = length l - n.
Proof.
  by revert l; induction n; intros [| a l]; [.. | apply IHn].
Qed.

Lemma list_prefix_prefix
  {A : Type}
  (l : list A)
  (n1 n2 : nat)
  (Hn : n1 <= n2)
  : list_prefix (list_prefix l n2) n1 = list_prefix l n1.
Proof.
  generalize dependent n1. generalize dependent n2.
  induction l; intros [| n2] [| n1] Hn; [done .. | by inversion Hn | done |].
  by simpl; f_equal; apply IHl; lia.
Qed.

Lemma list_prefix_suffix
  {A : Type}
  (l : list A)
  (n : nat)
  : list_prefix l n ++ list_suffix l n = l.
Proof.
  by revert n; induction l; intros [| n]; cbn; [.. | rewrite IHl].
Qed.

Lemma prefix_of_list_prefix
  {A : Type}
  (l : list A)
  (n : nat)
  : list_prefix l n `prefix_of` l.
Proof. by eexists; symmetry; apply list_prefix_suffix. Qed.

Definition list_segment
  {A : Type}
  (l : list A)
  (n1 n2 : nat)
  := list_suffix (list_prefix l n2) n1.

Lemma list_prefix_segment_suffix
  {A : Type}
  (l : list A)
  (n1 n2 : nat)
  (Hn : n1 <= n2)
  : list_prefix l n1 ++ list_segment l n1 n2 ++ list_suffix l n2 = l.
Proof.
  rewrite <- (list_prefix_suffix l n2) at 4.
  rewrite app_assoc.
  f_equal.
  unfold list_segment.
  rewrite <- (list_prefix_suffix (list_prefix l n2) n1) at 2.
  f_equal.
  symmetry.
  by apply list_prefix_prefix.
Qed.

Definition Forall_hd
  {A : Type}
  {P : A -> Prop}
  {a : A}
  {l : list A}
  (Hs : Forall P (a :: l))
  : P a.
Proof.
  by inversion Hs.
Defined.

Definition Forall_tl
  {A : Type}
  {P : A -> Prop}
  {a : A}
  {l : list A}
  (Hs : Forall P (a :: l))
  : Forall P l.
Proof.
  by inversion Hs.
Defined.

Fixpoint list_annotate
  {A : Type}
  (P : A -> Prop)
  {Pdec : forall a, Decision (P a)}
  (l : list A)
  (Hs : Forall P l)
  : list (dsig P).
Proof.
  destruct l as [| a l].
  - by exact [].
  - by exact ((dexist a (Forall_hd Hs)) :: list_annotate A P Pdec l (Forall_tl Hs)).
Defined.

Lemma list_annotate_length
  {A : Type}
  (P : A -> Prop)
  {Pdec : forall a, Decision (P a)}
  (l : list A)
  (Hs : Forall P l)
  : length (list_annotate P l Hs) = length l.
Proof.
  by induction l; cbn; [| rewrite IHl].
Qed.

Lemma list_annotate_pi
  {A : Type}
  (P : A -> Prop)
  {Pdec : forall a, Decision (P a)}
  (l : list A)
  (Hs : Forall P l)
  (Hs' : Forall P l)
  : list_annotate P l Hs = list_annotate P l Hs'.
Proof.
  revert Hs Hs'.
  induction l; [done |].
  intros; simpl.
  by f_equal; [apply dsig_eq | apply IHl].
Qed.

Lemma list_annotate_eq
  {A : Type}
  (P : A -> Prop)
  {Pdec : forall a, Decision (P a)}
  (l1 : list A)
  (Hl1 : Forall P l1)
  (l2 : list A)
  (Hl2 : Forall P l2)
  : list_annotate P l1 Hl1 = list_annotate P l2 Hl2 <-> l1 = l2.
Proof.
  split; [| intro; subst; apply list_annotate_pi].
  revert Hl1 l2 Hl2.
  induction l1; destruct l2; simpl; intros; [done.. |].
  inversion H.
  apply IHl1 in H2.
  by subst.
Qed.

Lemma list_annotate_unroll
  {A : Type}
  (P : A -> Prop)
  {Pdec : forall a, Decision (P a)}
  (a : A)
  (l : list A)
  (Hs : Forall P (a :: l))
  : list_annotate P (a :: l) Hs = dexist a (Forall_hd Hs) ::  list_annotate P l (Forall_tl Hs).
Proof. done. Qed.

Lemma list_annotate_app
  {A : Type}
  (P : A -> Prop)
  {Pdec : forall a, Decision (P a)}
  (l1 l2 : list A)
  (Hs : Forall P (l1 ++ l2)) :
    list_annotate P (l1 ++ l2) Hs =
    list_annotate P l1 (proj1 (proj1 (@Forall_app _ P l1 l2) Hs)) ++
    list_annotate P l2 (proj2 (proj1 (@Forall_app _ P l1 l2) Hs)).
Proof.
  induction l1; cbn; [by apply list_annotate_pi |].
  f_equal; [by apply dsig_eq |].
  by rewrite IHl1; f_equal; apply list_annotate_pi.
Qed.

Lemma nth_error_list_annotate
  {A : Type}
  (P : A -> Prop)
  (Pdec : forall a, Decision (P a))
  (l : list A)
  (Hs : Forall P l)
  (n : nat)
  : exists (oa : option (dsig P)),
    nth_error (list_annotate P l Hs) n = oa
    /\ option_map (@proj1_sig _ _) oa = nth_error l n.
Proof.
  generalize dependent l.
  induction n; intros [| a l] Hs.
  - by exists None.
  - inversion Hs; subst. exists (Some (dexist a (Forall_hd Hs))).
    by rewrite list_annotate_unroll.
  - by exists None.
  - by rewrite list_annotate_unroll; eauto.
Qed.

Fixpoint nth_error_filter_index
  {A} P `{forall (x : A), Decision (P x)}
  (l : list A)
  (n : nat)
  :=
  match l with
  | [] => None
  | a :: l =>
    if decide (P a) then
      match n with
      | 0 => Some 0
      | S n => option_map S (nth_error_filter_index P l n)
      end
    else
      option_map S (nth_error_filter_index P l n)
  end.

Lemma nth_error_filter_index_le
  {A} P `{forall (x : A), Decision (P x)}
  (l : list A)
  (n1 n2 : nat)
  (Hle : n1 <= n2)
  (in1 in2 : nat)
  (Hin1 : nth_error_filter_index P l n1 = Some in1)
  (Hin2 : nth_error_filter_index P l n2 = Some in2)
  : in1 <= in2.
Proof.
  generalize dependent in2.
  generalize dependent in1.
  generalize dependent n2.
  generalize dependent n1.
  induction l; intros; [by inversion Hin1 |].
  simpl in Hin1. simpl in Hin2.
  destruct (decide (P a)).
  - destruct n1; destruct n2.
    + by inversion Hin1; inversion Hin2; subst.
    + by destruct (nth_error_filter_index P l n2)
      ; inversion Hin1; inversion Hin2; subst; lia.
    + by inversion Hle.
    + destruct in1, in2; [lia | lia | |].
      * by destruct (nth_error_filter_index P l n2); inversion Hin2.
      * assert (Hle' : n1 <= n2) by lia.
        specialize (IHl n1 n2 Hle').
        destruct (nth_error_filter_index P l n1) eqn: Hin1'; inversion Hin1;
        subst; clear Hin1.
        destruct (nth_error_filter_index P l n2) eqn: Hin2'; inversion Hin2
        ; subst; clear Hin2.
        by specialize (IHl in1 eq_refl in2 eq_refl); lia.
  - specialize (IHl n1 n2 Hle).
    destruct (nth_error_filter_index P l n1) eqn: Hin1'; inversion Hin1
    ; subst; clear Hin1.
    destruct (nth_error_filter_index P l n2) eqn: Hin2'; inversion Hin2
    ; subst; clear Hin2.
    by specialize (IHl n0 eq_refl n3 eq_refl); lia.
Qed.

Fixpoint Forall_filter
  {A : Type}
  (P : A -> Prop)
  {Pdec : forall a : A, Decision (P a)}
  (l : list A) : Forall P (filter P l).
Proof.
  destruct l; cbn; [done |].
  by destruct (decide (P a)); eauto.
Defined.

(**
  Produces the sublist of elements of a list filtered by a decidable predicate
  each of them paired with the proof that it satisfies the predicate.
*)
Definition filter_annotate
  {A : Type}
  (P : A -> Prop)
  {Pdec : forall a : A, Decision (P a)}
  (l : list A) : list (dsig P) :=
  list_annotate _ _ (Forall_filter P l).

Definition filter_annotate_length
  {A : Type}
  (P : A -> Prop)
  {Pdec : forall a : A, Decision (P a)}
  (l : list A)
  : length (filter_annotate P l) = length (filter P l) :=
  list_annotate_length _ _ (Forall_filter P l).

Lemma filter_annotate_unroll
  {A : Type}
  (P : A -> Prop)
  {Pdec : forall a : A, Decision (P a)}
  (a : A)
  (l : list A)
  : filter_annotate P (a :: l) =
    let fa := filter_annotate P l in
    match decide (P a) with
    | left pa => dexist _ pa :: fa
    | _ => fa
    end.
Proof.
  by cbn; case_decide.
Qed.

Lemma filter_annotate_app
  {A : Type}
  (P : A -> Prop)
  {Pdec : forall a : A, Decision (P a)}
  (l1 l2 : list A)
  : filter_annotate P (l1 ++ l2) = filter_annotate P l1 ++ filter_annotate P l2.
Proof.
  induction l1; [done |].
  by simpl; rewrite! filter_annotate_unroll, IHl1; case_decide.
Qed.

(**
  Filters a list through a predicate, then transforms each element using a
  function which depends on the fact that the predicate holds.
*)
Definition list_filter_map
  {A B : Type}
  (P : A -> Prop)
  {Pdec : forall a, Decision (P a)}
  (f : dsig P -> B)
  (l : list A)
  : list B :=
  map f (filter_annotate P l).

Lemma list_filter_map_app
  {A B : Type}
  (P : A -> Prop)
  {Pdec : forall a, Decision (P a)}
  (f : dsig P -> B)
  (l1 l2 : list A)
  : list_filter_map P f (l1 ++ l2) = list_filter_map P f l1 ++ list_filter_map P f l2.
Proof.
  by unfold list_filter_map; rewrite filter_annotate_app, map_app.
Qed.

Lemma list_prefix_nth
  {A : Type}
  (s : list A)
  (n : nat)
  (i : nat)
  (Hi : i < n)
  : nth_error (list_prefix s n) i = nth_error s i.
Proof.
  revert s n Hi.
  induction i; intros [| a s] [| n] Hi; try done.
  - by inversion Hi.
  - by inversion Hi.
  - by cbn; rewrite (IHi s n); [| lia].
Qed.

Lemma nth_error_length
  {A : Type}
  (l : list A)
  (n : nat)
  (a : A)
  (Hnth : nth_error l n = Some a)
  : S n <= length l.
Proof.
  revert l a Hnth.
  by induction n; intros [| a l] b Hnth; cbn; inversion Hnth;
    [| specialize (IHn l b H0)]; lia.
Qed.

Lemma list_prefix_nth_last
  {A : Type}
  (l : list A)
  (n : nat)
  (nth : A)
  (Hnth : nth_error l n = Some nth)
  (_last : A)
  : nth = List.last (list_prefix l (S n)) _last.
Proof.
  specialize (nth_error_length l n nth Hnth); intro Hlen.
  specialize (list_prefix_length l (S n) Hlen); intro Hpref_len.
  symmetry in Hpref_len.
  specialize (list_prefix_nth l (S n) n); intro Hpref.
  rewrite <- Hpref in Hnth; [| by constructor].
  specialize (nth_error_last (list_prefix l (S n)) n Hpref_len _last); intro Hlast.
  by rewrite Hlast in Hnth; inversion Hnth.
Qed.

Lemma list_suffix_nth
  {A : Type}
  (s : list A)
  (n : nat)
  (i : nat)
  (Hi : n <= i)
  : nth_error (list_suffix s n) (i - n) = nth_error s i.
Proof.
  revert s n Hi.
  induction i; intros [| a s] [| n] Hi; cbn; try done.
  - by inversion Hi.
  - by apply nth_error_None; cbn; lia.
  - by apply IHi; lia.
Qed.

Lemma list_suffix_last
  {A : Type}
  (l : list A)
  (i : nat)
  (Hlt : i < length l)
  (_default : A)
  : List.last (list_suffix l i) _default  = List.last l _default.
Proof.
  revert l Hlt; induction i; intros [| a l] Hlt; [done.. |].
  simpl in Hlt.
  assert (Hlt' : i < length l) by lia.
  specialize (IHi l Hlt').
  rewrite unroll_last. simpl.
  rewrite IHi.
  destruct l.
  - by inversion Hlt; lia.
  - by rewrite unroll_last, unroll_last.
Qed.

Lemma list_suffix_last_default
  {A : Type}
  (l : list A)
  (i : nat)
  (Hlast : i = length l)
  (_default : A)
  : List.last (list_suffix l i) _default  = _default.
Proof.
  revert l Hlast; induction i; intros [| a l] Hlast; [done.. |].
  by apply IHi; inversion Hlast.
Qed.

Lemma list_segment_nth
  {A : Type}
  (l : list A)
  (n1 n2 : nat)
  (Hn : n1 <= n2)
  (i : nat)
  (Hi1 : n1 <= i)
  (Hi2 : i < n2)
  : nth_error (list_segment l n1 n2) (i - n1) = nth_error l i.
Proof.
  unfold list_segment.
  rewrite list_suffix_nth; [| done].
  by apply list_prefix_nth.
Qed.

Lemma list_segment_app
  {A : Type}
  (l : list A)
  (n1 n2 n3 : nat)
  (H12 : n1 <= n2)
  (H23 : n2 <= n3)
  : list_segment l n1 n2 ++ list_segment l n2 n3 = list_segment l n1 n3.
Proof.
  assert (Hle : n1 <= n3) by lia.
  specialize (list_prefix_segment_suffix l n1 n3 Hle); intro Hl1.
  specialize (list_prefix_segment_suffix l n2 n3 H23); intro Hl2.
  rewrite <- Hl2 in Hl1 at 4. clear Hl2.
  repeat rewrite app_assoc in Hl1.
  apply app_inv_tail in Hl1.
  specialize (list_prefix_suffix (list_prefix l n2) n1); intro Hl2.
  specialize (list_prefix_prefix l n1 n2 H12); intro Hl3.
  rewrite Hl3 in Hl2.
  rewrite <- Hl2 in Hl1.
  rewrite <- app_assoc in Hl1.
  by apply app_inv_head in Hl1.
Qed.

Lemma list_segment_singleton
  {A : Type}
  (l : list A)
  (n : nat)
  (a : A)
  (Hnth : nth_error l n = Some a)
  : list_segment l n (S n) = [a].
Proof.
  unfold list_segment.
  assert (Hle : S n <= length l)
    by (apply nth_error_length in Hnth; done).
  assert (Hlt : n < length (list_prefix l (S n)))
    by (rewrite list_prefix_length; try constructor; done).
  specialize (list_suffix_last (list_prefix l (S n)) n Hlt a); intro Hlast1.
  specialize (list_prefix_nth_last l n a Hnth a); intro Hlast2.
  rewrite <- Hlast2 in Hlast1.
  specialize (list_suffix_length (list_prefix l (S n)) n).
  rewrite list_prefix_length; [| done].
  intro Hlength.
  assert (Hs : S n - n = 1) by lia.
  rewrite Hs in Hlength.
  remember (list_suffix (list_prefix l (S n)) n) as x.
  clear -Hlength Hlast1.
  destruct x; inversion Hlength.
  destruct x; inversion H0.
  by simpl in Hlast1; subst.
Qed.

Lemma nth_error_map
  {A B : Type}
  (f : A -> B)
  (l : list A)
  (n : nat)
  : nth_error (List.map f l) n = option_map f (nth_error l n).
Proof.
  by revert n; induction l; intros [| n]; firstorder.
Qed.

Lemma exists_finite
  `{finite.Finite index}
  (P : index -> Prop)
  : (exists n : index, P n) <-> Exists P (enum index).
Proof.
  rewrite Exists_exists; split.
  - by intros [n Hn]; eexists; split; [apply elem_of_enum |].
  - by intros (n & _ & Hn); eexists.
Qed.

Definition map_option
  {A B : Type}
  (f : A -> option B)
  : list A -> list B
  :=
  fold_right
    (fun x lb =>
      match f x with
      | None => lb
      | Some b => b :: lb
      end)
    [].

Lemma map_option_app
  {A B : Type}
  (f : A -> option B)
  l1 l2
  : map_option f (l1 ++ l2) = map_option f l1 ++ map_option f l2.
Proof.
  induction l1; [done |].
  cbn; rewrite IHl1.
  by destruct (f a).
Qed.

Lemma map_option_app_rev
  {A B : Type}
  (f : A -> option B)
  l l1' l2'
  (Happ_rev : map_option f l = l1' ++ l2')
  : exists l1 l2, l = l1 ++ l2 /\ map_option f l1 = l1' /\ map_option f l2 = l2'.
Proof.
  revert l1' l2' Happ_rev.
  induction l; intros.
  - symmetry in Happ_rev.
    apply app_eq_nil in Happ_rev as [Hl1' Hl2']; subst.
    by exists [], [].
  - simpl in Happ_rev.
    destruct (f a) eqn: Hfa; swap 1 2.
    + destruct (IHl _ _ Happ_rev) as [_l1 [l2 [-> [<- <-]]]].
      by exists (a :: _l1), l2; cbn; rewrite Hfa.
    + destruct l1' as [| _b l1']; swap 1 2.
      * change (_b :: l1') with ([_b] ++ l1') in Happ_rev.
        rewrite <- app_assoc in Happ_rev. inversion Happ_rev.
        subst _b.
        specialize (IHl _ _ H1) as [_l1 [l2 [-> [<- <-]]]].
        by exists (a :: _l1), l2; cbn; rewrite Hfa.
      * simpl in Happ_rev. subst.
        by exists [], (a :: l); cbn; rewrite Hfa.
Qed.

Lemma map_option_length
  {A B : Type}
  (f : A -> option B)
  (l : list A)
  (Hfl : Forall (fun a => f a <> None) l)
  : length (map_option f l) = length l.
Proof.
  induction l; [done |].
  inversion Hfl; subst.
  specialize (IHl H2); cbn.
  by destruct (f a); cbn; congruence.
Qed.

Lemma map_option_nth
  {A B : Type}
  (f : A -> option B)
  (l : list A)
  (Hfl : Forall (fun a => f a <> None) l)
  (n := length l)
  (i : nat)
  (Hi : i < n)
  (dummya : A)
  (dummyb : B)
  : Some (nth i (map_option f l) dummyb) = f (nth i l dummya).
Proof.
  generalize dependent i.
  induction l; intros; simpl in *; [lia |].
  inversion Hfl; subst.
  destruct (f a) eqn: Hfa; [| done].
  destruct i; firstorder.
  by apply H; lia.
Qed.

(** [map_option] can be expressed as a [list_filter_map]. *)
Lemma map_option_as_filter
  {A B : Type}
  (f : A -> option B)
  (l : list A)
  : map_option f l = list_filter_map (is_Some ∘ f) (fun x => is_Some_proj (proj2_dsig x)) l.
Proof.
  induction l using rev_ind; [done |].
  rewrite map_option_app, IHl, list_filter_map_app; cbn; clear IHl.
  destruct (decide _).
  - by cbv; destruct i as [? ->].
  - by destruct (f x); [elim n |].
Qed.

Lemma map_option_Forall :
  forall {A B : Type} (f : A -> option B) (l : list A),
    Forall (fun x => ~ is_Some (f x)) l ->
      map_option f l = [].
Proof.
  induction 1; cbn; [done |].
  by destruct (f x); [contradict H |].
Qed.

Lemma elem_of_map_option :
  forall {A B : Type} (f : A -> option B) (l : list A) (y : B),
    y ∈ map_option f l <-> exists x : A, x ∈ l /\ f x = Some y.
Proof.
  induction l as [| h t]; cbn; intros y;
    [by setoid_rewrite elem_of_nil; firstorder |].
  destruct (f h) eqn: Heq.
  - setoid_rewrite elem_of_cons.
    split.
    + intros [-> | Hin]; [by exists h; itauto |].
      apply IHt in Hin as (x & Hinx & Hfx).
      by exists x; itauto.
    + intros (x & [-> | Hin] & Hfx); rewrite IHt.
      * by left; congruence.
      * by right; exists x.
  - setoid_rewrite elem_of_cons.
    rewrite IHt.
    by firstorder congruence.
Qed.

Lemma NoDup_map_option :
  forall {A B : Type} (f : A -> option B) (l : list A),
    (forall a1 a2 : A, is_Some (f a1) -> is_Some (f a2) -> f a1 = f a2 -> a1 = a2) ->
      NoDup l -> NoDup (map_option f l).
Proof.
  induction l as [| h t]; cbn; [by constructor |].
  intros Hinj Hnd; inversion Hnd; subst; clear Hnd.
  destruct (f h) eqn: Heq; [| by apply IHt].
  constructor; [| by apply IHt].
  intros Hin; apply elem_of_map_option in Hin as (x & Hinx & Hfx).
  assert (x = h) by (apply Hinj; [done.. | congruence]).
  by congruence.
Qed.

(** Unpack list of [option A] into list of [A]. *)
Definition cat_option {A : Type} : list (option A) -> list A :=
  @map_option (option A) A id.

Example cat_option1 : cat_option [Some 1; Some 5; None; Some 6; None] = [1; 5; 6].
Proof. by itauto. Qed.

Lemma cat_option_length
  {A : Type}
  (l : list (option A))
    (Hfl : Forall (fun a => a <> None) l)
  : length (cat_option l) = length l.
Proof.
  by apply map_option_length; itauto.
Qed.

Lemma cat_option_length_le
  {A : Type}
  (l : list (option A))
  : length (cat_option l) <= length l.
Proof.
  induction l; cbn.
  - by itauto.
  - by destruct (id a) eqn: eq_id; simpl in *; subst a; simpl; lia.
Qed.

Lemma cat_option_app
  {A : Type}
  (l1 l2 : list (option A)) :
  cat_option (l1 ++ l2) = cat_option l1 ++ cat_option l2.
Proof.
  induction l1; cbn.
  - by itauto.
  - by destruct a; cbn in *; rewrite IHl1.
Qed.

Lemma cat_option_nth
  {A : Type}
  (l : list (option A))
  (Hfl : Forall (fun a => a <> None) l)
  (n := length l)
  (i : nat)
  (Hi : i < n)
  (dummya : A)
  : Some (nth i (cat_option l) dummya) = (nth i l (Some dummya)).
Proof.
  specialize (@map_option_nth (option A) A id l); cbn.
  intros.
  unfold id in *.
  by apply H; itauto.
Qed.

Lemma nth_error_eq
  {A : Type}
  (l1 l2 : list A)
  (Hnth : forall n : nat, nth_error l1 n = nth_error l2 n)
  : l1 = l2.
Proof.
  generalize dependent l2.
  induction l1; intros [| a2 l2] Hnth; [done | ..].
  - by specialize (Hnth 0); simpl in Hnth; inversion Hnth.
  - by specialize (Hnth 0); simpl in Hnth; inversion Hnth.
  - assert (H0 := Hnth 0); cbn in H0; inversion H0; subst.
    f_equal.
    apply IHl1.
    intro n.
    by apply (Hnth (S n)).
Qed.

Lemma in_fast
  {A : Type}
  (l : list A)
  (a : A)
  (b : A)
  (Hin : In a (b :: l))
  (Hneq : b <> a) :
  In a l.
Proof.
  by destruct Hin.
Qed.

Fixpoint one_element_decompositions
  {A : Type}
  (l : list A)
  : list (list A * A * list A)
  :=
  match l with
  | [] => []
  | a :: l' =>
    ([], a, l')
    :: map
      (fun t => match t with (l1, b, l2) => (a :: l1, b, l2) end)
      (one_element_decompositions l')
  end.

Lemma elem_of_one_element_decompositions
  {A : Type}
  (l : list A)
  (pre suf : list A)
  (x : A)
  : (pre, x, suf) ∈ one_element_decompositions l
  <-> pre ++ [x] ++ suf = l.
Proof.
  revert suf. revert x. revert pre.
  induction l; intros pre x suf; split; simpl; intro H.
  - by inversion H.
  - by destruct pre; inversion H.
  - inversion H; subst; [done |].
    apply elem_of_list_fmap in H2 as [x0 [Heq Hin]].
    destruct x0 as ((prex0, x0), sufx0).
    specialize (IHl prex0 x0 sufx0).
    apply IHl in Hin.
    by inversion Heq; subst.
  - destruct pre.
    + by inversion H; left.
    + right. apply elem_of_list_fmap.
      rewrite <- app_comm_cons in H.
      inversion H. subst. clear H.
      exists (pre, x, suf).
      by rewrite IHl.
Qed.

Lemma in_one_element_decompositions_iff
  {A : Type}
  (l : list A)
  (pre suf : list A)
  (x : A)
  : In (pre, x, suf) (one_element_decompositions l)
  <-> pre ++ [x] ++ suf = l.
Proof.
  rewrite <- elem_of_list_In.
  by apply elem_of_one_element_decompositions.
Qed.

Definition two_element_decompositions
  {A : Type}
  (l : list A)
  : list (list A * A * list A * A * list A)
  :=
  flat_map
    (fun t =>
      match t with
        (l1, e1, l2) =>
        map
          (fun t => match t with (l2', e2, l3) => (l1, e1, l2', e2, l3) end)
          (one_element_decompositions l2)
      end)
    (one_element_decompositions l).

Lemma in_two_element_decompositions_iff
  {A : Type}
  (l : list A)
  (pre mid suf : list A)
  (x y : A)
  : In (pre, x, mid, y, suf) (two_element_decompositions l)
  <-> pre ++ [x] ++ mid ++ [y] ++ suf = l.
Proof.
  unfold two_element_decompositions.
  rewrite in_flat_map.
  split.
  - intros [((pre', x'), sufx) [Hdecx Hin]].
    apply in_map_iff in Hin.
    destruct Hin as [((mid', y'), suf') [Hdec Hin]].
    inversion Hdec. subst. clear Hdec.
    apply in_one_element_decompositions_iff in Hdecx.
    apply in_one_element_decompositions_iff in Hin.
    by subst.
  - remember (mid ++ [y] ++ suf) as sufx.
    intro H.
    exists (pre, x, sufx). apply in_one_element_decompositions_iff in H.
    split; [done |].
    apply in_map_iff. exists (mid, y, suf).
    by rewrite in_one_element_decompositions_iff.
Qed.

Lemma order_decompositions
  {A : Type}
  (pre1 suf1 pre2 suf2 : list A)
  (Heq : pre1 ++ suf1 = pre2 ++ suf2)
  : pre1 = pre2
  \/ (exists suf1', pre1 = pre2 ++ suf1')
  \/ (exists suf2', pre2 = pre1 ++ suf2').
Proof.
  remember (pre1 ++ suf1) as l.
  revert pre1 suf1 pre2 suf2 Heql Heq.
  induction l; intros.
  - left. symmetry in Heql, Heq.
    by apply app_nil in Heql as [-> ->], Heq as [-> ->].
  - destruct pre1 as [| a1 pre1]; destruct pre2 as [| a2 pre2]. 1-3: eauto.
    inversion Heql; subst a1; clear Heql.
    inversion Heq; subst a2; clear Heq.
    by destruct (IHl pre1 suf1 pre2 suf2 H1 H2)
      as [Heq | [[suf1' Hgt] | [suf2' Hlt]]]; subst; eauto.
Qed.

Lemma list_max_exists
   (l : list nat)
   (nz : list_max l > 0) :
   In (list_max l) l.
Proof.
  induction l.
  - by simpl in nz; lia.
  - simpl in *.
    destruct (a <=? (list_max l)) eqn: eq_leb.
    + assert (Nat.max a (list_max l) = list_max l) by lia.
      by itauto congruence.
    + assert (Nat.max a (list_max l) = a) by lia.
      by rewrite H; left.
Qed.

Lemma list_max_exists2
   (l : list nat)
   (Hne : l <> []) :
   In (list_max l) l.
Proof.
  destruct (list_max l) eqn: eq_max.
  - destruct l; [by itauto congruence |].
    specialize (list_max_le (n :: l) 0) as Hle.
    destruct Hle as [Hle _].
    rewrite eq_max in Hle. spec Hle. apply Nat.le_refl.
    rewrite Forall_forall in Hle.
    specialize (Hle n). spec Hle; [left |].
    by simpl; lia.
  - specialize (list_max_exists l) as Hmax.
    spec Hmax; [lia |].
    by rewrite <- eq_max.
Qed.

(**
  Returns all values which occur with maximum frequency in the given list.
  Note that these values are returned with their original multiplicity.
*)
Definition mode
  `{EqDecision A}
  (l : list A) : list A  :=
  let mode_value := list_max (List.map (count_occ decide_eq l) l) in
  filter (fun a => (count_occ decide_eq l a) = mode_value) l.

Example mode1 : mode [1; 1; 2; 3; 3] = [1; 1; 3; 3].
Proof. by itauto. Qed.

(**
  Computes the list suff which satisfies <<pref ++ suff = l>> or
  reports that no such list exists.
*)
Fixpoint complete_prefix
  `{EqDecision A}
  (l pref : list A) : option (list A) :=
  match l, pref with
  | l , [] => Some l
  | [], (b :: pref') => None
  | (a :: l'), (b :: pref') => match (decide_eq a b) with
                               | right _ => None
                               | _ => let res' := complete_prefix l' pref' in
                                      match res' with
                                      | None => None
                                      | Some s => Some s
                                      end
                               end
  end.

Example complete_prefix_some : complete_prefix [1; 2; 3; 4] [1; 2] = Some [3; 4].
Proof. by itauto. Qed.
Example complete_prefix_none : complete_prefix [1; 2; 3; 4] [1; 3] = None.
Proof. by itauto. Qed.

Lemma complete_prefix_empty
  `{EqDecision A}
  (l : list A) :
  complete_prefix l [] = Some l.
Proof.
  induction l; cbn; [done |].
  by destruct (complete_prefix l []).
Qed.

Lemma complete_prefix_correct
  `{EqDecision A}
  (l pref suff : list A) :
  l = pref ++ suff <->
  complete_prefix l pref = Some suff.
Proof.
  split.
  - generalize dependent suff.
    generalize dependent pref.
    induction l.
    + intros. simpl in *.
      by destruct pref, suff.
    + intros.
      destruct pref; cbn.
      * by rewrite H.
      * inversion H; subst.
        rewrite decide_True; [| done].
        by rewrite (IHl pref suff).
  - generalize dependent suff.
    generalize dependent pref.
    induction l; intros.
    + by destruct pref; destruct suff;
        simpl in H; itauto (auto || congruence).
    + destruct pref eqn: eq_pref.
      rewrite complete_prefix_empty in H.
      inversion H.
      itauto.
      simpl.
      simpl in H.
      destruct (decide (a = a0)); [| done].
      destruct (complete_prefix l l0) eqn: eq_cp; [| done].
      inversion H; subst.
      f_equal.
      specialize (IHl l0 suff).
      spec IHl; [| done].
      by rewrite eq_cp.
Qed.

(**
  Computes the list <<pref>> which satisfies <<pref ++ suff = l>> or
  reports that no such list exists.
*)
Definition complete_suffix
  `{EqDecision A}
  (l suff : list A) : option (list A) :=
  let res := complete_prefix (rev l) (rev suff) in
  match res with
  | None => None
  | Some ls => Some (rev ls)
  end.

Example complete_suffix_some : complete_suffix [1; 2; 3; 4] [3; 4] = Some [1; 2].
Proof. by itauto. Qed.

Lemma complete_suffix_correct
  `{EqDecision A}
  (l pref suff : list A) :
  l = pref ++ suff <->
  complete_suffix l suff = Some pref.
Proof.
  unfold complete_suffix.
  split.
  - intros.
    destruct (complete_prefix (rev l) (rev suff)) eqn: eq_c.
    apply complete_prefix_correct in eq_c.
    rewrite H in eq_c.
    rewrite rev_app_distr in eq_c.
    assert (l0 = rev pref) by (apply app_inv_head in eq_c; done).
    rewrite H0.
    f_equal.
    apply rev_involutive.
    assert (rev l = rev suff ++ rev pref) by (subst; apply rev_app_distr).
    apply complete_prefix_correct in H0.
    by rewrite eq_c in H0.
  - destruct (complete_prefix (rev l) (rev suff)) eqn: eq_c; [| done].
    inversion_clear 1.
    apply complete_prefix_correct in eq_c.
    apply rev_eq_app in eq_c.
    by rewrite rev_involutive in eq_c.
Qed.

Lemma complete_suffix_empty
  `{EqDecision A}
  (l : list A) :
  complete_suffix l [] = Some l.
Proof.
  unfold complete_suffix. simpl.
  rewrite complete_prefix_empty.
  f_equal.
  by apply rev_involutive.
Qed.

(** Elements belonging to first type in a list of a sum type. *)
Definition list_sum_project_left
  {A B : Type}
  (x : list (A + B))
  : list A
  :=
  map_option sum_project_left x.

(** Elements belonging to second type in a list of a sum type. *)
Definition list_sum_project_right
  {A B : Type}
  (x : list (A + B))
  : list B
  :=
  map_option sum_project_right x.

Lemma fold_right_andb_false l :
  fold_right andb false l = false.
Proof.
  induction l; cbn; [done |].
  by rewrite IHl, andb_false_r.
Qed.

Lemma sumbool_forall [A : Type] [P Q : A -> Prop] :
  (forall x : A, {P x} + {Q x}) -> forall l : list A, {Forall P l} + {Exists Q l}.
Proof.
  induction l.
  - by left; constructor.
  - by refine (if X a then if IHl then left _ else right _ else right _); constructor.
Qed.

Lemma list_sum_decrease [A : Type] (f g : A -> nat) (l : list A) :
  (forall a, In a l -> f a <= g a) -> Exists (fun a => f a < g a) l ->
  list_sum (map f l) < list_sum (map g l).
Proof.
  induction 2; cbn.
  - apply PeanoNat.Nat.add_lt_le_mono; [done |].
    induction l; cbn; [done |].
    by apply PeanoNat.Nat.add_le_mono; firstorder.
  - by apply PeanoNat.Nat.add_le_lt_mono; firstorder.
Qed.

(**
  Nearly the natural induction principle for [fold_left].
  Useful if you can think of [fold_left f] as transforming
  a list into a [B -> B] function, and can describe the
  effect with a [P : list A -> relation B].
  The assumption [Hstep] could be weakened by replacing [r]
  with [fold_left f l (f x a)], but that isn't useful in
  natural examples.
*)
Lemma fold_left_ind
      [A B : Type] (f : B -> A -> B) (P : list A -> B -> B -> Prop)
      (Hstart : forall x, P nil x x)
      (Hstep : forall x a l r,
          P l (f x a) r ->
          P (a :: l) x r) :
  forall l x, P l x (fold_left f l x).
Proof.
  induction l.
  apply Hstart.
  intro x.
  by apply Hstep, IHl.
Qed.

(**
  An induction principle for [fold_left] which
  decomposes the list from the right.
*)
Lemma fold_left_ind_rev
      [A B : Type] (f : B -> A -> B) (x0 : B)
      (P : list A -> B -> Prop)
      (Hstart : P nil x0)
      (Hstep : forall l a x, P l x -> P (l++a :: nil) (f x a)) :
  forall l, P l (fold_left f l x0).
Proof.
  induction l using rev_ind.
  - by apply Hstart.
  - by rewrite fold_left_app; apply Hstep.
Qed.

Section sec_suffix_quantifiers.

(** ** Quantifiers for all suffixes

  In this section we define list quantifiers similar to [Streams.ForAll] and
  [Streams.Exists] and prove several properties about them.

  Among the definitions, the more useful are [ForAllSuffix2] and [ExistsSuffix2]
  as they allow us to quantify over relations between consecutive elements.
*)

Context
  [A : Type]
  (P : list A -> Prop)
  .

Inductive ExistsSuffix : list A -> Prop :=
| SHere : forall l, P l -> ExistsSuffix l
| SFurther : forall a l, ExistsSuffix l -> ExistsSuffix (a :: l).

Inductive ForAllSuffix : list A -> Prop :=
| SNil : P [] -> ForAllSuffix []
| SHereAndFurther : forall a l, P (a :: l) -> ForAllSuffix l -> ForAllSuffix (a :: l).

Lemma fsHere : forall l, ForAllSuffix l -> P l.
Proof. by inversion 1. Qed.

Lemma fsFurther : forall a l, ForAllSuffix (a :: l) -> ForAllSuffix l.
Proof. by inversion 1. Qed.

Lemma ForAll_list_suffix : forall m x, ForAllSuffix x -> ForAllSuffix (list_suffix x m).
Proof.
  induction m; simpl; intros [] **; [done.. |].
  by apply fsFurther in H; apply IHm.
Qed.

Lemma ForAllSuffix_induction
  (Inv : list A -> Prop)
  (InvThenP : forall l, Inv l -> P l)
  (InvIsStable : forall a l, Inv (a :: l) -> Inv l)
  : forall l, Inv l -> ForAllSuffix l.
Proof.
  induction l; intros.
  - by constructor; apply InvThenP.
  - constructor.
    + by apply InvThenP.
    + by eapply IHl, InvIsStable.
Qed.

End sec_suffix_quantifiers.

Lemma ForAllSuffix_subsumption [A : Type] (P Q : list A -> Prop)
  (HPQ : forall l, P l -> Q l)
  : forall l, ForAllSuffix P l -> ForAllSuffix Q l.
Proof.
  by induction 1; constructor; auto.
Qed.

Definition ForAllSuffix1 [A : Type] (P : A -> Prop) : list A -> Prop :=
  ForAllSuffix (fun l => match l with | [] => True | a :: _ => P a end).

Lemma ForAllSuffix1_Forall [A : Type] (P : A -> Prop)
  : forall l, ForAllSuffix1 P l <-> Forall P l.
Proof.
  by split; induction 1; constructor; auto.
Qed.

Definition ExistsSuffix1 [A : Type] (P : A -> Prop) : list A -> Prop :=
  ExistsSuffix (fun l => match l with | [] => False | a :: _ => P a end).

Lemma ExistsSuffix1_Exists [A : Type] (P : A -> Prop)
  : forall l, ExistsSuffix1 P l <-> Exists P l.
Proof.
  split; induction 1.
  - by destruct l; [| left].
  - by right.
  - by left.
  - by right.
Qed.

Definition ForAllSuffix2 [A : Type] (R : A -> A -> Prop) : list A -> Prop :=
  ForAllSuffix (fun l => match l with | a :: b :: _ => R a b | _ => True end).

Lemma fsFurther2_transitive [A : Type] (R : A -> A -> Prop) {HT : Transitive R}
  : forall a b l, ForAllSuffix2 R (a :: b :: l) -> ForAllSuffix2 R (a :: l).
Proof.
  inversion 1. subst. destruct l.
  - by repeat constructor.
  - inversion H3; subst.
    by constructor; [transitivity b |].
Qed.

Lemma ForAllSuffix2_filter [A : Type] (R : A -> A -> Prop) `{HT : Transitive _ R}
  (P : A -> Prop) {Pdec : forall a, Decision (P a)}
  : forall l, ForAllSuffix2 R l -> ForAllSuffix2 R (filter P l).
Proof.
  induction l; [done |].
  intro Hl.
  unfold filter. simpl.
  spec IHl; [by apply fsFurther in Hl |].
  case_decide; [| done].
  constructor; [| done].
  clear IHl H.
  induction l; cbn; [done |].
  case_decide.
  - by inversion Hl.
  - by apply IHl; eapply fsFurther2_transitive.
Qed.

Lemma list_subseteq_tran : forall (A : Type) (l m n : list A),
 l ⊆ m -> m ⊆ n -> l ⊆ n.
Proof.
  intros A l m n Hlm Hmn x y.
  by apply Hmn, Hlm.
Qed.

#[export] Instance list_subseteq_dec `{EqDecision A} : RelDecision (@subseteq (list A) _).
Proof.
  intros x; induction x.
  - by left; apply list_subseteq_nil.
  - intro y; destruct (IHx y) as [Hsub | Hnsub].
    + destruct (decide (a ∈ y)).
      * by left; intros b Hb; inversion Hb; subst; [| apply Hsub].
      * by right; intro Hsub'; elim n; apply Hsub'; left.
    + right; intro Hsub; elim Hnsub.
      by intros b Hb; apply Hsub; right.
Qed.

Lemma elem_of_empty_nil [X : Type] (l : list X) :
  (forall v, v ∉ l) -> l = [].
Proof.
  destruct l as [| a]; [done |].
  by intro H; elim (H a); left.
Qed.

Lemma nodup_append_left {A} :
  forall (l1 l2 : list A), NoDup (l1 ++ l2) -> NoDup l1.
Proof.
  by intros l1 l2 [? _]%NoDup_app.
Qed.

Lemma subseteq_empty {A} : forall (l : list A),
  l ⊆ nil -> l = nil.
Proof.
  intros. destruct l; [done |].
  exfalso.
  specialize (H a (elem_of_list_here _ _)).
  by inversion H.
Qed.

Lemma NoDup_subseteq_length [A : Type]
  [l1 l2 : list A]
  (Hnodup : NoDup l1)
  (Hincl : l1 ⊆ l2)
  : length l1 <= length l2.
Proof.
  by apply submseteq_length, NoDup_submseteq.
Qed.

Lemma submseteq_tail_l [A] (x : A) l1 l2 :
  x :: l1 ⊆+ l2 -> l1 ⊆+ l2.
Proof.
  by apply submseteq_trans, submseteq_cons.
Qed.

Lemma submseteq_list_subseteq [A] (l1 l2 : list A) :
  l1 ⊆+ l2 -> l1 ⊆ l2.
Proof.
  by intros H ? Hx; eapply elem_of_submseteq.
Qed.

Lemma take_app_inv :
  forall [A : Type] (n : nat) (l l' : list A) (x : A),
    take n l = l' ++ [x] -> exists n' : nat, n = S n'.
Proof.
  induction n as [| n']; intros l l' x H.
  - by rewrite take_0 in H; apply app_cons_not_nil in H.
  - by exists n'.
Qed.

Lemma elem_of_list_prod :
  forall [A B : Type] (x : A) (y : B) (la : list A) (lb : list B),
    (x, y) ∈ list_prod la lb <-> x ∈ la /\ y ∈ lb.
Proof.
  intros.
  by rewrite elem_of_list_In, in_prod_iff, <- !elem_of_list_In.
Qed.

(** ** The function [lastn] and its properties *)

(** [lastn] returns a suffix of length <<n>> from the list <<l>>. *)
Definition lastn {A : Type} (n : nat) (l : list A) : list A :=
  rev (firstn n (rev l)).

(** If the list is [[]], then the result of [lastn] is also [[]]. *)
Lemma lastn_nil :
  forall {A : Type} (n : nat),
    lastn n (@nil A) = [].
Proof.
  by intros A n; unfold lastn; cbn; rewrite firstn_nil.
Qed.

(** If <<n>> is zero, then the result of [lastn] is [[]]. *)
Lemma lastn_0 :
  forall {A : Type} (l : list A),
    lastn 0 l = [].
Proof.
  by intros A l; unfold lastn; rewrite take_0.
Qed.

(** If <<n>> is greater than the length of the list, [lastn] returns the whole list. *)
Lemma lastn_ge :
  forall {A : Type} (n : nat) (l : list A),
    length l <= n -> lastn n l = l.
Proof.
  intros A n l Hge.
  unfold lastn.
  rewrite take_ge.
  - by rewrite rev_involutive.
  - by rewrite rev_length.
Qed.

(** [lastn] skips the prefix of the list as long as the suffix is long enough. *)
Lemma lastn_app_le :
  forall {A : Type} (n : nat) (l1 l2 : list A),
    n <= length l2 -> lastn n (l1 ++ l2) = lastn n l2.
Proof.
  intros A n l1 l2 Hlt.
  unfold lastn.
  rewrite rev_app_distr, take_app_le; [done |].
  by rewrite rev_length; lia.
Qed.

(** [lastn] either skips the head of the list or not, depending on how big a suffix we want. *)
Lemma lastn_cons :
  forall {A : Type} (n : nat) (h : A) (t : list A),
    lastn n (h :: t) = if decide (S (length t) <= n) then h :: t else lastn n t.
Proof.
  intros A n h t.
  case_decide; subst.
  - by rewrite lastn_ge; cbn; [| lia].
  - by rewrite (lastn_app_le _ [h] t); [| lia].
Qed.

(** If <<l1>> is a prefix of <<l2>>, then the reverse of <<l1>> is a suffix of <<l2>>. *)
Lemma suffix_rev :
  forall {A : Type} (l1 l2 : list A),
    prefix l1 l2 -> suffix (rev l1) (rev l2).
Proof.
  intros A l1 l2 [l ->].
  rewrite rev_app_distr.
  by exists (rev l).
Qed.

(**
  If <<n1>> is less than (or equal to) <<n2>>, then <<lastn n1 l>> is shorter than
  <<lastn n2 l>> and therefore is its suffix.
*)
Lemma suffix_lastn :
  forall {A : Type} (l : list A) (n1 n2 : nat),
    n1 <= n2 -> suffix (lastn n1 l) (lastn n2 l).
Proof.
  intros A l n1 n2 Hle.
  unfold lastn.
  apply suffix_rev.
  exists (take (n2 - n1) (drop n1 (rev l))).
  rewrite take_take_drop.
  by f_equal; lia.
Qed.

(** The length of <<lastn n l>> is the smaller of <<n>> and the length of <<l>>. *)
Lemma length_lastn :
  forall {A : Type} (n : nat) (l : list A),
    length (lastn n l) = min n (length l).
Proof.
  intros A n l.
  unfold lastn.
  by rewrite rev_length, take_length, rev_length.
Qed.

Program Definition not_null_element
  `{EqDecision A} [l : list A] (Hl : l <> []) : dsig (fun i => i ∈ l) :=
    dexist (is_Some_proj (proj2 (head_is_Some l) Hl)) _.
Next Obligation.
Proof.
  by intros A ? [| h t] ?; [| left].
Qed.

Program Definition element_of_subseteq
  `{EqDecision A} [l1 l2 : list A] (Hsub : l1 ⊆ l2)
  (di : dsig (fun i => i ∈ l1)) : dsig (fun i => i ∈ l2) :=
    dexist (` di) _.
Next Obligation.
Proof.
  by intros; cbn; destruct_dec_sig di i Hi Heq; subst; apply Hsub.
Qed.

Definition element_of_filter
  `{EqDecision A} [P : A -> Prop] `{forall x, Decision (P x)} [l : list A]
  : dsig (fun i => i ∈ filter P l) -> dsig (fun i => i ∈ l) :=
  element_of_subseteq (list_filter_subseteq P l).
