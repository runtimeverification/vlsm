From VLSM.Lib Require Import Itauto.
From stdpp Require Import prelude finite.
From Coq Require Import FinFun.
From VLSM.Lib Require Import Preamble.

(** * Utility: Lemmas About Lists *)

(**
  A list is either empty or it can be decomposed into an initial prefix
  and the last element.
*)
Lemma has_last_or_null :
  forall {A : Type} (l : list A),
    {l' : list A & {a : A | l = l' ++ (a :: nil)}} + {l = nil}.
Proof.
  destruct l.
  - by right.
  - by left; apply exists_last.
Qed.

(**
  Decompose a list in into a prefix <<l'>> and the last element <<a>>
  with an equation <<Heq>> stating that <<l = l' ++ [a]>>.
*)
Ltac destruct_list_last l l' a Heq :=
 destruct (has_last_or_null l) as [[l' [a Heq]] | Heq]; rewrite Heq in *; swap 1 2.

Lemma last_not_null :
  forall {A : Type} (l : list A) (a : A),
    l ++ [a] <> [].
Proof.
  by destruct l.
Qed.

(** Return the last element of the list if it's present and [None] otherwise. *)
Definition last_error {A : Type} (l : list A) : option A :=
  match l with
  | [] => None
  | a :: t => Some (List.last t a)
  end.

Lemma unfold_last_hd :
  forall {A : Type} (random a b : A) (l : list A),
    List.last (a :: b :: l) random = List.last (b :: l) random.
Proof. done. Qed.

Lemma swap_head_last :
  forall {A : Type} (random a b c : A) (l : list A),
    List.last (a :: b :: c :: l) random = List.last (b :: a :: c :: l) random.
Proof.
  by induction l.
Qed.

Lemma remove_hd_last :
  forall {A : Type} (hd1 hd2 d1 d2 : A) (tl : list A),
    List.last (hd1 :: hd2 :: tl) d1 = List.last (hd2 :: tl) d2.
Proof.
  induction tl; cbn; [done |].
  by destruct tl.
Qed.

Lemma unroll_last :
  forall {A : Type} (random a : A) (l : list A),
    List.last (a :: l) random = List.last l a.
Proof.
  induction l as [| h [| h' t]]; [done.. |].
  by rewrite swap_head_last, unfold_last_hd, IHl, unfold_last_hd.
Qed.

Lemma last_app :
  forall {A : Type} (l1 l2 : list A) (def : A),
    List.last (l1 ++ l2) def = List.last l2 (List.last l1 def).
Proof.
  induction l1; intros; [done |].
  by rewrite <- !app_comm_cons, !unroll_last.
Qed.

Lemma last_map :
  forall {A B : Type} (f : A -> B) (t : list A) (h : A) (def : B),
    List.last (map f (h :: t)) def = f (List.last t h).
Proof.
  induction t; intros; [done |].
  by rewrite map_cons, !unroll_last.
Qed.

Lemma last_error_some :
  forall {A : Type} (l : list A) (s random : A) (Herr : last_error l = Some s),
    List.last l random = s.
Proof.
  by destruct l; [| inversion 1; apply unroll_last].
Qed.

Lemma incl_singleton :
  forall {A : Type} (l : list A) (a : A),
    l ⊆ [a] -> forall b : A, b ∈ l -> b = a.
Proof.
  intros * Hsub * Hin.
  by apply elem_of_list_singleton, Hsub.
Qed.

Lemma Exists_first :
  forall {A : Type} (P : A -> Prop) (Pdec : forall a : A, Decision (P a)) (l : list A),
    Exists P l ->
    exists (prefix : list A) (suffix : list A) (first : A),
      P first /\
      l = prefix ++ [first] ++ suffix /\
      ~ Exists P prefix.
Proof.
  induction l as [| h t]; intros Hex; [by inversion Hex |].
  destruct (decide (P h)).
  - exists [], t, h.
    rewrite Exists_nil.
    by itauto.
  - apply Exists_cons in Hex as []; [done |].
    destruct (IHt H) as (prefix & suffix & first & p & -> & Hnex).
    exists (h :: prefix), suffix, first.
    rewrite Exists_cons.
    by itauto.
Qed.

Lemma map_list_subseteq :
  forall {A B : Type} (f : A -> B) (l1 l2 : list A),
    l1 ⊆ l2 -> map f l1 ⊆ map f l2.
Proof.
  unfold subseteq, list_subseteq.
  intros * Hsub b Hin.
  rewrite elem_of_list_fmap in Hin |- *.
  destruct Hin as (x & -> & Hin').
  exists x.
  by split; [| apply Hsub].
Qed.

Lemma app_cons {A} :
  forall (a : A) (l : list A),
    [a] ++ l = a :: l.
Proof. done. Qed.

Lemma last_error_is_last {A} :
  forall (l : list A) (x : A),
    last_error (l ++ [x]) = Some x.
Proof.
  intros [] x; cbn; [done |].
  by rewrite last_app.
Qed.

Lemma nth_error_last :
  forall {A : Type} (n : nat) (l : list A) (Hlast : S n = length l) (_last : A),
    nth_error l n = Some (List.last l _last).
Proof.
  intros.
  destruct_list_last l h t Heq; [by destruct n |].
  rewrite app_length in Hlast; cbn in Hlast.
  rewrite nth_error_app2, last_app by lia; cbn.
  by replace (n - length h) with 0 by lia.
Qed.

Lemma take_prefix :
  forall {A : Type} (l : list A) (n1 n2 : nat),
    n1 <= n2 -> take n1 (take n2 l) = take n1 l.
Proof.
  by intros; rewrite take_take, min_l.
Qed.

Lemma prefix_of_take :
  forall {A : Type} (l : list A) (n : nat),
    take n l `prefix_of` l.
Proof. by eexists; symmetry; apply take_drop. Qed.

(**
  Compute the sublist of list <<l>> which starts at index <<n1>>
  and ends before index <<n2>>.
  For example, <<list_segment [0; 1; 2; 3; 4; 5] 2 4 = [2; 3]>>.
*)
Definition list_segment {A : Type} (l : list A) (n1 n2 : nat) : list A :=
  drop n1 (take n2 l).

Lemma take_segment_suffix :
  forall {A : Type} (l : list A) (n1 n2 : nat),
    n1 <= n2 -> take n1 l ++ list_segment l n1 n2 ++ drop n2 l = l.
Proof.
  intros.
  unfold list_segment.
  rewrite <- (take_drop n2 l) at 4.
  rewrite <- (take_drop n1 (take n2 l)) at 2.
  by rewrite <- app_assoc, take_prefix.
Qed.

(**
  Annotate each element of a list with the proof that it satisfies the
  given decidable predicate.
*)
Fixpoint list_annotate
  {A : Type} {P : A -> Prop} {Pdec : forall a, Decision (P a)} {l : list A}
   : Forall P l -> list (dsig P) :=
  match l with
  | [] => fun _ => []
  | h :: t => fun Hs => dexist h (Forall_inv Hs) :: list_annotate (Forall_inv_tail Hs)
  end.

Section sec_list_annotate_props.

Context
  {A : Type}
  {P : A -> Prop}
  `{Pdec : forall a, Decision (P a)}
  .

Lemma list_annotate_length :
  forall (l : list A) (Hs : Forall P l),
    length (list_annotate Hs) = length l.
Proof.
  by induction l; cbn; intros; [| rewrite IHl].
Qed.

Lemma list_annotate_pi :
  forall (l : list A) (Hs : Forall P l) (Hs' : Forall P l),
    list_annotate Hs = list_annotate Hs'.
Proof.
  induction l; cbn; intros; [done |].
  by f_equal; [apply dsig_eq | apply IHl].
Qed.

Lemma list_annotate_eq :
  forall (l1 l2 : list A) (Hl1 : Forall P l1) (Hl2 : Forall P l2),
    list_annotate Hl1 = list_annotate Hl2 <-> l1 = l2.
Proof.
  split; [| by intros ->; apply list_annotate_pi].
  revert l2 Hl1 Hl2.
  induction l1 as [| h1 t1]; intros [| h2 t2] * Heq; [done.. |].
  inversion Heq; subst.
  by apply IHt1 in H1 as ->.
Qed.

Lemma list_annotate_app :
  forall (l1 l2 : list A) (Hs : Forall P (l1 ++ l2)),
    list_annotate Hs =
    list_annotate (proj1 (proj1 (@Forall_app _ P l1 l2) Hs)) ++
    list_annotate (proj2 (proj1 (@Forall_app _ P l1 l2) Hs)).
Proof.
  induction l1; cbn; intros; [by apply list_annotate_pi |].
  f_equal; [by apply dsig_eq |].
  by rewrite IHl1; f_equal; apply list_annotate_pi.
Qed.

Lemma nth_error_list_annotate :
  forall (n : nat) (l : list A) (Hs : Forall P l),
    exists (oa : option (dsig P)),
      nth_error (list_annotate Hs) n = oa /\ option_map (@proj1_sig _ _) oa = nth_error l n.
Proof.
  induction n as [| n']; intros [| h t] Hs; cbn.
  - by exists None.
  - inversion Hs; subst.
    by exists (Some (dexist h (Forall_inv Hs))).
  - by exists None.
  - by eauto.
Qed.

Lemma elem_of_list_annotate :
  forall (l : list A) (Hs : Forall P l) (a : {x : A | bool_decide (P x)}),
    a ∈ list_annotate Hs <-> `a ∈ l.
Proof.
  induction l; cbn; intros.
  - by rewrite !elem_of_nil.
  - by rewrite !elem_of_cons, IHl, (dsig_eq P a0); cbn.
Qed.

Lemma list_annotate_NoDup :
  forall (l : list A) (Hs : Forall P l),
    NoDup l -> NoDup (list_annotate Hs).
Proof.
  induction 1; cbn; constructor; [| by apply IHNoDup].
  by rewrite elem_of_list_annotate.
Qed.

Lemma list_annotate_forget :
  forall (l : list A) (Hs : Forall P l),
    map proj1_sig (list_annotate Hs) = l.
Proof.
  by induction l; cbn; intros; [| rewrite IHl].
Qed.

End sec_list_annotate_props.

(**
  Compute the index of the <<n>>-th element of the list that satisfies the
  predicate <<P>>.
*)
Fixpoint nth_error_filter_index
  {A : Type} (P : A -> Prop) `{forall (x : A), Decision (P x)}
  (l : list A) (n : nat) : option nat :=
  match l with
  | [] => None
  | h :: t =>
    if decide (P h) then
      match n with
      | 0 => Some 0
      | S n' => option_map S (nth_error_filter_index P t n')
      end
    else
      option_map S (nth_error_filter_index P t n)
  end.

Lemma nth_error_filter_index_le `{forall (x : A), Decision (P x)} :
  forall (l : list A) (n1 n2 in1 in2 : nat),
    n1 <= n2 ->
    nth_error_filter_index P l n1 = Some in1 ->
    nth_error_filter_index P l n2 = Some in2 ->
      in1 <= in2.
Proof.
  induction l; cbn; intros * Hle Hin1 Hin2; [by inversion Hin1 |].
  destruct (decide (P a)).
  - destruct n1, n2.
    + by congruence.
    + by inversion Hin1; lia.
    + by lia.
    + unfold option_map in Hin1, Hin2.
      destruct (nth_error_filter_index P l n1) eqn: Hin1'; inversion Hin1;
        subst; clear Hin1.
      destruct (nth_error_filter_index P l n2) eqn: Hin2'; inversion Hin2;
        subst; clear Hin2.
      by eapply le_n_S, IHl; cycle 1; [done.. | lia].
  - destruct (nth_error_filter_index P l n1) eqn: Hin1'; inversion Hin1;
      subst; clear Hin1.
    destruct (nth_error_filter_index P l n2) eqn: Hin2'; inversion Hin2;
      subst; clear Hin2.
    by eapply le_n_S, IHl.
Qed.

Lemma Forall_filter :
  forall {A : Type} (P : A -> Prop) {Pdec : forall a : A, Decision (P a)} (l : list A),
    Forall P (filter P l).
Proof.
  induction l as [| h t]; cbn; [by constructor |].
  by case_decide; [constructor |].
Qed.

(**
  Compute the sublist of a list that contains only elements that satisfy the
  given decidable predicate. Each element of the resulting list is paired with
  the proof that it satisfies the predicate.
*)
Fixpoint filter_annotate
  {A : Type} (P : A -> Prop) {Pdec : forall a : A, Decision (P a)}
  (l : list A) : list (dsig P) :=
  match l with
  | [] => []
  | h :: t =>
    match decide (P h) with
    | left p => dexist h p :: filter_annotate P t
    | right _ => filter_annotate P t
    end
  end.

Lemma filter_annotate_length :
  forall {A : Type} (P : A -> Prop) {Pdec : forall a : A, Decision (P a)} (l : list A),
    length (filter_annotate P l) = length (filter P l).
Proof.
  induction l as [| h t]; cbn; [done |].
  case_decide; cbn; [| done].
  by rewrite IHt.
Qed.

Lemma filter_annotate_unroll :
  forall {A : Type} (P : A -> Prop) {Pdec : forall a : A, Decision (P a)} (a : A) (l : list A),
    filter_annotate P (a :: l) =
    let fa := filter_annotate P l in
    match decide (P a) with
    | left pa => dexist _ pa :: fa
    | _ => fa
    end.
Proof. done. Qed.

Lemma filter_annotate_app :
  forall {A : Type} (P : A -> Prop) {Pdec : forall a : A, Decision (P a)} (l1 l2 : list A),
    filter_annotate P (l1 ++ l2) = filter_annotate P l1 ++ filter_annotate P l2.
Proof.
  induction l1; cbn; intros; [done |].
  case_decide; cbn; [| done].
  by rewrite IHl1.
Qed.

(**
  Filters a list through a predicate, then transforms each element using a
  function which depends on the fact that the predicate holds.
*)
Definition list_filter_map
  {A B : Type} (P : A -> Prop) {Pdec : forall a, Decision (P a)}
  (f : dsig P -> B) (l : list A) : list B :=
    map f (filter_annotate P l).

Lemma list_filter_map_app :
  forall {A B : Type} (P : A -> Prop) {Pdec : forall a, Decision (P a)}
    (f : dsig P -> B) (l1 l2 : list A),
      list_filter_map P f (l1 ++ l2) = list_filter_map P f l1 ++ list_filter_map P f l2.
Proof.
  by intros; unfold list_filter_map; rewrite filter_annotate_app, map_app.
Qed.

Lemma take_nth :
  forall {A : Type} (i n : nat) (s : list A),
    i < n -> nth_error (take n s) i = nth_error s i.
Proof.
  induction i; intros n [| h t] []; cbn; [done.. | |].
  - by apply IHi; lia.
  - by apply IHi; lia.
Qed.

Lemma nth_error_length :
  forall {A : Type} (n : nat) (l : list A) (a : A),
    nth_error l n = Some a -> S n <= length l.
Proof.
  induction n as [| n']; intros [| h t] a; inversion 1; cbn; [by lia |].
  by eapply le_n_S, IHn'.
Qed.

Lemma take_nth_last :
  forall {A : Type} (l : list A) (n : nat) (nth : A) (Hnth : nth_error l n = Some nth) (_last : A),
    nth = List.last (take (S n) l) _last.
Proof.
  intros.
  apply Some_inj.
  erewrite <- Hnth, <- nth_error_last.
  - by rewrite take_nth; [done | lia].
  - rewrite take_length.
    by apply nth_error_length in Hnth; lia.
Qed.

Lemma drop_S_tail :
  forall {A : Type} (l : list A) (n : nat),
    drop (S n) l = drop n (tail l).
Proof.
  by intros A [] n; cbn; [rewrite drop_nil |].
Qed.

Lemma drop_tail_comm :
  forall {A : Type} (l : list A) (n : nat),
    drop n (tail l) = tail (drop n l).
Proof.
  intros A l n; revert l; induction n; intros l.
  - by rewrite !drop_0.
  - by rewrite !drop_S_tail, IHn.
Qed.

Lemma drop_lookup :
  forall {A : Type} (s : list A) (n i : nat),
    n <= i -> drop n s !! (i - n) = s !! i.
Proof.
  intros.
  rewrite lookup_drop.
  by replace (n + (i - n)) with i by lia.
Qed.

Lemma drop_nth :
  forall {A : Type} (i n : nat) (l : list A),
    n <= i -> nth_error (drop n l) (i - n) = nth_error l i.
Proof.
  induction i; intros [| n'] [| h t] Hi; cbn; try done.
  - by inversion Hi.
  - by apply nth_error_None; cbn; lia.
  - by apply IHi; lia.
Qed.

Lemma drop_last :
  forall {A : Type} (i : nat) (l : list A) (_default : A),
    i < length l -> List.last (drop i l) _default  = List.last l _default.
Proof.
  induction i; intros [| h t] * Hlt; cbn in *; [done.. |].
  rewrite IHi by lia.
  destruct t; [| done].
  by inversion Hlt; lia.
Qed.

Lemma list_segment_nth :
  forall {A : Type} (l : list A) (n1 n2 : nat) (i : nat),
    n1 <= n2 -> n1 <= i -> i < n2 ->
      nth_error (list_segment l n1 n2) (i - n1) = nth_error l i.
Proof.
  intros.
  unfold list_segment.
  rewrite drop_nth; [| done].
  by apply take_nth.
Qed.

Lemma list_segment_app :
  forall {A : Type} (l : list A) (n1 n2 n3 : nat),
    n1 <= n2 -> n2 <= n3 ->
      list_segment l n1 n2 ++ list_segment l n2 n3 = list_segment l n1 n3.
Proof.
  intros.
  unfold list_segment.
  assert (Hle : n1 <= n3) by lia.
  pose proof (Hl1 := take_segment_suffix l n1 n3 Hle).
  rewrite <- (take_segment_suffix l n2 n3) in Hl1 at 4 by done.
  rewrite !app_assoc in Hl1.
  apply app_inv_tail in Hl1.
  rewrite <- (take_drop n1 (take n2 l)), <- app_assoc, (take_prefix l n1 n2) in Hl1 by done.
  by apply app_inv_head in Hl1.
Qed.

Lemma list_segment_singleton :
  forall {A : Type} (l : list A) (n : nat) (a : A),
    nth_error l n = Some a -> list_segment l n (S n) = [a].
Proof.
  intros * Hnth.
  apply nth_error_split in Hnth as (l1 & l2 & -> & <-).
  unfold list_segment.
  rewrite <- app_cons, app_assoc, take_app_length', drop_app_length; [done |].
  by rewrite app_length; cbn; lia.
Qed.

Lemma nth_error_map :
  forall {A B : Type} (f : A -> B) (l : list A) (n : nat),
    nth_error (List.map f l) n = option_map f (nth_error l n).
Proof.
  by induction l; intros [| n]; cbn; [.. | apply IHl].
Qed.

Lemma omap_app_rev :
  forall {A B : Type} (f : A -> option B) (l : list A) (l1' l2' : list B),
    omap f l = l1' ++ l2' ->
      exists l1 l2 : list A, l = l1 ++ l2 /\ omap f l1 = l1' /\ omap f l2 = l2'.
Proof.
  induction l; intros * Happ_rev.
  - symmetry in Happ_rev.
    apply app_eq_nil in Happ_rev as [Hl1' Hl2']; subst.
    by exists [], [].
  - cbn in Happ_rev.
    destruct (f a) eqn: Hfa; cycle 1.
    + destruct (IHl _ _ Happ_rev) as (_l1 & l2 & -> & <- & <-).
      by exists (a :: _l1), l2; cbn; rewrite Hfa.
    + destruct l1' as [| _b l1']; cbn in Happ_rev; inversion Happ_rev; subst.
      * by exists [], (a :: l); cbn; rewrite Hfa.
      * destruct (IHl _ _ H1) as (_l1 & l2 & -> & <- & <-).
        by exists (a :: _l1), l2; cbn; rewrite Hfa.
Qed.

Lemma omap_length :
  forall {A B : Type} (f : A -> option B) (l : list A),
    Forall (fun a => f a <> None) l -> length (omap f l) = length l.
Proof.
  induction 1; cbn; [done |].
  by case_match; cbn; congruence.
Qed.

Lemma omap_nth :
  forall {A B : Type} (f : A -> option B) (l : list A) (i : nat) (dummya : A) (dummyb : B),
    Forall (fun a => f a <> None) l -> i < length l ->
      Some (nth i (omap f l) dummyb) = f (nth i l dummya).
Proof.
  intros * Hall; revert i.
  induction Hall; cbn; intros; [by lia |].
  destruct i, (f x); cbn; [done.. | | done].
  by apply IHHall; lia.
Qed.

(** [omap] can be expressed as a [list_filter_map]. *)
Lemma omap_as_filter :
  forall {A B : Type} (f : A -> option B) (l : list A),
    omap f l = list_filter_map (is_Some ∘ f) (fun x => is_Some_proj (proj2_dsig x)) l.
Proof.
  induction l; cbn; [done |].
  case_decide; cbn.
  - by rewrite IHl; cbv; destruct H as [? ->].
  - by destruct (f a); [contradict H |].
Qed.

Lemma omap_Forall :
  forall {A B : Type} (f : A -> option B) (l : list A),
    Forall (fun x => ~ is_Some (f x)) l ->
      omap f l = [].
Proof.
  induction 1 as [| ? ? H]; cbn; [done |].
  by case_match; [contradict H |].
Qed.

Lemma NoDup_omap :
  forall {A B : Type} (f : A -> option B) (l : list A),
    (forall a1 a2 : A, is_Some (f a1) -> is_Some (f a2) -> f a1 = f a2 -> a1 = a2) ->
      NoDup l -> NoDup (omap f l).
Proof.
  intros A B f l Hinj Hnd.
  induction Hnd as [| h t Hnin Hnd IH]; cbn; [by constructor |].
  destruct (f h) eqn: Heq; [| by apply IH].
  constructor; [| by apply IH].
  intros Hin; apply elem_of_list_omap in Hin as (x & Hinx & Hfx).
  assert (x = h) by (apply Hinj; [done.. | congruence]).
  by congruence.
Qed.

(** Unpack list of [option A] into list of [A]. *)
Definition cat_option {A : Type} : list (option A) -> list A :=
  omap id.

Lemma cat_option_length :
  forall {A : Type} (l : list (option A)),
    Forall (fun a => a <> None) l -> length (cat_option l) = length l.
Proof.
  by intros; apply omap_length.
Qed.

Lemma cat_option_length_le :
  forall {A : Type} (l : list (option A)),
    length (cat_option l) <= length l.
Proof.
  by induction l as [| []]; cbn; [| lia..].
Qed.

Lemma cat_option_app :
  forall {A : Type} (l1 l2 : list (option A)),
    cat_option (l1 ++ l2) = cat_option l1 ++ cat_option l2.
Proof.
  by unfold cat_option; intros; rewrite omap_app.
Qed.

Lemma cat_option_nth :
  forall {A : Type} (l : list (option A)) (i : nat) (dummya : A),
    Forall (fun a => a <> None) l -> i < length l ->
      Some (nth i (cat_option l) dummya) = (nth i l (Some dummya)).
Proof.
  by unfold cat_option; intros; erewrite omap_nth.
Qed.

Lemma nth_error_eq :
  forall {A : Type} (l1 l2 : list A),
    (forall n : nat, nth_error l1 n = nth_error l2 n) -> l1 = l2.
Proof.
  induction l1; intros [| a2 l2] Hnth; [done | ..].
  - by specialize (Hnth 0); inversion Hnth.
  - by specialize (Hnth 0); inversion Hnth.
  - f_equal.
    + by specialize (Hnth 0); cbn in Hnth; congruence.
    + apply IHl1; intros n.
      by specialize (Hnth (S n)); cbn in Hnth.
Qed.

(**
  Compute the list of all decompositions of the given list <<l>> into
  triples <<(l1, x, l2)>> such that <<l = l1 ++ x :: l2>>.
*)
Fixpoint one_element_decompositions {A : Type} (l : list A) : list (list A * A * list A) :=
  match l with
  | [] => []
  | a :: l' =>
    ([], a, l')
    :: map
      (fun t => match t with (l1, b, l2) => (a :: l1, b, l2) end)
      (one_element_decompositions l')
  end.

Lemma elem_of_one_element_decompositions :
  forall {A : Type} (l pre suf : list A) (x : A),
    (pre, x, suf) ∈ one_element_decompositions l
      <->
    pre ++ [x] ++ suf = l.
Proof.
  induction l; split; cbn; intros Hin.
  - by inversion Hin.
  - by destruct pre; inversion Hin.
  - rewrite elem_of_cons, elem_of_list_fmap in Hin.
    destruct Hin as [[= -> -> ->] | (((pre', x'), suf') & [= -> -> ->] & Hin)]; [done |].
    by apply (IHl pre' suf' x') in Hin; subst.
  - destruct pre; inversion Hin; subst; clear Hin; [by left |].
    right.
    apply elem_of_list_fmap.
    exists (pre, x, suf).
    by rewrite IHl.
Qed.

(**
  Compute the list of all decompositions of the given list <<l>> into
  tuples <<(l1, x, l2, y, l3)>> such that <<l = l1 ++ x :: l2 ++ y :: l3>>.
*)
Definition two_element_decompositions
  {A : Type} (l : list A) : list (list A * A * list A * A * list A) :=
  flat_map
    (fun t =>
      match t with
        (l1, e1, l2) =>
        map
          (fun t => match t with (l2', e2, l3) => (l1, e1, l2', e2, l3) end)
          (one_element_decompositions l2)
      end)
    (one_element_decompositions l).

Lemma elem_of_two_element_decompositions :
  forall {A : Type} (l pre mid suf : list A) (x y : A),
    (pre, x, mid, y, suf) ∈ two_element_decompositions l
      <->
    pre ++ [x] ++ mid ++ [y] ++ suf = l.
Proof.
  intros.
  unfold two_element_decompositions.
  rewrite elem_of_list_In, in_flat_map; setoid_rewrite <- elem_of_list_In.
  split.
  - intros [((pre', x'), sufx) [Hdecx Hin]].
    apply elem_of_list_fmap in Hin as [[[mid' y'] suf'] [[= -> -> -> -> ->] Hin]].
    by apply elem_of_one_element_decompositions in Hdecx as <-, Hin as <-.
  - intros H.
    apply elem_of_one_element_decompositions in H.
    exists (pre, x, mid ++ [y] ++ suf).
    split; [done |].
    apply elem_of_list_fmap.
    exists (mid, y, suf).
    by rewrite elem_of_one_element_decompositions.
Qed.

Lemma order_decompositions :
  forall {A : Type} (pre1 suf1 pre2 suf2 : list A),
    pre1 ++ suf1 = pre2 ++ suf2 ->
    pre1 = pre2 \/ (exists suf1', pre1 = pre2 ++ suf1') \/ (exists suf2', pre2 = pre1 ++ suf2').
Proof.
  induction pre1; destruct pre2; cbn; [by eauto.. |].
  inversion 1; subst.
  by edestruct IHpre1 as [| [[] | []]]; [done | subst; eauto..].
Qed.

Lemma list_max_exists :
  forall (l : list nat),
    l <> [] -> list_max l ∈ l.
Proof.
  induction l as [| h t]; cbn; intros; [done |].
  destruct (PeanoNat.Nat.max_spec h (foldr Init.Nat.max 0 t))
    as [[Hlt ->] | [Hle ->]]; [| by left].
  right; apply IHt.
  by destruct t; [cbn in Hlt; lia |].
Qed.

(**
  Returns all values which occur with maximum frequency in the given list.
  Note that these values are returned with their original multiplicity.
*)
Definition mode `{EqDecision A} (l : list A) : list A :=
  let mode_value := list_max (List.map (count_occ decide_eq l) l) in
    filter (fun a => (count_occ decide_eq l a) = mode_value) l.

Example mode1 : mode [1; 1; 2; 3; 3] = [1; 1; 3; 3].
Proof. by itauto. Qed.

(**
  Computes the list <<suff>> which satisfies <<pref ++ suff = l>> or
  reports that no such list exists.
*)
Fixpoint complete_prefix `{EqDecision A} (l pref : list A) : option (list A) :=
  match l, pref with
  | l , [] => Some l
  | [], b :: pref' => None
  | a :: l', b :: pref' => if decide (a = b) then complete_prefix l' pref' else None
  end.

Example complete_prefix_some : complete_prefix [1; 2; 3; 4] [1; 2] = Some [3; 4].
Proof. by itauto. Qed.

Example complete_prefix_none : complete_prefix [1; 2; 3; 4] [1; 3] = None.
Proof. by itauto. Qed.

Lemma complete_prefix_empty `{EqDecision A} :
  forall (l : list A),
    complete_prefix l [] = Some l.
Proof.
  by induction l.
Qed.

Lemma complete_prefix_correct `{EqDecision A} :
  forall (l pref suff : list A),
    l = pref ++ suff <-> complete_prefix l pref = Some suff.
Proof.
  induction l; intros [] suff; cbn; [by itauto congruence.. |].
  case_decide; [| by itauto congruence].
  by rewrite <- IHl; itauto congruence.
Qed.

(**
  Computes the list <<pref>> which satisfies <<pref ++ suff = l>> or
  reports that no such list exists.
*)
Definition complete_suffix `{EqDecision A} (l suff : list A) : option (list A) :=
  match complete_prefix (rev l) (rev suff) with
  | None => None
  | Some ls => Some (rev ls)
  end.

Example complete_suffix_some : complete_suffix [1; 2; 3; 4] [3; 4] = Some [1; 2].
Proof. by itauto. Qed.

Lemma complete_suffix_correct `{EqDecision A} :
  forall (l pref suff : list A),
    l = pref ++ suff <-> complete_suffix l suff = Some pref.
Proof.
  split; unfold complete_suffix.
  - intros ->.
    replace (complete_prefix _ _) with (Some (rev pref)).
    + by rewrite rev_involutive.
    + symmetry; apply complete_prefix_correct.
      by rewrite rev_app_distr.
  - destruct (complete_prefix (rev l) (rev suff)) eqn: Heq; intros [= <-].
    apply complete_prefix_correct in Heq.
    apply rev_eq_app in Heq.
    by rewrite rev_involutive in Heq.
Qed.

Lemma complete_suffix_empty `{EqDecision A} :
  forall (l : list A),
    complete_suffix l [] = Some l.
Proof.
  unfold complete_suffix; cbn; intros.
  by rewrite complete_prefix_empty, rev_involutive.
Qed.

(** Keep elements which are [inl] but throw away those that are [inr]. *)
Definition list_sum_project_left {A B : Type} (x : list (A + B)) : list A :=
  omap sum_project_left x.

(** Keep elements which are [inr] but throw away those that are [inl]. *)
Definition list_sum_project_right {A B : Type} (x : list (A + B)) : list B :=
  omap sum_project_right x.

Lemma fold_right_andb_false :
  forall (l : list bool),
    fold_right andb false l = false.
Proof.
  induction l; cbn; [done |].
  by rewrite IHl, andb_false_r.
Qed.

Lemma sumbool_forall :
  forall {A : Type} {P Q : A -> Prop},
    (forall x : A, {P x} + {Q x}) ->
    forall l : list A, {Forall P l} + {Exists Q l}.
Proof.
  intros A P Q Hdec.
  induction l; [by left; constructor |].
  destruct (Hdec a); [| by right; constructor].
  by destruct IHl; [left | right]; constructor.
Qed.

Lemma list_sum_map :
  forall {A : Type} (f g : A -> nat) (l : list A),
    (forall x : A, x ∈ l -> f x <= g x) ->
      list_sum (map f l) <= list_sum (map g l).
Proof.
  induction l as [| h t]; cbn; intros Hle; [done |].
  apply PeanoNat.Nat.add_le_mono.
  - by apply Hle; left.
  - apply IHt; intros x Hin.
    by apply Hle; right.
Qed.

Lemma list_sum_decrease :
  forall {A : Type} (f g : A -> nat) (l : list A),
    (forall a, a ∈ l -> f a <= g a) ->
    Exists (fun a => f a < g a) l ->
      list_sum (map f l) < list_sum (map g l).
Proof.
  intros A f g l Hall Hex.
  induction Hex; cbn.
  - apply PeanoNat.Nat.add_lt_le_mono; [done |].
    apply list_sum_map.
    intros a' Hin.
    by apply Hall; right.
  - apply PeanoNat.Nat.add_le_lt_mono; [by apply Hall; left |].
    apply IHHex.
    intros a Hin.
    by apply Hall; right.
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
Lemma fold_left_ind :
  forall {A B : Type} (f : B -> A -> B) (P : list A -> B -> B -> Prop)
    (Hstart : forall x, P nil x x)
    (Hstep : forall x a l r, P l (f x a) r -> P (a :: l) x r),
  forall l x, P l x (fold_left f l x).
Proof.
  induction l.
  - by apply Hstart.
  - by intros x; apply Hstep, IHl.
Qed.

(**
  An induction principle for [fold_left] which
  decomposes the list from the right.
*)
Lemma fold_left_ind_rev :
  forall {A B : Type} (f : B -> A -> B) (x0 : B) (P : list A -> B -> Prop)
    (Hstart : P nil x0)
    (Hstep : forall l a x, P l x -> P (l ++ [a]) (f x a)),
  forall l, P l (fold_left f l x0).
Proof.
  induction l using rev_ind.
  - by apply Hstart.
  - by rewrite fold_left_app; apply Hstep.
Qed.

Section sec_suffix_quantifiers.

(** ** Quantifiers for all suffixes

  In this section we define inductive quantifiers for lists that are concerned
  with predicates over the sublists of the list instead of the elements. They
  are analogous to [Streams.ForAll] and [Streams.Exists]. We prove several
  properties about them.

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

Lemma fsHere :
  forall (l : list A),
    ForAllSuffix l -> P l.
Proof. by inversion 1. Qed.

Lemma fsFurther :
  forall (a : A) (l : list A),
    ForAllSuffix (a :: l) -> ForAllSuffix l.
Proof. by inversion 1. Qed.

Lemma ForAll_drop :
  forall (m : nat) (l : list A),
    ForAllSuffix l -> ForAllSuffix (drop m l).
Proof.
  induction m; intros [] Hall; cbn; [done.. |].
  by apply fsFurther in Hall; apply IHm.
Qed.

Lemma ForAllSuffix_induction :
  forall (Inv : list A -> Prop)
    (InvThenP : forall l, Inv l -> P l)
    (InvIsStable : forall a l, Inv (a :: l) -> Inv l),
  forall l, Inv l -> ForAllSuffix l.
Proof.
  induction l; intros.
  - by constructor; apply InvThenP.
  - constructor.
    + by apply InvThenP.
    + by eapply IHl, InvIsStable.
Qed.

End sec_suffix_quantifiers.

Lemma ForAllSuffix_subsumption :
  forall {A : Type} (P Q : list A -> Prop) (HPQ : forall l, P l -> Q l),
    forall (l : list A), ForAllSuffix P l -> ForAllSuffix Q l.
Proof.
  by induction 2; constructor; auto.
Qed.

Definition ForAllSuffix2 [A : Type] (R : A -> A -> Prop) : list A -> Prop :=
  ForAllSuffix (fun l => match l with | a :: b :: _ => R a b | _ => True end).

Lemma fsFurther2_transitive :
  forall {A : Type} (R : A -> A -> Prop) {HT : Transitive R} (a b : A) (l : list A),
    ForAllSuffix2 R (a :: b :: l) -> ForAllSuffix2 R (a :: l).
Proof.
  inversion 2; subst.
  destruct l.
  - by repeat constructor.
  - inversion H3; subst.
    by constructor; [transitivity b |].
Qed.

Lemma ForAllSuffix2_filter :
  forall {A : Type} (R : A -> A -> Prop) {HT : Transitive R}
    (P : A -> Prop) {Pdec : forall a, Decision (P a)},
  forall l, ForAllSuffix2 R l -> ForAllSuffix2 R (filter P l).
Proof.
  induction l; intros Hl; [done |].
  unfold filter; cbn.
  spec IHl; [by apply fsFurther in Hl |].
  case_decide; [| done].
  constructor; [| done].
  clear IHl H; induction l; cbn; [done |].
  case_decide.
  - by inversion Hl.
  - by apply IHl; eapply fsFurther2_transitive.
Qed.

Lemma list_subseteq_tran :
  forall (A : Type) (l m n : list A),
    l ⊆ m -> m ⊆ n -> l ⊆ n.
Proof.
  intros A l m n Hlm Hmn x y.
  by apply Hmn, Hlm.
Qed.

#[export] Instance list_subseteq_dec `{EqDecision A} : RelDecision (@subseteq (list A) _).
Proof.
  intros x; induction x.
  - by left; apply list_subseteq_nil.
  - intros y; destruct (IHx y) as [Hsub | Hnsub].
    + destruct (decide (a ∈ y)).
      * by left; inversion 1; subst; [| apply Hsub].
      * by right; intros Hsub'; contradict n; apply Hsub'; left.
    + right; intros Hsub; contradict Hnsub.
      by intros b Hb; apply Hsub; right.
Qed.

Lemma nodup_append_left :
  forall {A : Type} (l1 l2 : list A),
    NoDup (l1 ++ l2) -> NoDup l1.
Proof.
  by intros * [? _]%NoDup_app.
Qed.

Lemma NoDup_subseteq_length :
  forall {A : Type} {l1 l2 : list A},
    NoDup l1 -> l1 ⊆ l2 -> length l1 <= length l2.
Proof.
  by intros; apply submseteq_length, NoDup_submseteq.
Qed.

Lemma submseteq_tail_l :
  forall {A : Type} (x : A) (l1 l2 : list A),
    x :: l1 ⊆+ l2 -> l1 ⊆+ l2.
Proof.
  by intros A x l1 l2; apply submseteq_trans, submseteq_cons.
Qed.

Lemma submseteq_list_subseteq :
  forall {A : Type} (l1 l2 : list A),
    l1 ⊆+ l2 -> l1 ⊆ l2.
Proof.
  by intros A l1 l2 H ? Hx; eapply elem_of_submseteq.
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
  by intros; rewrite elem_of_list_In, in_prod_iff, <- !elem_of_list_In.
Qed.

(** ** The function [lastn] and its properties *)

(** [lastn] returns a suffix of length <<n>> from the list <<l>>. *)
Definition lastn {A : Type} (n : nat) (l : list A) : list A :=
  rev (take n (rev l)).

(** If the list is [[]], then the result of [lastn] is also [[]]. *)
Lemma lastn_nil :
  forall {A : Type} (n : nat),
    lastn n (@nil A) = [].
Proof.
  by intros A n; unfold lastn; cbn; rewrite take_nil.
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

(** ** Computing longest common prefixes and suffixes *)

(** *** Longest common prefix *)

Section sec_max_prefix.

Context
  {A : Type}
  `{EqDecision A}
  .

Lemma max_prefix_nil_l :
  forall (l : list A),
    max_prefix [] l = ([], l, []).
Proof. done. Qed.

Lemma max_prefix_nil_r :
  forall (l : list A),
    max_prefix l [] = (l, [], []).
Proof.
  by destruct l.
Qed.

Lemma max_prefix_diag :
  forall (l : list A),
    max_prefix l l = ([], [], l).
Proof.
  induction l as [| h t]; cbn; [done |].
  case_decide; [| done].
  by rewrite IHt; cbn.
Qed.

Lemma max_prefix_head :
  forall (l1 l2 : list A),
    head l1 <> head l2 -> max_prefix l1 l2 = (l1, l2, []).
Proof.
  intros [] [] Hneq; cbn in *; [done.. |].
  by case_decide; [congruence |].
Qed.

Lemma max_prefix_app :
  forall (l l1 l2 p r1 r2 : list A),
    max_prefix l1 l2 = (r1, r2, p) ->
      max_prefix (l ++ l1) (l ++ l2) = (r1, r2, l ++ p).
Proof.
  induction l as [| h t]; cbn; intros * Heq; [done |].
  case_decide; [| done].
  by apply IHt in Heq as ->; cbn.
Qed.

Lemma max_prefix_app_let :
  forall (l l1 l2 : list A),
    max_prefix (l ++ l1) (l ++ l2) =
      let '(r1, r2, p) := max_prefix l1 l2 in (r1, r2, l ++ p).
Proof.
  intros.
  destruct (max_prefix l1 l2) as [[]] eqn: Heq.
  by eapply max_prefix_app in Heq.
Qed.

Lemma max_prefix_head_inv :
  forall (l1 l2 p r1 r2 : list A),
    max_prefix l1 l2 = (r1, r2, p) ->
      r1 = [] /\ r2 = [] \/ head r1 <> head r2.
Proof.
  intros l1 l2 p [] [] Heq; cbn; [by left | by right.. |].
  apply max_prefix_max_snoc in Heq.
  by right; congruence.
Qed.

Lemma max_prefix_spec :
  forall (l1 l2 p r1 r2 : list A),
    max_prefix l1 l2 = (r1, r2, p)
      <->
    l1 = p ++ r1 /\ l2 = p ++ r2 /\ (r1 = [] /\ r2 = [] \/ head r1 <> head r2).
Proof.
  split.
  - split; [by eapply max_prefix_fst_alt |].
    split; [by eapply max_prefix_snd_alt |].
    by eapply max_prefix_head_inv.
  - intros (-> & -> & [[-> ->] |]).
    + by rewrite app_nil_r, max_prefix_diag.
    + by rewrite max_prefix_app_let, max_prefix_head, app_nil_r.
Qed.

Lemma max_prefix_comm :
  forall (l1 l2 p r1 r2 : list A),
    max_prefix l1 l2 = (r1, r2, p) ->
    max_prefix l2 l1 = (r2, r1, p).
Proof.
  induction l1 as [| h1 t1]; destruct l2 as [| h2 t2]; cbn; [by itauto congruence.. |].
  intros p r1 r2.
  destruct (max_prefix t1 t2) as [[]] eqn: Heq.
  case_decide; subst; intros [= <- <- <-]; cbn; case_decide; [| done..].
  by erewrite IHt1.
Qed.

Lemma max_prefix_comm_let :
  forall (l1 l2 : list A),
    max_prefix l2 l1 =
      let '(r1, r2, p) := max_prefix l1 l2 in (r2, r1, p).
Proof.
  intros.
  destruct (max_prefix l1 l2) as [[]] eqn: Heq.
  by apply max_prefix_comm in Heq.
Qed.

Lemma max_prefix_idem :
  forall (l1 l2 p r1 r2 : list A),
    max_prefix l1 l2 = (r1, r2, p) ->
    max_prefix r1 r2 = (r1, r2, []).
Proof.
  induction l1 as [| h1 t1]; destruct l2 as [| h2 t2]; cbn;
    only 1-3: intros * [= <- <- <-]; cbn; [done.. |].
  intros p r1 r2.
  destruct (max_prefix t1 t2) as [[]] eqn: Heq.
  case_decide; subst; intros [= <- <- <-]; cbn.
  - by apply IHt1 in Heq.
  - by case_decide.
Qed.

Lemma max_prefix_is_longest :
  forall (l1 l2 p r1 r2 p' : list A),
   max_prefix l1 l2 = (r1, r2, p) ->
   prefix p' l1 -> prefix p' l2 ->
   length p' <= length p.
Proof.
  intros l1 l2 p r1 r2 p' Hlc Hp1 Hp2.
  inversion Hlc; subst; apply prefix_length.
  by eapply max_prefix_max_alt.
Qed.

Lemma max_prefix_residual_suffix :
  forall (l1 l2 p r1 r2 : list A),
    max_prefix l1 l2 = (r1, r2, p) ->
      suffix r1 l1 /\ suffix r2 l2.
Proof.
  intros * Hprefix.
  apply max_prefix_spec in Hprefix as (-> & -> & _).
  by split; apply suffix_app_r.
Qed.

End sec_max_prefix.

(** *** Longest common suffix *)

Section sec_max_suffix.

Context
  {A : Type}
  `{EqDecision A}
  .

Lemma max_suffix_diag :
  forall (l : list A),
    max_suffix l l = ([], [], l).
Proof.
  intros.
  unfold max_suffix.
  by rewrite max_prefix_diag, reverse_involutive; cbn.
Qed.

Lemma max_suffix_app_let :
  forall (l l1 l2 : list A),
    max_suffix (l1 ++ l) (l2 ++ l) =
      let '(r1, r2, p) := max_suffix l1 l2 in (r1, r2, p ++ l).
Proof.
  intros.
  unfold max_suffix.
  rewrite !reverse_app, max_prefix_app_let.
  destruct (max_prefix (reverse l1) (reverse l2)) as [[]] eqn: Heq.
  by rewrite reverse_app, reverse_involutive.
Qed.

Lemma max_suffix_last :
  forall (l1 l2 : list A),
    last l1 <> last l2 -> max_suffix l1 l2 = (l1, l2, []).
Proof.
  intros * Hlast.
  unfold max_suffix.
  rewrite max_prefix_head.
  - by rewrite !reverse_involutive; cbn.
  - by rewrite !head_reverse.
Qed.

Lemma max_suffix_last_inv :
  forall (l1 l2 p r1 r2 : list A),
    max_suffix l1 l2 = (r1, r2, p) ->
      r1 = [] /\ r2 = [] \/ last r1 <> last r2.
Proof.
  intros * Heq.
  destruct_list_last r1 r1' h1 Heq1; destruct_list_last r2 r2' h2 Heq2; cbn;
    rewrite ?last_snoc; [by left | by right.. |].
  right; intros [= ->].
  by apply max_suffix_max_snoc in Heq.
Qed.

Lemma max_suffix_spec :
  forall (l1 l2 p r1 r2 : list A),
    max_suffix l1 l2 = (r1, r2, p)
      <->
    l1 = r1 ++ p /\ l2 = r2 ++ p /\ (r1 = [] /\ r2 = [] \/ last r1 <> last r2).
Proof.
  split.
  - split; [by eapply max_suffix_fst_alt |].
    split; [by eapply max_suffix_snd_alt |].
    by eapply max_suffix_last_inv.
  - intros (-> & -> & [[-> ->] |]); cbn.
    + by rewrite max_suffix_diag.
    + by rewrite max_suffix_app_let, max_suffix_last.
Qed.

Lemma max_suffix_comm_let :
  forall (l1 l2 : list A),
    max_suffix l2 l1 =
      let '(r1, r2, p) := max_suffix l1 l2 in (r2, r1, p).
Proof.
  intros.
  unfold max_suffix.
  rewrite max_prefix_comm_let.
  by destruct (max_prefix (reverse l1) (reverse l2)) as [[]].
Qed.

Lemma max_suffix_is_suffix :
  forall (l1 l2 p r1 r2 : list A),
    max_suffix l1 l2 = (r1, r2, p) ->
      suffix p l1 /\ suffix p l2.
Proof.
  intros * Hsuffix.
  apply max_suffix_spec in Hsuffix as (-> & -> & _).
  by split; apply suffix_app_r.
Qed.

Lemma suffix_max_suffix :
  forall (l l1 l2 : list A),
    suffix l l1 -> suffix l l2 ->
      let '(r1, r2, p) := max_suffix l1 l2 in suffix l p.
Proof.
  intros.
  destruct (max_suffix l1 l2) as [[]] eqn: Heq.
  by eapply max_suffix_max_alt.
Qed.

Lemma max_suffix_is_longest :
  forall (l1 l2 p r1 r2 p' : list A),
   max_suffix l1 l2 = (r1, r2, p) ->
   suffix p' l1 -> suffix p' l2 ->
   length p' <= length p.
Proof.
  intros l1 l2 p r1 r2 p' Hlc Hp1 Hp2.
  inversion Hlc; subst; apply suffix_length.
  by eapply max_suffix_max_alt.
Qed.

Lemma max_suffix_residual_prefix :
  forall (l1 l2 p r1 r2 : list A),
    max_suffix l1 l2 = (r1, r2, p) ->
      prefix r1 l1 /\ prefix r2 l2.
Proof.
  intros * Hsuffix.
  apply max_suffix_spec in Hsuffix as (-> & -> & _).
  by split; apply prefix_app_r.
Qed.

End sec_max_suffix.

Program Fixpoint Exists_choose_first
  `{P : A -> Prop} `{forall a, Decision (P a)} {l : list A} (Hl : Exists P l) {struct l} : A :=
  match l with
  | [] => _
  | a :: l => if decide (P a) then a else @Exists_choose_first A P _ l _
  end.
Next Obligation.
Proof. by intros; exfalso; subst; inversion Hl. Qed.
Next Obligation.
Proof. by intros; subst; apply Exists_cons in Hl as []. Qed.

Lemma Exists_choose_first_good :
  forall `(P : A -> Prop) `{forall a, Decision (P a)} (l : list A) (Hl : Exists P l),
    P (Exists_choose_first Hl).
Proof.
  induction l; cbn; intros; [by inversion Hl |].
  by case_decide; [| apply IHl].
Qed.
