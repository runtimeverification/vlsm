From stdpp Require Import prelude finite.
From Coq Require Import FinFun FunctionalExtensionality.
From VLSM Require Import Lib.Preamble.

(** * Utility lemmas about lists *)

Lemma map_comp
  [A B C : Type]
  (f : A -> B)
  (g : B -> C)
  : map (g ∘ f) = map g ∘ map f.
Proof.
  extensionality l.
  induction l; cbn; rewrite ?IHl; reflexivity.
Qed.

(** A list is empty if it has no members *)
Lemma empty_nil [X:Type] (l:list X) :
  (forall v, ~In v l) -> l = [].
Proof.
  clear.
  destruct l as [|a]. reflexivity.
  simpl. intro H. elim (H a). left. reflexivity.
Qed.

(** It is decidable whether a list is null or not *)
Lemma null_dec {S} (l : list S) : Decision (l = []).
Proof.
  destruct l; [left; reflexivity|right; congruence].
Qed.

(** A list is either null or it can be decomposed into an initial prefix
and a last element *)
Lemma has_last_or_null {S} (l : list S)
  : {l' : list S & {a : S | l = l' ++ (a::nil)}} + {l = nil} .
Proof.
  destruct (null_dec l).
  - right. assumption.
  - left. apply exists_last in n. assumption.
Qed.

(** destructs a list in @l@ in either null or a prefix @l'@ and
a last element @a@ with an equation @Heq@ stating that @l = l' ++ [a]@
*)
Ltac destruct_list_last l l' a Heq :=
 destruct (has_last_or_null l) as [[l' [a Heq]] | Heq]; rewrite Heq in *; swap 1 2.

Lemma last_not_null {S} (l : list S) (a : S)
  : l ++ [a] <> [].
Proof.
  intro contra. destruct l; discriminate contra.
Qed.

Definition last_error {S} (l : list S) : option S :=
  match l with
  | [] => None
  | a :: t => Some (List.last t a)
  end.

Lemma unfold_last_hd {S} : forall (random a b : S) (l : list S),
  List.last (a :: (b :: l)) random = List.last (b :: l) random.
Proof.
  intros random h1 h2 tl.
  unfold last. reflexivity.
Qed.

Lemma swap_head_last {S} : forall (random a b c : S) (l : list S),
  List.last (a :: b :: c :: l) random = List.last (b :: a :: c :: l) random.
Proof.
  intros random h1 h2 s tl.
  induction tl as [| hd tl IHl].
  - reflexivity.
  - simpl. reflexivity.
Qed.

Lemma remove_hd_last {X} :
  forall (hd1 hd2 d1 d2 : X) (tl : list X),
    List.last (hd1 :: hd2 :: tl) d1 = List.last (hd2 :: tl) d2.
Proof.
  intros. induction tl.
  simpl. reflexivity.
  rewrite unfold_last_hd.
  rewrite unfold_last_hd in IHtl.
  rewrite unfold_last_hd.
  rewrite unfold_last_hd.
  destruct tl.
  reflexivity.
  do 2 rewrite unfold_last_hd in IHtl.
  do 2 rewrite unfold_last_hd.
  assumption.
Qed.

Lemma unroll_last {S} : forall (random a : S) (l : list S),
  List.last (a :: l) random = List.last l a.
Proof.
  induction l; try reflexivity.
  destruct l; try reflexivity.
  rewrite swap_head_last. rewrite unfold_last_hd. rewrite IHl.
  rewrite unfold_last_hd. reflexivity.
Qed.

Lemma last_app
  {A}
  (l1 l2 : list A)
  (def : A)
  : List.last (l1 ++ l2) def = List.last l2 (List.last l1 def).
Proof.
  generalize dependent def.
  induction l1; try reflexivity; intro def.
  remember List.last as lst; simpl; subst lst.
  repeat rewrite unroll_last.
  apply IHl1.
Qed.

Lemma last_map
  {A B}
  (f : A -> B)
  (h : A)
  (t : list A)
  (def : B)
  : List.last (map f (h :: t)) def = f (List.last t h).
Proof.
  generalize dependent def. generalize dependent h.
  induction t; try reflexivity; intros.
  rewrite map_cons.
  repeat rewrite unroll_last.
  apply IHt.
Qed.

Lemma last_error_some {S}
  (l : list S)
  (s random : S)
  (Herr : last_error l = Some s) :
  List.last l random = s.
Proof.
  destruct l.
  - simpl in *. discriminate Herr.
  - simpl in Herr. inversion Herr.
    apply unroll_last.
Qed.

Lemma incl_empty : forall A (l : list A),
  incl l nil -> l = nil.
Proof.
  intros. destruct l; try reflexivity.
  exfalso. destruct (H a). left. reflexivity.
Qed.

Lemma incl_singleton {A} : forall (l : list A) (a : A),
  incl l [a] ->
  forall b, In b l -> b = a.
Proof.
  intros. induction l; inversion H0; subst.
  - clear H0. destruct (H b); try (left; reflexivity); subst; try reflexivity.
    inversion H0.
  - apply IHl; try assumption.
    apply incl_tran with (a0 :: l); try assumption.
    apply incl_tl. apply incl_refl.
Qed.

Lemma filter_in {A} P `{∀ (x:A), Decision (P x)} x s :
  In x s ->
  P x ->
  In x (filter P s).
Proof.
  intros.
  apply elem_of_list_In.
  apply elem_of_list_In in H0.
  apply elem_of_list_filter; auto.
Qed.

Lemma filter_incl {A} P `{∀ (x:A), Decision (P x)} s1 s2 :
  incl s1 s2 ->
  incl (filter P s1) (filter P s2).
Proof.
  induction s1; intros; intro x; intros.
  - contradict H1; auto.
  - rewrite filter_cons in H1.
    destruct (decide (P a)).
    + destruct H1.
      * subst. apply filter_in; try assumption. apply H0. left. reflexivity.
      * apply IHs1; try assumption. intro y; intro. apply H0. right. assumption.
    + apply IHs1; try assumption. intro y; intro. apply H0. right. assumption.
Qed.

Lemma filter_incl_fn {A} P Q
  `{∀ (x:A), Decision (P x)} `{∀ (x:A), Decision (Q x)} :
  (forall a, P a -> Q a) ->
  forall s, incl (filter P s) (filter Q s).
Proof.
  induction s; simpl.
  - apply incl_refl.
  - intro x; intros.
    rewrite filter_cons in H2.
    destruct (decide (P a)).
    + rewrite filter_cons.
      destruct (decide (Q a)).
      * destruct H2.
        -- left. rewrite H2. reflexivity.
        -- right. apply IHs. assumption.
      * contradict n. apply H1. assumption.
    + rewrite filter_cons.
      destruct (decide (Q a)).
      -- right. apply IHs. assumption.
      -- apply IHs. assumption.
Qed.

Lemma filter_length_fn {A} P Q
  `{∀ (x:A), Decision (P x)} `{∀ (x:A), Decision (Q x)}
  s (Hfg : Forall (fun a => P a -> Q a) s) :
  length (filter P s) <= length (filter Q s).
Proof.
  induction s; simpl.
  - lia.
  - inversion Hfg; subst. specialize (IHs H4).
    rewrite 2 filter_cons.
    destruct (decide (P a)).
    + destruct (decide (Q a)).
      * simpl; lia.
      * contradict n. apply H3. assumption.
    + destruct (decide (Q a)).
      * simpl. lia.
      * apply IHs.
Qed.

Lemma filter_eq_fn {A} P Q
 `{∀ (x:A), Decision (P x)} `{∀ (x:A), Decision (Q x)} s :
  (forall a, In a s -> P a <-> Q a) ->
  filter P s = filter Q s.
Proof.
 induction s; intros; try reflexivity. simpl.
 assert (IHs' : forall a : A, In a s -> P a <-> Q a).
 { intros. apply H1. right. assumption. }
 apply IHs in IHs'. clear IHs.
 rewrite 2 filter_cons.
 destruct (decide (P a)).
 - destruct (decide (Q a)).
   + rewrite IHs'. reflexivity.
   + contradict n.
     apply H1; try assumption.
     left. reflexivity.
 - destruct (decide (Q a)).
   + contradict n.
     apply H1; try assumption.
     left; reflexivity.
   + assumption.
Qed.

Lemma Forall_filter_nil {A} P `{∀ (x:A), Decision (P x)} l :
 Forall (fun a : A => ~ P a) l <-> filter P l = [].
Proof.
  rewrite Forall_forall.
  split; intro Hnone.
  - induction l; try reflexivity.
    assert (Hno_a := Hnone a).
    assert (Hin_a : a ∈ a :: l) by left.
    specialize (Hno_a Hin_a).
    rewrite filter_cons.
    destruct (decide (P a)); try congruence.
    apply IHl.
    intros b Hin_b.
    apply Hnone.
    right.
    assumption.
  - induction l; intros x Hx; inversion Hx; subst; clear Hx.
    + rewrite filter_cons in Hnone.
      destruct (decide (P a)); [inversion Hnone|assumption].
    + rewrite filter_cons in Hnone.
      destruct (decide (P a)); [inversion Hnone|].
      apply IHl; assumption.
Qed.

Lemma Exists_first
  {A : Type}
  (l : list A)
  (P : A -> Prop)
  (Pdec : forall a, Decision (P a))
  (Hsomething : Exists P l)
  : exists (prefix : list A)
         (suffix : list A)
         (first : A),
         P first /\
         l = prefix ++ [first] ++ suffix /\
         ~Exists P prefix.

Proof.
  induction l;[solve[inversion Hsomething]|].
  destruct (decide (P a)).
  - exists nil, l, a.
    rewrite Exists_nil.
    tauto.
  - apply Exists_cons in Hsomething.
    destruct Hsomething;[exfalso;tauto|].
    specialize (IHl H);clear H.
    destruct IHl as [prefix [suffix [first [Hf [-> Hnone_before]]]]].
    exists (a :: prefix), suffix, first.
    rewrite Exists_cons.
    tauto.
Qed.

Lemma in_not_in : forall A (x y : A) (l:list A),
  x ∈ l ->
  ~ y ∈ l ->
  x <> y.
Proof.
  intros. intro; subst. apply H0. assumption.
Qed.

Definition inb {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y}) (x : A) (xs : list A) :=
  if in_dec Aeq_dec x xs then true else false.

Lemma in_function {A}  (Aeq_dec : forall x y:A, {x = y} + {x <> y}) :
  PredicateFunction2 (@In A) (inb Aeq_dec).
Proof.
  intros x xs. unfold inb. destruct (in_dec Aeq_dec x xs); split; intros
  ; try assumption; try reflexivity; try contradiction; discriminate.
Qed.

Lemma in_correct `{EqDecision X} :
  forall (l : list X) (x : X),
    In x l <-> inb decide_eq x l = true.
Proof.
  intros s msg.
  apply in_function.
Qed.

Lemma in_correct_refl `{EqDecision X} :
  forall (l : list X) (x : X),
    In x l <-> inb decide_eq x l.
Proof.
  intros s msg.
  rewrite in_correct, Is_true_iff_eq_true.
  reflexivity.
Qed.

Lemma in_correct' `{EqDecision X} :
  forall (l : list X) (x : X),
    ~ In x l <-> inb decide_eq x l = false.
Proof.
  intros s msg.
  rewrite in_correct, not_true_iff_false.
  reflexivity.
Qed.

Definition inclb
  `{EqDecision A}
  (l1 l2 : list A)
  : bool
  := forallb (fun x : A => inb decide_eq x l2) l1.

Lemma incl_function `{EqDecision A} : PredicateFunction2 (@incl A) (inclb).
Proof.
  intros l1 l2. unfold inclb. rewrite forallb_forall.
  split; intros Hincl x Hx; apply in_correct; apply Hincl; assumption.
Qed.

Definition incl_correct `{EqDecision A}
  (l1 l2 : list A)
  : incl l1 l2 <-> inclb l1 l2 = true
  := incl_function l1 l2.

Lemma map_incl {A B} (f : B -> A) : forall s s',
  incl s s' ->
  incl (map f s) (map f s').
Proof.
  intros s s' Hincl fx Hin.
  apply in_map_iff .
  apply in_map_iff in Hin.
  destruct Hin as [x [Heq Hin]].
  exists x. split; try assumption. apply Hincl. assumption.
Qed.

Definition app_cons {A}
  (a : A)
  (l : list A)
  : [a] ++ l = a :: l
  := eq_refl.

Lemma append_nodup_left {A}:
  forall (l1 l2 : list A), List.NoDup (l1 ++ l2) -> List.NoDup l1.
Proof.
  induction l1; intros.
  - constructor.
  - inversion H. apply IHl1 in H3. constructor; try assumption. intro. apply H2.
    apply in_app_iff. left. assumption.
Qed.

Lemma append_nodup_right {A}:
  forall (l1 l2 : list A), List.NoDup (l1 ++ l2) -> List.NoDup l2.
Proof.
  induction l1; intros.
  - simpl in H. assumption.
  - simpl in H. inversion H. apply IHl1 in H3. assumption.
Qed.

Lemma nodup_append {A} : forall (l1 l2 : list A),
  NoDup l1 ->
  NoDup l2 ->
  (forall a, a ∈ l1 -> ~ a ∈ l2) ->
  (forall a, a ∈ l2 -> ~ a ∈ l1) ->
  NoDup (l1 ++ l2).
Proof.
  induction l1; simpl; intros; try assumption.
  inversion H; subst; clear H. constructor.
  - intro. apply elem_of_app in H. destruct H as [Inl1 | InL2].
    + apply H5. assumption.
    + apply (H1 a); try assumption.
      left.
  - apply IHl1; try assumption; intros.
    + apply H1. right. assumption.
    + apply H2 in H. intro. apply H. right. assumption.
Qed.

Lemma last_is_last {A} : forall (l : list A) (x dummy: A),
  List.last (l ++ [x]) dummy = x.
Proof.
  induction l; try reflexivity; intros.
  rewrite <- app_comm_cons. specialize (IHl x dummy). rewrite <- IHl at 2. simpl.
  destruct l; simpl; reflexivity.
Qed.

Lemma last_error_is_last {A} : forall (l : list A) (x : A),
  last_error (l ++ [x]) = Some x.
Proof.
  destruct l; try reflexivity; intros; simpl. apply f_equal. apply last_is_last.
Qed.

(** Polymorphic list library **)

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
  induction l as [|hd tl IHl].
  - split; intro H'.
    + unfold is_member in H'; inversion H'.
    + inversion H'.
  - split; intro H'.
    + simpl in H'.
      destruct (compare w hd) eqn:Hcmp;
        try (right; apply IHl; assumption ).
      apply StrictOrder_Reflexive in Hcmp.
      left. symmetry; assumption.
    + apply in_inv in H'.
      destruct H' as [eq | neq].
      rewrite eq.
      simpl.
      rewrite compare_eq_refl.
      reflexivity.
      rewrite <- IHl in neq.
      simpl. assert (H_dec := compare_eq_dec w hd).
      destruct H_dec as [Heq | Hneq].
      rewrite Heq. rewrite compare_eq_refl. reflexivity.
      destruct (compare w hd); try reflexivity;
        assumption.
Qed.

Lemma is_member_correct' {W} `{StrictlyComparable W}
  : forall l (w : W), is_member w l = false <-> ~ In w l.
Proof.
  intros.
  apply mirror_reflect.
  intros; apply is_member_correct.
Qed.

Lemma In_app_comm {X} : forall l1 l2 (x : X), In x (l1 ++ l2) <-> In x (l2 ++ l1).
Proof.
  intros l1 l2 x; split; intro H_in;
  apply in_or_app; apply in_app_or in H_in;
    destruct H_in as [cat | dog];
    tauto.
Qed.

Lemma nth_error_last
  {A : Type}
  (l : list A)
  (n : nat)
  (Hlast: S n = length l)
  (_last : A)
  : nth_error l n = Some (List.last l _last).
Proof.
  generalize dependent _last.
  generalize dependent l.
  induction n; intros.
  - destruct l; inversion Hlast. symmetry in H0.
    apply length_zero_iff_nil in H0. subst. reflexivity.
  - destruct l; inversion Hlast.
    specialize (IHn l H0 _last). rewrite unroll_last.
    simpl. rewrite IHn. f_equal.
    destruct l; inversion H0.
    repeat rewrite unroll_last.
    reflexivity.
Qed.

Fixpoint list_suffix
  {A : Type}
  (l : list A)
  (n : nat)
  {struct n}
  : list A
  := match n,l with
    | 0,_ => l
    | _,[] => []
    | S n, a :: l => list_suffix l n
    end.

Lemma list_suffix_map
  {A B : Type}
  (f : A -> B)
  (l : list A)
  (n : nat)
  : List.map f (list_suffix l n) = list_suffix (List.map f l) n.
Proof.
  generalize dependent l. induction n; intros [|a l]; try reflexivity.
  simpl.
  apply IHn.
Qed.

Fixpoint list_prefix
  {A : Type}
  (l : list A)
  (n : nat)
  : list A
  := match n,l with
    | 0,_ => []
    | _,[] => []
    | S n, a :: l => a :: list_prefix l n
    end.

Lemma list_prefix_split
  {A : Type}
  (l left right: list A)
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
    destruct l;
    reflexivity.
  - intros.
    destruct left.
    + discriminate Hlen.
    + assert (left_len = length left). {
        simpl in Hlen.
        inversion Hlen.
        intuition.
      }
      specialize (IHleft_len right left H (left ++ right) eq_refl).
      rewrite Hsplit.
      simpl.
      rewrite IHleft_len.
      reflexivity.
Qed.

Lemma list_prefix_map
  {A B : Type}
  (f : A -> B)
  (l : list A)
  (n : nat)
  : List.map f (list_prefix l n) = list_prefix (List.map f l) n.
Proof.
  generalize dependent l. induction n; intros [|a l]; try reflexivity.
  simpl.
  f_equal.
  apply IHn.
Qed.

Lemma list_prefix_length
  {A : Type}
  (l : list A)
  (n : nat)
  (Hlen : n <= length l)
  : length (list_prefix l n) = n.
Proof.
  generalize dependent l. induction n; intros [|a l] Hlen; try reflexivity.
  - inversion Hlen.
  - simpl in *. f_equal.
    apply IHn.
    lia.
Qed.

Lemma list_suffix_length
  {A : Type}
  (l : list A)
  (n : nat)
  : length (list_suffix l n) = length l - n.
Proof.
  generalize dependent l. induction n; intros [|a l]; try reflexivity.
  simpl. apply IHn.
Qed.

Lemma list_prefix_prefix
  {A : Type}
  (l : list A)
  (n1 n2 : nat)
  (Hn: n1 <= n2)
  : list_prefix (list_prefix l n2) n1 = list_prefix l n1.
Proof.
  generalize dependent n1. generalize dependent n2.
  induction l; intros [|n2] [|n1] Hn; try reflexivity.
  - inversion Hn.
  - simpl. f_equal. apply IHl. lia.
Qed.

Lemma list_prefix_suffix
  {A : Type}
  (l : list A)
  (n : nat)
  : list_prefix l n ++ list_suffix l n = l.
  Proof.
   generalize dependent n. induction l; intros [|n]; try reflexivity.
   simpl.
   f_equal. apply IHl.
  Qed.

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
  apply list_prefix_prefix.
  assumption.
Qed.

Definition Forall_hd
  {A : Type}
  {P : A -> Prop}
  {a : A}
  {l : list A}
  (Hs : Forall P (a :: l))
  : P a.
Proof.
  inversion Hs. subst. exact H1.
Defined.

Definition Forall_tl
  {A : Type}
  {P : A -> Prop}
  {a : A}
  {l : list A}
  (Hs : Forall P (a :: l))
  : Forall P l.
Proof.
  inversion Hs. subst. exact H2.
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
  - exact [].
  -
  exact ((dexist a (Forall_hd Hs)) :: list_annotate A P Pdec l (Forall_tl Hs)).
Defined.

Lemma list_annotate_length
  {A : Type}
  (P : A -> Prop)
  {Pdec : forall a, Decision (P a)}
  (l : list A)
  (Hs : Forall P l)
  : length (list_annotate P l Hs) = length l.
Proof.
  induction l; [reflexivity|].
  simpl. rewrite IHl. reflexivity.
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
  induction l; [reflexivity|].
  intros; simpl.
  f_equal; [|apply IHl].
  apply dsig_eq.
  reflexivity.
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
  split; [|intro; subst; apply list_annotate_pi].
  revert Hl1 l2 Hl2.
  induction l1; destruct l2; simpl; intros.
  - reflexivity.
  - discriminate.
  - discriminate.
  - inversion H.
    apply IHl1 in H2.
    subst. reflexivity.
Qed.

Lemma list_annotate_unroll
  {A : Type}
  (P : A -> Prop)
  {Pdec : forall a, Decision (P a)}
  (a : A)
  (l : list A)
  (Hs : Forall P (a :: l))
  : list_annotate P (a :: l) Hs = dexist a (Forall_hd Hs) ::  list_annotate P l (Forall_tl Hs).
Proof.
  reflexivity.
Qed.

Lemma list_annotate_app
  {A : Type}
  (P : A -> Prop)
  {Pdec : forall a, Decision (P a)}
  (l1 l2 : list A)
  (Hs : Forall P (l1 ++ l2))
  : list_annotate P (l1 ++ l2) Hs = list_annotate P l1 (proj1 (proj1 (@Forall_app _ P l1 l2) Hs)) ++ list_annotate P l2 (proj2 (proj1 (@Forall_app _ P l1 l2) Hs)).
Proof.
  induction l1; [apply list_annotate_pi|].
  simpl. f_equal.
  - apply dsig_eq. reflexivity.
  - rewrite IHl1. f_equal; apply list_annotate_pi.
Qed.

Lemma elem_of_list_annotate_forget
  {A : Type}
  (P : A -> Prop)
  {Pdec : forall a, Decision (P a)}
  (l : list A)
  (Hs : Forall P l)
  (xP : dsig P)
  (Hin : xP ∈ (list_annotate P l Hs))
  : (proj1_sig xP) ∈ l.
Proof.
  induction l.
  - inversion Hin.
  - rewrite list_annotate_unroll,elem_of_cons in Hin.
    destruct Hin as [Heq | Hin].
    + subst xP. left.
    + right. specialize (IHl (Forall_tl Hs)). apply IHl. assumption.
Qed.

Lemma elem_of_list_annotate
  `{EqDecision A}
  (P : A -> Prop)
  {Pdec : forall a, Decision (P a)}
  (l : list A)
  (Hs : Forall P l)
  (xP : dsig P)
  : xP ∈ (list_annotate P l Hs) <-> (` xP) ∈ l.
Proof.
  split; [apply elem_of_list_annotate_forget |].
  destruct_dec_sig xP x HPx HeqxP; subst; cbn.
  induction 1; cbn; rewrite elem_of_cons, dsig_eq; cbn; auto.
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
  - exists None. split; reflexivity.
  - inversion Hs; subst. exists (Some (dexist a (Forall_hd Hs))).
    rewrite list_annotate_unroll.
    split; reflexivity.
  - exists None. split; reflexivity.
  - rewrite list_annotate_unroll.
    specialize (IHn l (Forall_tl Hs)).
    destruct IHn as [oa [Hoa Hnth]].
    exists oa.
    split; assumption.
Qed.

Fixpoint nth_error_filter_index
  {A} P `{∀ (x:A), Decision (P x)}
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
  {A} P `{∀ (x:A), Decision (P x)}
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
  induction l; intros.
  - inversion Hin1.
  - simpl in Hin1. simpl in Hin2.
    destruct (decide (P a)).
    + destruct n1; destruct n2.
      * inversion Hin1; inversion Hin2; subst; assumption.
      * destruct (nth_error_filter_index P l n2)
        ; inversion Hin1; inversion Hin2; subst.
        lia.
      * inversion Hle.
      * { destruct in1, in2.
        - lia.
        - lia.
        - destruct (nth_error_filter_index P l n2); inversion Hin2.
        - assert (Hle' : n1 <= n2) by lia.
          specialize (IHl n1 n2 Hle').
          destruct (nth_error_filter_index P l n1) eqn:Hin1'; inversion Hin1;
          subst; clear Hin1.
          destruct (nth_error_filter_index P l n2) eqn:Hin2'; inversion Hin2
          ; subst; clear Hin2.
          specialize (IHl in1 eq_refl in2 eq_refl).
          lia.
        }
    + specialize (IHl n1 n2 Hle).
      destruct (nth_error_filter_index P l n1) eqn:Hin1'; inversion Hin1
      ; subst; clear Hin1.
      destruct (nth_error_filter_index P l n2) eqn:Hin2'; inversion Hin2
      ; subst; clear Hin2.
      specialize (IHl n0 eq_refl n3 eq_refl).
      lia.
Qed.

Lemma nth_error_filter
  {A} P `{∀ (x:A), Decision (P x)}
  (l : list A)
  (n : nat)
  (a : A)
  (Hnth : nth_error (filter P l) n = Some a)
  : exists (nth : nat),
    nth_error_filter_index P l n = Some nth
    /\ nth_error l nth = Some a.
Proof.
  generalize dependent a. generalize dependent n.
  induction l.
  - intros; simpl in Hnth. destruct n; inversion Hnth.
  - intros. rewrite filter_cons in Hnth. simpl. destruct (decide (P a)).
    + destruct n.
      * inversion Hnth; subst. exists 0; split; reflexivity.
      * simpl in Hnth.
        specialize (IHl n a0 Hnth).
        destruct IHl as [nth [Hnth' Ha0]].
        exists (S nth).
        split; try assumption.
        rewrite Hnth'.
        reflexivity.
    + specialize (IHl n a0 Hnth).
      destruct IHl as [nth [Hnth' Ha0]].
      exists (S nth).
      split; try assumption.
      rewrite Hnth'.
      reflexivity.
Qed.

Fixpoint Forall_filter
  {A : Type}
  (P : A -> Prop)
  {Pdec : forall a : A, Decision (P a)}
  (l : list A) : Forall P (filter P l).
Proof.
 destruct l; simpl.
 - exact (List.Forall_nil P).
 - specialize (Forall_filter A P _ l).
    unfold filter,list_filter.
    destruct (decide (P a)).
    + constructor; assumption.
    + assumption.
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
  unfold filter_annotate, filter.
  simpl.
  destruct (decide _); reflexivity.
Qed.

Lemma filter_annotate_app
  {A : Type}
  (P : A -> Prop)
  {Pdec : forall a : A, Decision (P a)}
  (l1 l2 : list A)
  : filter_annotate P (l1 ++ l2) = filter_annotate P l1 ++ filter_annotate P l2.
Proof.
  induction l1; [reflexivity|].
  simpl. rewrite! filter_annotate_unroll. rewrite IHl1. clear IHl1.
  destruct (decide _); reflexivity.
Qed.

(** Filters a list through a predicate, then transforms each element using a
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
  unfold list_filter_map. rewrite filter_annotate_app, map_app. reflexivity.
Qed.

Lemma list_prefix_nth
  {A : Type}
  (s : list A)
  (n : nat)
  (i : nat)
  (Hi : i < n)
  : nth_error (list_prefix s n) i = nth_error s i.
Proof.
  generalize dependent n. generalize dependent s.
  induction i; intros [|a s] [|n] Hi; try reflexivity.
  - inversion Hi.
  - inversion Hi.
  - simpl.
    assert (Hi': i < n) by lia.
    specialize (IHi s n Hi').
    rewrite IHi.
    reflexivity.
Qed.

Lemma nth_error_length
  {A : Type}
  (l : list A)
  (n : nat)
  (a : A)
  (Hnth : nth_error l n = Some a)
  : S n <= length l.
Proof.
  generalize dependent a. generalize dependent l.
  induction n; intros [|a l] b Hnth; simpl; inversion Hnth.
  - lia.
  - specialize (IHn l b H0).
    lia.
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
  rewrite <- Hpref in Hnth.
  - specialize (nth_error_last (list_prefix l (S n)) n Hpref_len _last); intro Hlast.
    rewrite Hlast in Hnth. inversion Hnth.
    reflexivity.
  - constructor.
Qed.

Lemma list_suffix_nth
  {A : Type}
  (s : list A)
  (n : nat)
  (i : nat)
  (Hi : n <= i)
  : nth_error (list_suffix s n) (i - n) = nth_error s i.
Proof.
  generalize dependent n. generalize dependent s.
  induction i; intros [|a s] [|n] Hi; try reflexivity.
  - inversion Hi.
  - simpl. apply nth_error_None. simpl. lia.
  - simpl.
    apply IHi.
    lia.
Qed.

Lemma list_suffix_lookup
  {A : Type}
  (s : list A)
  (n : nat)
  (i : nat)
  (Hi : n <= i)
  : list_suffix s n !! (i - n) = s !! i.
Proof.
  revert s n Hi.
  induction i; intros [|a s] [|n] Hi
  ; [reflexivity|reflexivity|reflexivity|lia|reflexivity|reflexivity|reflexivity|].
  simpl.
  apply IHi.
  lia.
Qed.

Lemma list_suffix_last
  {A : Type}
  (l : list A)
  (i : nat)
  (Hlt : i < length l)
  (_default : A)
  : List.last (list_suffix l i) _default  = List.last l _default.
Proof.
  generalize dependent l. induction i; intros [|a l] Hlt
  ; try reflexivity.
  simpl in Hlt.
  assert (Hlt': i < length l) by lia.
  specialize (IHi l Hlt').
  rewrite unroll_last. simpl.
  rewrite IHi.
  destruct l.
  - inversion Hlt; lia.
  - rewrite unroll_last. rewrite unroll_last. reflexivity.
Qed.

Lemma list_suffix_last_default
  {A : Type}
  (l : list A)
  (i : nat)
  (Hlast : i = length l)
  (_default : A)
  : List.last (list_suffix l i) _default  = _default.
Proof.
  generalize dependent l. induction i; intros [|a l] Hlast
  ; try reflexivity.
  - inversion Hlast.
  - simpl in Hlast. inversion Hlast.
  specialize (IHi l H0).
  simpl. subst.
  assumption.
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
  rewrite list_suffix_nth; try assumption.
  apply list_prefix_nth.
  assumption.
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
  apply app_inv_head in Hl1.
  symmetry.
  assumption.
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
    by (apply nth_error_length in Hnth; assumption).
  assert (Hlt : n < length (list_prefix l (S n)))
    by (rewrite list_prefix_length; try constructor; assumption).
  specialize (list_suffix_last (list_prefix l (S n)) n Hlt a); intro Hlast1.
  specialize (list_prefix_nth_last l n a Hnth a); intro Hlast2.
  rewrite <- Hlast2 in Hlast1.
  specialize (list_suffix_length (list_prefix l (S n)) n).
  rewrite list_prefix_length; try assumption.
  intro Hlength.
  assert (Hs: S n - n = 1) by lia.
  rewrite Hs in Hlength.
  remember (list_suffix (list_prefix l (S n)) n) as x.
  clear -Hlength Hlast1.
  destruct x; inversion Hlength.
  destruct x; inversion H0.
  simpl in Hlast1; subst; reflexivity.
Qed.

Lemma nth_error_map
  {A B : Type}
  (f : A -> B)
  (l : list A)
  (n : nat)
  : nth_error (List.map f l) n = option_map f (nth_error l n).
Proof.
  generalize dependent n.
  induction l; intros [|n]; try reflexivity; simpl.
  apply IHl.
Qed.

Lemma exists_finite
  `{finite.Finite index}
  (P : index -> Prop)
  : (exists n : index, P n) <-> Exists P (enum index).
Proof.
  rewrite Exists_exists; split.
  - intros [n Hn]; eexists; split; [apply elem_of_enum | eassumption].
  - intros (n & _ & Hn); eexists; eassumption.
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
      end
    )
    [].

Lemma map_option_comp_r
  [A B C : Type] (f : A -> B) (g : B -> option C) :
    map_option (g ∘ f) = map_option g ∘ map f.
Proof.
  extensionality l.
  induction l; cbn; rewrite ?IHl; reflexivity.
Qed.

Lemma map_option_comp_l
  [A B C : Type]
  (f : A -> option B)
  (g : B -> C)
  : map_option (option_map g ∘ f) = map g ∘ map_option f.
Proof.
  extensionality l.
  induction l; [reflexivity|].
  cbn.
  rewrite IHl.
  destruct (f a) as [b|]; reflexivity.
Qed.

Lemma map_option_comp_bind
  [A B C : Type]
  (f : A -> option B)
  (g : B -> option C)
  : map_option (mbind g ∘ f) = map_option g ∘ map_option f.
Proof.
  extensionality l.
  induction l; [reflexivity|]; cbn; rewrite IHl.
  destruct (f a) as [b|]; reflexivity.
Qed.

Lemma map_option_app
  {A B : Type}
  (f : A -> option B)
  l1 l2
  : map_option f (l1 ++ l2) = map_option f l1 ++ map_option f l2.
Proof.
  induction l1; [reflexivity|].
  change (a :: l1) with ([a] ++ l1).
  rewrite <- app_assoc. simpl.
  rewrite IHl1.
  destruct (f a); [|reflexivity].
  change (b :: map_option f l1) with ([b] ++ map_option f l1).
  rewrite <- app_assoc. reflexivity.
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
    apply app_eq_nil in Happ_rev as [Hl1' Hl2'].
    subst. exists [], []. repeat split.
  - simpl in Happ_rev.
    destruct (f a) eqn:Hfa; swap 1 2.
    + specialize (IHl _ _ Happ_rev) as [_l1 [l2 [Hl [H_l1 Hl2]]]].
      subst.
      exists (a :: _l1), l2.
      repeat split. simpl. rewrite Hfa. reflexivity.
    + destruct l1' as [|_b l1']; swap 1 2.
      * change (_b :: l1') with ([_b] ++ l1') in Happ_rev.
        rewrite <- app_assoc in Happ_rev. inversion Happ_rev.
        subst _b.
        specialize (IHl _ _ H1) as [_l1 [l2 [Hl [H_l1 Hl2]]]].
        subst.
        exists (a :: _l1), l2.
        repeat split. simpl. rewrite Hfa. reflexivity.
      * simpl in Happ_rev. subst.
        exists [], (a :: l).
        repeat split. simpl. rewrite Hfa. reflexivity.
Qed.

Lemma map_option_length
  {A B : Type}
  (f : A -> option B)
  (l : list A)
  (Hfl : Forall (fun a => f a <> None) l)
  : length (map_option f l) = length l.
Proof.
  induction l; try reflexivity.
  inversion Hfl; subst.
  spec IHl H2.
  simpl.
  destruct (f a); try (elim H1; reflexivity).
  simpl. f_equal. assumption.
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
  induction l; intros; simpl in *. { lia. }
  inversion Hfl. subst. spec IHl H2.
  destruct (f a) eqn: Hfa; try (elim H1; reflexivity).
  symmetry in Hfa.
  destruct i; try assumption.
  spec IHl i.
  spec IHl. { lia. }
  assumption.
Qed.

Lemma elem_of_map_option
  {A B : Type}
  (f : A -> option B)
  (l : list A)
  (b : B)
  : b ∈ map_option f l <-> exists a : A, a ∈ l /\ f a = Some b.
Proof.
  induction l as [| h t]; cbn.
  - setoid_rewrite elem_of_nil. firstorder.
  - destruct (f h) eqn: Heq; setoid_rewrite elem_of_cons
    ; firstorder; subst; intuition congruence + eauto.
Qed.

Lemma elem_of_map_option_rev
  {A B : Type}
  (f : A -> option B)
  (a : A)
  (b : B)
  (Hab : f a = Some b)
  (l : list A)
  : a ∈ l -> b ∈ map_option f l.
Proof.
  intro Ha; apply elem_of_map_option; exists a; intuition.
Qed.

Lemma in_map_option
  {A B : Type}
  (f : A -> option B)
  (l : list A)
  (b : B)
  : In b (map_option f l) <-> exists a : A, In a l /\ f a = Some b.
Proof.
  setoid_rewrite <- elem_of_list_In; apply elem_of_map_option.
Qed.

Lemma in_map_option_rev
  {A B : Type}
  (f : A -> option B)
  (a : A)
  (b : B)
  (Hab : f a = Some b)
  (l : list A)
  : In a l -> In b (map_option f l).
Proof.
  setoid_rewrite <- elem_of_list_In; apply elem_of_map_option_rev; assumption.
Qed.

(** [map_option] can be expressed as a [list_filter_map].
*)
Lemma map_option_as_filter
  {A B : Type}
  (f : A -> option B)
  (l : list A)
  : map_option f l = list_filter_map (is_Some ∘ f) (fun x => is_Some_proj (proj2_dsig x)) l.
Proof.
  induction l using rev_ind; [reflexivity|].
  rewrite map_option_app, IHl. clear IHl.
  rewrite list_filter_map_app. f_equal.
  cbn.
  destruct (decide _).
  - cbv. destruct (f x); [reflexivity|elim (is_Some_None (A := B)); assumption].
  - simpl. destruct (f x); [|reflexivity]. elim n. eexists; reflexivity.
Qed.

(* Unpack list of [option A] into list of [A] *)
Definition cat_option {A : Type} : list (option A) -> list A :=
  @map_option (option A) A id.

Example cat_option1 : cat_option [Some 1; Some 5; None; Some 6; None] = [1; 5; 6].
Proof. intuition. Qed.

Lemma cat_option_length
  {A : Type}
  (l : list (option A))
    (Hfl : Forall (fun a => a <> None) l)
  : length (cat_option l) = length l.
Proof.
  apply map_option_length; intuition.
Qed.

Lemma cat_option_length_le
  {A : Type}
  (l : list (option A))
  : length (cat_option l) <= length l.
Proof.
  induction l.
  - intuition.
  - simpl.
    destruct (id a) eqn : eq_id; simpl in *; subst a; simpl; lia.
Qed.

Lemma cat_option_app
  {A : Type}
  (l1 l2 : list (option A)) :
  cat_option (l1 ++ l2) = cat_option l1 ++ cat_option l2.
Proof.
  induction l1.
  - simpl in *. intuition.
  - destruct a eqn : eq_a;
      simpl in *;
      rewrite IHl1;
      reflexivity.
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
  specialize (@map_option_nth (option A) A id l). simpl in *.
  intros.
  unfold id in *.
  apply H.
  all : intuition.
Qed.

Lemma in_cat_option
  {A : Type}
  (l : list (option A))
  (a : A)
  : In a (cat_option l) <-> exists b : (option A), In b l /\ b = Some a.
Proof.
  apply in_map_option.
Qed.

Lemma map_option_incl
  {A B : Type}
  (f : A -> option B)
  (l1 l2 : list A)
  (Hincl : incl l1 l2)
  : incl (map_option f l1) (map_option f l2).
Proof.
  intro b. repeat rewrite in_map_option.
  firstorder.
Qed.

Lemma nth_error_eq
  {A : Type}
  (l1 l2 : list A)
  (Hnth: forall n : nat, nth_error l1 n = nth_error l2 n)
  : l1 = l2.
Proof.
  generalize dependent l2.
  induction l1; intros [| a2 l2] Hnth; try reflexivity.
  - specialize (Hnth 0); simpl in Hnth. inversion Hnth.
  - specialize (Hnth 0); simpl in Hnth. inversion Hnth.
  - assert (H0 := Hnth 0). simpl in H0.
    inversion H0; subst.
    f_equal.
    apply IHl1.
    intro n.
    specialize (Hnth (S n)).
    assumption.
Qed.

Lemma occurrences_ordering
  {A : Type}
  (a b : A)
  (la1 la2 lb1 lb2 : list A)
  (Heq : la1 ++ a :: la2 = lb1 ++ b :: lb2)
  (Ha : ~a ∈ (b :: lb2))
  : exists lab : list A, lb1 = la1 ++ a :: lab.
Proof.
  generalize dependent lb2. generalize dependent la2.
  generalize dependent b. generalize dependent lb1.
  generalize dependent a.
  induction la1; intros; destruct lb1 as [|b0 lb1]; simpl in *
  ; inversion Heq; subst.
  - rewrite elem_of_cons in Ha.
    destruct Ha. left. reflexivity.
  - exists lb1. reflexivity.
  - rewrite elem_of_cons in Ha.
    destruct Ha. right.
    apply elem_of_app.
    right; left; reflexivity.
  - specialize (IHla1 a0 lb1 b la2 lb2 H1 Ha).
    destruct IHla1 as [la0b Hla0b].
    exists la0b. subst. reflexivity.
Qed.

(* TODO remove (we have Exists_first) *)
Lemma exists_first
  {A : Type}
  (l : list A)
  (P : A -> Prop)
  (Pdec : forall a : A, {P a } + {~P a})
  (Hsomething : Exists P l) :
  exists (prefix : list A)
         (suffix : list A)
         (first : A),
         (P first) /\
         l = prefix ++ [first] ++ suffix /\
         ~Exists P prefix.
Proof.
  induction l.
  - inversion Hsomething.
  - destruct (Pdec a).
    + exists []. exists l. exists a. repeat split; try assumption.
      intro H; inversion H.
    + assert (Hl : Exists P l).
      { inversion Hsomething; subst; try (elim n; assumption). assumption. }
      specialize (IHl Hl).
      destruct IHl as [prefix [suffix [first [Hfirst [Heq Hprefix]]]]].
      exists (a :: prefix). exists suffix. exists first. repeat split; try assumption.
      * simpl. subst. reflexivity.
      * intro Hprefix'. inversion Hprefix'; try (elim n; assumption).
        elim Hprefix. assumption.
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
  destruct Hin.
  - subst. elim Hneq. reflexivity.
  - assumption.
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
  - inversion H.
  - destruct pre; inversion H.
  - inversion H; subst.
    + reflexivity.
    + apply elem_of_list_fmap in H2 as [x0 [Heq Hin]].
      destruct x0 as ((prex0,x0),sufx0).
      specialize (IHl prex0 x0 sufx0).
      apply IHl in Hin.
      subst l.
      inversion Heq. reflexivity.
  - destruct pre.
    + inversion H. left.
    + right. apply elem_of_list_fmap.
      rewrite <- app_comm_cons in H.
      inversion H. subst. clear H.
      exists (pre, x, suf).
      split; try reflexivity.
      apply IHl. reflexivity.
Qed.

Lemma in_one_element_decompositions_iff
  {A : Type}
  (l : list A)
  (pre suf : list A)
  (x : A)
  : In (pre, x, suf) (one_element_decompositions l)
  <-> pre ++ [x] ++ suf = l.
Proof.
  rewrite <- elem_of_list_In. apply elem_of_one_element_decompositions.
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
          (fun t => match t with (l2',e2, l3) => (l1, e1, l2', e2, l3) end)
          (one_element_decompositions l2)
      end
    )
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
    subst sufx l. reflexivity.
  - remember (mid ++ [y] ++ suf) as sufx.
    intro H.
    exists (pre, x, sufx). apply in_one_element_decompositions_iff in H.
    split; try assumption.
    apply in_map_iff. exists (mid, y, suf).
    split; try reflexivity.
    apply in_one_element_decompositions_iff. symmetry. assumption.
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
  generalize dependent Heq.
  generalize dependent Heql.
  revert pre1 suf1 pre2 suf2.
  induction l; intros.
  - left.
    symmetry in Heql. apply app_eq_nil in Heql. destruct Heql as [Hpre1 _]. subst pre1.
    symmetry in Heq. apply app_eq_nil in Heq. destruct Heq as [Hpre2 _]. subst pre2.
    reflexivity.
  - destruct pre1 as [| a1 pre1]; destruct pre2 as [|a2 pre2].
    + left. reflexivity.
    + right. right. exists (a2 :: pre2). reflexivity.
    + right. left. exists (a1 :: pre1). reflexivity.
    + inversion Heql. subst a1. clear Heql.
      inversion Heq. subst a2. clear Heq.
      specialize (IHl pre1 suf1 pre2 suf2 H1 H2).
      destruct IHl as [Heq | [Hgt | Hlt]].
      * left. f_equal. assumption.
      * destruct Hgt as [suf1' Hgt].
        right. left. exists suf1'. simpl. f_equal. assumption.
      * destruct Hlt as [suf2' Hlt].
        right. right. exists suf2'. simpl. f_equal. assumption.
Qed.

Lemma list_max_exists
   (l : list nat)
   (nz : list_max l > 0) :
   In (list_max l) l.
Proof.
  induction l.
  - simpl in nz. lia.
  - simpl in *.
    destruct (a <=? (list_max l)) eqn : eq_leb.
    + assert (Nat.max a (list_max l) = list_max l). {
         apply max_r.
         apply Nat.leb_le.
         assumption.
      }
      rewrite H in *.
      right.
      apply IHl.
      assumption.
    + assert (Nat.max a (list_max l) = a). {
        apply leb_iff_conv in eq_leb.
        apply max_l.
        lia.
      }
      rewrite H in *.
      left.
      reflexivity.
Qed.

Lemma list_max_exists2
   (l : list nat)
   (Hne : l <> []) :
   In (list_max l) l.
Proof.
  destruct (list_max l) eqn : eq_max.
  - destruct l;[intuition congruence|].
    specialize (list_max_le (n :: l) 0) as Hle.
    destruct Hle as [Hle _].
    rewrite eq_max in Hle. spec Hle. apply Nat.le_refl.
    rewrite Forall_forall in Hle.
    specialize (Hle n). spec Hle; [left |].
    simpl. lia.
  - specialize (list_max_exists l) as Hmax.
    spec Hmax. lia. rewrite <- eq_max. intuition.
Qed.

Lemma list_max_elem_of_exists
   (l : list nat)
   (nz : list_max l > 0) :
   (list_max l) ∈ l.
Proof.
  induction l; [simpl in nz; lia|].
  simpl in *.
  destruct (decide (a <= list_max l)) as [Hle|Hle].
  - assert (Nat.max a (list_max l) = list_max l). {
      apply max_r.
      assumption.
    }
    rewrite H in *.
    right.
    apply IHl.
    assumption.
  - assert (Nat.max a (list_max l) = a). {
      apply max_l.
      lia.
    }
    rewrite H in *.
    left.
Qed.

Lemma list_max_elem_of_exists2
   (l : list nat)
   (Hne : l <> []) :
   (list_max l) ∈ l.
Proof.
  destruct (list_max l) eqn : eq_max.
  - destruct l;[intuition congruence|].
    specialize (list_max_le (n :: l) 0) as Hle.
    destruct Hle as [Hle _].
    rewrite eq_max in Hle. spec Hle. apply Nat.le_refl.
    rewrite Forall_forall in Hle.
    specialize (Hle n). spec Hle. left.
    assert (Hn0: n = 0) by lia.
    rewrite Hn0; left.
  - specialize (list_max_elem_of_exists l) as Hmax.
    spec Hmax. lia. rewrite <- eq_max.
    assumption.
Qed.

(* Returns all values which occur with maximum frequency in the given list.
   Note that these values are returned with their original multiplicity. *)

Definition mode
  `{EqDecision A}
  (l : list A) : list A  :=
  let mode_value := list_max (List.map (count_occ decide_eq l) l) in
  filter (fun a => (count_occ decide_eq l a) = mode_value) l.

Example mode1 : mode [1; 1; 2; 3; 3] = [1; 1; 3; 3].
Proof. intuition. Qed.

Lemma mode_not_empty
  `{EqDecision A}
  (l : list A)
  (Hne : l <> []) :
  mode l <> [].
Proof.
  destruct l.
  elim Hne. reflexivity.
  remember (a :: l) as l'.
  remember (List.map (count_occ decide_eq l') l') as occurrences.

  assert (Hmaxp: list_max occurrences > 0). {
    rewrite Heqoccurrences.
    rewrite Heql'.
    simpl.
    rewrite decide_True.
    lia.
    reflexivity.
  }

  assert (exists a, (count_occ decide_eq l' a) = list_max occurrences). {
    assert (In (list_max occurrences) occurrences). {
      apply list_max_exists.
      rewrite Heqoccurrences.
      rewrite Heql'.
      rewrite Heqoccurrences in Hmaxp.
      rewrite Heql' in Hmaxp.
      assumption.
    }
    rewrite Heqoccurrences in H.
    rewrite in_map_iff in H.
    destruct H as [x [Heq Hin]].
    exists x.
    rewrite Heqoccurrences.
    assumption.
  }

  assert (exists a, In a (mode l')). {
    destruct H.
    exists x.
    specialize (count_occ_In decide_eq l' x).
    intros.
    destruct H0 as [_ H1].
    rewrite H in H1.
    specialize (H1 Hmaxp).
    unfold mode.
    apply filter_in.
    assumption.
    rewrite Heqoccurrences in H.
    rewrite H.
    reflexivity.
  }
  destruct H.
  intros contra.
  rewrite contra in H0.
  destruct H0.
  intuition.
Qed.

(* Computes the list suff which satisfies <<pref ++ suff = l>> or
   reports that no such list exists. *)

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

Example complete_prefix_some : complete_prefix [1;2;3;4] [1;2] = Some [3;4].
Proof. intuition. Qed.
Example complete_prefix_none : complete_prefix [1;2;3;4] [1;3] = None.
Proof. intuition. Qed.

Lemma complete_prefix_empty
  `{EqDecision A}
  (l : list A) :
  complete_prefix l [] = Some l.
Proof.
  induction l.
  - simpl. reflexivity.
  - simpl.
    destruct (complete_prefix l []).
    inversion IHl.
    reflexivity.
    discriminate IHl.
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
      destruct pref; destruct suff;
      try reflexivity;
      try discriminate H.
    + intros.
      unfold complete_prefix.
      destruct pref.
      * specialize (IHl [] l).
        spec IHl.
        intuition.
        rewrite app_nil_l in H.
        f_equal. intuition.
      * destruct (decide (a = a0)) eqn : eq_d.
        specialize (IHl pref suff).
        unfold complete_prefix in IHl.
        rewrite IHl.
        reflexivity.
        simpl in H.
        inversion H.
        reflexivity.
        inversion H.
        elim n. assumption.
   - generalize dependent suff.
     generalize dependent pref.
     induction l; intros.
     + destruct pref; destruct suff;
       try intuition;
       try discriminate H.
     + destruct pref eqn : eq_pref.
       rewrite complete_prefix_empty in H.
       inversion H.
       intuition.
       simpl.
       simpl in H.
       destruct (decide (a = a0)).
       destruct (complete_prefix l l0) eqn : eq_cp.
       inversion H.
       rewrite e.
       f_equal.
       specialize (IHl l0 suff).
       spec IHl.
       rewrite eq_cp.
       f_equal. assumption.
       assumption.
       discriminate H.
       discriminate H.
Qed.

(* Computes the list pref which satisfies <<pref ++ suff = l>> or
   reports that no such list exists. *)

Definition complete_suffix
  `{EqDecision A}
  (l suff : list A) : option (list A) :=
  let res := complete_prefix (rev l) (rev suff) in
  match res with
  | None => None
  | Some ls => Some (rev ls)
  end.

Example complete_suffix_some : complete_suffix [1;2;3;4] [3;4] = Some [1;2].
Proof. intuition. Qed.

Lemma complete_suffix_correct
  `{EqDecision A}
  (l pref suff : list A) :
  l = pref ++ suff <->
  complete_suffix l suff = Some pref.
Proof.
  unfold complete_suffix.
  split.
  - intros.
    destruct (complete_prefix (rev l) (rev suff)) eqn : eq_c.
    apply complete_prefix_correct in eq_c.
    rewrite H in eq_c.
    rewrite rev_app_distr in eq_c.
    assert (l0 = rev pref). {
      apply app_inv_head in eq_c.
      symmetry.
      assumption.
    }
    rewrite H0.
    f_equal.
    apply rev_involutive.
    assert (rev l = rev suff ++ rev pref). {
      apply rev_eq_app.
      rewrite rev_involutive.
      assumption.
    }
    apply complete_prefix_correct in H0.
    rewrite eq_c in H0.
    discriminate H0.
  - destruct (complete_prefix (rev l) (rev suff)) eqn : eq_c.
    intros.
    inversion H.
    apply complete_prefix_correct in eq_c.
    apply rev_eq_app in eq_c.
    rewrite rev_involutive in eq_c.
    assumption.
    intros.
    discriminate H.
Qed.

Lemma complete_suffix_empty
  `{EqDecision A}
  (l : list A) :
  complete_suffix l [] = Some l.
Proof.
  unfold complete_suffix. simpl.
  rewrite complete_prefix_empty.
  f_equal.
  apply rev_involutive.
Qed.

(** elements belonging to first type in a list of a sum type *)
Definition list_sum_project_left
  {A B : Type}
  (x : list (A + B))
  : list A
  :=
  map_option sum_project_left x.

(** elements belonging to second type in a list of a sum type *)
Definition list_sum_project_right
  {A B : Type}
  (x : list (A + B))
  : list B
  :=
  map_option sum_project_right x.

Lemma fold_right_andb_false l:
  fold_right andb false l = false.
Proof.
  induction l.
  - reflexivity.
  - simpl. rewrite IHl. apply andb_false_r.
Qed.

Definition Listing_finite_transparent `{EqDecision A} {l : list A} (finite_l : Listing l) : finite.Finite A.
Proof.
  exists l.
  - apply NoDup_ListNoDup. apply finite_l.
  - intro. apply elem_of_list_In. apply finite_l.
Defined.

Lemma Listing_finite `{EqDecision A} {l : list A} (finite_l : Listing l) : finite.Finite A.
Proof.
  apply (Listing_finite_transparent finite_l).
Qed.

Lemma sumbool_forall [A : Type] [P Q : A → Prop]:
  (∀ x : A, {P x} + {Q x}) → ∀ l : list A, {Forall P l} + {Exists Q l}.
Proof.
  induction l.
  left. constructor.
  refine (if X a then if IHl then left _ else right _ else right _);constructor;assumption.
Qed.

Lemma list_sum_decrease [A:Type] (f g: A -> nat) (l: list A):
  (forall a, In a l -> f a <= g a) -> Exists (fun a => f a < g a) l ->
  list_sum (map f l) < list_sum (map g l).
Proof.
  induction 2.
  - simpl.
    apply PeanoNat.Nat.add_lt_le_mono.
    assumption.
    induction l.
    + reflexivity.
    + simpl. apply PeanoNat.Nat.add_le_mono.
      apply H. firstorder.
      apply IHl. firstorder.
  - simpl.
    apply PeanoNat.Nat.add_le_lt_mono.
    apply H;left;reflexivity.
    apply IHExists. intros;apply H;right;assumption.
Qed.

(* Nearly the natural induction principle for fold_left.
   Useful if you can think of [[fold_left f]] as transforming
   a list into a [[B -> B]] function, and can describe the
   effect with a [[P : list A -> relation B]].
   The assumption [[Hstep]] could be weakened by replacing [[r]]
   with [[fold_left f l (f x a)]], but that isn't useful in
   natural examples.
 *)
Lemma fold_left_ind
      [A B:Type] (f: B -> A -> B) (P : list A -> B -> B -> Prop)
      (Hstart : forall x, P nil x x)
      (Hstep : forall x a l r,
          P l (f x a) r ->
          P (a :: l) x r):
  forall l x, P l x (fold_left f l x).
Proof.
  induction l.
  apply Hstart.
  intro x.
  apply Hstep, IHl.
Qed.

(* An induction principle for fold_left which
   decomposes the list from the right
 *)
Lemma fold_left_ind_rev
      [A B:Type] (f: B -> A -> B) (x0: B)
      (P : list A -> B -> Prop)
      (Hstart : P nil x0)
      (Hstep: forall l a x, P l x -> P (l++a::nil) (f x a)):
  forall l, P l (fold_left f l x0).
Proof.
  induction l using rev_ind.
  - apply Hstart.
  - rewrite fold_left_app. simpl.
    apply Hstep. assumption.
Qed.

Section suffix_quantifiers.

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
Proof.
  inversion 1; assumption.
Qed.

Lemma fsFurther : forall a l, ForAllSuffix (a :: l) -> ForAllSuffix l.
Proof.
  inversion 1; assumption.
Qed.

Lemma ForAll_list_suffix : forall m x, ForAllSuffix x -> ForAllSuffix (list_suffix x m).
Proof.
  induction m; simpl; intros; [assumption|destruct x].
  - assumption.
  - apply fsFurther in H. apply IHm. assumption.
Qed.

Lemma ForAllSuffix_induction
  (Inv : list A -> Prop)
  (InvThenP : forall l, Inv l -> P l)
  (InvIsStable : forall a l, Inv (a :: l) -> Inv l)
  : forall l, Inv l -> ForAllSuffix l.
Proof.
  induction l; intros.
  - constructor. apply InvThenP. assumption.
  - constructor.
    + apply InvThenP. assumption.
    + apply IHl. apply InvIsStable in H. assumption.
Qed.

End suffix_quantifiers.

Lemma ForAllSuffix_subsumption [A : Type] (P Q : list A -> Prop)
  (HPQ : forall l, P l -> Q l)
  : forall l, ForAllSuffix P l -> ForAllSuffix Q l.
Proof.
  induction 1; constructor.
  - apply HPQ. assumption.
  - apply HPQ. assumption.
  - assumption.
Qed.

Definition ForAllSuffix1 [A : Type] (P : A -> Prop) : list A -> Prop :=
  ForAllSuffix (fun l => match l with | [] => True | a :: _ => P a end).

Lemma ForAllSuffix1_Forall [A : Type] (P : A -> Prop)
  : forall l, ForAllSuffix1 P l <-> Forall P l.
Proof.
  split; induction 1; constructor; auto.
Qed.

Definition ExistsSuffix1 [A : Type] (P : A -> Prop) : list A -> Prop :=
  ExistsSuffix (fun l => match l with | [] => False | a :: _ => P a end).

Lemma ExistsSuffix1_Exists [A : Type] (P : A -> Prop)
  : forall l, ExistsSuffix1 P l <-> Exists P l.
Proof.
  split; induction 1.
  - destruct l; [contradiction|]. left. assumption.
  - right. assumption.
  - left. assumption.
  - right. assumption.
Qed.

Definition ForAllSuffix2 [A : Type] (R : A -> A -> Prop) : list A -> Prop :=
  ForAllSuffix (fun l => match l with | a :: b :: _ => R a b | _ => True end).

Lemma ForAllSuffix2_lookup [A : Type] (R : A -> A -> Prop) l
  : ForAllSuffix2 R l <-> forall n a b, l !! n = Some a -> l !! (S n) = Some b -> R a b.
Proof.
  split.
  - intros Hall n. apply ForAll_list_suffix with (m := n) in Hall.
    specialize (list_suffix_lookup l n n) as Hn.
    spec Hn; [lia|]. rewrite <- Hn. clear Hn.
    specialize (list_suffix_lookup l n (S n)) as Hn.
    spec Hn; [lia|]. rewrite <- Hn. clear Hn.
    replace (n - n) with 0 by lia.
    replace (S n - n) with 1 by lia.
    revert Hall. generalize (list_suffix l n).
    intros l0 Hall a b Ha Hb.
    destruct l0 as [|_a l0]; inversion Ha; subst _a; clear Ha.
    destruct l0 as [|_b l0]; inversion Hb; subst _b; clear Hb.
    apply fsHere in Hall. assumption.
  - apply
      (ForAllSuffix_induction
        (fun l => match l with | a :: b :: _ => R a b | _ => True end)
        (fun l => (∀ (n : nat) (a b : A),
          l !! n = Some a → l !! (S n) = Some b → R a b))); intros.
    + specialize (H 0).
      destruct l0 as [|a l0]; [exact I|].
      destruct l0 as [|b l0]; [exact I|].
      exact (H a b eq_refl eq_refl).
    + exact (H (S n) a0 b H0 H1).
Qed.

Lemma fsFurther2_transitive [A : Type] (R : A -> A -> Prop) {HT : Transitive R}
  : forall a b l, ForAllSuffix2 R (a::b::l) -> ForAllSuffix2 R (a::l).
Proof.
  inversion 1. subst. destruct l.
  - constructor; [exact I|]. constructor. exact I.
  - inversion H3. subst.
    constructor; [|assumption].
    transitivity b; assumption.
Qed.

Lemma ForAllSuffix2_transitive_lookup [A : Type] (R : A -> A -> Prop) {HT : Transitive R}
  : forall l, ForAllSuffix2 R l <-> forall m n a b, m < n -> l !! m = Some a -> l !! n = Some b -> R a b.
Proof.
  intro l.
  rewrite ForAllSuffix2_lookup.
  split; intro Hall.
  2: { intros n a b.  apply Hall.  lia.  }
  intros m n a b Hlt.
  apply le_plus_dec in Hlt as [k Hlt].
  subst n. revert a b. induction k; simpl; [apply Hall|].
  intros a b Ha Hb.
  assert (Hlt : k + S m < length l).
  { apply lookup_lt_Some in Hb. lia. }
  apply lookup_lt_is_Some in Hlt as [c Hc].
  specialize (Hall _ _ _ Hc Hb).
  specialize (IHk  _ _ Ha Hc).
  transitivity c; assumption.
Qed.

Lemma ForAllSuffix2_filter [A : Type] (R : A -> A -> Prop) `{HT : Transitive _ R}
  (P : A -> Prop) {Pdec : forall a, Decision (P a)}
  : forall l, ForAllSuffix2 R l -> ForAllSuffix2 R (filter P l).
Proof.
  induction l; [exact id|].
  intro Hl.
  unfold filter. simpl.
  spec IHl; [apply fsFurther in Hl; assumption|].
  case_decide; [|assumption].
  constructor; [|assumption].
  clear IHl H.
  induction l; [exact I|].
  spec IHl.
  { revert Hl. apply fsFurther2_transitive. assumption.
  }
  cbn. case_decide; [|assumption].
  inversion Hl. assumption.
Qed.


Lemma list_subseteq_tran : forall (A : Type) (l m n : list A),
 l ⊆ m → m ⊆ n → l ⊆ n.
Proof.
intros A l m n Hlm Hmn x y.
apply Hmn.
apply Hlm.
assumption.
Qed.

Global Instance list_subseteq_dec `{EqDecision A} : RelDecision (@subseteq (list A) _).
Proof.
  intros x.
  induction x.
  - left. apply list_subseteq_nil.
  - intro y. specialize (IHx y) as [Hsub | Hnsub].
    2: {
      right. intro Hsub. elim Hnsub.
      intros b Hb. apply Hsub. right. assumption.
    }
    destruct (decide (a ∈ y)).
    + left. intros b Hb. inversion Hb; subst; [assumption|]. apply Hsub. assumption.
    + right. intro Hsub'. elim n. apply Hsub'. left.
Qed.

Lemma filter_subseteq {A} P `{∀ (x:A), Decision (P x)} (s1 s2 : list A) :
  s1 ⊆ s2 ->
  (filter P s1) ⊆ (filter P s2).
Proof.
induction s1; intros; intro x; intros.
  - contradict H1.
    rewrite filter_nil; intro Hx. inversion Hx.
  - rewrite filter_cons in H1.
    destruct (decide (P a)).
    + rewrite elem_of_cons in H1.
      destruct H1.
      * subst; apply elem_of_list_filter.
        split; [assumption|].
        apply H0; left.
      * apply IHs1; try assumption. intro y; intro. apply H0. right. assumption.
    + apply IHs1; try assumption. intro y; intro. apply H0. right. assumption.
Qed.

Lemma filter_subseteq_fn {A} P Q
  `{∀ (x:A), Decision (P x)} `{∀ (x:A), Decision (Q x)} :
  (forall a, P a -> Q a) ->
  forall (s : list A), filter P s ⊆ filter Q s.
Proof.
induction s; simpl.
  - rewrite filter_nil; intros x Hx; inversion Hx.
  - intro x; intros.
    rewrite filter_cons in H2.
    destruct (decide (P a)).
    + rewrite elem_of_cons in H2.
      rewrite filter_cons.
      destruct (decide (Q a)).
      * destruct H2.
        -- subst; left.
        -- right. apply IHs. assumption.
      * contradict n. apply H1. assumption.
    + rewrite filter_cons.
      destruct (decide (Q a)).
      -- right. apply IHs. assumption.
      -- apply IHs. assumption.
Qed.

Lemma map_option_subseteq
  {A B : Type}
  (f : A -> option B)
  (l1 l2 : list A)
  (Hincl : l1 ⊆ l2)
  : (map_option f l1) ⊆ (map_option f l2).
Proof.
 intro b. repeat rewrite in_map_subseteq.
 intros Hb.
 apply elem_of_map_option.
 apply elem_of_map_option in Hb.
 destruct Hb as [a [Ha Hfa]].
 exists a.
 apply Hincl in Ha.
 split; assumption.
Qed.

Lemma elem_of_empty_nil [X:Type] (l:list X) :
  (forall v, v ∉ l) -> l = [].
Proof.
  destruct l as [|a]. reflexivity.
  simpl. intro H. elim (H a). left.
Qed.

Lemma nodup_append_left {A}:
  forall (l1 l2 : list A), NoDup (l1 ++ l2) -> NoDup l1.
Proof.
  induction l1; intros.
  - constructor.
  - inversion H. apply IHl1 in H3. constructor; try assumption. intro. apply H2.
    apply elem_of_app. left. assumption.
Qed.

Lemma subseteq_empty {A} : forall (l : list A),
  l ⊆ nil -> l = nil.
Proof.
  intros. destruct l; [reflexivity|].
  exfalso.
  specialize (H a (elem_of_list_here _ _)).
  inversion H.
Qed.

Lemma elem_of_cat_option
  {A : Type}
  (l : list (option A))
  (a : A)
  : a ∈ (cat_option l) <-> exists b : (option A), b ∈ l /\ b = Some a.
Proof.
  apply elem_of_map_option.
Qed.

Lemma Listing_NoDup {A} {l : list A} : Listing l -> NoDup l.
Proof.
 intros [Hnd Hfull].
 apply NoDup_ListNoDup in Hnd.
 assumption.
Qed.

Lemma NoDup_subseteq_length [A : Type]
  [l1 l2 : list A]
  (Hnodup : NoDup l1)
  (Hincl : l1 ⊆ l2)
  : length l1 <= length l2.
Proof.
  apply submseteq_length, NoDup_submseteq; assumption.
Qed.

Lemma take_app_inv :
  forall [A : Type] (n : nat) (l l' : list A) (x : A),
    take n l = l' ++ [x] -> exists n' : nat, n = S n'.
Proof.
  induction n as [| n']; intros l l' x H.
  - contradict H. rewrite take_0. apply app_cons_not_nil.
  - exists n'. reflexivity.
Qed.

Lemma elem_of_list_prod :
  forall [A B : Type] (x : A) (y : B) (la : list A) (lb : list B),
    (x, y) ∈ list_prod la lb <-> x ∈ la /\ y ∈ lb.
Proof.
  intros.
  rewrite elem_of_list_In, in_prod_iff, <- !elem_of_list_In.
  reflexivity.
Qed.
