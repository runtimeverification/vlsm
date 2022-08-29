From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From VLSM.Lib Require Import Preamble ListExtras ListSetExtras StdppListSet StdppExtras.

(** * Topological sorting implementation *)

(**
This module implements an algorithm producing a linear extension for a
given partial order using an approach similar to that of Kahn's topological
sorting algorithm.

The algorithm extracts an element with a minimal number of predecessors
among the current elements, then recurses on the remaining elements.

To begin with, we assume an unconstrained <<precedes>> function to say
whether an element precedes another.  The proofs will show that if
<<precedes>> determines a strict order on the set of elements in the list,
then the [top_sort] algorithm produces a linear extension of that ordering
(Lemmas [top_sort_precedes] and [top_sort_precedes_before]).
*)

Section min_predecessors.
(** ** Finding an element with a minimal number of predecessors *)

(** For this section we will fix a list <<l>> and count the predecessors
occurring in that list. *)

Context {A} (precedes : relation A) `{!RelDecision precedes} (l : list A).

Definition count_predecessors
  (a : A)
  : nat
  := length (filter (fun b => precedes b a) l).

Lemma zero_predecessors
  (a : A)
  (Ha : count_predecessors a = 0)
  : Forall (fun b => ~ precedes b a) l.
Proof.
  apply length_zero_iff_nil in Ha.
  apply Forall_filter_nil in Ha.
  apply Ha.
Qed.

(**
Finds an element minimizing [count_predecessors] in <<min :: remainder>>
*)

Fixpoint min_predecessors
  (remainder : list A)
  (min : A)
  : A
  :=
  match remainder with
  | [] => min
  | h::t =>
    if decide (count_predecessors h < count_predecessors min)
    then min_predecessors t h
    else min_predecessors t min
  end.

Lemma min_predecessors_in
  (l' : list A)
  (a : A)
  (min := min_predecessors l' a)
  : min = a \/ min ∈ l'.
Proof.
  unfold min; clear min. revert a.
  induction l'.
  - by intros; left.
  - intro a0. simpl.
    destruct (decide (count_predecessors a < count_predecessors a0));
    [destruct (IHl' a) | destruct (IHl' a0)]; rewrite elem_of_cons; itauto.
Qed.

Lemma min_predecessors_correct
  (l' : list A)
  (a : A)
  (min := min_predecessors l' a)
  (mins := count_predecessors min)
  : Forall (fun b => mins <= count_predecessors b) (a :: l').
Proof.
  unfold mins; clear mins. unfold min; clear min. generalize dependent a.
  induction l'; intros; rewrite Forall_forall; intros.
  - simpl in H; inversion H; subst; [simpl; lia|inversion H2].
  - rewrite elem_of_cons in H.
    setoid_rewrite Forall_forall in IHl'.
    destruct H as [Heq | Hin]; subst.
    + simpl. destruct (decide (count_predecessors a < count_predecessors a0)).
      * transitivity (count_predecessors a); [| lia].
        by apply IHl'; left.
      * by apply IHl'; left.
    + simpl. destruct (decide (count_predecessors a < count_predecessors a0)).
      * by apply IHl'.
      * apply not_lt in n. unfold ge in n.
        rewrite elem_of_cons in Hin.
        destruct Hin as [Heq | Hin]; subst.
        -- transitivity (count_predecessors a0); [| lia].
           by apply IHl'; left.
        -- by apply IHl'; right.
Qed.

(** Given <<P>> a property on <<A>>, [precedes_P] is the relation
induced by <<precedes>> on the subset of <<A>> determined by <<P>>. *)

Definition precedes_P
  (P : A -> Prop)
  (x y : sig P)
  : Prop
  := precedes (proj1_sig x) (proj1_sig y).

(** In what follows, let us fix a property <<P>> satisfied by all elements
of <<l>>, such that [precedes_P] <<P>> is a [StrictOrder].

Consequently, this means that <<precedes>> is a [StrictOrder] on the
elements of <<l>>.
*)

Context
  (P : A -> Prop)
  (HPl : Forall P l)
  {Hso : StrictOrder (precedes_P P)}
  .

(** Next we derive easier to work with formulations for the [StrictOrder]
properties associated with [precedes_P]. *)
Lemma precedes_irreflexive
  (a : A)
  (Ha : P a)
  : ~ precedes a a.
Proof.
  assert (H := StrictOrder_Irreflexive (exist P a Ha)).
  by unfold complement, precedes_P in H; cbn in H.
Qed.

Lemma precedes_asymmetric
  (a b : A)
  (Ha : P a)
  (Hb : P b)
  (Hab : precedes a b)
  : ~ precedes b a.
Proof.
  intro Hba.
  exact
    (StrictOrder_Asymmetric Hso
      (exist P a Ha) (exist P b Hb)
      Hab Hba
    ).
Qed.

Lemma precedes_transitive
  (a b c : A)
  (Ha : P a)
  (Hb : P b)
  (Hc : P c)
  (Hab : precedes a b)
  (Hbc : precedes b c)
  : precedes a c.
Proof.
  exact
    (RelationClasses.StrictOrder_Transitive
      (exist P a Ha) (exist P b Hb) (exist P c Hc)
      Hab Hbc
    ).
Qed.

(** If <<precedes>> is a [StrictOrder] on <<l>>, then there must exist an
element of <<l>> with no predecessors in <<l>>.
*)
Lemma count_predecessors_zero
  (Hl : l <> [])
  : Exists (fun a => count_predecessors a = 0) l.
Proof.
  unfold count_predecessors.
  induction l.
  - done.
  - inversion_clear HPl as [|? ? HPa HPl0].
    rewrite Exists_cons, filter_cons.
    rewrite decide_False; [| by apply precedes_irreflexive].
    destruct (decide (precedes a a)); [by contradict p; apply precedes_irreflexive |].
    assert ({ l0=[] }+{l0 <> [] }) by (destruct l0;clear;[left|right];congruence).
    destruct H as [?|Hl0];[subst l0|].
    + by left.
    + specialize (IHl0 HPl0 Hl0).
      apply Exists_exists in IHl0 as (x & Hin & Hlen).
      destruct (decide (precedes a x)).
      * left.
        destruct (Forall_forall P l0) as [Hall _].
        apply Nat.le_0_r.
        rewrite <- Hlen; clear Hlen.
        apply filter_length_fn.
        apply (Forall_impl P); [done |].
        by intros; apply precedes_transitive with a; eauto.
      * right. apply Exists_exists. exists x.
        rewrite filter_cons.
        by destruct (decide (precedes a x)).
Qed.

(**
Hence, computing [min_predecessors] on <<l>> yields an element with
no predecessors.
*)
Lemma min_predecessors_zero
  (l' : list A)
  (a : A)
  (Hl : l = a :: l')
  (min := min_predecessors l' a)
  : count_predecessors min = 0.
Proof.
  assert (Hl' : l <> []) by (intro H; rewrite Hl in H; inversion H).
  assert (Hx := count_predecessors_zero Hl').
  apply Exists_exists in Hx as (x & Hinx & Hcountx).
  assert (Hall := min_predecessors_correct l' a); cbn in Hall.
  rewrite Forall_forall in Hall.
  apply Nat.le_0_r.
  rewrite <- Hcountx.
  apply Hall.
  by rewrite <- Hl.
Qed.

End min_predecessors.

#[export] Instance precedes_P_transitive
  `{Transitive A preceeds} (P : A -> Prop)
  : Transitive (precedes_P preceeds P).
Proof.
  intros [x Hx] [y Hy] [z Hz]; unfold precedes_P.
  by etransitivity.
Qed.

#[export] Instance precedes_P_irreflexive
  `{Irreflexive A preceeds} (P : A -> Prop)
  : Irreflexive (precedes_P preceeds P).
Proof.
  intros [x Hx]; unfold precedes_P, complement; cbn.
  by apply irreflexivity.
Qed.

#[export] Instance precedes_P_strict
  `{StrictOrder A preceeds} (P : A -> Prop)
  : StrictOrder (precedes_P preceeds P).
Proof.
  split; typeclasses eauto.
Qed.

Section topologically_sorted.

(** ** Topologically sorted lists. Definition and properties. *)

Context {A} (precedes : relation A) `{!RelDecision precedes} (l : list A).

(**
We say that a list <<l>> is [topologically_sorted] w.r.t a <<precedes>>
relation iff <<a precedes b>> implies that <<a>> cannot occur after <<b>> in <<l>>.
*)
Definition topologically_sorted
  :=
  forall
    (a b : A)
    (Hab : precedes a b)
    (l1 l2 : list A)
    (Heq : l = l1 ++ [b] ++ l2)
    , ~a ∈ l2.

(** The following properties assume that <<precedes>> determines a [StrictOrder]
on the list
*)
Context
  (P : A -> Prop)
  {Hso : StrictOrder (precedes_P precedes P)}
  .

Section topologically_sorted_fixed_list.

Context
  (Hl : Forall P l)
  (Hts : topologically_sorted)
  .

(** If <<l>> is [topologically_sorted], then for any occurrences
of <<a>> and <<b>> in <<l>> such that <<a precedes b>> it must be that
the occurrence of <<a>> is before that of <<b>>.

Hence all occurrences of <<a>> must be before all occurrences of <<b>> in
a [topologically_sorted] list.
*)
Lemma topologically_sorted_occurrences_ordering
  (a b : A)
  (Hab : precedes a b)
  (la1 la2 : list A)
  (Heqa : l = la1 ++ [a] ++ la2)
  (lb1 lb2 : list A)
  (Heqb : l = lb1 ++ [b] ++ lb2)
  : exists (lab : list A), lb1 = la1 ++ a :: lab.
Proof.
  apply (occurrences_ordering a b la1 la2 lb1 lb2); [by cbn in *; congruence |].
  intro Ha. apply (Hts a b Hab lb1 lb2); [done |].
  apply elem_of_cons in Ha as []; subst; [| done].
  apply (precedes_irreflexive precedes P b) in Hab; [done |].
  rewrite Forall_forall in Hl; apply Hl.
  by rewrite Heqb, !elem_of_app, elem_of_list_singleton; auto.
Qed.

(**
If <<a>> and <<b>> are in a [topologically_sorted] list <<lts>> and <<a precedes b>>
then there is an <<a>> before any occurrence of <<b>> in <<lts>>.
*)
Corollary top_sort_before
  (a b : A)
  (Hab : precedes a b)
  (Ha : a ∈ l)
  (l1 l2 : list A)
  (Heq : l = l1 ++ [b] ++ l2)
  : a ∈ l1.
Proof.
  apply elem_of_list_split in Ha as (la1 & la2 & Ha).
  destruct (topologically_sorted_occurrences_ordering a b Hab la1 la2 Ha l1 l2 Heq) as [lab ->].
  rewrite elem_of_app.
  right; left.
Qed.

(**
As a corollary of the above, if <<a precedes b>> then <<a>> can be found before
<<b>> in l.
*)
Corollary top_sort_precedes
  (a b : A)
  (Hab : precedes a b)
  (Ha : a ∈ l)
  (Hb : b ∈ l)
  : exists l1 l2 l3, l = l1 ++ [a] ++ l2 ++ [b] ++ l3.
Proof.
  apply elem_of_list_split in Hb as (l12 & l3 & Hb').
  pose (top_sort_before a b Hab Ha l12 l3 Hb') as Htsb.
  apply elem_of_list_split in Htsb as (l1 & l2 & ->).
  exists l1, l2, l3. by rewrite Hb', <- app_assoc.
Qed.

End topologically_sorted_fixed_list.
End topologically_sorted.

Lemma toplogically_sorted_remove_last
  {A : Type}
  (precedes : relation A)
  `{!RelDecision precedes}
  (l : list A)
  (Hts : topologically_sorted precedes l)
  (init : list A)
  (final : A)
  (Hinit : l = init ++ [final])
  : topologically_sorted precedes init.
Proof.
  subst l.
  intros a b Hab l1 l2 Hinit.
  rewrite Hinit, <- !app_assoc in Hts.
  intro Hnin. eapply Hts; [done | done |].
  by apply elem_of_app; left.
Qed.

Definition precedes_closed
  {A : Type}
  (precedes : relation A)
  `{!RelDecision precedes}
  (s : set A)
  : Prop
  :=
  Forall (fun (b : A) => forall (a : A) (Hmj : precedes a b), a ∈ s) s.

Lemma precedes_closed_set_eq
  {A : Type}
  (precedes : relation A)
  `{!RelDecision precedes}
  (s1 s2 : set A)
  (Heq : set_eq s1 s2)
  : precedes_closed precedes s1 <-> precedes_closed precedes s2.
Proof.
  unfold precedes_closed; repeat rewrite Forall_forall; firstorder.
Qed.

Lemma topologically_sorted_precedes_closed_remove_last
  {A : Type}
  (precedes : relation A)
  `{!RelDecision precedes}
  (P : A -> Prop)
  {Hso : StrictOrder (precedes_P precedes P)}
  (l : list A)
  (Hl : Forall P l)
  (Hts : topologically_sorted precedes l)
  (init : list A)
  (final : A)
  (Hinit : l = init ++ [final])
  (Hpc : precedes_closed precedes l)
  : precedes_closed precedes init.
Proof.
  unfold precedes_closed in *.
  rewrite Forall_forall in Hpc. rewrite Forall_forall.
  subst l.
  intros b Hb a Hab.
  assert (Hb' : b ∈ (init ++ [final])) by (apply elem_of_app; left; done).
  specialize (Hpc b Hb' a Hab); apply elem_of_app in Hpc as [Ha | Ha]; [done |].
  rewrite elem_of_list_singleton in Ha; subst final.
  apply elem_of_list_split in Hb' as  (l1 & l2 & Heq).
  destruct (topologically_sorted_occurrences_ordering precedes
             (init ++ [a]) P Hl Hts a b Hab init [] eq_refl l1 l2 Heq)
        as [lab Hlab].
  apply (f_equal length) in Heq.
  by rewrite Hlab, !app_length in Heq; cbn in Heq; lia.
Qed.

Section top_sort.
(** ** The topological sorting algorithm *)

Context {A} `{EqDecision A} (precedes : relation A) `{!RelDecision precedes}.

(** Iteratively extracts <<n>> elements with minimal number of predecessors
from a given list.
 *)

Fixpoint top_sort_n
  (n : nat)
  (l : list A)
  : list A
  :=
  match n,l with
  | 0, _ => []
  | _, [] => []
  | S n', a :: l' =>
    let min := min_predecessors precedes l l' a in
    let l'' := set_remove min l in
    min :: top_sort_n n' l''
  end.

(** Repeats the procedure above to order all elements from the input list.
*)
Definition top_sort
  (l : list A)
  : list A
  := top_sort_n (length l) l.

(** The result of [top_sort] and its input are equal as sets.
*)
Lemma top_sort_set_eq
  (l : list A)
  : set_eq l (top_sort l).
Proof.
  unfold top_sort.
  remember (length l) as n. generalize dependent l.
  induction n; intros; destruct l; try apply set_eq_refl
  ; inversion Heqn.
  simpl.
  remember (min_predecessors precedes (a :: l) l a) as min.
  remember (set_remove min l) as l'.
  destruct (decide (min = a)); try rewrite e.
  - subst. by apply set_eq_cons, IHn.
  - specialize (min_predecessors_in precedes (a :: l) l a).
    rewrite <- Heqmin. simpl. intros [Heq | Hin]; [done |].
    assert (Hlen := set_remove_length min l Hin).
    rewrite <- Heql', <- H0 in *.
    specialize (IHn (a :: l') Hlen).
    split; intros x Hx; apply elem_of_cons in Hx as [-> | Hinx].
    + by right; apply IHn; left.
    + destruct (decide (x = min)); [subst x; left |].
      right; apply IHn; right. rewrite Heql'.
      by apply set_remove_3.
    + by right.
    + apply IHn, elem_of_cons in Hinx as [-> | Hinx]; [left |].
      by right; subst; apply set_remove_1 in Hinx.
Qed.

Lemma top_sort_nodup
  (l : list A)
  (Hl : NoDup l)
  : NoDup (top_sort l).
Proof.
  unfold top_sort.
  remember (length l) as len.
  generalize dependent l.
  induction len; intros.
  - symmetry in Heqlen. apply length_zero_iff_nil in Heqlen. subst l.
    constructor.
  - destruct l as [| a l].
    + constructor.
    + simpl.
      assert (Hl' : NoDup l) by (inversion Hl; done).
      assert (Hlen : len = length l) by (inversion Heqlen; done).
      assert (Hl'' : NoDup (set_remove (min_predecessors precedes (a :: l) l a) l))
        by (apply set_remove_nodup; done).
      destruct (decide (min_predecessors precedes (a :: l) l a = a)); constructor.
      * rewrite e in *.
        inversion Hl; subst. intro Ha; elim H1.
        by apply top_sort_set_eq in Ha.
      * by apply IHlen.
      * intro Hmin.
        assert (Hlen' : len = length (a :: set_remove (min_predecessors precedes (a :: l) l a) l)).
        { simpl.
          rewrite <- set_remove_length; [done |].
          by destruct (@min_predecessors_in _ precedes _ (a :: l) l a).
        }
        rewrite Hlen' in Hmin.
        apply (proj2 (top_sort_set_eq (a :: set_remove (min_predecessors precedes (a :: l) l a) l)))
          in Hmin.
        rewrite elem_of_cons in Hmin.
        destruct Hmin; [done |].
        by apply set_remove_2 in H.
      * apply IHlen.
        -- constructor; [| done].
           intro Ha. apply set_remove_iff in Ha; [| done].
           destruct Ha as [Ha _].
           by inversion Hl.
        -- simpl.
           rewrite <- set_remove_length; [done |].
           by destruct (@min_predecessors_in _ precedes _ (a :: l) l a).
Qed.

Context
  (P : A -> Prop)
  {Hso : StrictOrder (precedes_P precedes P)}
  (l : list A)
  (Hl : Forall P l)
  .

(** Under the assumption that <<precedes>> induces a [StrictOrder] on the elements of
<<l>>, [top_sort] <<l>> is [topologically_sorted].

*)
Lemma top_sort_sorted : topologically_sorted precedes (top_sort l).
Proof.
  intro a; intros.
  intro Ha2.
  assert (Ha : a ∈ l). {
    apply top_sort_set_eq.
    rewrite Heq. simpl. rewrite elem_of_app, elem_of_cons. auto.
  }
  unfold top_sort in Heq.
  remember (length l) as n.
  generalize dependent Heq.
  generalize dependent l2.
  generalize dependent l1.
  generalize dependent Ha.
  generalize dependent Hab.
  generalize dependent b.
  generalize dependent a.
  generalize dependent l.
  clear Hl l.
  induction n; intros
  ; try (symmetry in Heqn;  apply length_zero_iff_nil in Heqn; subst l; inversion Ha).
  destruct l as [| a0 l0]; inversion Hl; subst; simpl in Heq.
  + inversion Ha.
  + remember (min_predecessors precedes (a0 :: l0) l0 a0) as min.
    remember
      (match decide (min = a0) return (set A) with
      | left _ => l0
      | right _ => @cons A a0 (set_remove min l0)
      end) as l'.
    inversion Heqn.
    assert (Hall' : Forall P l').
    { rewrite Forall_forall. intros x Hx.
      rewrite Forall_forall in H2.
      destruct (decide (min = a0)); subst.
      - by apply H2.
      - apply elem_of_cons in Hx.
        destruct Hx as [-> | Hx]; [done |].
        apply set_remove_1 in Hx.
        by apply H2.
    }
    assert (Hlenl' : n = length l').
    {
      destruct (decide (min = a0)); subst; cbn; [done |].
      rewrite <- set_remove_length; [done |].
      by destruct (min_predecessors_in precedes (a0 :: l0) l0 a0) as [Heq' | Hin].
    }
    assert (Hminb : b <> min).
    {
      destruct (decide (b = min)); subst; [| done].
      pose (min_predecessors_zero precedes (a0 :: l0) P Hl l0 a0 eq_refl) as Hmin; simpl in Hmin.
      apply zero_predecessors in Hmin.
      rewrite Forall_forall in Hmin.
      apply Hmin in Ha.
      congruence.
    }
    destruct l1 as [| _min l1]; inversion Heq; [by subst |].
    subst _min.
    destruct (decide (a ∈ l')) as [i|i].
    - by apply (IHn l' Hall' Hlenl' a b Hab i l1 l2 Ha2).
    - assert (Hmina : min = a).
      {
        destruct (decide (min = a0)).
        * by subst a0 l'; apply elem_of_cons in Ha as [].
        * subst l'.
          apply elem_of_cons in Ha as [Heqa | Ha'].
          -- subst a0.
             rewrite elem_of_cons in i.
             by contradict i; left.
          -- destruct (decide (a = min)); [done |].
             apply (set_remove_3 _ _ _ Ha') in n1.
             by contradict i; right.
      }
      subst. apply i, top_sort_set_eq. unfold top_sort.
      rewrite <- Hlenl', H4, elem_of_app, !elem_of_cons. itauto.
Qed.

(** <<lts>> is a [topological_sorting] of <<l>> if it has the same elements as <<l>>
and is [topologically_sorted].
*)
Definition topological_sorting
  (l lts : list A)
  :=
  set_eq l lts /\ topologically_sorted precedes lts.

Corollary top_sort_correct : topological_sorting l (top_sort l).
Proof.
  split.
  - apply top_sort_set_eq.
  - apply top_sort_sorted.
Qed.

(** ** Maximal elements *)

Definition get_maximal_element := ListExtras.last_error (top_sort l).

Lemma maximal_element_in
  (a : A)
  (Hmax : get_maximal_element = Some a) :
  a ∈ l.
Proof.
  unfold get_maximal_element in Hmax.
  assert (exists l', l' ++ [a] = top_sort l). {
    destruct l.
    - simpl in Hmax. itauto congruence.
    - destruct (@exists_last _ (top_sort (a0 :: l0))) as (l' & a' & Heq).
      + cbn; itauto congruence.
      + rewrite Heq in *.
        rewrite (last_error_is_last l' a') in Hmax.
        exists l'.
        congruence.
  }
  assert (a ∈ (top_sort l)). {
    destruct H as [l' Heq].
    rewrite <- Heq.
    apply elem_of_app.
    right. left.
  }
  destruct (top_sort_correct) as [[_ Htop] _].
  itauto.
Qed.

Lemma get_maximal_element_correct
  (a max : A)
  (Hina : a ∈ l)
  (Hmax : get_maximal_element = Some max) :
  ~ precedes max a.
Proof.
  destruct top_sort_correct as [Hseteq Htop].
  unfold topologically_sorted in Htop.
  intros contra.
  assert (Hinmax: max ∈ l) by (apply maximal_element_in; itauto).
  assert (Hinatop : a ∈ (top_sort l)) by (apply Hseteq; itauto).
  apply elem_of_list_split in Hinatop as (prefA & sufA & HeqA).
  unfold get_maximal_element in Hmax.
  destruct sufA.
  - rewrite HeqA, (last_error_is_last prefA a) in Hmax; inversion Hmax; subst.
    specialize StrictOrder_Irreflexive as Hirr.
    unfold Irreflexive, complement, Reflexive in Hirr.
    assert (P max) by (eapply Forall_forall; done).
    by apply (Hirr (exist _ max H)).
  - destruct (@exists_last _ (a0 :: sufA)) as (l' & a' & Heq); [congruence |].
    rewrite HeqA, Heq in Hmax.
    pose (last_error_is_last (prefA ++ a :: l') a') as Hlast.
    rewrite <- app_assoc in Hlast; cbn in Hlast.
    assert (a' = max) as -> by itauto congruence.
    rewrite Heq in HeqA.
    exfalso; apply (Htop max a contra prefA (l' ++ [max]) HeqA), elem_of_app.
    right; left.
Qed.

Lemma get_maximal_element_some
  (Hne : l <> []) :
  exists a, get_maximal_element = Some a.
Proof.
  unfold get_maximal_element.
  destruct l.
  - congruence.
  - simpl.
    exists (List.last
       (top_sort_n (length l0)
          (if decide (min_predecessors precedes (a :: l0) l0 a = a)
           then l0
           else a :: set_remove (min_predecessors precedes (a :: l0) l0 a) l0))
       (min_predecessors precedes (a :: l0) l0 a)). itauto.
Qed.

End top_sort.

(** Some of the results above depend on the <<precedes>> relation being a
[StrictOrder] for a property-defined [sig] type.  However, when the relation
is strict to begin with, we can obtain simpler statements for these results.
*)
Section sec_simple_top_sort.

Context
  `{EqDecision A}
  (precedes : A -> A -> Prop)
  `{!RelDecision precedes}
  `{!StrictOrder precedes}
  .

#[local] Lemma Forall_True : forall l : list A, Forall (fun _ => True) l.
Proof.
  by intro; apply Forall_forall.
Qed.

Corollary simple_topologically_sorted_precedes_closed_remove_last
  (l : list A)
  (Hts : topologically_sorted precedes l)
  (init : list A)
  (final : A)
  (Hinit : l = init ++ [final])
  (Hpc : precedes_closed precedes l)
  : precedes_closed precedes init.
Proof.
  eapply topologically_sorted_precedes_closed_remove_last;
    [typeclasses eauto | apply Forall_True | done..].
Qed.

Corollary simple_top_sort_correct : forall l,
  topological_sorting precedes l (top_sort precedes l).
Proof.
  intro; eapply top_sort_correct; [typeclasses eauto | apply Forall_True].
Qed.

Corollary simple_maximal_element_in l
  (a : A)
  (Hmax : get_maximal_element precedes l = Some a) :
  a ∈ l.
Proof.
  eapply maximal_element_in; [typeclasses eauto | apply Forall_True | done].
Qed.

Corollary simple_get_maximal_element_correct l
  (a max : A)
  (Hina : a ∈ l)
  (Hmax : get_maximal_element precedes l = Some max) :
  ~ precedes max a.
Proof.
  eapply get_maximal_element_correct; [typeclasses eauto | apply Forall_True | done..].
Qed.

Corollary simple_get_maximal_element_some
  l (Hne : l <> []) :
  exists a, get_maximal_element precedes l = Some a.
Proof.
  eapply get_maximal_element_some; [apply Forall_True | done].
Qed.

End sec_simple_top_sort.
