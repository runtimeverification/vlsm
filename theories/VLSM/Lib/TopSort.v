From Cdcl Require Import Itauto. Local Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From VLSM Require Import Lib.Preamble Lib.ListExtras Lib.ListSetExtras Lib.StdppListSet.

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
then the [top_sort] algoritm produces a linear extension of that ordering
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
Finds an element minimizing [count_predecessesors] in <<min :: remainder>>
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
  - intros; left; reflexivity.
  - intro a0. simpl.
    destruct (decide (count_predecessors a < count_predecessors a0));
    [specialize (IHl' a)|specialize (IHl' a0)];
    destruct IHl'; rewrite elem_of_cons; itauto.
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
    destruct H as [Heq | Hin]; subst.
    + simpl. destruct (decide (count_predecessors a < count_predecessors a0)).
      * specialize (IHl' a). rewrite Forall_forall in IHl'.
        assert (Ha : a ∈ (a :: l')) by (left; reflexivity).
        specialize (IHl' a Ha).
        lia.
      * specialize (IHl' a0). rewrite Forall_forall in IHl'.
        assert (Hx : a0 ∈ (a0 :: l')) by (left; reflexivity).
        specialize (IHl' a0 Hx).
        assumption.
    + simpl. destruct (decide (count_predecessors a < count_predecessors a0)).
      * specialize (IHl' a). rewrite Forall_forall in IHl'.
        specialize (IHl' x Hin).
        assumption.
      * apply not_lt in n. unfold ge in n.
        rewrite elem_of_cons in Hin.
        destruct Hin as [Heq | Hin]; subst.
        -- specialize (IHl' a0). rewrite Forall_forall in IHl'.
           assert (Ha0 : a0 ∈ (a0 :: l')) by (left; reflexivity).
           specialize (IHl' a0 Ha0).
           lia.
        -- specialize (IHl' a0). rewrite Forall_forall in IHl'.
           assert (Hx : x ∈ (a0 :: l')) by (right; assumption).
           specialize (IHl' x Hx).
           assumption.
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
  specialize (StrictOrder_Irreflexive (exist P a Ha)).
  unfold complement; unfold precedes_P; simpl; intro Hirr.
  destruct (decide (precedes a a)); assumption.
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
  - elim Hl;reflexivity.
  - inversion_clear HPl as [|? ? HPa HPl0].
    specialize (IHl0 HPl0).
    apply Exists_cons.
    rewrite filter_cons.
    destruct (decide (precedes a a)); [contradict p;apply precedes_irreflexive; assumption|].
    assert ({ l0=[] }+{l0 <> [] }) by (destruct l0;clear;[left|right];congruence).
    destruct H as [?|Hl0];[subst l0|].
    + left. reflexivity.
    + specialize (IHl0 Hl0).
      apply Exists_exists in IHl0.
      destruct IHl0 as [x [Hin Hlen]].
      destruct (decide (precedes a x)).
      * left. (* inversion H2; subst. *)
        specialize (Forall_forall P l0); intros [Hall _].
        specialize (Hall HPl0 x Hin).
        match goal with |- ?X = 0  => cut (X <= 0) end.
        lia.
        rewrite <- Hlen;clear Hlen.
        apply filter_length_fn.
        revert HPl0.
        intro.
        apply (Forall_impl P); [assumption|].
        intros.
        apply precedes_transitive with a;assumption.
      * right. apply Exists_exists. exists x. split; try assumption.
        rewrite filter_cons.
        destruct (decide (precedes a x)); [contradict n0; assumption|].
        assumption.
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
  specialize (count_predecessors_zero Hl'); intro Hx.
  apply Exists_exists in Hx. destruct Hx as [x [Hinx Hcountx]].
  specialize (min_predecessors_correct l' a); simpl; intro Hall.
  rewrite Forall_forall in Hall.
  rewrite Hl in Hinx.
  specialize (Hall x Hinx).
  unfold min.
  lia.
Qed.

End min_predecessors.

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

(** If <<l>> is [topologically_sorted], then for any occurences
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
  assert (Hpa : P a).
  { rewrite Forall_forall in Hl. apply Hl. rewrite Heqa, !elem_of_app, elem_of_list_singleton. auto. }
  specialize (Hts a b Hab lb1 lb2 Heqb).
  rewrite Heqa in Heqb.
  assert (Ha : a ∉ (b :: lb2)).
  { intro Ha. apply Hts.
    rewrite elem_of_cons in Ha.
    destruct Ha; try assumption. subst.
    apply (precedes_irreflexive precedes P b Hpa) in Hab.
    contradict Hab.
  }
  specialize (occurrences_ordering a b la1 la2 lb1 lb2 Heqb Ha).
  intro; assumption.
Qed.

(**
If <<a>> and <<b>> are in a [topologically_sorted] list <<lts>> and <<a precedes b>>
then there is an <<a>> before any occurence of <<b>> in <<lts>>.
*)
Corollary top_sort_before
  (a b : A)
  (Hab : precedes a b)
  (Ha : a ∈ l)
  (l1 l2 : list A)
  (Heq : l = l1 ++ [b] ++ l2)
  : a ∈ l1.
Proof.
  apply elem_of_list_split in Ha.
  destruct Ha as [la1 [la2 Ha]].
  specialize (topologically_sorted_occurrences_ordering a b Hab la1 la2 Ha l1 l2 Heq).
  intros [lab Hlab].
  subst.
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
  apply elem_of_list_split in Hb.
  destruct Hb as [l12 [l3 Hb']].
  specialize (top_sort_before a b Hab Ha l12 l3 Hb').
  intros Ha12. apply elem_of_list_split in Ha12.
  destruct Ha12 as [l1 [l2 Ha12]].
  subst l12.
  exists l1. exists l2. exists l3. rewrite Hb'. rewrite <- app_assoc.
  reflexivity.
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
  specialize (Hts a b Hab l1 (l2 ++ [final])).
  rewrite Hinit in Hts. repeat rewrite <- app_assoc in Hts.
  specialize (Hts eq_refl). intro Hnin. apply Hts.
  apply elem_of_app. left. assumption.
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
  unfold precedes_closed. repeat rewrite Forall_forall.
  split; intros Hpc b Hb a Hab;
  apply Heq;
  apply Heq in Hb;
  apply (Hpc b Hb);
  assumption.
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
  assert (Hb' : b ∈ (init ++ [final])). {
    apply elem_of_app.
    left; assumption.
  }
  specialize (Hpc b Hb' a Hab).
  apply elem_of_app in Hpc.
  destruct Hpc as [Ha | Ha]; try assumption.
  rewrite elem_of_cons in Ha.
  destruct Ha as [Heq | Hn]; try inversion Hn.
  subst final.
  apply elem_of_list_split in Hb'.
  destruct Hb' as  [l1 [l2 Heq]].
  specialize
    (topologically_sorted_occurrences_ordering precedes
      (init ++ [a]) P Hl Hts a b Hab init [] eq_refl l1 l2 Heq
    ).
  intros [lab Hlab].
  rewrite Hlab in Heq. exfalso. clear -Heq.
  simpl in Heq. rewrite <- app_assoc in Heq. simpl in Heq.
  apply app_inv_head in Heq. inversion Heq.
  symmetry in H0. apply app_eq_nil in H0.
  destruct H0 as [_ H].
  inversion H.
Qed.

Section top_sort.
(** ** The topological sorting algorithm *)

Context {A} `{EqDecision A} (precedes : relation A) `{!RelDecision precedes}.

(** Iteratively extracts <<n>> elements with minimal number of precessors
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
  - apply set_eq_cons. specialize (IHn l H0). subst. assumption.
  - specialize (min_predecessors_in precedes (a :: l) l a).
    rewrite <- Heqmin. simpl. intros [Heq | Hin]; try (elim n0; assumption).
    specialize (IHn (a :: l')).
    specialize (set_remove_length min l Hin).
    rewrite <- Heql'. rewrite <- H0. intro Hlen.
    specialize (IHn Hlen).
    split; intros x Hx; rewrite elem_of_cons in Hx;
      destruct Hx as [Heq|Hinx]; try (subst x).
    + right. apply IHn. left.
    + destruct (decide (x = min)); try subst x.
      * left.
      * specialize (set_remove_3 _ _ l Hinx n1).
        rewrite <- Heql'. intro Hinx'.
        right. apply IHn. right. assumption.
    + right. assumption.
    + apply IHn in Hinx.
      rewrite elem_of_cons in Hinx.
      destruct Hinx as [Heq | Hinx]; try (subst; left; reflexivity).
      right. subst. apply set_remove_1 in Hinx. assumption.
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
      assert (Hl' : NoDup l) by (inversion Hl; assumption).
      assert (Hlen : len = length l) by (inversion Heqlen; reflexivity).
      assert (Hl'' : NoDup (set_remove (min_predecessors precedes (a :: l) l a) l))
        by (apply set_remove_nodup; assumption).
      destruct (decide (min_predecessors precedes (a :: l) l a = a)); constructor.
      * specialize (IHlen l Hl'  Hlen).
        rewrite e in *.
        inversion Hl; subst x l0. intro Ha. elim H1.
        apply top_sort_set_eq. subst len. assumption.
      * apply IHlen; try assumption.
      * intro Hmin.
        assert (Hlen' : len = length (a :: set_remove (min_predecessors precedes (a :: l) l a) l)).
        { simpl.
          rewrite <- set_remove_length; try assumption.
          pose (@min_predecessors_in _ precedes _ (a :: l) l a) as Hin.
          destruct Hin as [Heq | Hin]; try assumption.
          elim n. assumption.
        }
        rewrite Hlen' in Hmin.
        apply (proj2 (top_sort_set_eq (a :: set_remove (min_predecessors precedes (a :: l) l a) l)))
          in Hmin.
        rewrite elem_of_cons in Hmin.
        destruct Hmin; [done |].
        apply set_remove_2 in H; try assumption.
        elim H. reflexivity.
      * apply IHlen.
        -- constructor; try assumption.
           intro Ha. apply set_remove_iff in Ha; try assumption.
           destruct Ha as [Ha _].
           inversion Hl. elim H1. assumption.
        -- simpl.
           rewrite <- set_remove_length; try assumption.
           pose (@min_predecessors_in _ precedes _ (a :: l) l a) as Hin.
           destruct Hin as [Heq | Hin]; try assumption.
           elim n. assumption.
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
    rewrite Heq. simpl. apply elem_of_app. right. right. assumption.
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
  generalize dependent l. clear Hl l.
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
      destruct (decide (min = a0)).
      - subst a0 l'. apply H2. assumption.
      - subst l'.
        apply elem_of_cons in Hx.
        destruct Hx as [Heqx | Hx]; try (subst; assumption).
        apply set_remove_1 in Hx.
        apply H2. assumption.
    }
    assert (Hlenl' : n = length l').
    { destruct (decide (min = a0)).
      - subst a0.
        subst l'. assumption.
      - subst l'. simpl.
        rewrite <- set_remove_length; try assumption.
        specialize (min_predecessors_in precedes (a0 :: l0) l0 a0).
        rewrite <- Heqmin. simpl.
        intros [Heq' | Hin]; try assumption.
        elim n0. assumption.
    }
    specialize (IHn l' Hall' Hlenl' a b Hab).
    assert (Hminb : b <> min).
    { destruct (decide (b = min)); try assumption.
      subst b.
      specialize (min_predecessors_zero precedes (a0 :: l0) P Hl l0 a0 eq_refl).
      rewrite <- Heqmin. simpl. intro Hmin.
      apply zero_predecessors in Hmin.
      rewrite Forall_forall in Hmin.
      apply Hmin in Ha.
      congruence.
    }
    destruct l1 as [| _min l1]; inversion Heq
    ; try (subst b; elim Hminb; reflexivity).
    subst _min.
    destruct (decide (a ∈ l')) as [i|i].
    - apply (IHn i l1 l2 Ha2 H4).
    - assert (Hmina : min = a).
      destruct (decide (min = a0)).
      * by subst a0 l'; apply elem_of_cons in Ha as [].
      * subst l'.
        rewrite elem_of_cons in Ha.
        destruct Ha as [Heqa | Ha'].
        -- subst a0.
           rewrite elem_of_cons in i.
           contradict i.
           left; reflexivity.
        -- destruct (decide (a = min)); try (symmetry; assumption).
           apply (set_remove_3 _ _ _ Ha') in n1.
           contradict i.
           right; assumption.
      * subst a.
        apply i.
        apply top_sort_set_eq.
        unfold top_sort. rewrite <- Hlenl'.
        rewrite H4.
        rewrite elem_of_app.
        right. right. assumption.
Qed.

(** <<lts>> is a [topological_sorting] of <<l>> if it has the same elements as <<l>>
and is [toplogically_sorted].
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
    - specialize (@exists_last _ (top_sort (a0 :: l0))) as Hlast.
      spec Hlast. unfold top_sort. simpl. itauto congruence.
      destruct Hlast as [l' [a' Heq]].
      rewrite Heq in Hmax.
      rewrite Heq.
      exists l'.
      specialize (last_error_is_last l' a') as Hlast.
      itauto congruence.
  }
  assert (a ∈ (top_sort l)). {
    destruct H as [l' Heq].
    rewrite <- Heq.
    apply elem_of_app.
    right. left.
  }
  specialize (top_sort_correct) as [Htop _].
  destruct Htop as [_ Htop].
  specialize (Htop a H0).
  itauto.
Qed.

Lemma get_maximal_element_correct
  (a max : A)
  (Hina : a ∈ l)
  (Hmax : get_maximal_element = Some max) :
  ~ precedes max a.
Proof.
  specialize top_sort_correct as [Hseteq Htop].
  unfold topologically_sorted in Htop.
  intros contra.
  specialize (Htop max a contra).

  assert (Hinmax: max ∈ l) by (apply maximal_element_in; itauto).
  assert (Hinatop : a ∈ (top_sort l)) by (apply Hseteq; itauto).
  apply elem_of_list_split in Hinatop.
  destruct Hinatop as [prefA [sufA HeqA]].
  unfold get_maximal_element in Hmax.
  destruct sufA.
  - rewrite HeqA in Hmax.
    specialize (last_error_is_last prefA a) as Hlast.
    assert (a = max) by itauto congruence.
    subst a.
    specialize StrictOrder_Irreflexive as Hirr.
    unfold Irreflexive in Hirr. unfold complement in Hirr.
    unfold Reflexive in Hirr.
    assert (P max). {
      rewrite Forall_forall in Hl.
      apply Hl.
      assumption.
    }
    specialize (Hirr (exist _ max H)).
    itauto.
  - rewrite HeqA in Hmax.
    specialize (@exists_last _ (a0 :: sufA)) as Hex.
    spec Hex. itauto congruence.
    destruct Hex as [l' [a' Heq]].
    rewrite Heq in Hmax.
    specialize (last_error_is_last (prefA ++ a :: l') a') as Hlast.
    rewrite <- app_assoc in Hlast.
    simpl in Hlast.
    assert (a' = max) by itauto congruence.
    specialize (Htop prefA (l' ++ [a'])).
    rewrite Heq in HeqA.
    specialize (Htop HeqA).
    subst a'.
    contradict Htop.
    apply elem_of_app.
    right. left.
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
