From VLSM.Lib Require Import Itauto.
From Coq Require Import FunctionalExtensionality.
From stdpp Require Import prelude finite.
From VLSM.Lib Require Import Preamble StdppExtras ListExtras.

(** * Finitely supported functions *)

(**
  The support of a function (w.r.t. a specified codomain value) is the type of
  elements of its domain that are not mapped to the specified value.

  Note that we require the codomain to have decidable equality, because it
  allows for a straight-forward approach to proving equality of elements
  of the support.
*)
Definition support {A B} (s : B) (f : A -> B) `{EqDecision B} : Type :=
  dsig (fun a => f a <> s).

(** A function is finitely supported if its [support] is [Finite]. *)
Class FinSupp {A B} (s : B) (f : A -> B) `{EqDecision A} `{EqDecision B} :=
  finite_supp :> Finite (support s f).

Global Hint Mode FinSupp - - ! - - - : typeclass_instances.

(**
  We define a type to encapsulate functions of finite support.
  The notation <<f : A -fin<> b>> says that f represents a function from <<A>>
  to the type of <<b>> satisfying that only a finite set of elements from <<A>>
  are mapped to values other than <<b>>.
*)
Inductive FinSuppFn (A : Type) `(s : B) : Type :=
| fin_supp_fn (f : A -> B) `{FinSupp A B s f}.

Infix "-fin<>" := FinSuppFn (at level 60, right associativity).

Arguments fin_supp_fn {A}%type_scope {B}%type_scope
  s f%function_scope {EqDecision0 EqDecision1} H : assert.

(**
  We define a coercion to allow using an encapsulated finitely supported
  function as its underlying regular function.
*)
Definition fin_supp_fn_project `{b : B} `(fsf : A -fin<> b) : A -> B :=
  match fsf with fin_supp_fn _ f _ => f end.

Coercion fin_supp_fn_project : FinSuppFn >-> Funclass.

#[export] Instance fin_supp_fn_equiv {A B} {s : B} : Equiv (A -fin<> s) :=
  (fun f g => fin_supp_fn_project f = fin_supp_fn_project g).

#[export] Instance fin_supp_fn_equivalence {A B} {s : B} :
  Equivalence (≡@{A -fin<> s}).
Proof.
  unfold equiv, fin_supp_fn_equiv.
  constructor.
  - done.
  - by intros f g; apply symmetry.
  - by intros f g h; apply transitivity.
Qed.

#[export] Instance fin_supp_fn_project_proper {A B} {b : B} :
  Proper ((≡) ==> (=)) (@fin_supp_fn_project B b A).
Proof. by intros f g Heqv; inversion Heqv. Qed.

Lemma fin_supp_fn_equiv_unfold {A} `{b : B} (f g : A -fin<> b) :
  f ≡ g <-> fin_supp_fn_project f = fin_supp_fn_project g.
Proof. done. Qed.

Definition fin_supp_fn_source_dec `{b : B} `(f : A -fin<> b) : EqDecision A :=
  match f with @fin_supp_fn _ _ _ _ EqA _ _ => EqA end.

Definition fin_supp_fn_target_dec `{b : B} `(f : A -fin<> b) : EqDecision B :=
  match f with @fin_supp_fn _ _ _ _ _ EqB _ => EqB end.

#[export] Instance fin_supp_fn_has_fin_supp `{b : B} `(f : A -fin<> b) :
  @FinSupp _ _ b f
    (fin_supp_fn_source_dec f) (fin_supp_fn_target_dec f)
    :=
  match f with fin_supp_fn _ _ FinS => FinS end.

Definition fin_supp `{b : B} `(f : A -fin<> b) : list A :=
  map proj1_sig (enum (support b f)).

Lemma elem_of_fin_supp `{b : B} `(f : A -fin<> b) :
  forall (a : A), a ∈ fin_supp f <-> f a <> b.
Proof.
  unfold fin_supp.
  split; rewrite elem_of_list_fmap.
  - intros (asupp & -> & _).
    by destruct_dec_sig asupp _a H_a Heq; subst.
  - intros Ha.
    by exists (dexist a Ha); split; [| apply elem_of_enum].
Qed.

Lemma not_elem_of_fin_supp `{b : B} `(f : A -fin<> b) :
  forall (a : A), a ∉ fin_supp f <-> f a = b.
Proof.
  intro a; rewrite elem_of_fin_supp.
  destruct (@decide (f a = b)); [| itauto..].
  by eapply fin_supp_fn_target_dec.
Qed.

Lemma fin_supp_NoDup `{b : B} `(f : A -fin<> b) : NoDup (fin_supp f).
Proof. by apply dsig_NoDup, NoDup_enum. Qed.

#[export] Instance fin_supp_proper {A B} (b : B) : Proper ((≡) ==> (≡ₚ)) (@fin_supp B b A).
Proof.
  intros f g Heq.
  apply NoDup_Permutation; [by apply fin_supp_NoDup.. |].
  by intro; rewrite !elem_of_fin_supp, Heq.
Qed.

#[export] Instance fin_supp_fn_eq_dec {A} `{b : B} : RelDecision (≡@{A -fin<> b}).
Proof.
  intros f g.
  pose proof (fin_supp_fn_source_dec f).
  pose proof (fin_supp_fn_target_dec f).
  destruct (@finset_equiv_dec A (listset A) _ _ _ _ _ _ _ _ _
    (list_to_set (fin_supp f)) (list_to_set (fin_supp g))) as [Heqv | Hneqv]; cycle 1.
  - right; intros Heqv; contradict Hneqv.
    by rewrite Heqv.
  - destruct (decide (set_Forall (fun a => f a = g a) (list_to_set (C := listset A) (fin_supp f))))
      as [Hall | Hall]; [| by right; contradict Hall; rewrite Hall].
    left; apply fin_supp_fn_equiv_unfold; extensionality a.
    destruct (decide (a ∈ fin_supp f)) as [| Hf]; [by apply Hall, elem_of_list_to_set |].
    destruct (decide (a ∈ fin_supp g)) as [| Hg]; [by apply Hall; rewrite Heqv, elem_of_list_to_set |].
    apply not_elem_of_fin_supp in Hf, Hg.
    by congruence.
Qed.

Program Definition empty_supp_fn (A : Type) `(b : B)
  `{EqDecision A} `{EqDecision B} : A -fin<> b :=
  fin_supp_fn b (const b) {| enum := [] |}.
Next Obligation.
Proof. by constructor. Qed.
Next Obligation.
Proof. by intros; destruct_dec_sig x a Ha Heq; contradiction Ha. Qed.

Lemma empty_supp_fn_supp (A : Type) `(b : B) `{EqDecision A} `{EqDecision B} : fin_supp (empty_supp_fn A b) = [].
Proof. done. Qed.

Lemma empty_supp_fn_supp_inv `{b : B} `(f : A -fin<> b)
  (AEqd := fin_supp_fn_source_dec f) (BEqd := fin_supp_fn_target_dec f) :
  fin_supp f = [] -> f ≡ empty_supp_fn A b.
Proof.
  intros Hf; apply fin_supp_fn_equiv_unfold; extensionality a.
  change (f a = b).
  eapply not_elem_of_fin_supp.
  rewrite Hf.
  by apply not_elem_of_nil.
Qed.

Definition update_fn_supp `{s : B} `(f : A -fin<> s) (n : A) (b : B)
  (AEqd := fin_supp_fn_source_dec f) (BEqd := fin_supp_fn_target_dec f) : listset A :=
  if decide (b = s)
  then list_to_set (fin_supp f) ∖ {[n]}
  else {[n]} ∪ list_to_set (fin_supp f).

Lemma update_fn_supp_all `{s : B} `(f : A -fin<> s) (n : A) (b : B)
  (AEqd := fin_supp_fn_source_dec f) :
  Forall (fun a => update_fn f n b a <> s) (elements (update_fn_supp f n b)).
Proof.
  unfold update_fn_supp.
  apply Forall_forall; intros a.
  rewrite elem_of_elements.
  case_decide.
  - rewrite elem_of_difference, elem_of_singleton, elem_of_list_to_set,
      elem_of_fin_supp.
    by intros []; rewrite update_fn_neq.
  - rewrite elem_of_union, elem_of_singleton, elem_of_list_to_set,
      elem_of_fin_supp.
    destruct (decide (a = n)) as [-> |].
    + by rewrite update_fn_eq.
    + rewrite update_fn_neq by done.
      by intros [].
Qed.

Program Definition update_fn_fin_supp `{s : B} `(f : A -fin<> s) (n : A) (b : B)
  (AEqd := fin_supp_fn_source_dec f) (BEqd := fin_supp_fn_target_dec f)
  : A -fin<> s :=
  fin_supp_fn s (update_fn f n b) {| enum := list_annotate (update_fn_supp_all f n b) |}.
Next Obligation.
Proof. by intros; apply list_annotate_NoDup, NoDup_elements. Qed.
Next Obligation.
Proof.
  intros; destruct_dec_sig x a Ha Heq; subst.
  apply elem_of_list_annotate, elem_of_elements.
  unfold update_fn_supp; case_decide.
  - rewrite elem_of_difference, elem_of_list_to_set, elem_of_fin_supp,
      elem_of_singleton; cbn.
    destruct (@decide (a = n)) as [-> |].
    + by apply (fin_supp_fn_source_dec f).
    + by rewrite update_fn_eq in Ha.
    + by rewrite update_fn_neq in Ha.
  - rewrite elem_of_union, elem_of_list_to_set, elem_of_fin_supp,
      elem_of_singleton; cbn.
    destruct (@decide (a = n));
      [by apply (fin_supp_fn_source_dec f) | by left |].
    by right; rewrite update_fn_neq in Ha.
Qed.

#[export] Instance update_fn_fin_supp_proper {A} `{s : B} :
  Proper ((≡) ==> (=) ==> (=) ==> (≡)) (@update_fn_fin_supp B s A).
Proof.
  intros f g Heqv _n n -> _b b ->.
  apply fin_supp_fn_equiv_unfold; extensionality a; cbn.
  pose proof (fin_supp_fn_source_dec f).
  destruct (decide (a = n)) as [-> |]; [by rewrite !update_fn_eq |].
  rewrite !update_fn_neq by done.
  by rewrite Heqv.
Qed.

Lemma elem_of_update_fn_fin_supp `{s : B} `(f : A -fin<> s) (n : A) (b : B) :
  forall (a : A),
    a ∈ fin_supp (update_fn_fin_supp f n b)
      <->
    b = s /\ a ∈ fin_supp f /\ a <> n \/
    b <> s /\ (a ∈ fin_supp f \/ a = n).
Proof.
  intro; unfold fin_supp at 1; cbn.
  rewrite list_annotate_forget, elem_of_elements.
  unfold update_fn_supp; case_decide.
  - by rewrite elem_of_difference, elem_of_list_to_set, elem_of_singleton; split; itauto.
  - by rewrite elem_of_union, elem_of_list_to_set, elem_of_singleton; split; itauto.
Qed.

(** ** Finitely supported functions on naturals *)

Definition zero_fin_supp_nat_fn `{EqDecision A} : A -fin<> 0 :=
  empty_supp_fn A 0.

Definition succ_fin_supp_nat_fn `(f : A -fin<> 0) (n : A) : A -fin<> 0 :=
  update_fn_fin_supp f n (S (f n)).

#[export] Instance succ_fin_supp_nat_fn_proper {A} :
  Proper ((≡) ==> (=) ==> (≡)) (@succ_fin_supp_nat_fn A).
Proof.
  intros f g Heqv _n n ->.
  by apply update_fn_fin_supp_proper; [..| rewrite Heqv].
Qed.

Lemma elem_of_succ_fin_supp_nat_fn_fin_supp `(f : A -fin<> 0) (n : A) :
  forall (a : A),
    a ∈ fin_supp (succ_fin_supp_nat_fn f n) <-> a = n \/ a ∈ fin_supp f.
Proof.
  intro a; unfold succ_fin_supp_nat_fn; rewrite elem_of_update_fn_fin_supp.
  split.
  - by intros [[]|]; [lia | itauto].
  - by right; split; [lia | itauto].
Qed.

Lemma succ_fin_supp_nat_fn_supp_in `(f : A -fin<> 0) (n : A) :
  n ∈ fin_supp f -> fin_supp (succ_fin_supp_nat_fn f n) ≡ₚ fin_supp f.
Proof.
  intros.
  apply NoDup_Permutation; [by apply fin_supp_NoDup.. |].
  intros; rewrite elem_of_succ_fin_supp_nat_fn_fin_supp.
  by set_solver.
Qed.

Lemma succ_fin_supp_nat_fn_supp_not_in `(f : A -fin<> 0) (n : A) :
  n ∉ fin_supp f -> fin_supp (succ_fin_supp_nat_fn f n) ≡ₚ n :: fin_supp f.
Proof.
  intros; cbn; rewrite list_annotate_forget.
  unfold update_fn_supp; rewrite decide_False by lia.
  rewrite @elements_union_singleton;
    [| by typeclasses eauto | by rewrite elem_of_list_to_set].
  constructor; eapply @elements_list_to_set;
    [by typeclasses eauto | by apply fin_supp_NoDup].
Qed.

Definition delta_fin_supp_nat_fn `{EqDecision A} (n : A) : A -fin<> 0 :=
  succ_fin_supp_nat_fn zero_fin_supp_nat_fn n.

Lemma elem_of_delta_fin_supp_nat_fn_fin_supp `{EqDecision A} (n : A) :
  forall (a : A),
    a ∈ fin_supp (delta_fin_supp_nat_fn n) <-> a = n.
Proof.
  intros a.
  unfold delta_fin_supp_nat_fn;rewrite elem_of_succ_fin_supp_nat_fn_fin_supp; cbn.
  split; [| by left].
  by intros [| Ha]; [| inversion Ha].
Qed.

Definition sum_fin_supp_nat_fn `(f : A -fin<> 0) : nat :=
  sum_list_with f (fin_supp f).

Lemma sum_fin_supp_nat_fn_proper {A} : Proper ((≡) ==> (=)) (@sum_fin_supp_nat_fn A).
Proof.
  intros f g Heqv.
  unfold sum_fin_supp_nat_fn.
  rewrite (sum_list_with_proper f (fin_supp f) (fin_supp g)).
  - by apply sum_list_with_ext_forall; intros; rewrite Heqv.
  - by apply fin_supp_proper.
Qed.

Lemma sum_fin_supp_nat_fn_zero_inv `(f : A -fin<> 0) (AEqd := fin_supp_fn_source_dec f) :
  sum_fin_supp_nat_fn f = 0 -> f ≡ zero_fin_supp_nat_fn.
Proof.
  setoid_rewrite sum_list_with_zero; intros Hall.
  apply fin_supp_fn_equiv_unfold; extensionality a; cbn.
  destruct (decide (a ∈ fin_supp f)); [by apply Hall |].
  by rewrite elem_of_fin_supp in n; cbn in n; lia.
Qed.

Lemma sum_fin_supp_nat_fn_succ `(f : A -fin<> 0) (n : A) :
  sum_fin_supp_nat_fn (succ_fin_supp_nat_fn f n) = S (sum_fin_supp_nat_fn f).
Proof.
  unfold sum_fin_supp_nat_fn.
  pose proof (fin_supp_fn_source_dec f).
  destruct (decide (n ∈ fin_supp f)).
  - rewrite succ_fin_supp_nat_fn_supp_in by done.
    pose proof (Hnodup := fin_supp_NoDup f).
    revert Hnodup e; cbn.
    generalize (fin_supp f) as l; induction l; [by inversion 2 |].
    rewrite list.NoDup_cons, elem_of_cons; cbn.
    intros [Ha Hnodup] [<- | Hn].
    + rewrite update_fn_eq; cbn.
      do 2 f_equal.
      apply sum_list_with_ext_forall.
      by intros; rewrite update_fn_neq by set_solver.
    + rewrite update_fn_neq by set_solver.
      by rewrite IHl.
  - rewrite succ_fin_supp_nat_fn_supp_not_in by done.
    cbn; rewrite update_fn_eq.
    replace (f n) with 0 by (rewrite elem_of_fin_supp in n0; cbn in n0; lia).
    cbn; f_equal.
    apply sum_list_with_ext_forall.
    by intros; rewrite update_fn_neq; [| set_solver].
Qed.

(** The component-wise sum of two functions *)
Definition fin_supp_nat_fn_add_supp {A} (f1 f2 : A -fin<> 0) : listset A :=
    list_to_set (fin_supp f1) ∪ list_to_set (fin_supp f2).

Lemma fin_supp_nat_fn_add_supp_all {A} (f1 f2 : A -fin<> 0)
  (AEqd := fin_supp_fn_source_dec f1) :
  Forall (fun a => f1 a + f2 a <> 0)
    (elements (fin_supp_nat_fn_add_supp f1 f2)).
Proof.
  unfold fin_supp_nat_fn_add_supp; apply Forall_forall; intros a.
  rewrite elem_of_elements, elem_of_union, !elem_of_list_to_set,
    !elem_of_fin_supp.
  by lia.
Qed.

Program Definition fin_supp_nat_fn_add {A} (f1 f2 : A -fin<> 0)
  (EqA := fin_supp_fn_source_dec f1) : A -fin<> 0 :=
  @fin_supp_fn _ _ 0
    (fun a => f1 a + f2 a) _ _
    {| enum := list_annotate (fin_supp_nat_fn_add_supp_all f1 f2) |}.
Next Obligation.
Proof. by intros; apply list_annotate_NoDup, NoDup_elements. Qed.
Next Obligation.
Proof.
  intros; destruct_dec_sig x a Ha Heq; subst.
  apply elem_of_list_annotate, elem_of_elements, elem_of_union; cbn.
  rewrite !elem_of_list_to_set, !elem_of_fin_supp.
  by lia.
Qed.

#[export] Instance fin_supp_nat_fn_add_proper {A} :
  Proper ((≡) ==> (≡) ==> (≡)) (@fin_supp_nat_fn_add A).
Proof.
  intros f1 g1 Heqv1 f2 g2 Heqv2.
  apply fin_supp_fn_equiv_unfold; extensionality a; cbn.
  by rewrite Heqv1, Heqv2.
Qed.

Lemma elem_of_fin_supp_nat_fn_add_fin_supp {A} (f1 f2 : A -fin<> 0) :
  forall (a : A),
    a ∈ fin_supp (fin_supp_nat_fn_add f1 f2) <->
    a ∈ fin_supp f1 \/ a ∈ fin_supp f2.
Proof.
  intro; unfold fin_supp at 1; cbn.
  rewrite list_annotate_forget, elem_of_elements.
  unfold fin_supp_nat_fn_add_supp.
  by rewrite elem_of_union, !elem_of_list_to_set.
Qed.

#[export] Instance fin_supp_nat_fn_add_comm {A} : Comm (≡) (@fin_supp_nat_fn_add A).
Proof.
  intros f1 f2; apply fin_supp_fn_equiv_unfold.
  by extensionality a; cbn; lia.
Qed.

#[export] Instance fin_supp_nat_fn_add_left_id `{EqDecision A} :
  LeftId (≡) zero_fin_supp_nat_fn (@fin_supp_nat_fn_add A).
Proof. by intro; apply fin_supp_fn_equiv_unfold; extensionality a. Qed.

#[export] Instance fin_supp_nat_fn_add_right_id `{EqDecision A} :
  RightId (≡) zero_fin_supp_nat_fn (@fin_supp_nat_fn_add A).
Proof. by intro; apply fin_supp_fn_equiv_unfold; extensionality a; cbn; lia. Qed.

#[export] Instance fin_supp_nat_fn_add_assoc {A} : Assoc (≡) (@fin_supp_nat_fn_add A).
Proof.
  by intros f g h; rewrite !fin_supp_fn_equiv_unfold; extensionality a; cbn; lia.
Qed.

Lemma fin_supp_nat_fn_add_succ_l {A} (f1 f2 : A -fin<> 0) :
  forall (a : A),
    fin_supp_nat_fn_add (succ_fin_supp_nat_fn f1 a) f2
      ≡
    succ_fin_supp_nat_fn (fin_supp_nat_fn_add f1 f2) a.
Proof.
  intros a; apply fin_supp_fn_equiv_unfold; extensionality a'; cbn.
  pose proof (fin_supp_fn_source_dec f1).
  destruct (decide (a' = a)) as [-> |].
  - by rewrite !update_fn_eq.
  - by rewrite !update_fn_neq.
Qed.

Lemma fin_supp_nat_fn_add_succ_r {A} (f1 f2 : A -fin<> 0) :
  forall (a : A),
    fin_supp_nat_fn_add f2 (succ_fin_supp_nat_fn f1 a)
      ≡
    succ_fin_supp_nat_fn (fin_supp_nat_fn_add f2 f1) a.
Proof.
  by intros; rewrite (comm fin_supp_nat_fn_add), fin_supp_nat_fn_add_succ_l,
    (comm fin_supp_nat_fn_add).
Qed.

(**
  To be able to prove things by induction on finitely supported functions on
  naturals we define the following inductive property and then we show that it
  holds for all such functions.
*)
Inductive FinSuppNatFn {A} : (A -fin<> 0) -> Prop :=
| P_zero : forall (f' : A -fin<> 0) (EqA := fin_supp_fn_source_dec f'),
    f' ≡ zero_fin_supp_nat_fn -> FinSuppNatFn f'
| P_succ : forall (i : A) (f f' : A -fin<> 0), FinSuppNatFn f ->
    f' ≡ succ_fin_supp_nat_fn f i -> FinSuppNatFn f'.

Lemma FinSuppNatFn_complete `(f : A -fin<> 0) :  FinSuppNatFn f.
Proof.
  remember (sum_fin_supp_nat_fn f) as n.
  symmetry in Heqn.
  revert f Heqn; induction n; intros;
    [by apply sum_fin_supp_nat_fn_zero_inv in Heqn; constructor |].
  assert (Hex : Exists (fun (i : A) => f i <> 0) (fin_supp f)).
  {
    destruct (decide (Exists (fun (i : A) => f i <> 0) (fin_supp f))) as [| Hex]; [done |].
    apply not_Exists_Forall in Hex; [| by typeclasses eauto].
    replace (sum_fin_supp_nat_fn f) with 0 in Heqn; [done |].
    symmetry.
    apply sum_list_with_zero.
    intros a Ha.
    by rewrite Forall_forall in Hex; apply Hex in Ha; cbn in Ha; lia.
  }
  pose proof (Hx := Exists_choose_first_good _ _ Hex); cbn in Hx.
  pose (x := Exists_choose_first Hex).
  destruct (f x) as [| px] eqn: Heqx; [done |]; clear Hx.
  pose (f' := update_fn_fin_supp f x px).
  assert (Heq : f ≡ succ_fin_supp_nat_fn f' x).
  {
    subst f'; apply fin_supp_fn_equiv_unfold; extensionality a; cbn.
    destruct (@decide (a = x)) as [-> |].
    - by apply (fin_supp_fn_source_dec f).
    - by rewrite !update_fn_eq.
    - by rewrite !update_fn_neq.
  }
  constructor 2 with x f'; [| done].
  apply IHn; subst f'.
  rewrite sum_fin_supp_nat_fn_proper in Heqn by done.
  rewrite sum_fin_supp_nat_fn_succ in Heqn.
  by congruence.
Qed.

Lemma fin_supp_nat_fn_inv `(f : A -fin<> 0) (EqA := fin_supp_fn_source_dec f) :
  f ≡ zero_fin_supp_nat_fn
    \/
  exists (a : A) (f' : A -fin<> 0), f ≡ succ_fin_supp_nat_fn f' a.
Proof.
  pose proof (Hcomplete := FinSuppNatFn_complete f).
  by inversion Hcomplete; subst; [left | right; eexists _,_].
Qed.

Ltac destruct_fin_supp_nat_fn f f' n Heq :=
  destruct (fin_supp_nat_fn_inv f) as [Heq | (n & f' & Heq)].

Lemma fin_supp_nat_fn_ind `{EqDecision A}
  (P : (A -fin<> 0) -> Prop)
  (Hproper : Proper ((≡) ==> impl) P)
  (Hzero : P zero_fin_supp_nat_fn)
  (Hsucc : forall (i : A) (f : A -fin<> 0),
    P f -> P (succ_fin_supp_nat_fn f i)) :
  forall (f : A -fin<> 0), P f.
Proof.
  intros.
  pose proof (Hcomplete := FinSuppNatFn_complete f).
  by induction Hcomplete as [? ? ->| ? ? ? ? ? ->];
    [eapply Hproper; cycle 1 | apply Hsucc].
Qed.
