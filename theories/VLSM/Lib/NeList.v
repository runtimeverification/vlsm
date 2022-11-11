From stdpp Require Import prelude.

Inductive ne_list (A : Type) : Type :=
| ne_one : A -> ne_list A
| ne_cons : A -> ne_list A -> ne_list A.

Arguments ne_one {_} _ : assert.
Arguments ne_cons {_} _ _ : assert.

Global Infix ":::" := ne_cons (at level 60, right associativity).

Definition ne_list_hd {A} (l : ne_list A) : A :=
  match l with
  | ne_one a => a
  | ne_cons a _ => a
  end.

Definition ne_list_foldr {A B} (f : A -> B -> B) (b : B) (l : ne_list A) :=
  (fix fold (l : ne_list A) :=
    match l with
    | ne_one a => f a b
    | ne_cons a nel => f a (fold nel)
    end
  ) l.

Definition ne_list_foldl {A B} (b : B) (f : B -> A -> B) (l : ne_list A) :=
  (fix fold (carry : B) (l : ne_list A) :=
    match l with
    | ne_one a => f carry a
    | ne_cons a nel => fold (f carry a) nel
    end
  ) b l.

Definition ne_list_rev {A} (l : ne_list A) : ne_list A :=
  match l with
  | ne_one a => ne_one a
  | ne_cons a nel => ne_list_foldl (ne_one a) (flip ne_cons) nel
  end.

Definition ne_list_app {A} (l1 l2 : ne_list A) := ne_list_foldr ne_cons l2 l1.

#[export] Instance ne_list_ret : MRet ne_list :=
  fun A => ne_one.

#[export] Instance ne_list_bind : MBind ne_list :=
  fun A B f l => (fix bind (l : ne_list A) :=
    match l with
    | ne_one a => f a
    | ne_cons a nel => ne_list_app (f a) (bind nel)
    end
  ) l.

#[export] Instance ne_list_fmap  : FMap ne_list :=
  fun A B f => mbind (mret ∘ f).

#[export] Instance ne_list_join : MJoin ne_list :=
  fun A => mbind id.

Inductive ne_list_equiv `{Equiv A} : Equiv (ne_list A) :=
  | ne_one_equiv x y : x ≡ y -> ne_one x ≡ ne_one y
  | ne_cons_equiv x y l k : x ≡ y → l ≡ k → x ::: l ≡ y ::: k.
#[export] Existing Instance ne_list_equiv.


Definition ne_list_to_list {A} (nel : ne_list A) : list A :=
  ne_list_foldr cons [] nel.

Definition ne_list_length {A} (nel : ne_list A) := length (ne_list_to_list nel).

Lemma ne_list_to_list_unroll {A} (a : A) (nel : ne_list A) :
  ne_list_to_list (a ::: nel) = a :: ne_list_to_list nel.
Proof. done. Qed.

Definition ne_list_tl {A} (l : ne_list A) : list A :=
  match l with
  | ne_one _ => []
  | ne_cons _ nel => ne_list_to_list nel
  end.

Definition ne_list_option_cons {A} (a : A) (mnel : option (ne_list A)) : ne_list A :=
  from_option (ne_cons a) (ne_one a) mnel.

Definition list_to_ne_list {A} (l : list A) : option (ne_list A) :=
  foldr (fun a mnel => Some (ne_list_option_cons a mnel)) None l.

Lemma list_to_ne_list_unroll {A} (a : A) l :
  list_to_ne_list (a :: l) = Some (ne_list_option_cons a (list_to_ne_list l)).
Proof. done. Qed.

Record NeList (A : Type) : Type :=
{
  nl_hd : A;
  nl_tl : list A;
}.

Arguments nl_hd {_} _ : assert.
Arguments nl_tl {_} _ : assert.

Definition ne_list_to_NeList {A} (l : ne_list A) : NeList A :=
{|
  nl_hd := ne_list_hd l;
  nl_tl := ne_list_tl l;
|}.

Definition NeList_to_ne_list {A} (l : NeList A) : ne_list A :=
  ne_list_option_cons (nl_hd l) (list_to_ne_list (nl_tl l)).

Lemma NeList_to_ne_list_unroll {A} (a b : A) (l : list A) :
  NeList_to_ne_list {| nl_hd := a; nl_tl := b :: l |}
    =
  ne_cons a (NeList_to_ne_list {| nl_hd := b; nl_tl := l|}).
Proof. done. Qed. 

Lemma NeList_to_ne_list_to_list {A} :
  forall (l : NeList A),
  ne_list_to_list (NeList_to_ne_list l) = nl_hd l :: nl_tl l.
Proof.
  intros []; revert nl_hd0; induction nl_tl0; [done |].
  intros; rewrite NeList_to_ne_list_unroll, ne_list_to_list_unroll.
  by rewrite IHnl_tl0.
Qed.

Lemma NeList_to_ne_list_to_NeList {A} :
  forall (l : NeList A),
  ne_list_to_NeList (NeList_to_ne_list l) = l.
Proof.
  intros []; destruct nl_tl0; [done |].
  rewrite NeList_to_ne_list_unroll.
  unfold ne_list_to_NeList; f_equal.
  by apply NeList_to_ne_list_to_list.
Qed.

Lemma ne_list_to_list_to_nelist {A} :
  forall (l : ne_list A),
  list_to_ne_list (ne_list_to_list l) = Some l.
Proof.
  induction l; [done |].
  rewrite ne_list_to_list_unroll, list_to_ne_list_unroll.
  by rewrite IHl.
Qed.

Lemma ne_list_to_NeList_to_ne_list {A} :
  forall (l : ne_list A),
  NeList_to_ne_list (ne_list_to_NeList l) = l.
Proof.
  intros []; [done |].
  unfold ne_list_to_NeList, NeList_to_ne_list, nl_hd, nl_tl, ne_list_hd, ne_list_tl.
  by rewrite ne_list_to_list_to_nelist.
Qed.

#[export] Instance elem_of_ne_list {A} : ElemOf A (ne_list A) :=
  fun a nel => a ∈ ne_list_to_list nel.

#[export] Instance ne_list_subseteq {A} : SubsetEq (ne_list A) :=
  λ l1 l2, ∀ x, x ∈ l1 → x ∈ l2.

#[export] Instance elem_of_ne_list_dec `{dec : EqDecision A} :
  RelDecision (∈@{ne_list A}).
Proof.
  intros a l.
  unfold elem_of, elem_of_ne_list; cbn.
  typeclasses eauto.
Qed.
