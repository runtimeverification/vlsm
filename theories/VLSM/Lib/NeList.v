From stdpp Require Import prelude.
From VLSM.Lib Require Import ListExtras StdppExtras.

Set Default Proof Using "Type".

(** A straight-forward inductive definition of non-empty lists. *)
Inductive ne_list (A : Type) : Type :=
| nel_singl : A -> ne_list A
| nel_cons : A -> ne_list A -> ne_list A.

Arguments nel_singl  {_} _ : assert.
Arguments nel_cons {_} _ _ : assert.

Infix ":::" := nel_cons (at level 60, right associativity).

Definition ne_list_hd {A} (l : ne_list A) : A :=
  match l with
  | nel_singl a => a
  | nel_cons a _ => a
  end.

Definition ne_list_tl {A} (l : ne_list A) : option (ne_list A) :=
  match l with
  | nel_singl _ => None
  | nel_cons _ tl => Some tl
  end.

Definition ne_list_foldr {A B} (f : A -> B -> B) (b : B) (l : ne_list A) :=
  (fix fold (l : ne_list A) :=
    match l with
    | nel_singl a => f a b
    | nel_cons a tl => f a (fold tl)
    end) l.

Definition ne_list_app {A} (l1 l2 : ne_list A) := ne_list_foldr nel_cons l2 l1.

#[export] Instance ne_list_ret : MRet ne_list := @nel_singl.

#[export] Instance ne_list_bind : MBind ne_list :=
  fun A B f l => (fix bind (l : ne_list A) :=
    match l with
    | nel_singl a => f a
    | nel_cons a tl => ne_list_app (f a) (bind tl)
    end) l.

#[export] Instance ne_list_fmap  : FMap ne_list :=
  fun A B f => mbind (mret ∘ f).

#[export] Instance ne_list_join : MJoin ne_list :=
  fun A => mbind id.

Inductive ne_list_equiv `{Equiv A} : Equiv (ne_list A) :=
| ne_one_equiv x y : x ≡ y -> nel_singl x ≡ nel_singl y
| ne_cons_equiv x y l k : x ≡ y -> l ≡ k -> x ::: l ≡ y ::: k.

Definition ne_list_to_list {A} (nel : ne_list A) : list A :=
  ne_list_foldr cons [] nel.

Definition ne_list_length {A} (nel : ne_list A) := length (ne_list_to_list nel).

Lemma ne_list_min_length {A} (nel : ne_list A) : 1 <= ne_list_length nel.
Proof. by destruct nel; cbn; lia. Qed.

Lemma ne_list_to_list_unroll {A} (a : A) (tl : ne_list A) :
  ne_list_to_list (a ::: tl) = a :: ne_list_to_list tl.
Proof. done. Qed.

Definition ne_list_to_list_tl {A} (l : ne_list A) : list A :=
  match l with
  | nel_singl _ => []
  | nel_cons _ tl => ne_list_to_list tl
  end.

Definition ne_list_option_cons {A} (a : A) (mnel : option (ne_list A)) : ne_list A :=
  from_option (nel_cons a) (nel_singl a) mnel.

Definition list_to_option_ne_list {A} (l : list A) : option (ne_list A) :=
  foldr (fun a mnel => Some (ne_list_option_cons a mnel)) None l.

Lemma list_to_option_ne_list_unroll {A} (a : A) l :
  list_to_option_ne_list (a :: l) = Some (ne_list_option_cons a (list_to_option_ne_list l)).
Proof. done. Qed.

(** A definition of non-empty lists based on lists. *)
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
  nl_tl := ne_list_to_list_tl l;
|}.

Definition NeList_to_ne_list {A} (l : NeList A) : ne_list A :=
  ne_list_option_cons (nl_hd l) (list_to_option_ne_list (nl_tl l)).

Lemma NeList_to_ne_list_unroll {A} (a b : A) (l : list A) :
  NeList_to_ne_list {| nl_hd := a; nl_tl := b :: l |}
    =
  nel_cons a (NeList_to_ne_list {| nl_hd := b; nl_tl := l |}).
Proof. done. Qed.

Lemma NeList_to_ne_list_to_list {A} :
  forall (l : NeList A),
    ne_list_to_list (NeList_to_ne_list l) = nl_hd l :: nl_tl l.
Proof.
  intros [h t]; revert h; induction t; intros; [done |].
  by rewrite NeList_to_ne_list_unroll, ne_list_to_list_unroll, IHt.
Qed.

Lemma NeList_to_ne_list_to_NeList {A} :
  forall (l : NeList A),
    ne_list_to_NeList (NeList_to_ne_list l) = l.
Proof.
  intros [h1 [| h2 t]]; [done |].
  rewrite NeList_to_ne_list_unroll.
  unfold ne_list_to_NeList; f_equal.
  by apply NeList_to_ne_list_to_list.
Qed.

Lemma ne_list_to_list_to_nelist {A} :
  forall (l : ne_list A),
    list_to_option_ne_list (ne_list_to_list l) = Some l.
Proof.
  induction l; [done |].
  rewrite ne_list_to_list_unroll, list_to_option_ne_list_unroll.
  by rewrite IHl.
Qed.

Lemma ne_list_to_NeList_to_ne_list {A} :
  forall (l : ne_list A),
    NeList_to_ne_list (ne_list_to_NeList l) = l.
Proof.
  intros [a | a n]; [done |].
  unfold ne_list_to_NeList, NeList_to_ne_list, nl_hd, nl_tl, ne_list_hd, ne_list_to_list_tl.
  by rewrite ne_list_to_list_to_nelist.
Qed.

#[export] Instance elem_of_ne_list {A} : ElemOf A (ne_list A) :=
  fun a nel => a ∈ ne_list_to_list nel.

#[export] Instance ne_list_subseteq {A} : SubsetEq (ne_list A) :=
  fun l1 l2 => forall x, x ∈ l1 -> x ∈ l2.

#[export] Instance elem_of_ne_list_dec `{dec : EqDecision A} :
  RelDecision (∈@{ne_list A}).
Proof.
  intros a l.
  unfold elem_of, elem_of_ne_list; cbn.
  by typeclasses eauto.
Qed.

Definition ne_list_from_non_empty_list {A} (l : list A) : l <> [] -> ne_list A :=
  match l with
  | [] => fun H => False_rect _ (H eq_refl)
  | a :: l' => fun _ => NeList_to_ne_list {| nl_hd := a; nl_tl := l' |}
  end.

Definition list_function_restriction {A B} (f : A -> list B)
  (da : dsig (fun a => f a <> [])) : ne_list B :=
  ne_list_from_non_empty_list (f (` da)) (proj2_dsig da).

Lemma list_filter_map_mbind
  {A B : Type}
  (f : A -> list B)

  (l : list A)
  : mjoin (map ne_list_to_list
      (list_filter_map (fun a => f a <> []) (list_function_restriction f) l))
    = mbind f l.
Proof.
  induction l using rev_ind; [done |].
  rewrite mbind_app, list_filter_map_app, map_app, mjoin_app, IHl.
  cbn; clear IHl.
  f_equal; rewrite app_nil_r.
  destruct (decide _) as [Hfx | Hnfx]; cbn;
    [| by destruct (decide (f x = []))].
  unfold list_function_restriction, ne_list_from_non_empty_list; cbn in Hfx.
  remember (proj2_dsig _) as Hp; clear HeqHp; cbn in Hp.
  simpl.
  destruct (f x); [done |].
  by rewrite NeList_to_ne_list_to_list, app_nil_r.
Qed.

Lemma ne_list_concat_min_length
  {A : Type}
  (l : list (ne_list A))
  : length (mjoin (map ne_list_to_list l)) >= length l.
Proof.
  induction l; cbn; [by lia |].
  rewrite app_length.
  (* by specialize (ne_list_min_length a); unfold ne_list_length; lia. *)
  (* for some strange reason the line above does not work, so... this hack: *)
  assert (Hle : forall a b c, a >= 1 -> b >= c -> a + b >= S c) by lia.
  by apply Hle; [apply ne_list_min_length |].
Qed.

(**
  An alternative inductive definition of non-empty lists using a single
  constructor.
*)
Inductive NonEmptyList (A : Type) : Type := NEL_cons
{
  nel_hd : A;
  nel_tl : option (NonEmptyList A)
}.

Arguments nel_hd {_} _ : assert.
Arguments nel_tl {_} _ : assert.
Arguments NEL_cons {_} _ _ : assert.

#[export] Instance NonEmptyList_inhabited `{Inhabited A} : Inhabited (NonEmptyList A) :=
  populate (NEL_cons inhabitant None).

Definition NEL_singl `(a : A) : NonEmptyList A := NEL_cons a None.

Fixpoint NonEmptyList_ind'
  (A : Type) (P : NonEmptyList A -> Prop)
  (hd' : forall h : A, P (NEL_cons h None))
  (tl' : forall (h : A) (t : NonEmptyList A), P t -> P (NEL_cons h (Some t)))
  (l : NonEmptyList A) {struct l} : P l :=
match l with
| NEL_cons h None => hd' h
| NEL_cons h (Some t) => tl' h t (NonEmptyList_ind' A P hd' tl' t)
end.

Fixpoint NonEmptyList_to_ne_list `(l : NonEmptyList A) : ne_list A :=
  match nel_tl l with
  | None => nel_singl (nel_hd l)
  | Some l' => nel_cons (nel_hd l) (NonEmptyList_to_ne_list l')
  end.

Fixpoint ne_list_to_NonEmptyList `(l : ne_list A) : NonEmptyList A :=
  match l with
  | nel_singl a => NEL_singl a
  | nel_cons a l' => NEL_cons a (Some (ne_list_to_NonEmptyList l'))
  end.

Lemma NonEmptyList_to_ne_list_to_NonEmptyList `(l : NonEmptyList A) :
  ne_list_to_NonEmptyList (NonEmptyList_to_ne_list l) = l.
Proof. by induction l using NonEmptyList_ind'; cbn; [| rewrite IHl]. Qed.

Lemma ne_list_to_NonEmptyList_to_ne_list `(l : ne_list A) :
  NonEmptyList_to_ne_list (ne_list_to_NonEmptyList l) = l.
Proof. by induction l; cbn; [| rewrite IHl]. Qed.
