From Coq Require Export Program.Tactics.
Obligation Tactic := idtac.
From stdpp Require Import prelude.
From Coq Require Import Eqdep_dec.

(** * Utility: General Definitions, Results and Tactics *)

Tactic Notation "spec" hyp(H) :=
  match type of H with ?a -> _ =>
  let H1 := fresh in (assert (H1 : a);
  [| generalize (H H1); clear H H1; intro H]) end.

(** ** Basic logic *)

Lemma Is_true_iff_eq_true : forall x : bool, x = true <-> x.
Proof.
  split.
  - by apply Is_true_eq_left.
  - by apply Is_true_eq_true.
Qed.

Lemma and_proper_l (A B C : Prop) : (A -> (B <-> C)) -> (A /\ B) <-> (A /\ C).
Proof. by firstorder. Qed.

Lemma impl_proper (A B C : Prop) : (A -> (B <-> C)) -> (A -> B) <-> (A -> C).
Proof. by firstorder. Qed.

(** ** Decidable propositions *)

Lemma Decision_iff : forall {P Q}, (P <-> Q) -> Decision P -> Decision Q.
Proof. by firstorder. Qed.

#[export] Instance bool_decision {b : bool} : Decision b :=
  match b with
  | true => left I
  | false => right (fun H => H)
  end.

Notation decide_eq := (fun x y => decide (x = y)).

(** ** Lemmas about transitive closure *)

Lemma transitive_tc_idempotent `(Transitive A R) :
  forall a b, R a b <-> tc R a b.
Proof.
  split; [by constructor |].
  induction 1; [done |].
  by etransitivity.
Qed.

(**
  If a relation <<R>> reflects a predicate <<P>>, then its transitive
  closure will also reflect it.
*)
Lemma tc_reflect
  `(R : relation A)
  (P : A -> Prop)
  (Hreflects : forall dm m, R dm m -> P m -> P dm)
  : forall dm m, tc R dm m -> P m -> P dm.
Proof. by induction 1; firstorder. Qed.

(** Characterization of [tc] in terms of the last transitivity step. *)
Lemma tc_r_iff `(R : relation A) :
  forall x z, tc R x z <-> R x z \/ exists y, tc R x y /\ R y z.
Proof.
  split.
  - intros Htc; apply tc_nsteps in Htc as (n & Hn & Hsteps).
    induction Hsteps; [lia |].
    destruct n; [by inversion Hsteps; subst; left |].
    spec IHHsteps; [lia |]; right; destruct IHHsteps as [Hyz | (y0 & Hyy0 & Hy0z)].
    + by exists y; split; [constructor |].
    + exists y0; split; [| done].
      apply tc_nsteps.
      apply tc_nsteps in Hyy0 as (m & Hm & Hyy0).
      exists (S m); split; [lia |].
      by econstructor.
  - intros [Hxz | (y & Hxy & Hyz)]; [by constructor |].
    by eapply tc_r.
Qed.

Lemma tc_wf_projected
  `{R1 : relation A} `(R2 : relation B) `{!Transitive R2} (f : A -> B) :
  (forall x y, R1 x y -> R2 (f x) (f y)) ->
  well_founded R2 -> well_founded (tc R1).
Proof.
  intros Hpreserve.
  apply wf_projected with f.
  induction 1; [by apply Hpreserve |].
  transitivity (f y); [| done].
  by apply Hpreserve.
Qed.

Lemma tc_reflect_irreflexive
  `(R : relation A) `{!Irreflexive (tc R)} : Irreflexive R.
Proof.
 intros ? ?.
 by eapply irreflexivity with (R := tc R); [| constructor].
Qed.

Lemma Proper_reflects_Irreflexive
  `(R1 : relation A) `(R2 : relation B) (f : A -> B)
  : Proper (R1 ==> R2) f -> Irreflexive R2 -> Irreflexive R1.
Proof.
  intros Hproper Hirreflexive x Hx.
  by apply Hirreflexive with (f x), Hproper.
Qed.

Lemma Proper_tc
  `(R1 : relation A) `(R2 : relation B) (f : A -> B) `{!Transitive R2}
  : Proper (R1 ==> R2) f -> Proper (tc R1 ==> R2) f.
Proof.
  intros Hproper x y Hxy; induction Hxy; [by apply Hproper |].
  by etransitivity; [apply Hproper |].
Qed.

(** ** Equality of dependent pairs *)

Lemma exists_proj1_sig {A : Type} (P : A -> Prop) (a : A) :
  (exists xP : {x | P x}, proj1_sig xP = a) <-> P a.
Proof.
  split.
  - by intros [[x Hx] [= ->]].
  - by intro Ha; exists (exist _ a Ha).
Qed.

Lemma dec_sig_to_exist {A} {P} {P_dec : forall x : A, Decision (P x)} (a : dsig P)
  : exists (a' : A) (e : P a'), a = dexist a' e.
Proof.
  by exists (proj1_sig a), (proj2_dsig a); apply dsig_eq.
Qed.

Ltac destruct_dec_sig a a' e H := pose proof (dec_sig_to_exist a) as (a' & e & H).

Lemma dec_sig_sigT_eq
  {A} (P : A -> Prop) {P_dec : forall x, Decision (P x)}
  (F : A -> Type)
  (a : A)
  (b1 b2 : F a)
  (e1 e2 : P a)
  (pa1 := dexist a e1)
  (pa2 := dexist a e2)
  (Heqb : b1 = b2)
  : @existT _ (fun pa : dsig P => F (proj1_sig pa)) pa1 b1
  = @existT _ (fun pa : dsig P => F (proj1_sig pa)) pa2 b2.
Proof.
  subst b2 pa1 pa2.
  unfold dexist.
  replace (bool_decide_pack (P a) e1) with (bool_decide_pack (P a) e2); [done |].
  by apply proof_irrel.
Qed.

Lemma dec_sig_sigT_eq_rev
  `{EqDecision A} (P : A -> Prop) {P_dec : forall x, Decision (P x)}
  (F : A -> Type)
  (a : A)
  (b1 b2 : F a)
  (e1 e2 : P a)
  (pa1 := dexist a e1)
  (pa2 := dexist a e2)
  : @existT _ (fun pa : dsig P => F (proj1_sig pa)) pa1 b1
      = @existT _ (fun pa : dsig P => F (proj1_sig pa)) pa2 b2 ->
    b1 = b2.
Proof.
  subst pa1 pa2.
  unfold dexist.
  replace (bool_decide_pack (P a) e1) with (bool_decide_pack (P a) e2); [| by apply proof_irrel].
  apply inj_pair2_eq_dec.
  intros x y; destruct (decide (` x = ` y)).
  - by left; apply dsig_eq.
  - by right; intros ->.
Qed.

(* https://coq.discourse.group/t/writing-equality-decision-that-reduces-dec-x-x-for-opaque-x/551/2 *)

Lemma eq_dec_refl :
  forall {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) (x : A),
    eq_dec x x = left eq_refl.
Proof.
  intros A eq_dec x.
  destruct (eq_dec x x); [| done].
  by rewrite K_dec_type with (P := fun prf => prf = eq_refl).
Qed.

(** ** Minimal elements *)

(**
  A minimal element of a subset <<S>> (defined by a predicate <<P>>) of some
  preordered set is defined as an element of S that is not greater than any other
  element in S.
*)
Definition minimal_among `(R : relation A) (P : A -> Prop) (m : A) : Prop :=
  P m /\ (forall m', P m' -> R m' m -> R m m').

Remark minimal_among_le_0 : minimal_among le (const True) 0.
Proof.
  by split; [| lia].
Qed.

Section sec_find_least_among.
(**
  Given a decidable property on naturals and a natural number on which the
  property holds, we can compute the least natural number on which it holds.
*)

Context
  (P : nat -> Prop)
  `{forall n, Decision (P n)}
  (bound : nat)
  (Hbound : P bound).

#[local] Fixpoint find_least_among_helper (dif : nat) : nat :=
  match dif with
  | 0 => bound
  | S dif' =>
    if decide (P (bound - dif))
      then bound - dif
      else find_least_among_helper dif'
  end.

Definition find_least_among : nat := find_least_among_helper bound.

#[local] Lemma find_least_among_helper_bounded :
  forall n, bound - n <= find_least_among_helper n <= bound.
Proof. by induction n; cbn; [| case_decide]; lia. Qed.

#[local] Lemma find_least_among_helper_has_property :
  forall n, P (find_least_among_helper n).
Proof. by induction n; cbn; [| case_decide]. Qed.

#[local] Lemma find_least_among_helper_minimal :
  forall n m,
    bound - n <= m <= bound -> m < find_least_among_helper n -> ~ P m.
Proof.
  induction n; cbn; [by lia |].
  case_decide; [by lia |].
  intros.
  destruct (decide (m = bound - S n)); [by subst |].
  by apply IHn; lia.
Qed.

#[local] Lemma find_least_among_helper_is_minimal :
  forall n,
    minimal_among le
      (fun m => bound - n <= m <= bound /\ P m)
      (find_least_among_helper n).
Proof.
  split; [split |].
  - by apply find_least_among_helper_bounded.
  - by apply find_least_among_helper_has_property.
  - intros ? [Hm' Hpm'] Hle.
    destruct (decide (find_least_among_helper  n = m')); [by lia |].
    by exfalso; eapply find_least_among_helper_minimal with n m'; [| lia |].
Qed.

Lemma find_least_among_is_minimal
  : minimal_among le P find_least_among.
Proof.
  destruct (find_least_among_helper_is_minimal bound) as [[[_ ?] ?] Hmin'].
  split; [done |].
  intros; apply Hmin'; [| done].
  split; [| done].
  split; [by lia |].
  by etransitivity.
Qed.

End sec_find_least_among.

(** A more concise definition of minimality for strict orders. *)
Definition strict_minimal_among `(R : relation A) (P : A -> Prop) (m : A) : Prop :=
  P m /\ (forall m', P m' -> ~ R m' m).

Remark strict_minimal_among_lt_0 : minimal_among lt (const True) 0.
Proof.
  by split; [| lia].
Qed.

(** The minimality definitions are equivalent for [Asymmetric] relations. *)
Lemma asymmetric_minimal_among_iff
  `(R : relation A) `{!Asymmetric R} (P : A -> Prop)
  : forall m, minimal_among R P m <-> strict_minimal_among R P m.
Proof.
  unfold minimal_among, strict_minimal_among; specialize asymmetry.
  by firstorder.
Qed.

(** The minimality definitions are equivalent for [StrictOrder]s. *)
Lemma strict_minimal_among_iff
  `(R : relation A) `{!StrictOrder R} (P : A -> Prop)
  : forall m, minimal_among R P m <-> strict_minimal_among R P m.
Proof.
  by apply asymmetric_minimal_among_iff; typeclasses eauto.
Qed.

(** Dually, a maximal element is a minimal element w.r.t. the inverse relation. *)
Definition maximal_among `(R : relation A) := minimal_among (flip R).

Definition strict_maximal_among `(R : relation A) := strict_minimal_among (flip R).

(** ** Comparison operators *)

(** *** Reflexive comparison operators *)

Class CompareReflexive {A} (compare : A -> A -> comparison) : Prop :=
  compare_eq : forall x y, compare x y = Eq <-> x = y.

#[global] Hint Mode CompareReflexive ! - : typeclass_instances.

Lemma compare_eq_refl {A} `{CompareReflexive A} :
  forall x, compare x x = Eq.
Proof. by intros; apply H. Qed.

(** *** Transitive comparison operators *)

Class CompareTransitive {A} (compare : A -> A -> comparison) : Prop :=
  compare_transitive : forall x y z c, compare x y = c -> compare y z = c -> compare x z = c.

#[global] Hint Mode CompareTransitive ! - : typeclass_instances.

(** *** Comparison operators that correspond to a strict order *)

Class CompareStrictOrder {A} (compare : A -> A -> comparison) : Prop :=
{
  StrictOrder_Reflexive :> CompareReflexive compare;
  StrictOrder_Transitive :> CompareTransitive compare;
}.

#[global] Hint Mode CompareStrictOrder ! - : typeclass_instances.

(** Strictly-ordered comparisons entail decidable equality. *)
#[export] Instance compare_eq_dec {A} `{CompareStrictOrder A} : EqDecision A.
Proof.
  intros x y; destruct (compare x y) eqn: Hxy.
  - by left; apply compare_eq.
  - by right; intros ->; rewrite compare_eq_refl in Hxy.
  - by right; intros ->; rewrite compare_eq_refl in Hxy.
Qed.

(** *** Asymmetric comparison operators *)

Class CompareAsymmetric {A} (compare : A -> A -> comparison) : Prop :=
  compare_asymmetric : forall x y, compare x y = CompOpp (compare y x).

#[global] Hint Mode CompareAsymmetric ! - : typeclass_instances.

Lemma compare_asymmetric' {A} `{CompareAsymmetric A} :
  forall x y, compare x y = Lt <-> compare y x = Gt.
Proof.
  intros x y.
  rewrite compare_asymmetric.
  by destruct (compare y x); cbn; firstorder congruence.
Qed.

(** Strictly-ordered comparisons are asymmetric. *)
#[export] Instance compare_asymmetric_intro {A} `{CompareStrictOrder A} :
  CompareAsymmetric compare.
Proof.
  intros x y; destruct (compare y x) eqn: Hyx.
  - by rewrite compare_eq in *.
  - destruct (compare x y) eqn: Hxy; cbn; [| | done].
    + by apply compare_eq in Hxy; subst; rewrite compare_eq_refl in Hyx.
    + assert (Hxx : compare x x = Lt) by (eapply compare_transitive; done).
      by rewrite compare_eq_refl in Hxx.
  - destruct (compare x y) eqn: Hxy; cbn; [| done |].
    + by apply compare_eq in Hxy; subst; rewrite compare_eq_refl in Hyx.
    + assert (Hxx : compare x x = Gt) by (eapply compare_transitive; done).
      by rewrite compare_eq_refl in Hxx.
Qed.

(** [compare_lt] is the relation that corresponds to <<compare>>. *)
Definition compare_lt {A} (compare : A -> A -> comparison) (x y : A) : Prop :=
  compare x y = Lt.

#[export] Instance compare_lt_dec [A : Type]
  (compare : A -> A -> comparison) {Hord : CompareStrictOrder compare}
  : RelDecision (compare_lt compare).
Proof.
  intros x y; unfold compare_lt.
  by typeclasses eauto.
Qed.

(** *** Properties of [compare_lt] *)

Lemma compare_lt_irreflexive {A} `{CompareReflexive A} :
  Irreflexive (compare_lt compare).
Proof.
  by intros x; compute; rewrite compare_eq_refl.
Qed.

Lemma compare_lt_transitive {A} `{CompareTransitive A} :
  Transitive (compare_lt compare).
Proof.
  by intros x y z Hxy Hyz; eapply compare_transitive.
Qed.

Lemma compare_lt_strict_order {A} `{CompareStrictOrder A} :
  StrictOrder (compare_lt compare).
Proof.
  split.
  - by apply compare_lt_irreflexive.
  - by apply compare_lt_transitive.
Qed.

Lemma compare_lt_asymmetric {A} `{CompareStrictOrder A} :
  Asymmetric (compare_lt compare).
Proof.
  unfold compare_lt; intros x y Hxy Hyx.
  assert (Hxx : compare x x = Lt) by (eapply compare_transitive; eauto).
  by rewrite compare_eq_refl in Hxx.
Qed.

(** ** Strictly ordered types *)

Class StrictlyComparable (X : Type) : Type :=
{
  compare : X -> X -> comparison;
  compare_strictorder :> CompareStrictOrder compare;
}.
#[global] Hint Mode StrictlyComparable ! : typeclass_instances.

Definition comparable `(R : relation A) : relation A :=
  fun x y => exists c, CompSpec (=) R x y c.

Lemma tc_CompSpec :
  forall A (Peq Plt : relation A) (a b : A) (c : comparison),
  CompSpec Peq Plt a b c -> CompSpec Peq (tc Plt) a b c.
Proof. by intros *; inversion 1; subst; repeat constructor. Qed.

Lemma tc_comparable :
  forall A (R : relation A) (a b : A),
    comparable R a b -> comparable (tc R) a b.
Proof.
  by intros *; inversion 1; subst; econstructor; apply tc_CompSpec.
Qed.

#[export] Instance comparable_symmetric {A : Type} (R : A -> A -> Prop) :
  Symmetric (comparable R).
Proof.
  intros a b; intros [c Hc]; subst; inversion Hc; subst.
  - by eexists.
  - by exists Gt; constructor.
  - by exists Lt; constructor.
Qed.

#[export] Instance comparable_reflexive {A : Type} (R : A -> A -> Prop) :
  Reflexive (comparable R).
Proof. by intro; exists Eq; constructor. Qed.

#[export] Instance comparable_dec
  `(R : relation A) `{EqDecision A} `{!RelDecision R} :
  RelDecision (comparable R).
Proof.
  intros a b.
  destruct (decide (a = b)); [by subst; left |].
  destruct (decide (R a b)); [by left; exists Lt; constructor |].
  destruct (decide (R b a)); [by left; exists Gt; constructor |].
  by right; intros [c Hc]; inversion Hc.
Qed.

(** *** Comparison for subtypes *)

Definition dsig_compare
  {X} `{StrictlyComparable X} (P : X -> Prop) {Pdec : forall x, Decision (P x)}
  (x y : dsig P) : comparison :=
    compare (`x) (`y).

Lemma dsig_compare_reflexive
  {X} `{StrictlyComparable X} (P : X -> Prop) {Pdec : forall x, Decision (P x)}
  : CompareReflexive (dsig_compare P).
Proof.
  by intros x y; unfold dsig_compare; rewrite dsig_eq, compare_eq.
Qed.

Lemma dsig_compare_transitive
  {X} `{StrictlyComparable X} (P : X -> Prop) {Pdec : forall x, Decision (P x)}
  : CompareTransitive (dsig_compare P).
Proof.
  by intros x y z; unfold dsig_compare; apply compare_transitive.
Qed.

Lemma CompareStrictOrder_dsig_compare
  {X} `{StrictlyComparable X} (P : X -> Prop) {Pdec : forall x, Decision (P x)}
  : CompareStrictOrder (dsig_compare P).
Proof.
  split.
  - by apply dsig_compare_reflexive.
  - by apply dsig_compare_transitive.
Qed.

#[export] Instance StrictlyComparable_dsig
  {X} `{StrictlyComparable X} (P : X -> Prop) {Pdec : forall x, Decision (P x)}
  {Inh : Inhabited (dsig P)}
  : StrictlyComparable (dsig P) :=
{
  compare := dsig_compare P;
  compare_strictorder := CompareStrictOrder_dsig_compare P
}.

(** *** Comparison for options *)

Definition option_compare
  (X : Type) `{StrictlyComparable X}
  (ox oy : option X) : comparison :=
  match ox, oy with
  | None, None => Eq
  | None, _ => Lt
  | _, None => Gt
  | Some x, Some y => compare x y
  end.

Lemma option_compare_reflexive
  (X : Type) `{StrictlyComparable X}
  : CompareReflexive (option_compare X).
Proof.
  by intros [x |] [y |]; cbn; rewrite ?compare_eq; firstorder congruence.
Qed.

Lemma option_compare_transitive
  (X : Type) `{StrictlyComparable X}
  : CompareTransitive (option_compare X).
Proof.
  intros [x |] [y |] [z |] [| |]; simpl; intros Hxy Hyz; try done.
  - by apply (compare_transitive x y z).
  - by apply (compare_transitive x y z).
  - by apply (compare_transitive x y z).
Qed.

Lemma CompareStrictOrder_option_compare
  (X : Type) `{StrictlyComparable X}
  : CompareStrictOrder (option_compare X).
Proof.
  split.
  - by apply option_compare_reflexive.
  - by apply option_compare_transitive.
Qed.

#[export] Instance StrictlyComparable_option
  (X : Type) `{StrictlyComparable X} : StrictlyComparable (option X) :=
{
  compare := option_compare X;
  compare_strictorder := CompareStrictOrder_option_compare _;
}.

(** *** Comparison for pairs and triples *)

Definition pair_compare
  (X Y : Type) `{StrictlyComparable X} `{StrictlyComparable Y}
  : (X * Y) -> (X * Y) -> comparison :=
  fun '(x1, y1) '(x2, y2) =>
  match compare x1 x2 with
  | Eq => compare y1 y2
  | c => c
  end.

Lemma pair_compare_reflexive
  (X Y : Type) `{StrictlyComparable X} `{StrictlyComparable Y}
  : CompareReflexive (pair_compare X Y).
Proof.
  intros [x1 y1] [x2 y2]; split; cbn.
  - destruct (compare x1 x2) eqn: Hx, (compare y1 y2) eqn: Hy; intros [=].
    by apply compare_eq in Hx, Hy; subst.
  - by intros [= -> ->]; cbn; rewrite !compare_eq_refl.
Qed.

Lemma pair_compare_lt
  {X Y : Type} `{StrictlyComparable X} `{StrictlyComparable Y} :
    forall (x1 x2 : X) (y1 y2 : Y) (c : comparison),
      pair_compare X Y (x1, y1) (x2, y2) = c ->
        compare x1 x2 = c \/ x1 = x2 /\ compare y1 y2 = c.
Proof.
  cbn; intros x1 x2 y1 y2 c Hcmp.
  rewrite <- compare_eq.
  by destruct (compare x1 x2), (compare y1 y2); auto.
Qed.

Lemma pair_compare_transitive
  {X Y : Type} `{StrictlyComparable X} `{StrictlyComparable Y}
  : CompareTransitive (pair_compare X Y).
Proof.
  intros [x1 y1] [x2 y2] [x3 y3] comp H12 H23.
  destruct comp eqn: H_comp.
  - by apply pair_compare_reflexive; apply pair_compare_reflexive in H12, H23; congruence.
  - destruct (pair_compare_lt x1 x2 y1 y2 Lt H12) as [left | [-> right]],
             (pair_compare_lt x2 x3 y2 y3 Lt H23) as [left' | [-> right']]; cbn.
    + by replace (compare x1 x3) with Lt by (symmetry; eapply compare_transitive; done).
    + by rewrite left.
    + by rewrite left'.
    + by rewrite compare_eq_refl; eapply compare_transitive.
  - destruct (pair_compare_lt x1 x2 y1 y2 Gt H12) as [left | [-> right]],
             (pair_compare_lt x2 x3 y2 y3 Gt H23) as [left' | [-> right']]; cbn.
    + by replace (compare x1 x3) with Gt by (symmetry; eapply compare_transitive; done).
    + by rewrite left.
    + by rewrite left'.
    + by rewrite compare_eq_refl; eapply compare_transitive.
Qed.

Lemma CompareStrictOrder_pair_compare
  {X Y : Type} `{StrictlyComparable X} `{StrictlyComparable Y}
  : CompareStrictOrder (pair_compare X Y).
Proof.
  split.
  - by apply pair_compare_reflexive.
  - by apply pair_compare_transitive.
Qed.

#[export] Instance StrictlyComparable_pair
  (X Y : Type) `{StrictlyComparable X} `{StrictlyComparable Y} : StrictlyComparable (X * Y) :=
{
  compare := pair_compare X Y;
  compare_strictorder := CompareStrictOrder_pair_compare;
}.

#[export] Instance TripleStrictlyComparable
  (X Y Z : Type) `{StrictlyComparable X} `{StrictlyComparable Y} `{StrictlyComparable Z}
  : StrictlyComparable (X * Y * Z) :=
{
  compare := pair_compare (X * Y) Z;
  compare_strictorder := CompareStrictOrder_pair_compare;
}.

(** *** Comparison for lists *)

Fixpoint list_compare
  (A : Type) `{StrictlyComparable A}
  (l1 l2 : list A) : comparison :=
  match l1, l2 with
  | [], [] => Eq
  | [], _ => Lt
  | _, [] => Gt
  | h1 :: t1, h2 :: t2 =>
    match compare h1 h2 with
    | Eq => list_compare A t1 t2
    | cmp => cmp
    end
  end.

Lemma list_compare_reflexive
  {A : Type} `{StrictlyComparable A}
  : CompareReflexive (list_compare A).
Proof.
  intros l1; induction l1 as [| h1 t1]; intros [| h2 t2]; [done.. |].
  split; cbn.
  - intros Heq.
    destruct (compare h1 h2) eqn: Hcmp; [| done..].
    apply compare_eq in Hcmp as ->.
    by apply IHt1 in Heq as ->.
  - inversion 1; subst.
    by rewrite compare_eq_refl, IHt1.
Qed.

Lemma list_compare_transitive
  {A : Type} `{StrictlyComparable A}
  : CompareTransitive (list_compare A).
Proof.
  intros l1 l2 l3; revert l1 l3.
  induction l2 as [| h2 t2]; cbn; [by destruct l1, l3; cbn; congruence |].
  destruct l1 as [| h1 t1], l3 as [| h3 t3]; cbn; [by congruence.. |].
  intros c.
  destruct (compare h1 h2) eqn: H12, (compare h2 h3) eqn: H23;
    rewrite ?compare_eq in H12; rewrite ?compare_eq in H23; subst;
    rewrite ?compare_eq_refl, ?H12, ?H23; only 2-4, 6-8: congruence.
  - by apply IHt2.
  - by rewrite (StrictOrder_Transitive _ _ _ _ H12 H23).
  - by rewrite (StrictOrder_Transitive _ _ _ _ H12 H23).
Qed.

#[export] Instance CompareStrictOrder_list_compare
  {A : Type} `{StrictlyComparable A}
  : CompareStrictOrder (list_compare A).
Proof.
  split.
  - by apply list_compare_reflexive.
  - by apply list_compare_transitive.
Qed.

#[export] Instance StrictlyComparable_list
  {A : Type} `{StrictlyComparable A} : StrictlyComparable (list A) :=
{
  compare := list_compare A;
  compare_strictorder := CompareStrictOrder_list_compare;
}.

(** ** Liveness *)

Definition bounding (P : nat -> Prop)
  :=  {n1 : nat | forall (n2 : nat), n1 <= n2 -> ~ P n2}.

Definition liveness (P : nat -> Prop)
  := forall (n1 : nat), { n2 : nat | n1 <= n2 /\ P n2}.

Definition liveness_dec (P : nat -> Prop)
  := forall (n1 : nat), { n2 : nat | n1 <= n2 /\ P n2} + {~ exists n2 : nat, n1 <= n2 /\ P n2}.

Definition min_liveness (P : nat -> Prop)
  := forall (n1 : nat), { n2 : nat | n1 <= n2 /\ P n2
               /\ forall (n3 : nat), n2 <= n3 /\ P n3 -> n2 <= n3}.

Lemma not_bounding_impl_liveness
  (P : nat -> Prop)
  (Hdec : liveness_dec P)
  (Hnbound : ~ exists n1 : nat, forall (n2 : nat), n1 <= n2 -> ~ P n2)
  : liveness P.
Proof.
  intros n1.
  specialize (Hdec n1).
  destruct Hdec as [Hex | Hnex]; [done |].
  contradiction Hnbound.
  exists n1.
  intros n2 Hleq HnP.
  apply Hnex.
  by exists n2.
Qed.

(** ** Misc *)

(** Extracts the left element from a sum, if possible. *)
Definition sum_project_left {A B : Type} (x : A + B) : option A :=
  match x with
  | inl a => Some a
  | inr _ => None
  end.

(** Extracts the right element from a sum, if possible. *)
Definition sum_project_right {A B : Type} (x : A + B) : option B :=
  match x with
  | inl _ => None
  | inr b => Some b
  end.

Program Definition not_lt_plus_dec {m n} (Hnlt : ~ n < m) : {k | k + m = n} :=
  exist _ (n - m) _.
Next Obligation.
Proof. by cbn; lia. Qed.

Definition update `{EqDecision A} `(f : A -> B) (a : A) (b : B) : A -> B :=
  fun a' : A => if decide (a = a') then b else f a'.

Lemma update_eq `{EqDecision A} `(f : A -> B) (a : A) (b : B) :
  update f a b a = b.
Proof.
  by unfold update; rewrite decide_True.
Qed.

Lemma update_neq `{EqDecision A} `(f : A -> B) (a : A) (b : B) (a' : A) :
  a <> a' -> update f a b a' = f a'.
Proof.
  by intros; unfold update; rewrite decide_False.
Qed.
