From Coq Require Export Program.Tactics.
Obligation Tactic := idtac.
From stdpp Require Import prelude.
From Coq Require Import Eqdep_dec.

(** * General utility definitions, lemmas, and tactics *)

(** ** Tactics for specializing hypotheses *)

Tactic Notation "spec" hyp(H) :=
  match type of H with ?a -> _ =>
  let H1 := fresh in (assert (H1: a);
  [|generalize (H H1); clear H H1; intro H]) end.
Tactic Notation "spec_save" hyp(H) :=
  match type of H with ?a -> _ =>
  let H1 := fresh in (assert (H1: a);
  [|generalize (H H1); clear H; intro H]) end.
Tactic Notation "spec" hyp(H) constr(a) :=
  (generalize (H a); clear H; intro H).
Tactic Notation "spec" hyp(H) constr(a) constr(b) :=
  (generalize (H a b); clear H; intro H).
Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) :=
  (generalize (H a b c); clear H; intro H).
Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) :=
  (generalize (H a b c d); clear H; intro H).
Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) constr(e) :=
  (generalize (H a b c d e); clear H; intro H).

(** ** Basic logic *)

Lemma Is_true_iff_eq_true: forall x: bool, x = true <-> x.
Proof.
  split.
  - apply Is_true_eq_left.
  - apply Is_true_eq_true.
Qed.

Lemma and_proper_l (A B C : Prop) : (A -> (B <-> C)) -> (A /\ B) <-> (A /\ C).
Proof. firstorder. Qed.

Lemma impl_proper (A B C : Prop) : (A -> (B <-> C)) -> (A -> B) <-> (A -> C).
Proof. firstorder. Qed.

(** ** Decidable propositions *)

Lemma Decision_iff : forall {P Q}, (P <-> Q) -> Decision P -> Decision Q.
Proof. firstorder. Qed.
Lemma Decision_and : forall {P Q}, Decision P -> Decision Q -> Decision (P /\ Q).
Proof. firstorder. Qed.
Lemma Decision_or : forall {P Q}, Decision P -> Decision Q -> Decision (P \/ Q).
Proof. firstorder. Qed.
Lemma Decision_not : forall {P}, Decision P -> Decision (~P).
Proof. firstorder. Qed.

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
Proof. induction 1; firstorder. Qed.

(** Characterization of [tc] in terms of the last transitivity step. *)
Lemma tc_r_iff `(R : relation A) :
  forall x z, tc R x z <-> R x z \/ exists y, tc R x y /\ R y z.
Proof.
  split.
  - intros Htc; apply tc_nsteps in Htc as (n & Hn & Hsteps).
    induction Hsteps; [lia |].
    destruct n; [inversion Hsteps; subst; by left |].
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
  `{R1 : relation A} `(R2 : relation B) `{!Transitive R2} (f : A → B) :
  (∀ x y, R1 x y → R2 (f x) (f y)) →
  wf R2 → wf (tc R1).
Proof.
  intros Hpreserve.
  apply wf_projected with f.
  induction 1; [by apply Hpreserve |].
  transitivity (f y); [| done].
  by apply Hpreserve.
Qed.

Lemma tc_reflect_irreflexive
  `(R : relation A) `{!Irreflexive (tc R)} : Irreflexive R.
Proof. by intros ? ?; eapply irreflexivity with (R := tc R); [| constructor]. Qed.

(** ** Equality of dependent pairs *)

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
  apply proof_irrel.
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
  replace (bool_decide_pack (P a) e1) with (bool_decide_pack (P a) e2)
  ; [| apply proof_irrel].
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
  firstorder.
Qed.

(** The minimality definitions are equivalent for [StrictOrder]s. *)
Lemma strict_minimal_among_iff
  `(R : relation A) `{!StrictOrder R} (P : A -> Prop)
  : forall m, minimal_among R P m <-> strict_minimal_among R P m.
Proof.
  apply asymmetric_minimal_among_iff; typeclasses eauto.
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

Lemma compare_eq_lt {A} `{CompareReflexive A} :
  forall x, ~ compare x x = Lt.
Proof.
  by intros x; rewrite compare_eq_refl.
Qed.

Lemma compare_lt_neq {A} `{CompareReflexive A} :
  forall x y, compare x y = Lt -> x <> y.
Proof.
  intros x y Hcomp Hnot.
  by subst; apply (compare_eq_lt y) in Hcomp.
Qed.

Lemma compare_eq_gt {A} `{CompareReflexive A} :
  forall x, ~ compare x x = Gt.
Proof.
  by intros x; rewrite compare_eq_refl.
Qed.

Lemma compare_gt_neq {A} `{CompareReflexive A} :
  forall x y, compare x y = Gt -> x <> y.
Proof.
  intros x y H_comp H_not.
  by subst; apply compare_eq_gt in H_comp.
Qed.

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
  - by right; intros ->; apply compare_eq_lt in Hxy.
  - by right; intros ->; apply compare_eq_gt in Hxy.
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
  destruct (compare y x); cbn; firstorder congruence.
Qed.

(** Strictly-ordered comparisons are asymmetric. *)
#[export] Instance compare_asymmetric_intro {A} `{CompareStrictOrder A} :
  CompareAsymmetric compare.
Proof.
  intros x y; destruct (compare y x) eqn: Hyx.
  - by rewrite compare_eq in *.
  - destruct (compare x y) eqn: Hxy; cbn; [| | done].
    + apply compare_eq in Hxy; subst. by apply compare_eq_lt in Hyx.
    + assert (Hxx : compare x x = Lt) by (eapply compare_transitive; done).
      by apply compare_eq_lt in Hxx.
  - destruct (compare x y) eqn: Hxy; cbn; [| done |].
    + apply compare_eq in Hxy; subst. by apply compare_eq_gt in Hyx.
    + assert (Hxx : compare x x = Gt) by (eapply compare_transitive; done).
      by apply compare_eq_gt in Hxx.
Qed.

(** [compare_lt] is the relation that corresponds to <<compare>>. *)
Definition compare_lt {A} (compare : A -> A -> comparison) (x y : A) : Prop :=
  compare x y = Lt.

#[export] Instance compare_lt_dec [A : Type]
  (compare : A -> A -> comparison) {Hord : CompareStrictOrder compare}
  : RelDecision (compare_lt compare).
Proof.
  intros x y; unfold compare_lt.
  typeclasses eauto.
Qed.

(** *** Properties of [compare_lt] *)

Lemma compare_lt_irreflexive {A} `{CompareReflexive A} :
  Irreflexive (compare_lt compare).
Proof.
  intros x; apply compare_eq_lt.
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
  by eapply (compare_eq_lt x), compare_transitive.
Qed.

(** ** Strictly ordered inhabited types *)

Class StrictlyComparable (X : Type) : Type :=
{
  inhabited : X;
  compare : X -> X -> comparison;
  compare_strictorder :> CompareStrictOrder compare;
}.
#[global] Hint Mode StrictlyComparable ! : typeclass_instances.

#[export] Existing Instance compare_strictorder.

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

#[local] Obligation Tactic := Tactics.program_simpl.
Program Definition sigify_compare
  {X} `{StrictlyComparable X} (P : X -> Prop) : {x | P x} -> {x | P x} -> comparison := _.
Next Obligation.
  exact (compare X0 X1).
Defined.

Definition dsigify_compare
  {X} `{StrictlyComparable X} (P : X -> Prop) {Pdec : forall x, Decision (P x)}
  : dsig P -> dsig P -> comparison :=
  fun x y => compare (proj1_sig x) (proj1_sig y).

Lemma dsigify_compare_reflexive
  {X} `{StrictlyComparable X} (P : X -> Prop) {Pdec : forall x, Decision (P x)}
  : CompareReflexive (dsigify_compare P).
Proof.
  intros x y. rewrite dsig_eq. apply compare_strictorder.
Qed.

Lemma dsigify_compare_transitive
  {X} `{StrictlyComparable X} (P : X -> Prop) {Pdec : forall x, Decision (P x)}
  : CompareTransitive (dsigify_compare P).
Proof.
  intros x y z. apply compare_strictorder.
Qed.

Lemma dsigify_compare_strictorder
  {X} `{StrictlyComparable X} (P : X -> Prop) {Pdec : forall x, Decision (P x)}
  : CompareStrictOrder (dsigify_compare P).
Proof.
  split.
  - apply dsigify_compare_reflexive.
  - apply dsigify_compare_transitive.
Qed.

Definition dsigify_compare_strictly_comparable
  {X} `{StrictlyComparable X} (P : X -> Prop) {Pdec : forall x, Decision (P x)}
  {Inh : Inhabited (dsig P)}
  : StrictlyComparable (dsig P) :=
  {| inhabited := inhabitant
  ; compare := dsigify_compare P
  ; compare_strictorder := dsigify_compare_strictorder P
  |}.

#[local] Obligation Tactic := idtac.

(** *** Comparison for options *)

Definition option_compare
  {X : Type}
  (compare : X -> X -> comparison)
  (ox oy : option X)
  : comparison
  :=
  match ox, oy with
  | None, None => Eq
  | None, _ => Lt
  | _, None => Gt
  | Some x, Some y => compare x y
  end.

Lemma option_compare_reflexive
  (X : Type)
  {Xsc : StrictlyComparable X}
  : CompareReflexive (option_compare (@compare X _)).
Proof.
  intros [x |] [y |]; cbn; rewrite ?compare_eq; firstorder congruence.
Qed.

Lemma option_compare_transitive
  (X : Type)
  {Xsc : StrictlyComparable X}
  : CompareTransitive (option_compare (@compare X _)).
Proof.
  intros [x |] [y |] [z |] [| |]; simpl; intros Hxy Hyz; try done.
  - by apply (compare_transitive x y z).
  - by apply (compare_transitive x y z).
  - by apply (compare_transitive x y z).
Qed.

Lemma strictorder_option
  {X: Type}
  (Xsc : StrictlyComparable X)
  : CompareStrictOrder (option_compare (@compare X _)).
Proof.
  split.
  - by apply option_compare_reflexive.
  - by apply option_compare_transitive.
Qed.

#[export] Instance OptionStrictlyComparable
  (X : Type) {Xsc : StrictlyComparable X} : StrictlyComparable (option X) :=
{
  inhabited := None;
  compare := option_compare compare;
  compare_strictorder := strictorder_option Xsc;
}.

(** *** Comparison for pairs *)

Definition compare_compose
  (X Y : Type) `{StrictlyComparable X} `{StrictlyComparable Y}
  : (X * Y) -> (X * Y) -> comparison :=
  fun '(x1, y1) '(x2, y2) =>
  match compare x1 x2 with
  | Eq => compare y1 y2
  | c => c
  end.

Definition inhabited_compose
  {X Y : Type} `{HscX : StrictlyComparable X} `{HscY : StrictlyComparable Y}
  : X * Y := (inhabited, inhabited).

Lemma reflexive_compose
  {X Y : Type} `{StrictlyComparable X} `{StrictlyComparable Y}
  : CompareReflexive (compare_compose X Y).
Proof.
  intros [x1 y1] [x2 y2].
  split.
  - cbn; intros Hcmp.
    destruct (compare x1 x2) eqn: Hx, (compare y1 y2) eqn: Hy; try done.
    by apply compare_eq in Hx, Hy; subst.
  - by intros [= -> ->]; cbn; rewrite !compare_eq_refl.
Qed.

Lemma compare_compose_lt
  {X Y : Type} `{StrictlyComparable X} `{StrictlyComparable Y} :
    forall (x1 x2 : X) (y1 y2 : Y) (c : comparison),
      compare_compose X Y (x1, y1) (x2, y2) = c ->
        compare x1 x2 = c \/ x1 = x2 /\ compare y1 y2 = c.
Proof.
  intros x1 x2 y1 y2 c Hcmp; cbn in Hcmp.
  rewrite <- compare_eq.
  by destruct (compare x1 x2), (compare y1 y2); auto.
Qed.

Lemma transitive_compose
  {X Y : Type} `{StrictlyComparable X} `{StrictlyComparable Y}
  : CompareTransitive (compare_compose X Y).
Proof.
  intros [x1 y1] [x2 y2] [x3 y3] comp H12 H23.
  destruct comp eqn: H_comp.
  - by apply reflexive_compose; apply reflexive_compose in H12, H23; congruence.
  - destruct (compare_compose_lt x1 x2 y1 y2 Lt H12) as [left | [-> right]],
             (compare_compose_lt x2 x3 y2 y3 Lt H23) as [left' | [-> right']]; cbn.
    + by replace (compare x1 x3) with Lt by (symmetry; eapply compare_transitive; done).
    + by rewrite left.
    + by rewrite left'.
    + by rewrite compare_eq_refl; eapply compare_transitive.
  - destruct (compare_compose_lt x1 x2 y1 y2 Gt H12) as [left | [-> right]],
             (compare_compose_lt x2 x3 y2 y3 Gt H23) as [left' | [-> right']]; cbn.
    + by replace (compare x1 x3) with Gt by (symmetry; eapply compare_transitive; done).
    + by rewrite left.
    + by rewrite left'.
    + by rewrite compare_eq_refl; eapply compare_transitive.
Qed.

Lemma strictorder_compose
  {X Y : Type} `{StrictlyComparable X} `{StrictlyComparable Y}
  : CompareStrictOrder (compare_compose X Y).
Proof.
  split.
  - by apply reflexive_compose.
  - by apply transitive_compose.
Qed.

#[export] Instance ComposeStrictlyComparable
  (X Y : Type) `{StrictlyComparable X} `{StrictlyComparable Y} : StrictlyComparable (X * Y) :=
{
  inhabited := inhabited_compose;
  compare := compare_compose X Y;
  compare_strictorder := strictorder_compose;
}.

(** *** Comparison for triples, with some helper functions *)

#[export] Instance TripleStrictlyComparable
  (X Y Z : Type) `{StrictlyComparable X} `{StrictlyComparable Y} `{StrictlyComparable Z}
  : StrictlyComparable (X * Y * Z) :=
{
  inhabited := inhabited_compose;
  compare := compare_compose (X * Y) Z;
  compare_strictorder := strictorder_compose;
}.

Definition triple_strictly_comparable_proj1_inhabited
  {X Y Z} `{HscXYZ : StrictlyComparable (X * Y * Z)} : X.
Proof.
  by destruct HscXYZ as [((x, _), _) _ _].
Defined.

Definition triple_strictly_comparable_proj1_compare
  {X Y Z} `{HscXYZ : StrictlyComparable (X * Y * Z)} (x1 x2 : X) : comparison.
Proof.
  destruct HscXYZ as [((x, y), z) compare _].
  exact (compare (x1, y, z) (x2, y, z)).
Defined.

#[export] Instance triple_strictly_comparable_proj1_strictorder
  {X Y Z} `{HscXYZ : StrictlyComparable (X * Y * Z)}
  : CompareStrictOrder (@triple_strictly_comparable_proj1_compare X Y Z HscXYZ) | 100.
Proof.
  destruct HscXYZ, inhabited0 as [[x0 y0] z0].
  split.
  - by intros x y; cbn; rewrite compare_eq; firstorder congruence.
  - by intros x1 x2 x3 cmp; cbn; apply compare_transitive.
Qed.

Definition triple_strictly_comparable_proj1
  {X Y Z} (HscT :  StrictlyComparable (X * Y * Z))
  : StrictlyComparable X :=
{|
  inhabited := triple_strictly_comparable_proj1_inhabited;
  compare := triple_strictly_comparable_proj1_compare;
  compare_strictorder := triple_strictly_comparable_proj1_strictorder;
|}.

Definition triple_strictly_comparable_proj2_inhabited
  {X Y Z} `{HscXYZ : StrictlyComparable (X * Y * Z)} : Y.
Proof.
  by destruct HscXYZ as [[(_, y) _] _ _].
Defined.

Definition triple_strictly_comparable_proj2_compare
  {X Y Z} `{HscXYZ : StrictlyComparable (X * Y * Z)} (y1 y2 : Y) : comparison.
Proof.
  destruct HscXYZ as [[(x, y) z] compare _].
  exact (compare (x, y1, z) (x, y2, z)).
Defined.

#[export] Instance triple_strictly_comparable_proj2_strictorder
  {X Y Z} `{HscXYZ : StrictlyComparable (X * Y * Z)}
  : CompareStrictOrder (@triple_strictly_comparable_proj2_compare X Y Z HscXYZ) | 100.
Proof.
  destruct HscXYZ, inhabited0 as [[x0 y0] z0].
  split.
  - by intros x y; cbn; rewrite compare_eq; firstorder congruence.
  - by intros x1 x2 x3 cmp; cbn; apply compare_transitive.
Qed.

Definition triple_strictly_comparable_proj2
  {X Y Z} (HscT :  StrictlyComparable (X * Y * Z))
  : StrictlyComparable Y :=
{|
  inhabited := triple_strictly_comparable_proj2_inhabited;
  compare := triple_strictly_comparable_proj2_compare;
  compare_strictorder := triple_strictly_comparable_proj2_strictorder;
|}.

Definition triple_strictly_comparable_proj3_inhabited
  {X Y Z} `{HscXYZ : StrictlyComparable (X * Y * Z)} : Z.
Proof.
  by destruct HscXYZ as [[_ z] _ _].
Defined.

Definition triple_strictly_comparable_proj3_compare
  {X Y Z} `{HscXYZ : StrictlyComparable (X * Y * Z)} (z1 z2 : Z) : comparison.
Proof.
  destruct HscXYZ as [[(x, y) z] compare _].
  exact (compare (x, y, z1) (x, y, z2)).
Defined.

#[export] Instance triple_strictly_comparable_proj3_strictorder
  {X Y Z} `{HscXYZ : StrictlyComparable (X * Y * Z)}
  : CompareStrictOrder (@triple_strictly_comparable_proj3_compare X Y Z HscXYZ) | 100.
Proof.
  destruct HscXYZ, inhabited0 as [[x0 y0] z0].
  split.
  - by intros x y; cbn; rewrite compare_eq; firstorder congruence.
  - by intros x1 x2 x3 cmp; cbn; apply compare_transitive.
Qed.

Definition triple_strictly_comparable_proj3
  {X Y Z} (HscT :  StrictlyComparable (X * Y * Z))
  : StrictlyComparable Z :=
{|
  inhabited := triple_strictly_comparable_proj3_inhabited;
  compare := triple_strictly_comparable_proj3_compare;
  compare_strictorder := triple_strictly_comparable_proj3_strictorder;
|}.

(** ** Liveness *)

Definition bounding (P : nat -> Prop)
  :=  {n1 : nat | forall (n2 : nat), n1 <= n2 -> ~P n2}.

Definition liveness (P : nat -> Prop)
  := forall (n1 : nat), { n2 : nat | n1 <= n2 /\ P n2}.

Definition liveness_dec (P : nat -> Prop)
  := forall (n1 : nat), { n2 : nat | n1 <= n2 /\ P n2} + {~exists n2:nat, n1 <= n2 /\ P n2}.

Definition min_liveness (P : nat -> Prop)
  := forall (n1 : nat), { n2 : nat | n1 <= n2 /\ P n2
               /\ forall (n3 : nat), n2 <= n3 /\ P n3 -> n2 <= n3}.

Lemma not_bounding_impl_liveness
  (P : nat -> Prop)
  (Hdec : liveness_dec P)
  (Hnbound : ~exists n1:nat, forall (n2:nat), n1 <= n2 -> ~P n2)
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

Program Definition not_lt_plus_dec {m n} (Hnlt : ~n < m) : {k | k + m = n} :=
  exist _ (n - m) _.
Next Obligation.
  cbn; lia.
Qed.
