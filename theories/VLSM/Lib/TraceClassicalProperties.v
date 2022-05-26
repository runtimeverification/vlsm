From Coq Require Import Classical ClassicalEpsilon.
From VLSM Require Import Lib.SsrExport Lib.Traces Lib.TraceProperties.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** * Properties of possibly-infinite traces requiring classical logic *)

Section TraceClassicalProperties.

Context {A B : Type}.

Local Notation trace := (@trace A B).
Local Notation propT := (@propT A B).

(** ** Relating finiteness and infiniteness *)

Lemma not_infiniteT_finiteT : forall tr : trace,
 ~ infiniteT tr -> finiteT tr.
Proof.
move => tr Hnot.
case: (classic (finiteT tr)) => Hinf //.
case: Hnot.
exact: not_finiteT_infiniteT.
Qed.

Lemma finiteT_infiniteT : forall tr : trace,
 finiteT tr \/ infiniteT tr.
Proof.
move => tr.
case: (classic (finiteT tr)) => Hinf; first by left.
right; exact: not_finiteT_infiniteT.
Qed.

Definition finiteT_infiniteT_dec (tr : trace) : { finiteT tr }+{ infiniteT tr } :=
match excluded_middle_informative (finiteT tr) with
| left Hfin => left Hfin
| right Hfin => right (not_finiteT_infiniteT Hfin)
end.

(** ** Using midpoints to show the right associativity of the append property *)

CoFixpoint midp (p0 p1: trace -> Prop) tr0 tr1 (h: followsT (appendT p0 p1) tr0 tr1) : trace :=
match followsT_dec h with
| inl (existT tr (exist a (conj _ (conj _ H)))) =>
  let: exist x _ := constructive_indefinite_description _ H in x
| inr (existT tr (existT tr' (existT a (exist b (conj _ (conj _ H)))))) =>
  Tcons a b (@midp _ _ _ _ H)
end.

Lemma midpointT_midp : forall (p0 p1: trace -> Prop) tr0 tr1 (h : followsT (appendT p0 p1) tr0 tr1),
 midpointT h (midp h).
Proof.
cofix CIH.
dependent inversion h; subst.
- rewrite [midp _]trace_destr /=.
  case: (constructive_indefinite_description _ _) => /= x [a1 hm].
  by apply: midpointT_nil => //; case: x a1 hm.
- rewrite [midp _]trace_destr /=.
  exact: (@midpointT_delay _ _ p0 p1 (Tcons a b tr) (Tcons a b tr') (followsT_delay a b f) tr tr' f a b (midp f)).
Qed.

Lemma appendT_assoc_R: forall p1 p2 p3,
 forall tr : trace, (appendT p1 (appendT p2 p3)) tr -> (appendT (appendT p1 p2)  p3) tr.
Proof.
move => p1 p2 p3 tr0 [tr1 [h1 h2]].
exists (midp h2); split.
- exists tr1; split => //.
  exact: (midpointT_before (midpointT_midp h2)).
- exact: (midpointT_after (midpointT_midp h2)).
Qed.

Lemma AppendT_assoc_R: forall (p1 p2 p3 : propT), (p1 *** p2 *** p3) =>> (p1 *** p2) *** p3.
Proof.
move => [f1 hf1] [f2 hf2] [f3 hf3] tr0 /= h1.
exact: appendT_assoc_R.
Qed.

End TraceClassicalProperties.
