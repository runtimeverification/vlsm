From Coq Require Import Program.Equality.
From VLSM Require Import Lib.SsrExport Lib.Traces.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** * Core properties of possibly-infinite traces *)

(** The property encodings and many specific properties are adapted from the paper
#<a href="https://arxiv.org/abs/1412.6579">A Hoare logic for the coinductive trace-based big-step semantics of While</a>#. *)

Section TraceProperties.

Context {A B : Type}.

Local Notation trace := (@trace A B).

(** We want to reason about trace properties that do not distinguish
bisimilar traces; these are called _setoid_ properties. *)

Definition setoidT (p : trace -> Prop) :=
forall tr0, p tr0 -> forall tr1, bisim tr0 tr1 -> p tr1.

Definition propT := { p : trace -> Prop | setoidT p }.

(** ** Infiniteness property *)

CoInductive infiniteT : trace -> Prop :=
| infiniteT_delay : forall a b tr,
   infiniteT tr ->
   infiniteT (Tcons a b tr).

Lemma infiniteT_setoidT : setoidT infiniteT.
Proof.
cofix CIH.
move => tr0 h0 tr1 h1.
invs h0; invs h1.
exact: (infiniteT_delay a b (CIH _ H _ H4)).
Qed.

Definition InfiniteT : propT :=
exist _ (fun tr => infiniteT tr) infiniteT_setoidT.

Lemma infiniteT_cons : forall a b tr,
 infiniteT (Tcons a b tr) -> infiniteT tr.
Proof.
move => a b tr Hinf.
by inversion Hinf.
Qed.

Lemma infiniteT_trace_append :
 forall tr, infiniteT tr -> forall tr', infiniteT (tr' +++ tr).
Proof.
cofix CIH.
move => tr Htr.
case => [a|a b tr']; first by rewrite trace_append_nil.
rewrite trace_append_cons.
exact/infiniteT_delay/CIH.
Qed.

Lemma trace_append_infiniteT :
 forall tr, infiniteT tr -> forall tr', infiniteT (tr +++ tr').
Proof.
cofix CIH.
case => [a|a b tr0] Hinf; inversion Hinf => tr'; subst.
rewrite trace_append_cons.
exact/infiniteT_delay/CIH.
Qed.

(** ** Finiteness property *)

Inductive finiteT : trace -> Prop :=
| finiteT_nil : forall a,
   finiteT (Tnil a)
| finiteT_delay : forall (a : A) (b : B) tr,
   finiteT tr ->
   finiteT (Tcons a b tr).

Lemma finiteT_setoidT : setoidT finiteT.
Proof.
move => tr1. elim => [a | a b tr1' Hfin IH] tr2 h0; invs h0.
- exact: finiteT_nil.
- exact/finiteT_delay/IH.
Qed.

Definition FiniteT : propT :=
exist _ (fun tr => finiteT tr) finiteT_setoidT.

Lemma invert_finiteT_delay (a : A) (b : B) (tr : trace)
 (h : finiteT (Tcons a b tr)) : finiteT tr.
Proof. by inversion h. Defined.

(** Equality coincides with bisimilarity for finite traces. *)

Lemma finiteT_bisim_eq : forall tr,
 finiteT tr -> forall tr', bisim tr tr' -> tr = tr'.
Proof.
move => tr; elim => [a tr'|a b tr0 Hfin IH tr'] Hbis; invs Hbis => //.
by rewrite (IH _ H3).
Qed.

(** Basic connections between finiteness and infiniteness. *)

Lemma finiteT_infiniteT_not : forall tr,
 finiteT tr -> infiniteT tr -> False.
Proof.
by move => tr; elim => [a|a b tr' Hfin IH] Hinf; inversion Hinf.
Qed.

Lemma not_finiteT_infiniteT : forall tr,
 ~ finiteT tr -> infiniteT tr.
Proof.
cofix CIH.
case => [a | a b tr] Hfin; first by case: Hfin; apply: finiteT_nil.
apply: infiniteT_delay.
apply: CIH => Hinf.
case: Hfin.
exact: finiteT_delay.
Qed.

(** ** Final element properties *)

Inductive finalTA : trace -> A -> Prop :=
| finalTA_nil : forall a,
   finalTA (Tnil a) a
| finalTA_delay : forall a b a' tr,
   finalTA tr a' ->
   finalTA (Tcons a b tr) a'.

Inductive finalTB : trace -> B -> Prop :=
| finalTB_nil : forall a b a',
   finalTB (Tcons a b (Tnil a')) b
| finalTB_delay : forall a b b' tr,
   finalTB tr b' ->
   finalTB (Tcons a b tr) b'.

Lemma finalTA_finiteT : forall tr a, finalTA tr a -> finiteT tr.
Proof.
move => tr a; elim => [a1 | a1 b a2 tr' Hfinal IH].
- exact: finiteT_nil.
- exact/finiteT_delay/IH.
Qed.

Lemma finalTB_finiteT : forall tr b, finalTB tr b -> finiteT tr.
Proof.
move => tr b; elim => [a1 b1 a2 | a1 b1 b2 a2 Hfin IH].
- exact/finiteT_delay/finiteT_nil.
- exact: finiteT_delay.
Qed.

Fixpoint finalA (tr : trace) (h : finiteT tr) {struct h} : A :=
match tr as tr' return (finiteT tr' -> A) with
| Tnil a => fun _ => a
| Tcons a b tr => fun h => finalA (invert_finiteT_delay h)
end h.

Lemma finiteT_finalTA : forall tr (h : finiteT tr),
 finalTA tr (finalA h).
Proof.
refine (fix IH tr h {struct h} := _).
case: tr h => [a | a b tr] h; dependent inversion h => /=.
- exact: finalTA_nil.
- exact: finalTA_delay.
Qed.

Lemma finalTA_hd_append_trace : forall tr0 a,
 finalTA tr0 a -> forall tr1, hd tr1 = a ->
 hd (tr0 +++ tr1) = hd tr0.
Proof.
move => tr a; elim => {tr a} [a tr <- | a b a' tr Hfinal IH tr'] //=.
Qed.

(** ** Basic trace properties and connectives *)

Definition ttT : trace -> Prop := fun tr => True.

Lemma ttT_setoidT : setoidT ttT.
Proof. by []. Qed.

Definition TtT : propT :=
exist _ ttT ttT_setoidT.

Definition ffT : trace -> Prop := fun tr => False.

Lemma ffT_setoidT : setoidT ffT.
Proof. by []. Qed.

Definition FfT : propT :=
exist _ ffT ffT_setoidT.

Definition notT (p : trace -> Prop) : trace -> Prop := fun tr => ~ p tr.

Lemma notT_setoidT : forall p, setoidT p -> setoidT (notT p).
Proof.
move => p hp tr h1 tr' h2 h3.
apply: h1. apply: hp _ h3 _ (bisim_sym h2).
Qed.

Definition NotT (p : propT) : propT :=
let: exist f hf := p in
exist _ (notT f) (notT_setoidT hf).

Definition satisfyT (p : propT) : trace -> Prop :=
fun tr => let: exist f0 h0 := p in f0 tr.

Program Definition ExT {T: Type} (p: T -> propT) : propT :=
exist _ (fun tr => exists x, satisfyT (p x) tr) _.
Next Obligation.
move => tr0 [x h0] tr1 h1. exists x.
case: (p x) h0 => [f0 h2] /= h0.
exact: h2 _ h0 _ h1.
Defined.

Lemma andT_setoidT : forall f0 f1,
 setoidT f0 -> setoidT f1 ->
 setoidT (fun tr => f0 tr /\ f1 tr).
Proof.
move => f0 f1 h0 h1 tr0 [h2 h3] tr1 h4; split.
- exact: h0 _ h2 _ h4.
- exact: h1 _ h3 _ h4.
Qed.

Definition AndT (p1 p2 : propT) : propT :=
let: exist f0 h0 := p1 in
let: exist f1 h1 := p2 in
exist _ (fun tr => f0 tr /\ f1 tr) (andT_setoidT h0 h1).

Local Infix "andT" := AndT (at level 60, right associativity).

Lemma orT_setoidT : forall f0 f1,
 setoidT f0 -> setoidT f1 ->
 setoidT (fun tr => f0 tr \/ f1 tr).
Proof.
move => f0 f1 h0 h1 tr0 [h2|h2] tr1 h3.
- by left; apply: h0 _ h2 _ h3.
- by right; apply: h1 _ h2 _ h3.
Qed.

Definition OrT (p1 p2: propT) : propT :=
let: exist f0 h0 := p1 in
let: exist f1 h1 := p2 in
exist _ (fun tr => f0 tr \/ f1 tr) (orT_setoidT h0 h1).

Local Infix "orT" := OrT (at level 60, right associativity).

Definition propT_imp (p1 p2: propT) : Prop :=
forall tr, satisfyT p1 tr -> satisfyT p2 tr.

Local Infix "=>>" := propT_imp (at level 60, right associativity).

Lemma propT_imp_conseq_L: forall p0 p1 q, p0 =>> p1 -> p1 =>> q -> p0 =>> q.
Proof.
move => [p0 hp0] [p1 hp1] [q hq] h0 h1 tr0 /= h2.
exact/h1/h0.
Qed.

Lemma propT_imp_conseq_R: forall p q0 q1,
 q0 =>> q1 -> p =>> q0 -> p =>> q1.
Proof.
move => [p hp] [q0 hq0] [q1 hq1] h0 h1 tr0 /= h2.
exact/h0/h1.
Qed.

Lemma propT_imp_andT: forall p q0 q1,
 p =>> q0 -> p =>> q1 -> p =>> (q0 andT q1).
Proof.
move => [p hp] [q0 hq0] [q1 hq1] h0 h1 tr0 /= h2. split.
- exact: h0.
- exact: h1.
Qed.

Lemma propT_imp_refl : forall p, p =>> p.
Proof. by move => p. Qed.

Lemma satisfyT_cont : forall p0 p1,
 p0 =>> p1 -> forall tr, satisfyT p0 tr -> satisfyT p1 tr.
Proof.
move => [f0 h0] [f1 h1] h2 tr /= h3.
exact: h2.
Qed.

Lemma propT_imp_trans : forall p q r, p =>> q -> q =>> r -> p =>> r.
Proof.
move => p q r h0 h1 tr0 h2.
exact/(satisfyT_cont h1)/(satisfyT_cont h0 h2).
Qed.

Lemma OrT_left : forall p1 p2, p1 =>> (p1 orT p2).
Proof.
move => [f1 hf1] [f2 hf2] tr /= h1. by left.
Qed.

Lemma OrT_right: forall p1 p2, p2 =>> (p1 orT p2).
Proof.
move => [f1 hf1] [f2 hf2] tr /= h1. by right.
Qed.

(** ** Basic trace element properties and connectives *)

Definition propA := A -> Prop.

Definition ttA : propA := fun a => True.

Definition ffA : propA := fun a => False.

Definition propA_imp (u1 u2: propA) : Prop := forall a, u1 a -> u2 a.

Local Infix "->>" := propA_imp (at level 60, right associativity).

Definition andA (u1 u2: propA) : propA := fun a => u1 a /\ u2 a.

Local Infix "andA" := andA (at level 60, right associativity).

Definition exA {T : Type} (u: T -> propA) : propA :=
fun st => exists x, u x st.

(** ** Singleton property *)

Definition singletonT (u : propA) : trace -> Prop :=
fun tr => exists a, u a /\ bisim tr (Tnil a).

Lemma nil_singletonT : forall (u : propA) a, u a -> singletonT u (Tnil a).
Proof. by move => u st h0; exists st; split; last by apply: bisim_refl. Qed.

Lemma singletonT_setoidT : forall u, setoidT (singletonT u).
Proof.
move => u tr0 [a [h0 h2]] tr1 h1.
invs h2; invs h1.
exact: nil_singletonT.
Qed.

Lemma singletonT_cont : forall u v, u ->> v ->
 forall tr, singletonT u tr -> singletonT v tr.
Proof.
move => u v huv tr0 [a [h0 h1]]. invs h1.
exact/nil_singletonT/huv.
Qed.

Lemma singletonT_nil: forall u a, singletonT u (Tnil a) -> u a.
Proof. by move => u st [a [h0 h1]]; invs h1. Qed.

Definition SingletonT (u: propA) : propT :=
exist _ (singletonT u) (@singletonT_setoidT u).

Local Notation "[| p |]" := (SingletonT p) (at level 80).

Lemma SingletonT_cont: forall u v, u ->> v -> [|u|] =>> [|v|].
Proof.
move => u v h0 tr0 [a [h1 h2]].
invs h2.
exact/nil_singletonT/h0.
Qed.

(** ** Duplicate element property *)

Definition dupT (u : propA) (b : B) : trace -> Prop :=
fun tr => exists a, u a /\ bisim tr (Tcons a b (Tnil a)).

Lemma dupT_singl :
  forall (u : propA) a b,
    u a -> dupT u b (Tcons a b (Tnil a)).
Proof.
move => u a b h.
exists a; split.
- exact: h.
- exact: bisim_refl.
Qed.

Lemma dupT_cont: forall (u0 u1: propA) b,
 u0 ->> u1 -> forall tr, dupT u0 b tr -> dupT u1 b tr.
Proof.
move => u0 u1 b hu tr [a [h0 h1]].
invs h1; invs H1.
exact/dupT_singl/hu.
Qed.

Lemma dupT_setoidT : forall u b, setoidT (dupT u b).
Proof.
move => u b tr0 [a [h0 h1]] tr1 h2.
invs h1; invs H1; invs h2; invs H3.
exact/dupT_singl.
Qed.

Definition DupT (u : propA) (b : B) : propT :=
exist _ (dupT u b) (@dupT_setoidT u b).

Local Notation "<< p ; b >>" := (DupT p b) (at level 80).

Lemma DupT_cont: forall u v b, u ->> v -> <<u;b>> =>> <<v;b>>.
Proof.
move => u v b h0 tr0 /=.
exact: dupT_cont.
Qed.

(** ** Follows property *)

(** The follows property holds for two traces when the first is a
prefix of the second, and [p] holds for the suffix. *)

CoInductive followsT (p : trace -> Prop) : trace -> trace -> Prop :=
| followsT_nil : forall a tr,
   hd tr = a ->
   p tr ->
   followsT p (Tnil a) tr
| followsT_delay: forall a b tr tr',
   followsT p tr tr' ->
   followsT p (Tcons a b tr) (Tcons a b tr').

Lemma followsT_hd: forall p tr0 tr1, followsT p tr0 tr1 -> hd tr0 = hd tr1.
Proof. by move => p tr0 tr1 h0; invs h0. Qed.

Definition followsT_dec : forall p tr0 tr1 (h: followsT p tr0 tr1),
 { tr & { a | tr0 = Tnil a /\ hd tr = a /\ p tr } } +
 { tr & { tr' & { a & { b | tr0 = Tcons a b tr /\ tr1 = Tcons a b tr' /\ followsT p tr tr'} } } }.
Proof.
move => p [a|a b tr0] tr1 h.
- by left; exists tr1, a; inversion h.
- case: tr1 h => [a0|a0 b0 tr1] h.
  * by left; exists (Tnil a); exists a; inversion h.
  * by right; exists tr0, tr1, a, b; inversion h.
Defined.

Lemma followsT_setoidT : forall (p : trace -> Prop) (hp: forall tr0, p tr0 -> forall tr1, bisim tr0 tr1 -> p tr1),
 forall tr0 tr1, followsT p tr0 tr1 ->
 forall tr2, bisim tr0 tr2 -> forall tr3, bisim tr1 tr3 ->
 followsT p tr2 tr3.
Proof.
move => p hp.
cofix CIH.
move => tr0 tr1 h0 tr2 h1 tr3 h2. invs h0.
- invs h1. have h0 := bisim_hd h2. symmetry in h0.
  exact: followsT_nil h0 (hp _ H0 _ h2).
- invs h2; invs h1.
  exact: (followsT_delay a b (CIH _ _ H _ H5 _ H4)).
Qed.

Lemma followsT_setoidT_L : forall p,
 forall tr0 tr1, followsT p tr0 tr1 ->
 forall tr2, bisim tr0 tr2 ->  followsT p tr2 tr1.
Proof.
move => p. cofix CIH. move =>  tr tr0 h0 tr1 h1. invs h0; invs h1.
- exact: followsT_nil.
- exact: (followsT_delay a b (CIH _ _ H _ H4)).
Qed.

Lemma followsT_setoidT_R : forall (p: trace -> Prop)
 (hp: forall tr0, p tr0 -> forall tr1, bisim tr0 tr1 -> p tr1),
 forall tr tr0, followsT p tr tr0 ->
 forall tr1, bisim tr0 tr1 -> followsT p tr tr1.
Proof.
move => p hp. cofix CIH.
move => tr tr0 h0 tr1 h1. invs h0.
- apply: followsT_nil; first by symmetry; apply: (bisim_hd h1).
  exact: hp _ H0 _ h1.
- invs h1. exact: (followsT_delay a b (CIH _ _  H _ H4)).
Qed.

Lemma followsT_cont : forall (p q : trace -> Prop),
(forall tr, p tr -> q tr) ->
forall tr0 tr1, followsT p tr0 tr1 -> followsT q tr0 tr1.
Proof.
move => p q hpq. cofix CIH. move => tr0 tr1 h0. invs h0.
- apply: followsT_nil => //.
  exact: hpq _ H0.
- exact/followsT_delay/CIH.
Qed.

Lemma followsT_singletonT: forall u tr0 tr1,
 followsT (singletonT u) tr0 tr1 -> bisim tr0 tr1.
Proof.
move => u. cofix CIH. move => tr0 tr1 h0. invs h0.
- move: H0 => [a [h0 h1]]. invs h1 => /=.
  exact: bisim_refl.
- exact/bisim_cons/CIH.
Qed.

Lemma followsT_singleton_andA_L: forall u0 u1 tr0,
 followsT (singletonT (u0 andA u1)) tr0 tr0 ->
 followsT (singletonT u0) tr0 tr0.
Proof.
move => u0 u1. cofix CIH. case.
- move => a h0. inversion h0. clear H1 H.
  move: H0 => /= H0; invs h0.
  move: H3 => [a' [h1 h2]]. invs h2. move: h1 => [h1 h2].
  apply: followsT_nil => //.
  exact: nil_singletonT.
- move => a b tr0 h0; invs h0.
  exact/followsT_delay/CIH.
Qed.

Lemma followsT_singleton_andA_R: forall u0 u1 tr0,
 followsT (singletonT (u0 andA u1)) tr0 tr0 ->
 followsT (singletonT u1) tr0 tr0.
Proof.
move => u0 u1. cofix CIH. case.
- move => a h0. inversion h0. clear H1 H.
  move: H0 => /= H0; invs h0.
  move: H3 => [a' [h1 h2]]. invs h2. move: h1 => [h1 h2].
  apply: followsT_nil => //.
  exact: nil_singletonT.
- move => a b tr0 h0; invs h0.
  exact/followsT_delay/CIH.
Qed.

Lemma singletonT_andA_followsT: forall u v tr,
 followsT (singletonT u) tr tr -> followsT (singletonT v) tr tr ->
 followsT (singletonT (u andA v)) tr tr.
Proof.
move => u v. cofix CIH. move => tr h0 h1; invs h0; invs h1.
- apply: followsT_nil => //.
  apply: nil_singletonT.
  by split; apply: singletonT_nil.
- exact/followsT_delay/CIH.
Qed.

Lemma followsT_ttA : forall tr, followsT (singletonT ttA) tr tr.
Proof.
cofix CIH. case => [a|a b tr0].
- apply: followsT_nil => //.
  exact: nil_singletonT.
- exact/followsT_delay/CIH.
Qed.

(** ** Append property *)

(** The append property holds for a trace whenever it has
a prefix for which [p1] holds, and [p2] holds for the suffix. *)

Definition appendT (p1 p2: trace -> Prop) : trace -> Prop :=
fun tr => exists tr', p1 tr' /\ followsT p2 tr' tr.

Local Infix "*+*" := appendT (at level 60, right associativity).

Lemma appendT_cont : forall (p0 p1 q0 q1 : trace -> Prop),
 (forall tr, p0 tr -> p1 tr) ->
 (forall tr, q0 tr -> q1 tr) ->
 forall tr, appendT p0 q0 tr -> appendT p1 q1 tr.
Proof.
move => p0 p1 q0 q1 hp hq tr [tr0 [h0 h1]].
exists tr0; split; first by apply: hp.
move: {h0} tr0 tr h1. cofix CIH.
move => tr0 tr1 h0; invs h0.
- apply: followsT_nil => //. exact: hq _ H0.
- exact/followsT_delay/CIH.
Qed.

Lemma appendT_cont_L : forall (p0 p1 q: trace -> Prop),
 (forall tr, p0 tr -> p1 tr) ->
 forall tr, (appendT p0 q tr) -> (appendT p1 q tr).
Proof.
move => p0 p1 q hp tr.
exact: (@appendT_cont _ _ q q hp _).
Qed.

Lemma appendT_cont_R: forall (p q0 q1: trace -> Prop),
(forall tr, q0 tr -> q1 tr) ->
forall tr, (appendT p q0 tr) -> (appendT p q1 tr).
Proof.
move => p q0 q1 hq tr.
exact: (@appendT_cont p p _ _ _ hq).
Qed.

Lemma appendT_setoidT: forall (p0 p1: trace -> Prop),
 setoidT p1 -> setoidT (appendT p0 p1).
Proof.
move => p0 p1 hp1 tr0 h0 tr1 h1.
move: h0 => [tr2 [h0 h2]]. exists tr2; split; first by apply: h0.
exact: (followsT_setoidT_R hp1 h2 h1).
Qed.

Lemma followsT_followsT: forall p q tr0 tr1 tr2, followsT p tr0 tr1 ->
 followsT q tr1 tr2 -> followsT (p *+* q) tr0 tr2.
Proof.
move => p q. cofix CIH. case.
- move => a tr1 tr2 h0 h1. invs h0. have := followsT_hd h1 => h2.
  apply: followsT_nil => //. by exists tr1.
- move => a b tr0 tr1 tr2 h0 h1; invs h0; invs h1.
  exact: followsT_delay _ _ (CIH _ _ _ H3 H4).
Qed.

Lemma appendT_assoc_L : forall p1 p2 p3 tr,
 (appendT (appendT p1 p2) p3) tr -> appendT p1 (appendT p2 p3) tr.
Proof.
move => p1 p2 p3 tr0 h1. move: h1 => [tr1 [h1 h2]]. move: h1 => [tr2 h1].
move: h1 => [h1 h3]. exists tr2; split => //. clear h1.
move: tr2 tr0 tr1 h2 h3. cofix CIH.
move => tr0 tr1 tr2 h1 h2; invs h2.
- apply: followsT_nil; last by exists tr2.
  symmetry. exact: followsT_hd h1.
- invs h1. exact: followsT_delay _ _ (CIH _ _ _ H4 H).
Qed.

Lemma appendT_finalTA: forall (p q : trace -> Prop) tr0 tr1,
 p tr0 -> q tr1 -> finalTA tr0 (hd tr1) ->
 (p *+* q) (tr0 +++ tr1).
Proof.
move => p q tr0 tr1 hp hq hfin. exists tr0. split => //.
move: {hp} tr0 tr1 hq hfin. cofix CIH. case.
- move => a tr0 hq h1. rewrite trace_append_nil. invs h1.
  exact: followsT_nil.
- move => a b tr0 tr1 h0 h1.
  invs h1. rewrite [Tcons a b tr0 +++ tr1]trace_destr /=.
  exact/followsT_delay/CIH.
Qed.

Definition AppendT (p1 p2: propT) : propT :=
let: exist f0 h0 := p1 in
let: exist f1 h1 := p2 in
exist _ (appendT f0 f1) (appendT_setoidT h1).

Local Infix "***" := AppendT (at level 60, right associativity).

Lemma AppendT_assoc_L: forall p1 p2 p3, ((p1 *** p2) *** p3) =>> (p1 *** p2 *** p3).
Proof.
move => [f1 hf1] [f2 hf2] [f3 hf3] tr0 /= h1.
exact: appendT_assoc_L.
Qed.

Lemma AppendT_cont : forall p1 p2 q1 q2, p1 =>> p2 -> q1 =>> q2 -> (p1 *** q1) =>> (p2 *** q2).
Proof.
move => [p1 hp1] [p2 hp2] [q1 hq1] [q2 hq2] h0 h1 tr0 /= h2.
apply: (appendT_cont _ _ h2).
- exact: h0.
- exact: h1.
Qed.

Lemma AppendT_cont_L: forall p1 p2 q, p1 =>> p2 -> (p1 *** q) =>> (p2 *** q).
Proof.
move => [p1 hp1] [p2 hp2] [q hq] h0 tr0 /=.
exact: appendT_cont_L.
Qed.

Lemma AppendT_cont_R : forall q p1 p2, p1 =>> p2 -> (q *** p1) =>> (q *** p2).
Proof.
move => [q hq] [p1 hp1] [p2 hp2] h0 tr0 /= h1.
exact: (@appendT_cont q q p1 p2).
Qed.

Lemma AppendT_ttA: forall p, p =>> (p *** [|ttA|]).
Proof.
move => [f hp] tr0 /= h0.
exists tr0; split => //.
move: {h0 hp} tr0. cofix CIH.
case => [a|a b tr0].
- exact/followsT_nil/nil_singletonT.
- exact/followsT_delay/CIH.
Qed.

Lemma SingletonT_DupT_AppendT_andA_DupT : forall u v b, ([|u|] *** <<v;b>>) =>> <<u andA v;b>>.
Proof.
move => u v b tr0 [tr1 [[a [h0 h2]] h1]] /=.
invs h2; invs h1; move: H1 => [a [h1 h2]]; invs h2; invs H1.
exact: dupT_singl.
Qed.

Lemma DupT_andA_AppendT_SingletonT_DupT : forall u v b, <<u andA v;b>> =>> ([|u|] *** <<v;b>>).
Proof.
move => u v b tr0 [a [[hu hv] h1]].
invs h1; invs H1. exists (Tnil a); split; first by apply: nil_singletonT.
apply: followsT_nil => //.
exact: dupT_singl.
Qed.

Lemma DupT_andA_AppendT_SingletonT : forall u v b, <<u andA v;b>> =>> <<u;b>> *** [|v|].
Proof.
move => u v b tr0 [a [[hu hv] h0]].
invs h0; invs H1. exists (Tcons a b (Tnil a)); split.
- exact: dupT_singl.
- apply: followsT_delay. apply: followsT_nil => //.
  exact: nil_singletonT.
Qed.

Lemma DupT_AppendT_SingletonT_andA_DupT : forall u v b, (<<u;b>> *** [|v|]) =>> <<u andA v;b>>.
Proof.
move => u v b tr0 [tr1 [[a [hu h0]] h1]].
invs h0; invs H1; invs h1; invs H3; move: H1 => [a [hv h0]]; invs h0 => /=.
exact: dupT_singl.
Qed.

Lemma AppendT_andA : forall u v, ([|u|] *** [|v|]) =>> [|u andA v|].
Proof.
move => u v tr0 [tr1 [[a [hu h0]] h1]].
invs h0; invs h1; move: H1 => [a [hv h0]]; invs h0 => /=.
exact: nil_singletonT.
Qed.

Lemma andA_AppendT: forall u v, [|u andA v|] =>> [|u|] *** [|v|].
Proof.
move => u v tr0 [a [[hu hv] h0]].
invs h0. exists (Tnil a). split; first by apply: nil_singletonT.
apply: followsT_nil => //.
exact: nil_singletonT.
Qed.

Lemma SingletonT_AppendT: forall v p, ([|v|] *** p) =>> p.
Proof.
move => v [p hp] tr0 /= [tr1 [[a [h0 h2]] h1]].
by invs h1; invs h2.
Qed.

Lemma implies_ttA_AppendT: forall p, p =>> [|ttA|] *** p.
Proof.
move => [p hp] tr0 /= htr0.
exists (Tnil (hd tr0)); split.
- exact: nil_singletonT.
- exact: followsT_nil.
Qed.

Lemma appendT_singletonT: forall p (hp: setoidT p) u tr,
 appendT p (singletonT u) tr -> p tr.
Proof.
move => p hp u tr0 [tr1 [h1 h2]].
exact: (hp _ h1 _ (followsT_singletonT h2)).
Qed.

Lemma AppendT_Singleton: forall p v, (p *** [|v|]) =>> p.
Proof.
move => [p hp] v tr0 /=.
exact: appendT_singletonT.
Qed.

Lemma AppendT_ttA_implies : forall p, (p *** [|ttA|]) =>> p.
Proof.
move => p.
exact: AppendT_Singleton.
Qed.

Lemma implies_AppendT_ttA: forall p, p =>> p *** [|ttA|].
Proof.
move => [p hp] tr0 /= htr0.
exists tr0; split => //.
move: {hp htr0} tr0. cofix CIH.
case => [a|a b tr0].
- apply: followsT_nil => //.
  exact: nil_singletonT.
- exact/followsT_delay/CIH.
Qed.

Lemma TtT_AppendT_idem: (TtT *** TtT) =>> TtT.
Proof. by []. Qed.

Lemma AppendT_FiniteT_idem : (FiniteT *** FiniteT) =>> FiniteT.
Proof.
move => tr0 [tr1 [Hfin Hfol]].
elim: Hfin tr0 Hfol => [a tr0'|a b tr1' h0 IH tr0] Hfol; invs Hfol => //.
exact/finiteT_delay/IH.
Qed.

Lemma FiniteT_AppendT_idem : FiniteT =>> FiniteT *** FiniteT.
Proof.
move => tr0 h0.
exists (Tnil (hd tr0)); split.
- exact: finiteT_nil.
- exact: followsT_nil.
Qed.

Lemma FiniteT_SingletonT: forall u, (FiniteT *** [|u|]) =>> FiniteT.
Proof.
move => u tr /= [tr1 [h0 h1]].
exact: (finiteT_setoidT h0 (followsT_singletonT h1)).
Qed.

Lemma InfiniteT_implies_AppendT : InfiniteT =>> (TtT *** [|ffA|]).
Proof.
move => tr0 [a b tr1] HinfT /=.
exists (Tcons a b tr1); split => {tr0} //.
move: a b tr1 HinfT. cofix CIH.
move => a b tr1 HinfT; invs HinfT.
exact/followsT_delay/CIH.
Qed.

Lemma AppendT_implies_InfiniteT: (TtT *** [|ffA|]) =>> InfiniteT.
Proof.
move => tr0 [tr1 [_ h1]] /=.
move: tr0 tr1 h1; cofix CIH => tr0 tr1 h1; invs h1.
- by move: H0 => [a [h1 h2]]; inversion h1.
- exact: infiniteT_delay _ _ (CIH _ _ H).
Qed.

(** ** Iteration property *)

CoInductive iterT (p : trace -> Prop) : trace -> Prop :=
| iterT_stop : forall a,
   iterT p (Tnil a)
| iterT_loop : forall tr tr0,
   p tr ->
   followsT (iterT p) tr tr0 ->
   iterT p tr0.

Lemma iterT_setoidT : forall p (hp: setoidT p), setoidT (iterT p).
Proof.
move => p hp. cofix CIH.
have h0 : forall tr, setoidT (followsT (iterT p) tr).
 cofix CIH1. move => tr tr0 h0 tr1 h1.
 invs h0; last by invs h1; apply: (followsT_delay _ _ (CIH1 _ _ H _ H4)).
 apply: followsT_nil; first by symmetry; apply: bisim_hd h1.
 exact: CIH _ H0 _ h1.
move => tr0 h1 tr1 h2; invs h1.
- invs h2. exact: iterT_stop.
- exact: iterT_loop H (h0 _ _ H0 _ h2).
Qed.

Lemma iterT_cont: forall (p0 p1 : trace -> Prop),
 (forall tr, p0 tr -> p1 tr) ->
 forall tr, iterT p0 tr -> iterT p1 tr.
Proof.
move => p0 p1 hp. cofix CIH.
have h : forall tr0 tr1, followsT (iterT p0) tr0 tr1 -> followsT (iterT p1) tr0 tr1.
 cofix CIH0. move => tr0 tr1 h0.
 invs h0; last by apply: (followsT_delay _ _ (CIH0 _ _ H)).
 exact/followsT_nil/CIH.
move => tr0 h0; invs h0; first by apply: iterT_stop.
exact: iterT_loop (hp _ H)  (h _ _ H0).
Qed.

Lemma iterT_appendT_dupT: forall (u : propA) p b tr,
 u (hd tr) -> iterT (appendT p (dupT u b)) tr ->
 followsT (singletonT u) tr tr.
Proof.
move => u p b. cofix CIH. move => tr h0 h1; invs h1.
- apply: followsT_nil => //.
  exact: nil_singletonT.
- move: H h0 => [tr1 [_ h1]] _.
  move: tr tr1 tr0 h1 H0. cofix CIH1.
  move => tr0 tr1 tr2 h0 h1; invs h0.
  + move: H0 => [a [h0 h3]].
    invs h3; invs H1; invs h1; invs H3.
    exact/followsT_delay/CIH.
  + invs h1. exact: followsT_delay _ _ (CIH1 _ _ _ H H4).
Qed.

Definition IterT (p : propT) : propT :=
let: exist f0 h0 := p in
exist _ (iterT f0) (iterT_setoidT h0).

Lemma IterT_cont : forall p q, p =>> q -> (IterT p) =>> (IterT q).
Proof.
move => [p hp] [q hq] h0 tr0 /=.
exact: (iterT_cont (fun tr => h0 tr)).
Qed.

Lemma iterT_split_1: forall p tr, iterT p tr -> (singletonT ttA tr) \/ (appendT p (iterT p) tr).
Proof.
move => p tr h0. invs h0.
- by left; apply: nil_singletonT.
- by right; exists tr0.
Qed.

Lemma IterT_unfold_0: forall p, IterT p =>> ([|ttA|] orT (p *** IterT p)).
Proof.
move => [p hp] tr0 /= h0.
exact: iterT_split_1 h0.
Qed.

Lemma iterT_split_2: forall tr p,
 (singletonT ttA tr) \/ (appendT p (iterT p) tr) -> iterT p tr.
Proof.
move => tr p [[a [h0 h1]]|[tr0 [h0 h1]]].
- invs h1. exact: iterT_stop.
- exact: iterT_loop h0 h1.
Qed.

Lemma IterT_fold_0 : forall p, ([|ttA|] orT (p *** IterT p)) =>> IterT p.
Proof.
move => [p hp] tr0 /=.
exact: iterT_split_2.
Qed.

Lemma iterT_unfold_1 : forall p tr, (iterT p *+* p) tr -> iterT p tr.
Proof.
move => p tr [tr0 [h0 h1]].
move: tr0 tr h0 h1. cofix CIH.
move => tr0 tr1 h0 h1; invs h0.
- invs h1. apply: (iterT_loop H1). move: {H1} tr1. cofix CIH0.
  case => [a|a b tr0]; first by apply: followsT_nil => //; apply: iterT_stop.
  exact/followsT_delay/CIH0.
- apply: (iterT_loop H). move: {H} tr tr0 tr1 H0 h1. cofix CIH0.
  move => tr0 tr1 tr2 h0 h1; invs h0.
  + rewrite (followsT_hd h1).
    exact: followsT_nil _ (CIH _ _ H0 h1).
  + invs h1.
    exact: followsT_delay _ _ (CIH0 _ _ _ H H4).
Qed.

Lemma IterT_unfold_1 : forall p, (IterT p *** p) =>> IterT p.
Proof.
move => [p hp] tr /= h0.
exact: iterT_unfold_1 h0.
Qed.

Lemma IterT_unfold_2: forall p, ([|ttA|] orT (IterT p *** p)) =>> IterT p.
Proof.
move => [p hp] tr0 /= [[a [_ h0]]|H].
- invs h0. exact: iterT_stop.
- exact: iterT_unfold_1 H.
Qed.

Lemma stop_IterT : forall p, [|ttA|] =>> IterT p.
Proof.
move => [p hp] /= t0 [x [_ h0]]. invs h0 => /=.
exact: iterT_stop.
Qed.

Lemma IterT_fold_L : forall p, (p *** IterT p) =>> IterT p.
Proof.
move => [p hp] tr0 /= [tr1 [h0 h1]].
exact: (iterT_loop h0).
Qed.

Lemma iterT_iterT_2 : forall p tr, iterT p tr -> appendT (iterT p) (iterT p) tr.
Proof.
move => p tr0 h0. exists tr0. split => //.
move: {h0} tr0. cofix CIH.
case => [a|a b tr0].
- apply: followsT_nil => //. exact: iterT_stop.
- exact/followsT_delay/CIH.
Qed.

Lemma IterT_IterT_2 : forall p, IterT p =>> (IterT p *** IterT p).
Proof.
move => [p hp] tr0 /=.
exact: iterT_iterT_2.
Qed.

Lemma iterT_iterT : forall p tr, appendT (iterT p) (iterT p) tr -> (iterT p) tr.
Proof.
move => p tr0 [tr1 [h0 h1]].
move: tr1 tr0 h0 h1. cofix CIH. move => tr0 tr1 h0; invs h0 => h0.
- by invs h0.
- apply: (iterT_loop H).
  move: {H} tr tr0 tr1 H0 h0. cofix CIH2. move => tr0 tr1 tr2 h0; invs h0 => h0.
  + rewrite (followsT_hd h0).
    exact: followsT_nil _ (CIH _ _ H0 h0).
  - invs h0.
    exact: followsT_delay _ _ (CIH2 _ _ _ H H4).
Qed.

Lemma IterT_IterT : forall p, (IterT p *** IterT p) =>> IterT p.
Proof. move => [p hp] tr /=. exact: iterT_iterT. Qed.

Lemma IterT_DupT : forall v b,
 ([|v|] *** (IterT (TtT *** <<v;b>>))) =>> (TtT *** [|v|]).
Proof.
move => v b tr0 [tr1 [[a [h0 h2]] h1]].
invs h2; invs h1 => /=.
exists tr0. split => //.
move: tr0 h0 H1. cofix CIH. move => tr0 h0 h1; invs h1.
- apply: followsT_nil => //=. exact: nil_singletonT.
- move: H h0 => [tr1 [_ h1]] _.
  move: tr1 tr tr0 h1 H0. cofix CIH0. move => tr0 tr1 tr2 h0 h1; invs h0.
  + move: H0 => [a [h0 h2]].
    invs h2; invs H1; invs h1; invs H3.
    exact/followsT_delay/CIH.
  + invs h1. exact: followsT_delay _ _ (CIH0 _ _ _ H H4).
Qed.

(** ** Last property *)

Definition lastA (p : trace -> Prop) : propA :=
fun a => exists tr, p tr /\ finalTA tr a.

Lemma lastA_cont: forall (p q : trace -> Prop),
 (forall tr, p tr -> q tr) ->
 lastA p ->> lastA q.
Proof.
move => p0 p1 hp. move => a [tr [h0 h1]].
exists tr; split; first by apply: hp _ h0.
exact: h1.
Qed.

Definition LastA (p : propT) : propA :=
let: exist f0 h0 := p in lastA f0.

Lemma LastA_cont : forall p q, p =>> q -> LastA p ->> LastA q.
Proof.
move => [f hf] [g hg] /= h0.
exact/lastA_cont/h0.
Qed.

Lemma LastA_SingletonT_fold : forall u, LastA ([|u|]) ->> u.
Proof.
move => u a [tr0 [[st1 [h1 h3]] h2]].
by invs h3; invs h2.
Qed.

Lemma LastA_SingletonT_unfold : forall u, u ->> LastA ([|u|]).
Proof.
move => u a h0. exists (Tnil a). split.
- exact: nil_singletonT.
- exact: finalTA_nil.
Qed.

Lemma lastA_appendA : forall p q a, lastA (appendT p q) a -> lastA q a.
Proof.
move => p q a [tr0 [[tr [_ h2]] h1]].
move: h1 tr h2; elim => {tr0 a} [a | a b a' tr0 Hfinal IH] tr h0; invs h0.
- exists (Tnil a). by split; last by apply: finalTA_nil.
- exists (Tcons a b tr0). by split; last by apply: finalTA_delay.
- exact: IH _ H1.
Qed.

Lemma LastA_AppendA : forall p v, LastA (p *** [|v|]) ->> v.
Proof.
move => [p hp] v /= a [tr [[tr' [_ h0]] h1]].
move: h1 tr' h0; elim => {tr a} [a | a b a' tr Hfinal IH] tr0 h0; invs h0.
- move: H0 => [a0 [h0 h1]]. by invs h1.
- move: H0 => [a0 [_ h0]]. by invs h0.
- exact: IH _ H1.
Qed.

Lemma LastA_andA : forall p u, ((LastA p) andA u) ->> LastA (p *** [|u|]).
Proof.
move => [p hp] u a [[tr0 [h2 h3]] h1].
exists tr0. split => //. exists tr0. split => //.
move: {h2} tr0 a h3 h1. cofix CIH. move => tr0 a h0; invs h0 => h0.
- exact/followsT_nil/nil_singletonT.
- exact: followsT_delay _ _ (CIH _ _ H h0).
Qed.

Lemma LastA_IterA : forall v b p,
 LastA ([|v|] *** (IterT (p *** <<v;b>>))) ->> v.
Proof.
move => v b p a h0.
have h1: p =>> TtT by [].
have h2 := LastA_cont (AppendT_cont_R (IterT_cont (AppendT_cont_L h1))) h0.
have := LastA_cont (@IterT_DupT v b) h2.
exact: LastA_AppendA.
Qed.

Lemma IterT_LastA_DupT : forall v b,
 (<<v;b>> *** (IterT (TtT *** <<v;b>>))) =>> (TtT *** [|v|]).
Proof.
move => v b tr0 [tr1 [[a [h0 h2]] h1]].
invs h2; invs H1; invs h1; invs H3 => /=.
exists (Tcons (hd tr') b tr'). split => //.
apply: followsT_delay => //.
move: tr' h0 H1. cofix CIH. move => tr0 h0 h1; invs h1.
- exact/followsT_nil/nil_singletonT.
- move: {h0} H => [tr1 [_ h1]].
  move: tr1 tr tr0 h1 H0. cofix CIH0. move => tr0 tr1 tr2 h0 h1; invs h0.
  + move: H0 => [a [h0 h2]].
    invs h2; invs H1; invs h1; invs H3.
    exact/followsT_delay/CIH.
  + invs h1. exact: followsT_delay _ _ (CIH0 _ _ _ H H4).
Qed.

Lemma LastA_LastA : forall p q,
 (LastA ([|LastA p|] *** q)) ->> (LastA (p *** q)).
Proof.
move => [p hp] [q hq] a /= [tr1 [[tr0 [[tr2 [h0 h3]] h2]] h1]].
invs h3; invs h2. move: h0 => [tr2 [h0 h2]].
exists (tr2 +++ tr1). split.
- exists tr2. split => //.
  move: {h0 h1} tr2 h2. cofix CIH.
  case => [a0|a0 b tr0] h0.
  + rewrite trace_append_nil. apply: followsT_nil => //. by invs h0.
  + invs h0. rewrite trace_append_cons.
    exact/followsT_delay/CIH.
- move => {H1 h0}; move h0: (hd tr1) h2 => a0 h2.
  move: h2 tr1 h0 h1; elim => {tr2 a0} [a0 | a0 b a1 tr2 Hfinal IH] tr0 h0 h1.
  + by rewrite trace_append_nil.
  + rewrite trace_append_cons.
    apply: finalTA_delay.
    exact: IH _ h0 h1.
Qed.

Lemma SingletonT_andA_AppendT : forall u v,
 (v andA u) ->> LastA ([|v|] *** [|u|]).
Proof.
move => u v a [h0 h1].
exists (Tnil a). split; last by apply: finalTA_nil.
exists (Tnil a). split; first by apply: nil_singletonT.
exact/followsT_nil/nil_singletonT.
Qed.

CoFixpoint lastdup (tr : trace) (b : B) : trace :=
match tr with
| Tnil a => Tcons a b (Tnil a)
| Tcons a b' tr' => Tcons a b' (lastdup tr' b)
end.

Lemma lastdup_hd: forall tr b, hd tr = hd (lastdup tr b).
Proof.
by case => [a b|a b tr b0]; rewrite [lastdup _ _]trace_destr.
Qed.

Lemma followsT_dupT : forall u tr b,
 followsT (singletonT u) tr tr ->
 followsT (dupT u b) tr (lastdup tr b).
Proof.
cofix CIH. move => u tr0 b h0; invs h0.
- rewrite [lastdup _ _]trace_destr /=.
  move: H0 => [a0 [h0 h1]]. invs h1.
  apply: followsT_nil => //.
  exact: dupT_singl.
- rewrite [lastdup _ _]trace_destr /=.
  exact/followsT_delay/CIH.
Qed.

Lemma finalTA_lastdup : forall tr a b,
 finalTA tr a -> finalTA (lastdup tr b) a.
Proof.
move => tr a b1; elim => {tr a} [a | a1 b2 a2 tr Hfinal IH].
- rewrite [lastdup _ _]trace_destr /=.
  apply: finalTA_delay. exact: finalTA_nil.
- rewrite [lastdup _ _]trace_destr /=.
  exact: finalTA_delay.
Qed.

Lemma LastA_DupT : forall p u b,
 LastA (p *** [|u|]) ->> LastA (p *** <<u;b>>).
Proof.
move => [p hp] u b a [tr0 [[tr1 [h0 h2]] h1]].
exists (lastdup tr0 b); split; last by apply: finalTA_lastdup.
have h3 := followsT_singletonT h2.
exists tr0; split.
- exact: hp _ h0 _ h3.
- have h4 := followsT_setoidT (@singletonT_setoidT _) h2 h3 (bisim_refl _) => {h2}.
  exact: followsT_dupT b h4.
Qed.

(** ** Midpoint property *)

(** This property identifies a trace that is both a suffix of [tr0] and a prefix of [tr1],
and is the stepping stone to showing the right associativity of the append property. *)

CoInductive midpointT (p0 p1: trace -> Prop) (tr0 tr1: trace) (h: followsT (appendT p0 p1) tr0 tr1) : trace -> Prop :=
| midpointT_nil : forall tr,
   tr0 = Tnil (hd tr1) ->
   p0 tr ->
   followsT p1 tr tr1 ->
   midpointT h tr
| midpointT_delay : forall tr2 tr3 (h1: followsT (appendT p0 p1) tr2 tr3) (a : A) (b: B) tr',
   tr0 = Tcons a b tr2 ->
   tr1 = Tcons a b tr3 ->
   @midpointT p0 p1 tr2 tr3 h1 tr' ->
   midpointT h (Tcons a b tr').

Lemma midpointT_before: forall p0 p1 tr0 tr1 (h: followsT (appendT p0 p1) tr0 tr1) tr',
 midpointT h tr' -> followsT p0 tr0 tr'.
Proof.
cofix CIH. dependent inversion h; subst.
- move => tr' hm.
  invs hm; invs H; invs a0; invs H; invs h.  
  apply: followsT_nil => //.
  by inversion H1.
- subst; move => [a0|a0 b0 tr0] hm; first by inversion hm.
  invs hm; try invs H; invs H2; invs H3.
  exact: followsT_delay _ _ (CIH _ _ _ _ h1 _ _).
Qed.

Lemma midpointT_after: forall p0 p1 tr0 tr1 (h: followsT (appendT p0 p1) tr0 tr1) tr',
 midpointT h tr' -> followsT p1 tr' tr1.
Proof.
cofix CIH. dependent inversion h; subst => tr0 hm.
- by invs hm; invs h.
- invs hm; invs H; invs H0.
  exact: followsT_delay _ _ (CIH _ _ _ _ h1 _ _).
Qed.

End TraceProperties.

(** ** Trace property operators and notations *)

Infix "andT" := AndT (at level 60, right associativity).
Infix "orT" := OrT (at level 60, right associativity).
Infix "=>>" := propT_imp (at level 60, right associativity).
Infix "->>" := propA_imp (at level 60, right associativity).
Infix "andA" := andA (at level 60, right associativity).
Notation "[| p |]" := (@SingletonT _ _ p) (at level 80).
Infix "*+*" := appendT (at level 60, right associativity).
Infix "***" := AppendT (at level 60, right associativity).
Notation "<< p ; b >>" := (@DupT _ _ p b) (at level 80).
