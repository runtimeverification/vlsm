From VLSM Require Import Lib.SsrExport.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** * Definition of possibly-infinite traces *)

Ltac invs h := inversion h; subst => {h}.

Section Traces.

Context {A B : Type}.

(** ** Core trace definition and decomposition *)

(** This definition is similar to that for lazy lists from Chapter 13
of the #<a href="https://github.com/coq-community/coq-art">Coq'Art book</a>#.
However, to support traces following labeled transition relations, constructors
have additional elements. *)

CoInductive trace : Type :=
| Tnil : A -> trace
| Tcons : A -> B -> trace -> trace.

Definition hd tr :=
match tr with
| Tnil a => a
| Tcons a b tr0 => a
end.

Definition trace_decompose (tr: trace): trace :=
match tr with
| Tnil a => Tnil a
| Tcons a b tr' => Tcons a b tr'
end.

Lemma trace_destr: forall tr, tr = trace_decompose tr.
Proof. by case. Qed.

(** ** Bisimulations between traces *)

CoInductive bisim : trace -> trace -> Prop :=
| bisim_nil : forall a,
   bisim (Tnil a) (Tnil a)
| bisim_cons : forall a b tr tr',
   bisim tr tr' ->
   bisim (Tcons a b tr) (Tcons a b tr').

Lemma bisim_refl : forall tr, bisim tr tr.
Proof.
cofix CIH.
case => [a|a b tr]; first exact: bisim_nil.
exact/bisim_cons/CIH.
Qed.

Lemma bisim_sym : forall tr1 tr2, bisim tr1 tr2 -> bisim tr2 tr1.
Proof.
cofix CIH.
case => [a|a b tr1] tr2 Hbs; invs Hbs; first exact: bisim_nil.
exact/bisim_cons/CIH.
Qed.

Lemma bisim_trans : forall tr1 tr2 tr3,
 bisim tr1 tr2 -> bisim tr2 tr3 -> bisim tr1 tr3.
Proof.
cofix CIH.
case => [a|a b tr1] tr2 tr0 Hbs Hbs'; invs Hbs; invs Hbs'; first exact: bisim_nil.
exact: (bisim_cons _ _ (CIH _ _ _ H3 H4)).
Qed.

Lemma bisim_hd: forall tr0 tr1, bisim tr0 tr1 -> hd tr0 = hd tr1.
Proof. by move => tr0 tr1 []. Qed.

(** ** Appending traces to one another *)

CoFixpoint trace_append (tr tr': trace): trace :=
match tr with
| Tnil a => tr'
| Tcons a b tr0 => Tcons a b (trace_append tr0 tr')
end.

#[local] Infix "+++" := trace_append (at level 60, right associativity).

Lemma trace_append_nil : forall a tr, (Tnil a) +++ tr = tr.
Proof.
move => a tr.
rewrite [Tnil a +++ tr]trace_destr.
by case tr.
Qed.

Lemma trace_append_cons : forall a b tr tr',
 (Tcons a b tr) +++ tr' = Tcons a b (tr +++ tr').
Proof.
move => a b tr tr'.
rewrite [Tcons a b tr +++ tr']trace_destr.
by case tr.
Qed.

Lemma trace_append_bism : forall tr1 tr2 tr3 tr4,
 bisim tr1 tr2 -> bisim tr3 tr4 -> bisim (tr1 +++ tr3) (tr2 +++ tr4).
Proof.
cofix CIH.
move => tr1 tr2 tr3 tr4 [a1 | a1 b1 tr1' tr2' Hbs1'] Hbs2.
- rewrite 2!trace_append_nil. exact: Hbs2.
- rewrite 2!trace_append_cons.
  exact/bisim_cons/CIH.
Qed.

End Traces.

Infix "+++" := trace_append (at level 60, right associativity).
