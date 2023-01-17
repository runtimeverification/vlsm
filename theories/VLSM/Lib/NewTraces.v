From VLSM.Lib Require Import Preamble.

Section sec_traces.

Context {A B : Type}.

Inductive traceF (X : Type) : Type :=
| Tnil'  : A -> traceF X
| Tcons' : A -> B -> X -> traceF X.

#[global] Arguments Tnil'  {X} _.
#[global] Arguments Tcons' {X}  _ _ _.

#[projections(primitive)]
CoInductive trace : Type := Trace
{
  Out : traceF trace;
}.

Notation Tnil a := (Trace (Tnil' a)).
Notation Tcons a b t := (Trace (Tcons' a b t)).

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

(** ** Bisimulations between traces *)

CoInductive bisim : trace -> trace -> Prop :=
| bisim_nil : forall a,
   bisim (Tnil a) (Tnil a)
| bisim_cons : forall a b tr tr',
   bisim tr tr' ->
   bisim (Tcons a b tr) (Tcons a b tr').

End sec_traces.