From stdpp Require Import prelude finite.

Definition support `(f : A -> B) `{Inhabited B} : Type :=
  {a : A | f a <> inhabitant}.

#[export] Instance EqDecision_support `(f : A -> B) `{Inhabited B} `{EqDecision A} :
  EqDecision (support f).
Proof.
  intros [a1 p1] [a2 p2]; red.
  destruct (decide (a1 = a2)) as [-> |].
  - left; f_equal.
    admit.
  - by right; intros [=].
Admitted.

Definition FinitelySupported `(f : A -> B) `{EqDecision A} `{Inhabited B} : Type :=
  Finite (support f).

Section sec_fin_dom_fn_prop.

Context
  `{EqDecision A}
  `{Inhabited B}
  .