From Equations Require Export Equations.

(** * Equations utility definitions

  The definition of [inspect] is available in Equations as of version 1.3+8.16.
  Notation <<eq:>> is not yet available (exists only in examples).

  [inspect x] allows to pattern-match [x] while retaining a propositional
  equality with [x].

  See #<a href="https://github.com/mattam82/Coq-Equations/blob/v1.3-8.16/theories/Prop/Logic.v#L31">here</a>#.
*)
Definition inspect {A} (a : A) : {b | a = b} :=
  exist _ a eq_refl.

(**
  The [inspect] definition is used to pack a value with a proof
  of an equality to itself. When pattern matching on the first component in
  this existential type, we keep information about the origin of the pattern
  available in the second component, the equality.

  See #<a href="https://github.com/mattam82/Coq-Equations/blob/v1.3-8.16/examples/Basics.v#L527">here</a>#.
*)
Global Notation "x 'eq:' p" := (exist _ x p) (only parsing, at level 20).
