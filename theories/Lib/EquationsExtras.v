From Equations Require Export Equations.
Export Equations.Prop.Logic.

(** * Equations utility definitions

  The [inspect] definition is used to pack a value with a proof
  of an equality to itself. When pattern matching on the first component in
  this existential type, we keep information about the origin of the pattern
  available in the second component, the equality.

  See
  #<a href="https://github.com/mattam82/Coq-Equations/blob/v1.3-8.16/examples/Basics.v#L527">
  here
  </a>#.
*)
Notation "x 'eq:' p" := (exist _ x p) (only parsing, at level 20).
