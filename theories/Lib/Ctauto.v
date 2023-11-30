From Cdcl Require Export Itauto.

(** * Utility: Classical Itauto Tactic

  This module contains a version of the itauto tactic that uses classical logic
  freely. See the comments in VLSM.Lib.Itauto for more details.
*)

Ltac gen_conflicts tac :=
  intros; unfold not in *; unfold iff in *;
  cdcl_nnpp; unfold not;
  (cdcl_conflicts tac).

Tactic Notation "itauto" tactic(tac) :=
  gen_conflicts tac ;
  vitautog.

Tactic Notation "itauto" :=
  itauto auto.

Ltac itautor tac := let t := solve[tac | itauto tac] in itauto t.
