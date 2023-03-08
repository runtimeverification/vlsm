From Cdcl Require Export Itauto.

Ltac gen_conflicts tac :=
  intros; unfold not in *; unfold iff in *;
  (cdcl_conflicts tac).

Tactic Notation "itauto" tactic(tac) :=
  gen_conflicts tac ;
  vitautog.

Tactic Notation "itauto" :=
  itauto auto.

Ltac itautor tac := let t := solve[tac | itauto tac] in itauto t.
