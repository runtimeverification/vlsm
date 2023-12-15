From Cdcl Require Export Itauto.

(** * Utility: Constructive Itauto Tactic

  This module contains a workaround that prevents the itauto tactic from using
  classical logic.

  The problem is that itauto uses classical logic by default if the current
  module requires (even if only transitively) any module that uses classical
  logic. For example, most modules about real numbers from the standard library
  cause itauto to use excluded middle basically each time it's called.

  The solution is to redefine the itauto tactic to avoid doing this.

  Every time we want to use itauto, we should import it from the current module
  instead of directly from the Cdcl library.

  TODO: This problem was fixed upstream for the Itauto version for Coq 8.18, so
  this workaround should be removed after the minimum Coq version we support is
  8.18.
*)

Ltac gen_conflicts tac :=
  intros; unfold not in *; unfold iff in *;
  (cdcl_conflicts tac).

Tactic Notation "itauto" tactic(tac) :=
  gen_conflicts tac ;
  vitautog.

Tactic Notation "itauto" :=
  itauto auto.

Ltac itautor tac := let t := solve[tac | itauto tac] in itauto t.

(* required for documentation generation *)
Definition iYC2 := True.
