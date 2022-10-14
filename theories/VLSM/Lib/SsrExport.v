(** * SSReflect exports *)

From Coq Require Export ssreflect.
#[export] Set SsrOldRewriteGoalsOrder.
#[export] Set Asymmetric Patterns.
#[export] Set Bullet Behavior "None".

(* required for documentation generation *)
Definition iYC2 := True.
