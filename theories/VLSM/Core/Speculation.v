From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From VLSM.Lib Require Import Preamble.
From VLSM.Core Require Import VLSM Plans.

(** * Speculative VLSMs

  This module introduces the speculative VLSM construction. It models the
  speculative execution of transitions from the underlying VLSM which can then
  be committed or rolled back.

*)

Section sec_speculative.

Context
  {message : Type}
  (X : VLSM message).

Inductive SpeculativeLabel : Type :=
| Execute
| Rollback
| Commit
| Speculate (plan : list (vplan_item X)).

Inductive SpeculativeState : Type :=
| Actual (s : vstate X)
| Speculative
    (start current : vstate X) (plan : list (vplan_item X)) (outputs : list (option message)).

Definition speculative_initial_state_prop (s : SpeculativeState) : Prop :=
match s with
| Actual s' => vinitial_state_prop X s'
| _         => False
end.

#[export] Instance speculative_s0 :
  Inhabited {s : SpeculativeState | speculative_initial_state_prop s}.
Proof.
  constructor; split with (Actual (` (vs0 X))).
  by destruct (vs0 X).
Defined.

Definition speculative_transition
  (sl : SpeculativeLabel) (ssim : SpeculativeState * option message)
  : SpeculativeState * option message :=
match sl, ssim with
| Speculate plan, (Actual s, None) =>
    (Speculative s s plan [], None)
| Execute, (Speculative start current (Build_plan_item lbl msg :: plan) outputs, None) =>
    let (current', om) := vtransition X lbl (current, msg) in
      (Speculative start current' plan (outputs ++ [om]), None)
| Rollback, (Speculative start _ (_ :: _) _, None) =>
    (Actual start, None)
| Commit, (Speculative _ current [] [], None) =>
    (Actual current, None)
| Commit, (Speculative start current [] (om :: outputs), None) =>
    (Speculative start current [] outputs, om)
| _, (s, _) => (s, None)
end.

Definition speculative_valid
  (sl : SpeculativeLabel) (ssim : SpeculativeState * option message) : Prop :=
match sl, ssim with
| Speculate plan, (Actual _, None) =>
    plan <> []
| Execute, (Speculative _ current (Build_plan_item lbl msg :: _) _, None) =>
    vvalid X lbl (current, msg)
| Rollback, (Speculative _ current (Build_plan_item lbl msg :: _) _, None) =>
    ~ vvalid X lbl (current, msg)
| Commit, (Speculative _ _ plan _, None) =>
    plan = []
| _, _ => False
end.

Definition speculative_vlsm_type : VLSMType message :=
{|
  state := SpeculativeState;
  label := SpeculativeLabel;
|}.

Definition speculative_vlsm_machine : VLSMMachine speculative_vlsm_type :=
{|
  initial_state_prop := speculative_initial_state_prop;
  s0 := speculative_s0;
  initial_message_prop := vinitial_message_prop X;
  transition := speculative_transition;
  valid := speculative_valid;
|}.

Definition speculative_vlsm : VLSM message :=
{|
  vtype := speculative_vlsm_type;
  vmachine := speculative_vlsm_machine;
|}.

End sec_speculative.
