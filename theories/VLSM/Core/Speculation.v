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
| Simulate
| Rollback
| Commit
| Speculate (plan : list (vplan_item X)).

Inductive SpeculativeState : Type :=
| Certain (s : vstate X)
| Speculative
    (start current : vstate X) (plan : list (vplan_item X)) (outputs : list (option message)).

Definition speculative_initial_state_prop (s : SpeculativeState) : Prop :=
match s with
| Certain s' => vinitial_state_prop X s'
| _          => False
end.

Definition speculative_s0 : Inhabited {s : SpeculativeState | speculative_initial_state_prop s}.
Proof.
  destruct (vs0 X) as [s Hinit].
  by constructor; split with (Certain s).
Defined.

Definition speculative_transition
  (sl : SpeculativeLabel) (ssim : SpeculativeState * option message)
  : SpeculativeState * option message :=
match sl, ssim with
| Speculate plan, (Certain s, None) =>
    (Speculative s s plan [], None)
| Simulate, (Speculative start current (PlanItem lbl msg :: plan) outputs, None) =>
    let (current', om) := vtransition X lbl (current, msg) in
      (Speculative start current' plan (outputs ++ [om]), None)
| Rollback, (Speculative start _ (_ :: _) _, None) =>
    (Certain start, None)
| Commit, (Speculative _ current [] [], None) =>
    (Certain current, None)
| Commit, (Speculative start current [] (om :: outputs), None) =>
    (Speculative start current [] outputs, om)
| _, (s, _) => (s, None)
end.

Definition speculative_valid
  (sl : SpeculativeLabel) (ssim : SpeculativeState * option message) : Prop :=
match sl, ssim with
| Speculate plan, (Certain _, None) =>
    plan <> []
| Simulate, (Speculative _ current (PlanItem lbl msg :: _) _, None) =>
    vvalid X lbl (current, msg)
| Rollback, (Speculative _ current (PlanItem lbl msg :: _) _, None) =>
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
