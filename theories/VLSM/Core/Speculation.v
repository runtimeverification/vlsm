From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From VLSM.Lib Require Import Preamble.
From VLSM.Core Require Import VLSM.

(** * Speculative VLSMs

  This module introduces the speculative VLSM construction (also called the
  transactional version of a VLSM) which can speculatively execute transitions
  from the underlying VLSM and then rollback or commit them.

*)

Section sec_speculative.

Context
  {message : Type}
  (X : VLSM message).

Inductive SpeculativeLabel : Type :=
| Simulate  : SpeculativeLabel
| Rollback  : SpeculativeLabel
| Commit    : SpeculativeLabel
| Speculate : list (vlabel X * option message) -> SpeculativeLabel.

Inductive SpeculativeState : Type :=
| Underlying  : vstate X -> SpeculativeState
| Speculative :
    vstate X -> vstate X -> list (vlabel X * option message) -> list (option message) ->
      SpeculativeState.

Definition speculative_initial_state_prop (s : SpeculativeState) : Prop :=
match s with
| Underlying s' => vinitial_state_prop X s'
| _             => False
end.

Definition speculative_s0 : Inhabited {s : SpeculativeState | speculative_initial_state_prop s}.
Proof.
  destruct (vs0 X) as [s Hinit].
  by constructor; split with (Underlying s).
Defined.

Definition speculative_initial_message_prop (m : message) : Prop := vinitial_message_prop X m.

Definition speculative_transition
  (sl : SpeculativeLabel) (ssim : SpeculativeState * option message)
  : SpeculativeState * option message :=
match sl, ssim with
| Speculate c, (Underlying s, None) =>
    (Speculative s s c [], None)
| Simulate, (Speculative s1 s2 ((lbl, msg) :: c) msgs, None) =>
    let (s, m) := vtransition X lbl (s2, msg) in
      (Speculative s1 s c (msgs ++ [m]), None)
| Rollback, (Speculative s1 s2 ((lbl, msg) :: c) msgs, None) =>
    (Underlying s1, None)
| Commit, (Speculative s1 s2 [] [], None) =>
    (Underlying s2, None)
| Commit, (Speculative s1 s2 [] (msg :: msgs), None) =>
    (Speculative s1 s2 [] msgs, msg)
| _, (s, _) => (s, None)
end.

Definition speculative_valid
  (sl : SpeculativeLabel) (ssim : SpeculativeState * option message) : Prop :=
match sl, ssim with
| Speculate c, (Underlying s, None) =>
    c <> []
| Simulate, (Speculative s1 s2 ((lbl, msg) :: c) msgs, None) =>
    vvalid X lbl (s2, msg)
| Rollback, (Speculative s1 s2 ((lbl, msg) :: c) msgs, None) =>
    ~ vvalid X lbl (s2, msg)
| Commit, (Speculative s1 s2 c msgs, None) =>
    c = []
| _, _ => False
end.

Definition SpeculativeVlsmType : VLSMType message :=
{|
  state := SpeculativeState;
  label := SpeculativeLabel;
|}.

Definition SpeculativeVlsmMachine : VLSMMachine SpeculativeVlsmType :=
{|
  initial_state_prop := speculative_initial_state_prop;
  s0 := speculative_s0;
  initial_message_prop := vinitial_message_prop X;
  transition := speculative_transition;
  valid := speculative_valid;
|}.

Definition SpeculativeVLSM : VLSM message :=
{|
  vtype := SpeculativeVlsmType;
  vmachine := SpeculativeVlsmMachine;
|}.

End sec_speculative.
