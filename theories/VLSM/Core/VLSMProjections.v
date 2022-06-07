From Cdcl Require Import Itauto. Local Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From VLSM.Lib Require Import Preamble ListExtras StreamExtras StreamFilters.
From VLSM.Core Require Import VLSM.
From VLSM.Core.VLSMProjections Require Export VLSMPartialProjection VLSMTotalProjection.
From VLSM.Core.VLSMProjections Require Export VLSMEmbedding VLSMInclusion VLSMEquality.

Section same_VLSM_full_projection.

Context
  {message : Type}
  (X1 X2 : VLSM message)
  (Heq : X1 = X2)
  .

Lemma same_VLSM_full_projection
  : VLSM_full_projection X1 X2 (same_VLSM_label_rew Heq) (same_VLSM_state_rew Heq).
Proof.
  apply basic_VLSM_strong_full_projection; intro.
  - apply same_VLSM_valid_preservation.
  - apply same_VLSM_transition_preservation.
  - apply same_VLSM_initial_state_preservation.
  - by apply same_VLSM_initial_message_preservation.
Qed.

End same_VLSM_full_projection.
