From Cdcl Require Import Itauto. Local Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From Coq Require Import FunctionalExtensionality.
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

Lemma same_VLSM_preloaded_full_projection
  : VLSM_full_projection
    (pre_loaded_with_all_messages_vlsm X1) (pre_loaded_with_all_messages_vlsm X2)
    (same_VLSM_label_rew Heq) (same_VLSM_state_rew Heq).
Proof.
  apply basic_VLSM_strong_full_projection.
  - cbv; apply same_VLSM_valid_preservation.
  - cbv; apply same_VLSM_transition_preservation.
  - cbv; apply same_VLSM_initial_state_preservation.
  - cbv; trivial.
Qed.

End same_VLSM_full_projection.

Section VLSM_projection_composition.

Context
  {message}
  [X Y Z : VLSM message]
  `(HXY : VLSM_projection X Y xy_label xy_state)
  `(HYZ : VLSM_projection Y Z yz_label yz_state)
  .

Lemma pre_VLSM_projection_composition_transition_item_project
  : pre_VLSM_projection_transition_item_project (type X) (type Z)
      (mbind yz_label ∘ xy_label) (yz_state ∘ xy_state)
      =
    mbind (pre_VLSM_projection_transition_item_project (type Y) (type Z) yz_label yz_state)
      ∘ (pre_VLSM_projection_transition_item_project (type X) (type Y) xy_label xy_state).
Proof.
  extensionality item; destruct item; cbn.
  unfold pre_VLSM_projection_transition_item_project; cbn.
  destruct (xy_label l) as [lY|]; reflexivity.
Qed.

Lemma pre_VLSM_projection_composition_finite_trace_project
  : pre_VLSM_projection_finite_trace_project (type X) (type Z)
      (mbind yz_label ∘ xy_label) (yz_state ∘ xy_state)
      =
    pre_VLSM_projection_finite_trace_project (type Y) (type Z) yz_label yz_state
      ∘ pre_VLSM_projection_finite_trace_project (type X) (type Y) xy_label xy_state.
Proof.
  unfold pre_VLSM_projection_finite_trace_project.
  setoid_rewrite pre_VLSM_projection_composition_transition_item_project.
  setoid_rewrite map_option_comp_bind.
  reflexivity.
Qed.

Lemma VLSM_projection_composition
  : VLSM_projection X Z (mbind yz_label ∘ xy_label) (yz_state ∘ xy_state).
Proof.
  constructor; [constructor|]; intros sX trX HtrX
  ; replace (pre_VLSM_projection_finite_trace_project _ _ _ _)
      with 
      ((pre_VLSM_projection_finite_trace_project (type Y) (type Z) yz_label yz_state
      ∘ pre_VLSM_projection_finite_trace_project (type X) (type Y) xy_label xy_state))
      by (symmetry; apply pre_VLSM_projection_composition_finite_trace_project).
  - unfold compose.
    erewrite final_state_project; [|eapply projection_type; eassumption|assumption].
    eapply final_state_project; [apply projection_type; assumption|].
    apply VLSM_projection_finite_valid_trace_from with (Hsimul := HXY); assumption.
  - apply VLSM_projection_finite_valid_trace with (Hsimul := HYZ),
      VLSM_projection_finite_valid_trace with (Hsimul := HXY).
    assumption.
Qed.

End VLSM_projection_composition.