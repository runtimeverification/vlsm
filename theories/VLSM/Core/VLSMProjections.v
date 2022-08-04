From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From Coq Require Import FunctionalExtensionality.
From VLSM.Core Require Import VLSM.
From VLSM.Core Require Export VLSMProjections.VLSMPartialProjection VLSMProjections.VLSMTotalProjection.
From VLSM.Core Require Export VLSMProjections.VLSMEmbedding VLSMProjections.VLSMInclusion VLSMProjections.VLSMEquality.

(** * VLSM Projection Properties *)

Section same_VLSM_full_projection.

(** ** Same VLSM full projection *)

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

Section transitivity_props.

(** ** Transitivity properties *)

Lemma pre_VLSM_projection_finite_trace_project_trans
  {message : Type}
  (TX TY TZ : VLSMType message)
  (project_labelXY : @label _ TX -> option (@label _ TY))
  (project_stateXY : @state _ TX -> @state _ TY)
  (project_labelYZ : @label _ TY -> option (@label _ TZ))
  (project_stateYZ : @state _ TY -> @state _ TZ)
  : forall trX,
    pre_VLSM_projection_finite_trace_project TX TZ
      (mbind project_labelYZ ∘ project_labelXY)
      (project_stateYZ ∘ project_stateXY)
      trX
      =
    pre_VLSM_projection_finite_trace_project TY TZ project_labelYZ project_stateYZ
      (pre_VLSM_projection_finite_trace_project TX TY project_labelXY project_stateXY
        trX).
Proof.
  induction trX; [done |]; destruct a; cbn;
    unfold pre_VLSM_projection_transition_item_project; cbn;
    unfold mbind, option_bind; cbn.
  destruct (project_labelXY l) as [lY |]; [| done]; cbn;
    unfold pre_VLSM_projection_transition_item_project; cbn.
  destruct (project_labelYZ lY) as [lZ |]; [| done]; cbn.
  by f_equal.
Qed.

Lemma VLSM_projection_trans
  {message}
  (X Y Z : VLSM message)
  (project_labelXY : vlabel X -> option (vlabel Y))
  (project_stateXY : vstate X -> vstate Y)
  (ProjXY : VLSM_projection X Y project_labelXY project_stateXY)
  (project_labelYZ : vlabel Y -> option (vlabel Z))
  (project_stateYZ : vstate Y -> vstate Z)
  (ProjYZ : VLSM_projection Y Z project_labelYZ project_stateYZ)
  : VLSM_projection X Z
    (mbind project_labelYZ ∘ project_labelXY)
    (project_stateYZ ∘ project_stateXY).
Proof.
  constructor; [split |]; intros sX trX HtrX; cbn;
    setoid_rewrite pre_VLSM_projection_finite_trace_project_trans.
  - rewrite <- !final_state_project; [done | apply ProjXY | done | apply ProjYZ |].
    by eapply (VLSM_projection_finite_valid_trace_from ProjXY).
  - by eapply (VLSM_projection_finite_valid_trace ProjYZ),
              (VLSM_projection_finite_valid_trace ProjXY).
Qed.

Lemma VLSM_projection_embedding_trans
  {message}
  (X Y Z : VLSM message)
  (project_labelXY : vlabel X -> option (vlabel Y))
  (project_stateXY : vstate X -> vstate Y)
  (ProjXY : VLSM_projection X Y project_labelXY project_stateXY)
  (project_labelYZ : vlabel Y -> vlabel Z)
  (project_stateYZ : vstate Y -> vstate Z)
  (ProjYZ : VLSM_full_projection Y Z project_labelYZ project_stateYZ)
  : VLSM_projection X Z
    (fmap project_labelYZ ∘ project_labelXY)
    (project_stateYZ ∘ project_stateXY).
Proof.
  apply VLSM_full_projection_is_projection in ProjYZ.
  replace (fmap project_labelYZ ∘ project_labelXY)
     with (mbind (Some ∘ project_labelYZ) ∘ project_labelXY).
  - by apply VLSM_projection_trans.
  - by extensionality x.
Qed.

Lemma VLSM_embedding_projection_trans
  {message}
  (X Y Z : VLSM message)
  (project_labelXY : vlabel X -> vlabel Y)
  (project_stateXY : vstate X -> vstate Y)
  (ProjXY : VLSM_full_projection X Y project_labelXY project_stateXY)
  (project_labelYZ : vlabel Y -> option (vlabel Z))
  (project_stateYZ : vstate Y -> vstate Z)
  (ProjYZ : VLSM_projection Y Z project_labelYZ project_stateYZ)
  : VLSM_projection X Z
    (project_labelYZ ∘ project_labelXY)
    (project_stateYZ ∘ project_stateXY).
Proof.
  apply VLSM_full_projection_is_projection in ProjXY.
  replace (project_labelYZ ∘ project_labelXY)
     with (mbind project_labelYZ ∘ (Some ∘ project_labelXY)).
  - by apply VLSM_projection_trans.
  - by extensionality x.
Qed.

Lemma pre_VLSM_full_projection_finite_trace_project_trans
  {message}
  (TX TY TZ : VLSMType message)
  (project_labelXY : @label _ TX -> @label _ TY)
  (project_stateXY : @state _ TX -> @state _ TY)
  (project_labelYZ : @label _ TY -> @label _ TZ)
  (project_stateYZ : @state _ TY -> @state _ TZ)
  : forall trX,
    pre_VLSM_full_projection_finite_trace_project TX TZ
      (project_labelYZ ∘ project_labelXY)
      (project_stateYZ ∘ project_stateXY)
      trX
      =
    pre_VLSM_full_projection_finite_trace_project  TY TZ project_labelYZ project_stateYZ
      (pre_VLSM_full_projection_finite_trace_project  TX TY project_labelXY project_stateXY
        trX).
Proof. by induction trX; [| destruct a; cbn; f_equal]. Qed.

Lemma VLSM_embedding_trans
  {message}
  (X Y Z : VLSM message)
  (project_labelXY : vlabel X -> vlabel Y)
  (project_stateXY : vstate X -> vstate Y)
  (ProjXY : VLSM_full_projection X Y project_labelXY project_stateXY)
  (project_labelYZ : vlabel Y -> vlabel Z)
  (project_stateYZ : vstate Y -> vstate Z)
  (ProjYZ : VLSM_full_projection Y Z project_labelYZ project_stateYZ)
  : VLSM_full_projection X Z
    (project_labelYZ ∘ project_labelXY)
    (project_stateYZ ∘ project_stateXY).
Proof.
  constructor; intros sX trX HtrX.
  setoid_rewrite pre_VLSM_full_projection_finite_trace_project_trans.
  by eapply (VLSM_full_projection_finite_valid_trace ProjYZ),
            (VLSM_full_projection_finite_valid_trace ProjXY).
Qed.

Lemma VLSM_projection_incl_trans
  {message}
  (X : VLSM message)
  {T : VLSMType message}
  {MY MZ : VLSMMachine T}
  (Y := mk_vlsm MY)
  (Z := mk_vlsm MZ)
  (project_labelXY : vlabel X -> option (vlabel Y))
  (project_stateXY : vstate X -> vstate Y)
  (ProjXY : VLSM_projection X Y project_labelXY project_stateXY)
  (ProjYZ : VLSM_incl Y Z)
  : VLSM_projection X Z project_labelXY project_stateXY.
Proof.
  replace project_labelXY with (fmap id ∘ project_labelXY)
    by (extensionality lX; cbv; destruct (project_labelXY lX); done).
  change project_stateXY with (id ∘ project_stateXY).
  by apply (VLSM_projection_embedding_trans X Y Z); [| apply VLSM_incl_is_full_projection].
Qed.

Lemma VLSM_embedding_incl_trans
  {message}
  (X : VLSM message)
  {T : VLSMType message}
  {MY MZ : VLSMMachine T}
  (Y := mk_vlsm MY)
  (Z := mk_vlsm MZ)
  (project_labelXY : vlabel X -> vlabel Y)
  (project_stateXY : vstate X -> vstate Y)
  (ProjXY : VLSM_full_projection X Y project_labelXY project_stateXY)
  (ProjYZ : VLSM_incl Y Z)
  : VLSM_full_projection X Z project_labelXY project_stateXY.
Proof.
  change project_labelXY with (id ∘ project_labelXY).
  change project_stateXY with (id ∘ project_stateXY).
  by apply (VLSM_embedding_trans X Y Z); [| apply VLSM_incl_is_full_projection].
Qed.

Lemma VLSM_incl_projection_trans
  {message}
  {T : VLSMType message}
  {MX MY : VLSMMachine T}
  (X := mk_vlsm MX)
  (Y := mk_vlsm MY)
  (Z : VLSM message)
  (ProjXY : VLSM_incl X Y)
  (project_labelYZ : vlabel Y -> option (vlabel Z))
  (project_stateYZ : vstate Y -> vstate Z)
  (ProjYZ : VLSM_projection Y Z project_labelYZ project_stateYZ)
  : VLSM_projection X Z project_labelYZ project_stateYZ.
Proof.
  apply (VLSM_embedding_projection_trans X Y Z); [| done].
  by apply VLSM_incl_is_full_projection in ProjXY.
Qed.

Lemma VLSM_incl_embedding_trans
  {message}
  {T : VLSMType message}
  {MX MY : VLSMMachine T}
  (X := mk_vlsm MX)
  (Y := mk_vlsm MY)
  (Z : VLSM message)
  (ProjXY : VLSM_incl X Y)
  (project_labelYZ : vlabel Y -> vlabel Z)
  (project_stateYZ : vstate Y -> vstate Z)
  (ProjYZ : VLSM_full_projection Y Z project_labelYZ project_stateYZ)
  : VLSM_full_projection X Z project_labelYZ project_stateYZ.
Proof.
  apply (VLSM_embedding_trans X Y Z); [| done].
  by apply VLSM_incl_is_full_projection in ProjXY.
Qed.

Lemma VLSM_projection_eq_trans
  {message}
  (X : VLSM message)
  {T : VLSMType message}
  {MY MZ : VLSMMachine T}
  (Y := mk_vlsm MY)
  (Z := mk_vlsm MZ)
  (project_labelXY : vlabel X -> option (vlabel Y))
  (project_stateXY : vstate X -> vstate Y)
  (ProjXY : VLSM_projection X Y project_labelXY project_stateXY)
  (ProjYZ : VLSM_eq Y Z)
  : VLSM_projection X Z project_labelXY project_stateXY.
Proof. by apply VLSM_projection_incl_trans; [| apply VLSM_eq_proj1]. Qed.

Lemma VLSM_embedding_eq_trans
  {message}
  (X : VLSM message)
  {T : VLSMType message}
  {MY MZ : VLSMMachine T}
  (Y := mk_vlsm MY)
  (Z := mk_vlsm MZ)
  (project_labelXY : vlabel X -> vlabel Y)
  (project_stateXY : vstate X -> vstate Y)
  (ProjXY : VLSM_full_projection X Y project_labelXY project_stateXY)
  (ProjYZ : VLSM_eq Y Z)
  : VLSM_full_projection X Z project_labelXY project_stateXY.
Proof. by apply VLSM_embedding_incl_trans; [| apply VLSM_eq_proj1]. Qed.

Lemma VLSM_eq_projection_trans
  {message}
  {T : VLSMType message}
  {MX MY : VLSMMachine T}
  (X := mk_vlsm MX)
  (Y := mk_vlsm MY)
  (Z : VLSM message)
  (ProjXY : VLSM_eq X Y)
  (project_labelYZ : vlabel Y -> option (vlabel Z))
  (project_stateYZ : vstate Y -> vstate Z)
  (ProjYZ : VLSM_projection Y Z project_labelYZ project_stateYZ)
  : VLSM_projection X Z project_labelYZ project_stateYZ.
Proof. by apply VLSM_incl_projection_trans; [apply VLSM_eq_proj1 |]. Qed.

Lemma VLSM_eq_embedding_trans
  {message}
  {T : VLSMType message}
  {MX MY : VLSMMachine T}
  (X := mk_vlsm MX)
  (Y := mk_vlsm MY)
  (Z : VLSM message)
  (ProjXY : VLSM_eq X Y)
  (project_labelYZ : vlabel Y -> vlabel Z)
  (project_stateYZ : vstate Y -> vstate Z)
  (ProjYZ : VLSM_full_projection Y Z project_labelYZ project_stateYZ)
  : VLSM_full_projection X Z project_labelYZ project_stateYZ.
Proof. by apply VLSM_incl_embedding_trans; [apply VLSM_eq_proj1 |]. Qed.

End transitivity_props.
