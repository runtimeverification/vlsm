From VLSM.Lib Require Import Itauto.
From stdpp Require Import prelude.
From Coq Require Import FunctionalExtensionality.
From VLSM.Core Require Import VLSM.
From VLSM.Core Require Export VLSMPartialProjection VLSMStutteringEmbedding.
From VLSM.Core Require Export VLSMTotalProjection VLSMEmbedding.
From VLSM.Core Require Export VLSMInclusion VLSMEquality.

(** * VLSM Projection Properties *)

Section sec_same_VLSM_embedding.

(** ** Same VLSM embedding *)

Context
  {message : Type}
  (X1 X2 : VLSM message)
  (Heq : X1 = X2)
  .

Lemma same_VLSM_embedding
  : VLSM_embedding X1 X2 (same_VLSM_label_rew Heq) (same_VLSM_state_rew Heq).
Proof.
  apply basic_VLSM_strong_embedding; intro.
  - by apply same_VLSM_valid_preservation.
  - by apply same_VLSM_transition_preservation.
  - by apply same_VLSM_initial_state_preservation.
  - by apply same_VLSM_initial_message_preservation.
Qed.

End sec_same_VLSM_embedding.

Section sec_transitivity_props.

(** ** Transitivity properties *)

Lemma pre_VLSM_projection_finite_trace_project_trans
  {message : Type}
  (TX TY TZ : VLSMType message)
  (project_labelXY : label TX -> option (label TY))
  (project_stateXY : state TX -> state TY)
  (project_labelYZ : label TY -> option (label TZ))
  (project_stateYZ : state TY -> state TZ)
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
  (project_labelXY : label X -> option (label Y))
  (project_stateXY : state X -> state Y)
  (ProjXY : VLSM_projection X Y project_labelXY project_stateXY)
  (project_labelYZ : label Y -> option (label Z))
  (project_stateYZ : state Y -> state Z)
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
  (project_labelXY : label X -> option (label Y))
  (project_stateXY : state X -> state Y)
  (ProjXY : VLSM_projection X Y project_labelXY project_stateXY)
  (project_labelYZ : label Y -> label Z)
  (project_stateYZ : state Y -> state Z)
  (ProjYZ : VLSM_embedding Y Z project_labelYZ project_stateYZ)
  : VLSM_projection X Z
    (fmap project_labelYZ ∘ project_labelXY)
    (project_stateYZ ∘ project_stateXY).
Proof.
  apply VLSM_embedding_is_projection in ProjYZ.
  replace (fmap project_labelYZ ∘ project_labelXY)
     with (mbind (Some ∘ project_labelYZ) ∘ project_labelXY).
  - by apply VLSM_projection_trans.
  - by extensionality x.
Qed.

Lemma VLSM_embedding_projection_trans
  {message}
  (X Y Z : VLSM message)
  (project_labelXY : label X -> label Y)
  (project_stateXY : state X -> state Y)
  (ProjXY : VLSM_embedding X Y project_labelXY project_stateXY)
  (project_labelYZ : label Y -> option (label Z))
  (project_stateYZ : state Y -> state Z)
  (ProjYZ : VLSM_projection Y Z project_labelYZ project_stateYZ)
  : VLSM_projection X Z
    (project_labelYZ ∘ project_labelXY)
    (project_stateYZ ∘ project_stateXY).
Proof.
  apply VLSM_embedding_is_projection in ProjXY.
  replace (project_labelYZ ∘ project_labelXY)
     with (mbind project_labelYZ ∘ (Some ∘ project_labelXY)).
  - by apply VLSM_projection_trans.
  - by extensionality x.
Qed.

Lemma pre_VLSM_embedding_finite_trace_project_trans
  {message}
  (TX TY TZ : VLSMType message)
  (project_labelXY : label TX -> label TY)
  (project_stateXY : state TX -> state TY)
  (project_labelYZ : label TY -> label TZ)
  (project_stateYZ : state TY -> state TZ)
  : forall trX,
    pre_VLSM_embedding_finite_trace_project TX TZ
      (project_labelYZ ∘ project_labelXY)
      (project_stateYZ ∘ project_stateXY)
      trX
      =
    pre_VLSM_embedding_finite_trace_project  TY TZ project_labelYZ project_stateYZ
      (pre_VLSM_embedding_finite_trace_project  TX TY project_labelXY project_stateXY
        trX).
Proof. by induction trX; [| destruct a; cbn; f_equal]. Qed.

Lemma VLSM_embedding_trans
  {message}
  (X Y Z : VLSM message)
  (project_labelXY : label X -> label Y)
  (project_stateXY : state X -> state Y)
  (ProjXY : VLSM_embedding X Y project_labelXY project_stateXY)
  (project_labelYZ : label Y -> label Z)
  (project_stateYZ : state Y -> state Z)
  (ProjYZ : VLSM_embedding Y Z project_labelYZ project_stateYZ)
  : VLSM_embedding X Z
    (project_labelYZ ∘ project_labelXY)
    (project_stateYZ ∘ project_stateXY).
Proof.
  constructor; intros sX trX HtrX.
  setoid_rewrite pre_VLSM_embedding_finite_trace_project_trans.
  by eapply (VLSM_embedding_finite_valid_trace ProjYZ),
            (VLSM_embedding_finite_valid_trace ProjXY).
Qed.

Lemma VLSM_projection_incl_trans
  {message}
  (X : VLSM message)
  {T : VLSMType message}
  {MY MZ : VLSM T}
  (Y := mk_vlsm MY)
  (Z := mk_vlsm MZ)
  (project_labelXY : label X -> option (label Y))
  (project_stateXY : state X -> state Y)
  (ProjXY : VLSM_projection X Y project_labelXY project_stateXY)
  (ProjYZ : VLSM_incl Y Z)
  : VLSM_projection X Z project_labelXY project_stateXY.
Proof.
  replace project_labelXY with (fmap id ∘ project_labelXY)
    by (extensionality lX; cbv; destruct (project_labelXY lX); done).
  change project_stateXY with (id ∘ project_stateXY).
  by apply (VLSM_projection_embedding_trans X Y Z); [| apply VLSM_incl_is_embedding].
Qed.

Lemma VLSM_embedding_incl_trans
  {message}
  (X : VLSM message)
  {T : VLSMType message}
  {MY MZ : VLSM T}
  (Y := mk_vlsm MY)
  (Z := mk_vlsm MZ)
  (project_labelXY : label X -> label Y)
  (project_stateXY : state X -> state Y)
  (ProjXY : VLSM_embedding X Y project_labelXY project_stateXY)
  (ProjYZ : VLSM_incl Y Z)
  : VLSM_embedding X Z project_labelXY project_stateXY.
Proof.
  change project_labelXY with (id ∘ project_labelXY).
  change project_stateXY with (id ∘ project_stateXY).
  by apply (VLSM_embedding_trans X Y Z); [| apply VLSM_incl_is_embedding].
Qed.

Lemma VLSM_incl_projection_trans
  {message}
  {T : VLSMType message}
  {MX MY : VLSM T}
  (X := mk_vlsm MX)
  (Y := mk_vlsm MY)
  (Z : VLSM message)
  (ProjXY : VLSM_incl X Y)
  (project_labelYZ : label Y -> option (label Z))
  (project_stateYZ : state Y -> state Z)
  (ProjYZ : VLSM_projection Y Z project_labelYZ project_stateYZ)
  : VLSM_projection X Z project_labelYZ project_stateYZ.
Proof.
  apply (VLSM_embedding_projection_trans X Y Z); [| done].
  by apply VLSM_incl_is_embedding in ProjXY.
Qed.

Lemma VLSM_incl_embedding_trans
  {message}
  {T : VLSMType message}
  {MX MY : VLSM T}
  (X := mk_vlsm MX)
  (Y := mk_vlsm MY)
  (Z : VLSM message)
  (ProjXY : VLSM_incl X Y)
  (project_labelYZ : label Y -> label Z)
  (project_stateYZ : state Y -> state Z)
  (ProjYZ : VLSM_embedding Y Z project_labelYZ project_stateYZ)
  : VLSM_embedding X Z project_labelYZ project_stateYZ.
Proof.
  apply (VLSM_embedding_trans X Y Z); [| done].
  by apply VLSM_incl_is_embedding in ProjXY.
Qed.

Lemma VLSM_projection_eq_trans
  {message}
  (X : VLSM message)
  {T : VLSMType message}
  {MY MZ : VLSM T}
  (Y := mk_vlsm MY)
  (Z := mk_vlsm MZ)
  (project_labelXY : label X -> option (label Y))
  (project_stateXY : state X -> state Y)
  (ProjXY : VLSM_projection X Y project_labelXY project_stateXY)
  (ProjYZ : VLSM_eq Y Z)
  : VLSM_projection X Z project_labelXY project_stateXY.
Proof. by apply VLSM_projection_incl_trans; [| apply ProjYZ]. Qed.

Lemma VLSM_embedding_eq_trans
  {message}
  (X : VLSM message)
  {T : VLSMType message}
  {MY MZ : VLSM T}
  (Y := mk_vlsm MY)
  (Z := mk_vlsm MZ)
  (project_labelXY : label X -> label Y)
  (project_stateXY : state X -> state Y)
  (ProjXY : VLSM_embedding X Y project_labelXY project_stateXY)
  (ProjYZ : VLSM_eq Y Z)
  : VLSM_embedding X Z project_labelXY project_stateXY.
Proof. by apply VLSM_embedding_incl_trans; [| apply ProjYZ]. Qed.

Lemma VLSM_eq_projection_trans
  {message}
  {T : VLSMType message}
  {MX MY : VLSM T}
  (X := mk_vlsm MX)
  (Y := mk_vlsm MY)
  (Z : VLSM message)
  (ProjXY : VLSM_eq X Y)
  (project_labelYZ : label Y -> option (label Z))
  (project_stateYZ : state Y -> state Z)
  (ProjYZ : VLSM_projection Y Z project_labelYZ project_stateYZ)
  : VLSM_projection X Z project_labelYZ project_stateYZ.
Proof. by apply VLSM_incl_projection_trans; [apply ProjXY |]. Qed.

Lemma VLSM_eq_embedding_trans
  {message}
  {T : VLSMType message}
  {MX MY : VLSM T}
  (X := mk_vlsm MX)
  (Y := mk_vlsm MY)
  (Z : VLSM message)
  (ProjXY : VLSM_eq X Y)
  (project_labelYZ : label Y -> label Z)
  (project_stateYZ : state Y -> state Z)
  (ProjYZ : VLSM_embedding Y Z project_labelYZ project_stateYZ)
  : VLSM_embedding X Z project_labelYZ project_stateYZ.
Proof. by apply VLSM_incl_embedding_trans; [apply ProjXY |]. Qed.

End sec_transitivity_props.
