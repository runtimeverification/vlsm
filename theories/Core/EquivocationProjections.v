From stdpp Require Import prelude.
From VLSM.Lib Require Import Preamble.
From VLSM.Core Require Import VLSM Equivocation.
From VLSM.Core Require Import Composition VLSMProjections Validator ProjectionTraces.

(** * Core: VLSM Projections and Messages Properties

  In this section, we show that messages properties (oracles like [has_been_sent],
  [has_been_received], and [has_been_directly_observed]) are reflected and, in some cases,
  preserved by VLSM projections.
*)

Section sec_projection_oracle.

(** ** VLSM projections reflect message properties *)

Context
  {message : Type}
  {X Y : VLSM message}
  {label_project : label X -> option (label Y)}
  {state_project : state X -> state Y}
  (Hsimul : VLSM_projection (preloaded_with_all_messages_vlsm X) (preloaded_with_all_messages_vlsm Y)
    label_project state_project)
  .

Section sec_selectors.

Context
  (selectorX : message -> transition_item X -> Prop)
  (selectorY : message -> transition_item Y -> Prop)
  (Hselector : forall itemX itemY,
    input itemX = input itemY -> output itemX = output itemY ->
    forall m, selectorX m itemX <-> selectorY m itemY)
  .

(**
  Given the fact that all traces leading to a state in X project to traces
  leading to its projection in Y, and since all messages in a trace projection
  come from the original trace, it follows that any oracle for Y with the same
  selector is reflected to X.
*)
Lemma VLSM_projection_oracle_reflect
  (oracleX : state X -> message -> Prop)
  (oracleY : state Y -> message -> Prop)
  (HstepwiseX : oracle_stepwise_props (vlsm := X) selectorX oracleX)
  (HstepwiseY : oracle_stepwise_props (vlsm := Y) selectorY oracleY)
  : forall s, constrained_state_prop X s ->
  forall m, oracleY (state_project s) m -> oracleX s m.
Proof.
  intros s Hs m Hm.
  apply (prove_all_have_message_from_stepwise _ _ _ _ HstepwiseX _ Hs m).
  intros isX trX HtrX.
  apply (VLSM_projection_finite_valid_trace_init_to Hsimul) in HtrX.
  apply (VLSM_projection_valid_state Hsimul) in Hs as HsY.
  apply (prove_all_have_message_from_stepwise _ _ _ _ HstepwiseY _ HsY m) in Hm.
  specialize (Hm _ _ HtrX).
  apply Exists_exists in Hm as [itemY [HitemY Hm]].
  apply pre_VLSM_projection_finite_trace_project_elem_of_iff in HitemY
    as [itemX [HitemX Hpr]].
  apply Exists_exists.
  exists itemX. split; [done |].
  revert Hm.
  unfold pre_VLSM_projection_transition_item_project in Hpr.
  destruct (label_project (l itemX)); [| by congruence].
  inversion Hpr.
  by apply Hselector.
Qed.

End sec_selectors.

Lemma VLSM_projection_has_been_sent_reflect
  `{HasBeenSentCapability message X}
  `{HasBeenSentCapability message Y}
  : forall s, constrained_state_prop X s ->
    forall m, has_been_sent Y (state_project s) m -> has_been_sent X s m.
Proof.
  apply VLSM_projection_oracle_reflect with (field_selector output) (field_selector output).
  - by intros [] [] **; cbn in *; subst.
  - by apply (has_been_sent_stepwise_props X).
  - by apply (has_been_sent_stepwise_props Y).
Qed.

Lemma VLSM_projection_has_been_received_reflect
  `{HasBeenReceivedCapability message X}
  `{HasBeenReceivedCapability message Y}
  : forall s, constrained_state_prop X s ->
    forall m, has_been_received Y (state_project s) m -> has_been_received X s m.
Proof.
  apply VLSM_projection_oracle_reflect with (field_selector input) (field_selector input).
  - by intros [] [] **; cbn in *; subst.
  - by apply (has_been_received_stepwise_props X).
  - by apply (has_been_received_stepwise_props Y).
Qed.

Lemma VLSM_projection_has_been_directly_observed_reflect
  `{HasBeenSentCapability message X}
  `{HasBeenReceivedCapability message X}
  `{HasBeenSentCapability message Y}
  `{HasBeenReceivedCapability message Y}
  : forall s, constrained_state_prop X s ->
    forall m, has_been_directly_observed Y (state_project s) m -> has_been_directly_observed X s m.
Proof.
  apply VLSM_projection_oracle_reflect with item_sends_or_receives item_sends_or_receives.
  - by intros [] [] **; cbn in *; subst.
  - by apply has_been_directly_observed_stepwise_props.
  - by apply has_been_directly_observed_stepwise_props.
Qed.

End sec_projection_oracle.

Section sec_weak_embedding_oracle.

(** ** [VLSM_weak_embedding]s preserve message properties *)

Context
  {message : Type}
  {X Y : VLSM message}
  {label_project : label X -> label Y}
  {state_project : state X -> state Y}
  (Hsimul : VLSM_weak_embedding (preloaded_with_all_messages_vlsm X)
    (preloaded_with_all_messages_vlsm Y) label_project state_project)
  .

Section sec_selectors.

Context
  (selectorX : message -> transition_item X -> Prop)
  (selectorY : message -> transition_item Y -> Prop)
  (Hselector : forall itemX itemY,
    input itemX = input itemY -> output itemX = output itemY ->
    forall m, selectorX m itemX <-> selectorY m itemY)
  .

Lemma VLSM_weak_embedding_selected_message_exists_in_some_preloaded_traces
  s m
  : selected_message_exists_in_some_preloaded_traces X selectorX s m ->
  selected_message_exists_in_some_preloaded_traces Y selectorY (state_project s) m.
Proof.
  intros [is [tr [Htr Hm]]].
  destruct Htr as [Htr His].
  apply (VLSM_weak_embedding_finite_valid_trace_from_to Hsimul) in Htr.
  apply valid_trace_first_pstate in Htr as Hpr_is.
  apply valid_state_has_trace in Hpr_is as [is' [tr_is Hpr_is]].
  exists is', (tr_is ++ (VLSM_weak_embedding_finite_trace_project Hsimul tr)).
  destruct Hpr_is as [Hpr_is His'].
  repeat split; [| done |].
  - by eapply (finite_valid_trace_from_to_app (preloaded_with_all_messages_vlsm Y)).
  - apply Exists_app. right.
    apply Exists_exists in Hm as [item [Hitem Hm]].
    apply elem_of_list_split in Hitem as [pre [suf Heqtr]].
    subst tr.
    setoid_rewrite map_app.
    apply List.Exists_app. right. simpl. left.
    remember  (pre_VLSM_embedding_transition_item_project _ _ _ _ _) as itemY.
    by apply (Hselector item itemY); subst.
Qed.

Lemma VLSM_weak_embedding_oracle
  oracleX oracleY
  (HstepwiseX : oracle_stepwise_props (vlsm := X) selectorX oracleX)
  (HstepwiseY : oracle_stepwise_props (vlsm := Y) selectorY oracleY)
  (HoracleX_dec : RelDecision oracleX)
  (HoracleY_dec : RelDecision oracleY)
  : forall s, constrained_state_prop X s ->
    forall m, oracleX s m -> oracleY (state_project s) m.
Proof.
  intros s Hs m Hm.
  apply (prove_all_have_message_from_stepwise _ _ _ _ HstepwiseX _ Hs m) in Hm.
  apply (selected_messages_consistency_prop_from_stepwise _ _ _ _ HstepwiseX HoracleX_dec _ Hs) in Hm.
  apply (VLSM_weak_embedding_valid_state Hsimul) in Hs as HsY.
  apply (prove_all_have_message_from_stepwise _ _ _ _ HstepwiseY _ HsY m).
  apply (selected_messages_consistency_prop_from_stepwise _ _ _ _ HstepwiseY HoracleY_dec _ HsY).
  by apply VLSM_weak_embedding_selected_message_exists_in_some_preloaded_traces.
Qed.

End sec_selectors.

Lemma VLSM_weak_embedding_has_been_sent
  `{HasBeenSentCapability message X}
  `{HasBeenSentCapability message Y}
  : forall s, constrained_state_prop X s ->
    forall m, has_been_sent X s m -> has_been_sent Y (state_project s) m.
Proof.
  apply VLSM_weak_embedding_oracle with (field_selector output) (field_selector output).
  - by intros [] [] Hin Hout; cbn in *; subst.
  - by apply (has_been_sent_stepwise_props X).
  - by apply (has_been_sent_stepwise_props Y).
  - by apply has_been_sent_dec.
  - by apply has_been_sent_dec.
Qed.

Lemma VLSM_weak_embedding_has_been_received
  `{HasBeenReceivedCapability message X}
  `{HasBeenReceivedCapability message Y}
  : forall s, constrained_state_prop X s ->
    forall m, has_been_received X s m -> has_been_received Y (state_project s) m.
Proof.
  apply VLSM_weak_embedding_oracle with (field_selector input) (field_selector input).
  - by intros [] [] Hin Hout; cbn in *; subst.
  - by apply (has_been_received_stepwise_props X).
  - by apply (has_been_received_stepwise_props Y).
  - by apply has_been_received_dec.
  - by apply has_been_received_dec.
Qed.

Lemma VLSM_weak_embedding_has_been_directly_observed
  `{HasBeenSentCapability message X}
  `{HasBeenReceivedCapability message X}
  `{HasBeenSentCapability message Y}
  `{HasBeenReceivedCapability message Y}
  : forall s, constrained_state_prop X s ->
    forall m, has_been_directly_observed X s m -> has_been_directly_observed Y (state_project s) m.
Proof.
  apply VLSM_weak_embedding_oracle with item_sends_or_receives item_sends_or_receives.
  - by intros [] [] **; cbn in *; subst.
  - by apply has_been_directly_observed_stepwise_props.
  - by apply has_been_directly_observed_stepwise_props.
  - by apply has_been_directly_observed_dec.
  - by apply has_been_directly_observed_dec.
Qed.

End sec_weak_embedding_oracle.

Section sec_embedding_oracle.

(** ** [VLSM_embedding]s both preserve and reflect message properties *)

Context
  {message : Type}
  {X Y : VLSM message}
  {label_project : label X -> label Y}
  {state_project : state X -> state Y}
  (Hsimul :
    VLSM_embedding (preloaded_with_all_messages_vlsm X)
      (preloaded_with_all_messages_vlsm Y) label_project state_project)
  .

Lemma VLSM_embedding_has_been_sent
  `{HasBeenSentCapability message X}
  `{HasBeenSentCapability message Y}
  : forall s, constrained_state_prop X s ->
    forall m, has_been_sent X s m -> has_been_sent Y (state_project s) m.
Proof.
  exact (VLSM_weak_embedding_has_been_sent (VLSM_embedding_weaken Hsimul)).
Qed.

Lemma VLSM_embedding_has_been_received
  `{HasBeenReceivedCapability message X}
  `{HasBeenReceivedCapability message Y}
  : forall s, constrained_state_prop X s ->
    forall m, has_been_received X s m -> has_been_received Y (state_project s) m.
Proof.
  exact (VLSM_weak_embedding_has_been_received (VLSM_embedding_weaken Hsimul)).
Qed.

Lemma VLSM_embedding_has_been_directly_observed
  `{HasBeenSentCapability message X}
  `{HasBeenReceivedCapability message X}
  `{HasBeenSentCapability message Y}
  `{HasBeenReceivedCapability message Y}
  : forall s, constrained_state_prop X s ->
    forall m, has_been_directly_observed X s m -> has_been_directly_observed Y (state_project s) m.
Proof.
  exact (VLSM_weak_embedding_has_been_directly_observed (VLSM_embedding_weaken Hsimul)).
Qed.

Lemma VLSM_embedding_has_been_sent_reflect
  `{HasBeenSentCapability message X}
  `{HasBeenSentCapability message Y}
  : forall s, constrained_state_prop X s ->
    forall m, has_been_sent Y (state_project s) m -> has_been_sent X s m.
Proof.
  exact (VLSM_projection_has_been_sent_reflect  (VLSM_embedding_is_projection Hsimul)).
Qed.

Lemma VLSM_embedding_has_been_received_reflect
  `{HasBeenReceivedCapability message X}
  `{HasBeenReceivedCapability message Y}
  : forall s, constrained_state_prop X s ->
    forall m, has_been_received Y (state_project s) m -> has_been_received X s m.
Proof.
  exact (VLSM_projection_has_been_received_reflect  (VLSM_embedding_is_projection Hsimul)).
Qed.

Lemma VLSM_embedding_has_been_directly_observed_reflect
  `{HasBeenSentCapability message X}
  `{HasBeenReceivedCapability message X}
  `{HasBeenSentCapability message Y}
  `{HasBeenReceivedCapability message Y}
  : forall s, constrained_state_prop X s ->
    forall m, has_been_directly_observed Y (state_project s) m -> has_been_directly_observed X s m.
Proof.
  exact (VLSM_projection_has_been_directly_observed_reflect (VLSM_embedding_is_projection Hsimul)).
Qed.

End sec_embedding_oracle.

Section sec_incl_oracle.

(** ** [VLSM_incl]usions both preserve and reflect message properties *)

Context
  {message : Type}
  {T : VLSMType message}
  {MX MY : VLSMMachine T}
  (X := mk_vlsm MX)
  (Y := mk_vlsm MY)
  (Hincl : VLSM_incl (preloaded_with_all_messages_vlsm X) (preloaded_with_all_messages_vlsm Y))
  .

Lemma VLSM_incl_has_been_sent
  `{HasBeenSentCapability message X}
  `{HasBeenSentCapability message Y}
  : forall s, constrained_state_prop X s ->
    forall m, has_been_sent X s m -> has_been_sent Y s m.
Proof.
  intros s Hs m Hm.
  by eapply
    (@VLSM_embedding_has_been_sent _ X Y _ _
      (VLSM_incl_is_embedding Hincl)).
Qed.

Lemma VLSM_incl_has_been_received
  `{HasBeenReceivedCapability message X}
  `{HasBeenReceivedCapability message Y}
  : forall s, constrained_state_prop X s ->
    forall m, has_been_received X s m -> has_been_received Y s m.
Proof.
  intros s Hs m Hm.
  by eapply
    (@VLSM_embedding_has_been_received _ X Y _ _
      (VLSM_incl_is_embedding Hincl)).
Qed.

Lemma VLSM_incl_has_been_directly_observed
  `{HasBeenSentCapability message X}
  `{HasBeenReceivedCapability message X}
  `{HasBeenSentCapability message Y}
  `{HasBeenReceivedCapability message Y}
  : forall s, constrained_state_prop X s ->
    forall m, has_been_directly_observed X s m -> has_been_directly_observed Y s m.
Proof.
  intros s Hs m Hm.
  by eapply
    (@VLSM_embedding_has_been_directly_observed _ X Y _ _
      (VLSM_incl_is_embedding Hincl)).
Qed.

Lemma VLSM_incl_has_been_sent_reflect
  `{HasBeenSentCapability message X}
  `{HasBeenSentCapability message Y}
  : forall s, constrained_state_prop X s ->
    forall m, has_been_sent Y s m -> has_been_sent X s m.
Proof.
  intros s Hs m Hm.
  by eapply
    (@VLSM_embedding_has_been_sent_reflect _ X Y _ _
      (VLSM_incl_is_embedding Hincl)).
Qed.

Lemma VLSM_incl_has_been_received_reflect
  `{HasBeenReceivedCapability message X}
  `{HasBeenReceivedCapability message Y}
  : forall s, constrained_state_prop X s ->
    forall m, has_been_received Y s m -> has_been_received X s m.
Proof.
  intros s Hs m Hm.
  by eapply
    (@VLSM_embedding_has_been_received_reflect _ X Y _ _
      (VLSM_incl_is_embedding Hincl)).
Qed.

Lemma VLSM_incl_has_been_directly_observed_reflect
  `{HasBeenSentCapability message X}
  `{HasBeenReceivedCapability message X}
  `{HasBeenSentCapability message Y}
  `{HasBeenReceivedCapability message Y}
  : forall s, constrained_state_prop X s ->
    forall m, has_been_directly_observed Y s m -> has_been_directly_observed X s m.
Proof.
  intros s Hs m Hm.
  by eapply
    (@VLSM_embedding_has_been_directly_observed_reflect _ X Y _ _
      (VLSM_incl_is_embedding Hincl)).
Qed.

End sec_incl_oracle.

Section sec_same_IM_oracle_properties.

Context
  {message : Type}
  `{finite.Finite index}
  (IM1 IM2 : index -> VLSM message)
  `{forall i, HasBeenSentCapability (IM1 i)}
  `{forall i, HasBeenSentCapability (IM2 i)}
  (Heq : forall i, IM1 i = IM2 i)
  .

(**
  If two indexed sets of VLSMs are extensionally-equal, then the
  [has_been_sent] predicate is preserved through the [same_IM_state_rew] map.
*)
Lemma same_IM_composite_has_been_sent_preservation s1 m
  (Hs1 : constrained_state_prop (free_composite_vlsm IM1) s1)
  : composite_has_been_sent IM1 s1 m ->
    composite_has_been_sent IM2 (same_IM_state_rew Heq s1) m.
Proof.
  specialize (same_IM_preloaded_free_embedding IM1 IM2 Heq) as Hproj.
  intros Hbs1_m.
  by specialize (VLSM_embedding_has_been_sent Hproj _ Hs1 m Hbs1_m).
Qed.

End sec_same_IM_oracle_properties.

Section sec_sender_safety_can_emit_projection.

Context
  {message : Type}
  `{EqDecision index}
  (IM : index -> VLSM message)
  {validator : Type}
  (A : validator -> index)
  (sender : message -> option validator)
  (Hsender_safety : sender_safety_alt_prop IM A sender)
  (j : index)
  (m : message)
  (Hj : option_map A (sender m) = Some j)
  .

(**
  Under [sender_safety_alt_prop]erty assumptions, if a message can be emitted
  by the free composition (preloaded with all messages), then it can also be
  emitted by the component corresponding to its sender (preloaded with all messages).
*)
Lemma can_emit_projection :
  can_emit (preloaded_with_all_messages_vlsm (free_composite_vlsm IM)) m ->
  can_emit (preloaded_with_all_messages_vlsm (IM j)) m.
Proof.
  destruct (sender m) as [v |] eqn: Hsender; simpl in Hj; [| by congruence].
  apply Some_inj in Hj.
  specialize (Hsender_safety _ _ Hsender).
  intros [(s0, om0) [(i, li) [s1 Hemitted]]].
  specialize (preloaded_component_projection IM i) as Hproj.
  specialize (VLSM_projection_input_valid_transition Hproj (existT i li) li)
    as Htransition.
  spec Htransition; [by apply (composite_project_label_eq IM) |].
  apply Htransition in Hemitted. clear Htransition.
  remember (s0 i) as s0i. clear s0 Heqs0i.
  remember (s1 i) as s1i. clear s1 Heqs1i.
  specialize (Hsender_safety i).
  spec Hsender_safety; [by eexists _, _, _ |].
  rewrite Hsender_safety in Hj; subst.
  by eexists _, _, _.
Qed.

End sec_sender_safety_can_emit_projection.
