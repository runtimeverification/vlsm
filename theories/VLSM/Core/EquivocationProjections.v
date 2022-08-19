From stdpp Require Import prelude.
From VLSM.Lib Require Import Preamble.
From VLSM.Core Require Import VLSM Equivocation.
From VLSM.Core Require Import Composition VLSMProjections Validator ProjectionTraces.

(** * VLSM projections and messages properties

In this section we show that messages properties (oracles like [has_been_sent],
[has_been_received], and [has_been_directly_observed]) are reflected and, in some cases,
preserved by VLSM projections.
*)

Section projection_oracle.
(** ** [VLSM_projection]s reflect message properties *)

Context
  {message : Type}
  {X Y : VLSM message}
  {label_project : vlabel X -> option (vlabel Y)}
  {state_project : vstate X -> vstate Y}
  (Hsimul : VLSM_projection (pre_loaded_with_all_messages_vlsm X) (pre_loaded_with_all_messages_vlsm Y) label_project state_project)
  .

Section selectors.

Context
  (selectorX : message -> vtransition_item X -> Prop)
  (selectorY : message -> vtransition_item Y -> Prop)
  (Hselector : forall itemX itemY,
    input itemX = input itemY -> output itemX = output itemY ->
    forall m, selectorX m itemX <-> selectorY m itemY)
  .

(** Given the fact that all traces leading to a state in X project to traces
leading to its projection in Y, and since all messages in a trace projection
come from the original trace, it follows that any oracle for Y with the same
selector is reflected to X.
*)
Lemma VLSM_projection_oracle_reflect
  (oracleX : vstate X -> message -> Prop)
  (oracleY : vstate Y -> message -> Prop)
  (HstepwiseX : oracle_stepwise_props (vlsm := X) selectorX oracleX)
  (HstepwiseY : oracle_stepwise_props (vlsm := Y) selectorY oracleY)
  : forall s, valid_state_prop (pre_loaded_with_all_messages_vlsm X) s ->
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
  apply elem_of_list_In in HitemY.
  apply pre_VLSM_projection_finite_trace_project_in_iff in HitemY
    as [itemX [HitemX Hpr]].
  apply Exists_exists.
  apply elem_of_list_In in HitemX.
  exists itemX. split; [done |].
  revert Hm.
  unfold pre_VLSM_projection_transition_item_project in Hpr.
  destruct (label_project (l itemX)); [|congruence].
  inversion Hpr.
  by apply Hselector.
Qed.

End selectors.

Lemma VLSM_projection_has_been_sent_reflect
  `{HasBeenSentCapability message X}
  `{HasBeenSentCapability message Y}
  : forall s, valid_state_prop (pre_loaded_with_all_messages_vlsm X) s ->
    forall m, has_been_sent Y (state_project s) m -> has_been_sent X s m.
Proof.
  apply VLSM_projection_oracle_reflect with (field_selector output) (field_selector output).
  - by intros [] [] **; cbn in *; subst.
  - by apply (has_been_sent_stepwise_from_trace X).
  - by apply (has_been_sent_stepwise_from_trace Y).
Qed.

Lemma VLSM_projection_has_been_received_reflect
  `{HasBeenReceivedCapability message X}
  `{HasBeenReceivedCapability message Y}
  : forall s, valid_state_prop (pre_loaded_with_all_messages_vlsm X) s ->
    forall m, has_been_received Y (state_project s) m -> has_been_received X s m.
Proof.
  apply VLSM_projection_oracle_reflect with (field_selector input) (field_selector input).
  - by intros [] [] **; cbn in *; subst.
  - by apply (has_been_received_stepwise_from_trace X).
  - by apply (has_been_received_stepwise_from_trace Y).
Qed.

Lemma VLSM_projection_has_been_directly_observed_reflect
  `{HasBeenSentCapability message X}
  `{HasBeenReceivedCapability message X}
  `{HasBeenSentCapability message Y}
  `{HasBeenReceivedCapability message Y}
  : forall s, valid_state_prop (pre_loaded_with_all_messages_vlsm X) s ->
    forall m, has_been_directly_observed Y (state_project s) m -> has_been_directly_observed X s m.
Proof.
  apply VLSM_projection_oracle_reflect with item_sends_or_receives item_sends_or_receives.
  - by intros [] [] **; cbn in *; subst.
  - by apply has_been_directly_observed_stepwise_props.
  - by apply has_been_directly_observed_stepwise_props.
Qed.

End projection_oracle.

Section weak_full_projection_oracle.
(** ** [VLSM_weak_full_projection]s preserve message properties *)

Context
  {message : Type}
  {X Y : VLSM message}
  {label_project : vlabel X -> vlabel Y}
  {state_project : vstate X -> vstate Y}
  (Hsimul : VLSM_weak_full_projection (pre_loaded_with_all_messages_vlsm X) (pre_loaded_with_all_messages_vlsm Y) label_project state_project)
  .

Section selectors.

Context
  (selectorX : message -> vtransition_item X -> Prop)
  (selectorY : message -> vtransition_item Y -> Prop)
  (Hselector : forall itemX itemY,
    input itemX = input itemY -> output itemX = output itemY ->
    forall m, selectorX m itemX <-> selectorY m itemY)
  .

Lemma VLSM_weak_full_projection_selected_message_exists_in_some_preloaded_traces
  s m
  : selected_message_exists_in_some_preloaded_traces X selectorX s m ->
  selected_message_exists_in_some_preloaded_traces Y selectorY (state_project s) m.
Proof.
  intros [is [tr [Htr Hm]]].
  destruct Htr as [Htr His].
  apply (VLSM_weak_full_projection_finite_valid_trace_from_to Hsimul) in Htr.
  apply valid_trace_first_pstate in Htr as Hpr_is.
  apply valid_state_has_trace in Hpr_is as [is' [tr_is Hpr_is]].
  exists is', (tr_is ++ (VLSM_weak_full_projection_finite_trace_project Hsimul tr)).
  destruct Hpr_is as [Hpr_is His'].
  repeat split; [| done|].
  - by eapply (finite_valid_trace_from_to_app (pre_loaded_with_all_messages_vlsm Y)).
  - apply Exists_app. right.
    apply Exists_exists in Hm as [item [Hitem Hm]].
    apply elem_of_list_split in Hitem as [pre [suf Heqtr]].
    subst tr.
    setoid_rewrite map_app.
    apply List.Exists_app. right. simpl. left.
    remember  (pre_VLSM_full_projection_transition_item_project _ _ _ _ _) as itemY.
    by apply (Hselector item itemY); subst.
Qed.

Lemma VLSM_weak_full_projection_oracle
  oracleX oracleY
  (HstepwiseX : oracle_stepwise_props (vlsm := X) selectorX oracleX)
  (HstepwiseY : oracle_stepwise_props (vlsm := Y) selectorY oracleY)
  (HoracleX_dec : RelDecision oracleX)
  (HoracleY_dec : RelDecision oracleY)
  : forall s, valid_state_prop (pre_loaded_with_all_messages_vlsm X) s ->
    forall m, oracleX s m -> oracleY (state_project s) m.
Proof.
  intros s Hs m Hm.
  apply (prove_all_have_message_from_stepwise _ _ _ _ HstepwiseX _ Hs m) in Hm.
  apply (selected_messages_consistency_prop_from_stepwise _ _ _ _ HstepwiseX HoracleX_dec _ Hs) in Hm.
  apply (VLSM_weak_full_projection_valid_state Hsimul) in Hs as HsY.
  apply (prove_all_have_message_from_stepwise _ _ _ _ HstepwiseY _ HsY m).
  apply (selected_messages_consistency_prop_from_stepwise _ _ _ _ HstepwiseY HoracleY_dec _ HsY).
  revert Hm.
  apply VLSM_weak_full_projection_selected_message_exists_in_some_preloaded_traces.
Qed.

End selectors.

Lemma VLSM_weak_full_projection_has_been_sent
  `{HasBeenSentCapability message X}
  `{HasBeenSentCapability message Y}
  : forall s, valid_state_prop (pre_loaded_with_all_messages_vlsm X) s ->
    forall m, has_been_sent X s m -> has_been_sent Y (state_project s) m.
Proof.
  apply VLSM_weak_full_projection_oracle with (field_selector output) (field_selector output).
  - by intros [] [] Hin Hout; cbn in *; subst.
  - apply (has_been_sent_stepwise_from_trace X).
  - apply (has_been_sent_stepwise_from_trace Y).
  - apply has_been_sent_dec.
  - apply has_been_sent_dec.
Qed.

Lemma VLSM_weak_full_projection_has_been_received
  `{HasBeenReceivedCapability message X}
  `{HasBeenReceivedCapability message Y}
  : forall s, valid_state_prop (pre_loaded_with_all_messages_vlsm X) s ->
    forall m, has_been_received X s m -> has_been_received Y (state_project s) m.
Proof.
  apply VLSM_weak_full_projection_oracle with (field_selector input) (field_selector input).
  - by intros [] [] Hin Hout; cbn in *; subst.
  - apply (has_been_received_stepwise_from_trace X).
  - apply (has_been_received_stepwise_from_trace Y).
  - apply has_been_received_dec.
  - apply has_been_received_dec.
Qed.

Lemma VLSM_weak_full_projection_has_been_directly_observed
  `{HasBeenSentCapability message X}
  `{HasBeenReceivedCapability message X}
  `{HasBeenSentCapability message Y}
  `{HasBeenReceivedCapability message Y}
  : forall s, valid_state_prop (pre_loaded_with_all_messages_vlsm X) s ->
    forall m, has_been_directly_observed X s m -> has_been_directly_observed Y (state_project s) m.
Proof.
  apply VLSM_weak_full_projection_oracle with item_sends_or_receives item_sends_or_receives.
  - by intros [] [] **; cbn in *; subst.
  - apply has_been_directly_observed_stepwise_props.
  - apply has_been_directly_observed_stepwise_props.
  - apply has_been_directly_observed_dec.
  - apply has_been_directly_observed_dec.
Qed.

End weak_full_projection_oracle.

Section full_projection_oracle.
(** ** [VLSM_full_projection]s both preserve and reflect message properties *)

Context
  {message : Type}
  {X Y : VLSM message}
  {label_project : vlabel X -> vlabel Y}
  {state_project : vstate X -> vstate Y}
  (Hsimul : VLSM_full_projection (pre_loaded_with_all_messages_vlsm X) (pre_loaded_with_all_messages_vlsm Y) label_project state_project)
  .

Definition VLSM_full_projection_has_been_sent
  `{HasBeenSentCapability message X}
  `{HasBeenSentCapability message Y}
  : forall s, valid_state_prop (pre_loaded_with_all_messages_vlsm X) s ->
    forall m, has_been_sent X s m -> has_been_sent Y (state_project s) m
  := VLSM_weak_full_projection_has_been_sent (VLSM_full_projection_weaken Hsimul).

Definition VLSM_full_projection_has_been_received
  `{HasBeenReceivedCapability message X}
  `{HasBeenReceivedCapability message Y}
  : forall s, valid_state_prop (pre_loaded_with_all_messages_vlsm X) s ->
    forall m, has_been_received X s m -> has_been_received Y (state_project s) m
  := VLSM_weak_full_projection_has_been_received (VLSM_full_projection_weaken Hsimul).

Definition VLSM_full_projection_has_been_directly_observed
  `{HasBeenSentCapability message X}
  `{HasBeenReceivedCapability message X}
  `{HasBeenSentCapability message Y}
  `{HasBeenReceivedCapability message Y}
  : forall s, valid_state_prop (pre_loaded_with_all_messages_vlsm X) s ->
    forall m, has_been_directly_observed X s m -> has_been_directly_observed Y (state_project s) m
  := VLSM_weak_full_projection_has_been_directly_observed (VLSM_full_projection_weaken Hsimul).

Definition VLSM_full_projection_has_been_sent_reflect
  `{HasBeenSentCapability message X}
  `{HasBeenSentCapability message Y}
  : forall s, valid_state_prop (pre_loaded_with_all_messages_vlsm X) s ->
    forall m, has_been_sent Y (state_project s) m -> has_been_sent X s m
  := VLSM_projection_has_been_sent_reflect  (VLSM_full_projection_is_projection Hsimul).

Definition VLSM_full_projection_has_been_received_reflect
  `{HasBeenReceivedCapability message X}
  `{HasBeenReceivedCapability message Y}
  : forall s, valid_state_prop (pre_loaded_with_all_messages_vlsm X) s ->
    forall m, has_been_received Y (state_project s) m -> has_been_received X s m
  := VLSM_projection_has_been_received_reflect  (VLSM_full_projection_is_projection Hsimul).

Definition VLSM_full_projection_has_been_directly_observed_reflect
  `{HasBeenSentCapability message X}
  `{HasBeenReceivedCapability message X}
  `{HasBeenSentCapability message Y}
  `{HasBeenReceivedCapability message Y}
  : forall s, valid_state_prop (pre_loaded_with_all_messages_vlsm X) s ->
    forall m, has_been_directly_observed Y (state_project s) m -> has_been_directly_observed X s m
  := VLSM_projection_has_been_directly_observed_reflect  (VLSM_full_projection_is_projection Hsimul).

End full_projection_oracle.

Section incl_oracle.
(** ** [VLSM_incl]usions both preserve and reflect message properties *)

Context
  {message : Type}
  {T : VLSMType message}
  {MX MY : VLSMMachine T}
  (X := mk_vlsm MX)
  (Y := mk_vlsm MY)
  (Hincl : VLSM_incl (pre_loaded_with_all_messages_vlsm X) (pre_loaded_with_all_messages_vlsm Y))
  .

Lemma VLSM_incl_has_been_sent
  `{HasBeenSentCapability message X}
  `{HasBeenSentCapability message Y}
  : forall s, valid_state_prop (pre_loaded_with_all_messages_vlsm X) s ->
    forall m, has_been_sent X s m -> has_been_sent Y s m.
Proof.
  intros s Hs m Hm.
  by eapply
    (@VLSM_full_projection_has_been_sent _ X Y _ _
      (VLSM_incl_is_full_projection Hincl)).
Qed.

Lemma VLSM_incl_has_been_received
  `{HasBeenReceivedCapability message X}
  `{HasBeenReceivedCapability message Y}
  : forall s, valid_state_prop (pre_loaded_with_all_messages_vlsm X) s ->
    forall m, has_been_received X s m -> has_been_received Y s m.
Proof.
  intros s Hs m Hm.
  by eapply
    (@VLSM_full_projection_has_been_received _ X Y _ _
      (VLSM_incl_is_full_projection Hincl)).
Qed.

Lemma VLSM_incl_has_been_directly_observed
  `{HasBeenSentCapability message X}
  `{HasBeenReceivedCapability message X}
  `{HasBeenSentCapability message Y}
  `{HasBeenReceivedCapability message Y}
  : forall s, valid_state_prop (pre_loaded_with_all_messages_vlsm X) s ->
    forall m, has_been_directly_observed X s m -> has_been_directly_observed Y s m.
Proof.
  intros s Hs m Hm.
  by eapply
    (@VLSM_full_projection_has_been_directly_observed _ X Y _ _
      (VLSM_incl_is_full_projection Hincl)).
Qed.

Lemma VLSM_incl_has_been_sent_reflect
  `{HasBeenSentCapability message X}
  `{HasBeenSentCapability message Y}
  : forall s, valid_state_prop (pre_loaded_with_all_messages_vlsm X) s ->
    forall m, has_been_sent Y s m -> has_been_sent X s m.
Proof.
  intros s Hs m Hm.
  by eapply
    (@VLSM_full_projection_has_been_sent_reflect _ X Y _ _
      (VLSM_incl_is_full_projection Hincl)).
Qed.

Lemma VLSM_incl_has_been_received_reflect
  `{HasBeenReceivedCapability message X}
  `{HasBeenReceivedCapability message Y}
  : forall s, valid_state_prop (pre_loaded_with_all_messages_vlsm X) s ->
    forall m, has_been_received Y s m -> has_been_received X s m.
Proof.
  intros s Hs m Hm.
  by eapply
    (@VLSM_full_projection_has_been_received_reflect _ X Y _ _
      (VLSM_incl_is_full_projection Hincl)).
Qed.

Lemma VLSM_incl_has_been_directly_observed_reflect
  `{HasBeenSentCapability message X}
  `{HasBeenReceivedCapability message X}
  `{HasBeenSentCapability message Y}
  `{HasBeenReceivedCapability message Y}
  : forall s, valid_state_prop (pre_loaded_with_all_messages_vlsm X) s ->
    forall m, has_been_directly_observed Y s m -> has_been_directly_observed X s m.
Proof.
  intros s Hs m Hm.
  by eapply
    (@VLSM_full_projection_has_been_directly_observed_reflect _ X Y _ _
      (VLSM_incl_is_full_projection Hincl)).
Qed.

End incl_oracle.

Section same_IM_oracle_properties.

Context
  {message : Type}
  `{finite.Finite index}
  (IM1 IM2 : index -> VLSM message)
  `{forall i, HasBeenSentCapability (IM1 i)}
  `{forall i, HasBeenSentCapability (IM2 i)}
  (Heq : forall i, IM1 i = IM2 i)
  .

(** If two indexed sets of VLSMs are extensionally-equal, then the
[has_been_sent] predicate is preserved through the [same_IM_state_rew] map.
*)
Lemma same_IM_composite_has_been_sent_preservation s1 m
  (Hs1 : valid_state_prop (pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM1)) s1)
  : composite_has_been_sent IM1 s1 m ->
    composite_has_been_sent IM2 (same_IM_state_rew Heq s1) m.
Proof.
  specialize (same_IM_preloaded_free_full_projection IM1 IM2 Heq) as Hproj.
  intros Hbs1_m.
  by specialize (VLSM_full_projection_has_been_sent Hproj _ Hs1 m Hbs1_m).
Qed.

End same_IM_oracle_properties.

Section sender_safety_can_emit_projection.

Context
  {message : Type}
  `{EqDecision index}
  (IM : index -> VLSM message)
  {validator : Type}
  (A : validator -> index)
  (sender : message -> option validator)
  (Hsender_safety : sender_safety_alt_prop IM A sender)
  (PreFree := pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM))
  (j : index)
  (m : message)
  (Hj : option_map A (sender m) = Some j)
  .

(** Under [sender_safety_alt_prop]erty assumptions, if a message can be emitted
by the free composition (pre-loaded with all messages), then it can also be
emitted by the node corresponding to its sender (pre-loaded with all messages).
*)
Lemma can_emit_projection
  : can_emit PreFree m -> can_emit (pre_loaded_with_all_messages_vlsm (IM j)) m.
Proof.
  destruct (sender m) as [v|] eqn:Hsender; simpl in Hj; [|congruence].
  apply Some_inj in Hj.
  specialize (Hsender_safety _ _ Hsender).
  intros [(s0,om0) [(i, li) [s1 Hemitted]]].
  specialize (preloaded_component_projection IM i) as Hproj.
  specialize (VLSM_projection_input_valid_transition Hproj (existT i li) li)
    as Htransition.
  spec Htransition; [apply (composite_project_label_eq IM)|].
  apply Htransition in Hemitted. clear Htransition.
  remember (s0 i) as s0i. clear s0 Heqs0i.
  remember (s1 i) as s1i. clear s1 Heqs1i.
  spec Hsender_safety i.
  spec Hsender_safety; [by eexists _,_, _ |].
  rewrite Hsender_safety in Hj; subst.
  by eexists _,_, _.
Qed.

End sender_safety_can_emit_projection.
