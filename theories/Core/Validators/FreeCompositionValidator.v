From VLSM.Lib Require Import Itauto.
From stdpp Require Import prelude.
From VLSM.Core Require Import VLSM Composition Equivocation MessageDependencies.
From VLSM.Core Require Import VLSMProjections ProjectionTraces.

(** * Sufficient conditions for being a validator for the free composition *)

(** ** Message validators are validators for the free composition *)

Section sec_free_composition_validator.

Context
  `{EqDecision index}
  `(IM : index -> VLSM message)
  .

(**
  If a component is a message-validator for the free composition, then any
  constrained trace of the component lifts to a valid trace of the composition.
*)
Lemma free_component_message_validator_valid_trace :
  forall (i : index),
    component_message_validator_prop IM (free_constraint IM) i ->
  forall is fi tr,
    finite_constrained_trace_init_to (IM i) is fi tr ->
    finite_valid_trace_init_to (free_composite_vlsm IM) (lift_to_composite_state' IM i is)
      (lift_to_composite_state' IM i fi) (lift_to_composite_finite_trace IM i tr).
Proof.
  intros i Hvalid isi fi tri Htri.
  apply pre_traces_with_valid_inputs_are_valid.
  - by apply (VLSM_embedding_finite_valid_trace_init_to
      (lift_to_composite_preloaded_VLSM_embedding IM i)).
  - rewrite Forall_forall.
    intros item Hitem.
    apply elem_of_list_fmap in Hitem as (itemi & -> & Hitem); cbn in isi, fi.
    apply elem_of_list_split in Hitem as (pre & suf & Heqtri).
    destruct Htri as [Htri _].
    apply valid_trace_forget_last in Htri.
    eapply (input_valid_transition_to (pre_loaded_with_all_messages_vlsm (IM i)))
      in Heqtri as Ht; [| done].
    destruct itemi, input as [m |]; cbn in *;
      [| by apply option_valid_message_None].
    unshelve eapply VLSM_incl_valid_message;
      [| by apply free_composite_vlsm_spec | by do 2 red |].
    by eapply Hvalid, input_valid_transition_iff; eexists.
Qed.

(**
  If a component is a message-validator for the free composition,
  then it is also a "full" validator for the free composition.
*)
Lemma free_component_message_validator_yields_validator :
  forall (i : index),
    component_message_validator_prop IM (free_constraint IM) i ->
    component_projection_validator_prop IM (free_constraint IM) i.
Proof.
  intros i Hvalid li si iom Ht.
  unfold input_constrained in Ht.
  apply input_valid_transition_iff in Ht as [[si' oom] Ht].
  apply (exists_right_finite_trace_from (pre_loaded_with_all_messages_vlsm (IM i)))
    in Ht as (isi & tri & Htri & Hsi').
  apply free_component_message_validator_valid_trace in Htri as [Htr _]; [| done].
  setoid_rewrite map_app in Htr.
  apply finite_valid_trace_from_to_app_split in Htr as [_ Ht].
  apply valid_trace_forget_last, first_transition_valid in Ht as [Hv _].
  eexists; split; cycle 1.
  - apply (@VLSM_incl_input_valid _ _ (free_composite_vlsm IM)); [| done].
    by apply free_composite_vlsm_spec.
  - subst si.
    pose proof (Heq_last := lift_to_composite_finite_trace_last IM i isi tri).
    apply (f_equal (fun s => s i)) in Heq_last.
    unfold lift_to_composite_state', lift_to_composite_state at 1 in Heq_last.
    by rewrite state_update_eq in Heq_last.
Qed.

End sec_free_composition_validator.

(** ** Sufficient conditions for being a message validator for the free composition *)

Section sec_free_composition_message_validator.

Context
  `{EqDecision index}
  `(IM : index -> VLSM message)
  `(sender : message -> option validator)
  (A : validator -> index)
  (Hchannel : channel_authentication_prop  IM A sender)
  `{FinSet message Cm}
  (message_dependencies : message -> Cm)
  (full_message_dependencies : message -> Cm)
  `{!FullMessageDependencies message_dependencies full_message_dependencies}
  `{forall i : index, HasBeenSentCapability (IM i)}
  `{forall i : index, HasBeenReceivedCapability (IM i)}
  `{forall i : index, MessageDependencies (IM i) message_dependencies}
  .

(** Property that there is a component which can emit a given message *)
Definition emittable (m : message) : Prop :=
  exists i, can_emit (pre_loaded_with_all_messages_vlsm (IM i)) m.

(**
  A sufficient condition for determining that a message is valid for the free
  composition (see lemma [free_valid_message_is_valid]).
*)
Inductive free_valid_message (m : message) : Prop :=
{
  fvm_emittable : emittable m;
  fvm_dependencies : set_Forall free_valid_message (message_dependencies m);
}.

(**
  A component satisfies the [free_valid_message_condition] property
  if the validity of receiving a message in a (constrained) state implies the
  [free_valid_message] property for that message
*)
Definition free_valid_message_condition (i : index) : Prop :=
  forall l s m,
    input_constrained (IM i) l (s, Some m) ->
      free_valid_message m.

(**
  Under full-node assumptions, [free_valid_message_condition] can be
  simplified to only requiring that the message is [emittable].
*)
Definition full_node_free_valid_message_condition (i : index) : Prop :=
  forall l s m,
    input_constrained (IM i) l (s, Some m) ->
      emittable m.

Lemma full_node_free_valid_message_entails_helper :
  forall (i : index),
    message_dependencies_full_node_condition_prop (IM i) message_dependencies ->
    full_node_free_valid_message_condition i ->
  forall l s m,
    input_constrained (IM i) l (s, Some m) ->
    (forall dm, has_been_directly_observed (IM i) s dm -> free_valid_message dm) ->
      free_valid_message m.
Proof.
  intros i Hfulli Hfree l s m Hv Hobs.
  constructor; [by eapply Hfree |].
  intros dm Hdm.
  eapply Hobs, Hfulli; [| done].
  by apply Hv.
Qed.

Lemma full_node_free_valid_message_entails :
  forall (i : index),
    message_dependencies_full_node_condition_prop (IM i) message_dependencies ->
    full_node_free_valid_message_condition i ->
      free_valid_message_condition i.
Proof.
  intros i Hfulli Hfree l s m Hv.
  eapply full_node_free_valid_message_entails_helper; [done.. |].
  destruct Hv as [Hs _].
  induction Hs using valid_state_prop_ind; intros dm Hdm;
    [by contradict Hdm; apply has_been_directly_observed_no_inits |].
  eapply has_been_directly_observed_step_update in Hdm; [| done].
  destruct Hdm as [[-> | ->]|]; [.. | by apply IHHs].
  - by destruct Ht; eapply full_node_free_valid_message_entails_helper.
  - assert (Hdm : can_produce (pre_loaded_with_all_messages_vlsm (IM i)) s' dm)
      by (eexists _,_; done).
    apply message_dependencies_are_necessary in Hdm as Hdeps.
    constructor; [by eexists; apply can_emit_iff; eexists |].
    intros dm' Hdm'.
    assert (dm' <> dm).
    {
      intros ->.
      eapply (irreflexivity (msg_dep_happens_before message_dependencies) dm).
      by constructor.
    }
    eapply Hdeps, has_been_directly_observed_step_update in Hdm'; [| done].
    destruct Hdm' as [[-> | Hdm'] |]; [.. | by congruence | by apply IHHs].
    by destruct Ht; eapply full_node_free_valid_message_entails_helper.
Qed.

Lemma free_valid_message_emittable_from_dependencies :
  forall (m : message),
    free_valid_message m ->
    Emittable_from_dependencies_prop (message_dependencies := message_dependencies) IM A sender m.
Proof.
  intros m [[i Hemit] _].
  apply Hchannel in Hemit as Hauth.
  unfold channel_authenticated_message in Hauth.
  destruct (sender m) eqn: Hsender; [| done].
  apply Some_inj in Hauth as <-.
  constructor 1 with v; [done |].
  by apply message_dependencies_are_sufficient.
Qed.

Lemma msg_dep_reflects_free_valid_message :
  forall (dm m : message),
    msg_dep_rel message_dependencies dm m ->
    free_valid_message m -> free_valid_message dm.
Proof.
  intros dm m Hdep [_ Hall].
  by apply Hall.
Qed.

Lemma free_valid_message_is_valid :
  forall m : message,
    free_valid_message m ->
      valid_message_prop (free_composite_vlsm IM) m.
Proof.
  intros m Hm.
  eapply free_valid_from_all_dependencies_emitable_from_dependencies; [done |].
  unfold all_dependencies_emittable_from_dependencies_prop.
  intros dm; rewrite elem_of_cons.
  intros [-> | Hdm]; [by apply free_valid_message_emittable_from_dependencies |].
  apply free_valid_message_emittable_from_dependencies.
  apply elem_of_elements, full_message_dependencies_happens_before in Hdm.
  eapply msg_dep_happens_before_reflect; [| done..].
  by apply msg_dep_reflects_free_valid_message.
Qed.

Section sec_free_valid_message_validators.

(**
  If the validity predicate of a component implies that its input message
  satisfies [free_valid_message], then the component is a message validator,
  and therefore, a validator for the free composition.
*)

Context
  (i : index)
  (Hfree_valid_message_inputs : free_valid_message_condition i)
  .

Lemma free_valid_message_yields_message_validator :
  component_message_validator_prop IM (free_constraint IM) i.
Proof.
  intros li si im Him.
  unshelve eapply VLSM_incl_valid_message;
    [| by apply free_composite_vlsm_spec | by do 2 red |].
  by eapply free_valid_message_is_valid, Hfree_valid_message_inputs, Him.
Qed.

Lemma free_valid_message_yields_projection_validator :
  component_projection_validator_prop IM (free_constraint IM) i.
Proof.
  by apply free_component_message_validator_yields_validator,
    free_valid_message_yields_message_validator.
Qed.

End sec_free_valid_message_validators.

Section sec_full_node_free_valid_message_validators.

Context
  (i : index)
  (Hfulli : message_dependencies_full_node_condition_prop (IM i) message_dependencies)
  (Hfree : full_node_free_valid_message_condition i)
  .

Lemma full_node_free_valid_message_yields_message_validator :
  component_message_validator_prop IM (free_constraint IM) i.
Proof.
  by apply free_valid_message_yields_message_validator,
    full_node_free_valid_message_entails.
Qed.

Lemma full_node_free_valid_message_yields_projection_validator :
  component_projection_validator_prop IM (free_constraint IM) i.
Proof.
  by apply free_valid_message_yields_projection_validator,
    full_node_free_valid_message_entails.
Qed.

End sec_full_node_free_valid_message_validators.

End sec_free_composition_message_validator.
