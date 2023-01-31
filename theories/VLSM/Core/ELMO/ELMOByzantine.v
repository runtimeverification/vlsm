From stdpp Require Import prelude.
From Coq Require Import Reals.
From VLSM.Lib Require Import Measurable.
From VLSM.Core Require Import VLSM Composition ProjectionTraces VLSMProjections.
From VLSM.Core Require Import Equivocation MessageDependencies FixedSetEquivocation.
From VLSM.Core Require Import ReachableThreshold Validator.
From VLSM.Core Require Import ByzantineTraces FixedSetByzantineTraces.
From VLSM.Core Require Import BaseELMO ELMO.

Section sec_elmo_byzantine.

Context
  {Address : Type}
  {measurable_Address : Measurable Address}
  `{FinSet Address Ca}
  (threshold : R)
  `{!ReachableThreshold Address Ca threshold}
  `{FinSet index Ci}
  `{!finite.Finite index}
  `{Inhabited index}
  (idx : index -> Address)
  `{!Inj (=) (=) idx}
  (ELMOComponent := fun i : index => ELMOComponent threshold idx (Ca := Ca) i)
  (ELMOProtocol := ELMOProtocol threshold idx (Ca := Ca)).

Corollary ELMOcomponent_byzantine_fault_tolerance :
  forall i : index,
    forall tr, byzantine_trace_prop (ELMOComponent i) tr ->
      valid_trace_prop
        (pre_composite_vlsm_induced_projection_validator
          ELMOComponent (ELMO_global_constraint threshold idx) i)
        tr.
Proof.
  by intro i; apply validator_component_byzantine_fault_tolerance,
    ELMOComponents_validating.
Qed.

Corollary ELMOcomposite_byzantine_traces_are_not_byzantine :
  forall tr, byzantine_trace_prop ELMOProtocol tr -> valid_trace_prop ELMOProtocol tr.
Proof.
  apply composite_validator_byzantine_traces_are_not_byzantine.
  by intro; eapply component_projection_validator_is_message_validator, ELMOComponents_validating.
Qed.

Definition ELMO_fixed_equivocation_global_constraint
  (equivocating_nodes : Ci)
  (l : composite_label ELMOComponent)
  (som : composite_state ELMOComponent * option Message) : Prop :=
match l, som.2 with
| existT _ Receive, Some m =>
  composite_has_been_directly_observed ELMOComponent som.1 m
    \/
  ELMO_A idx (adr (state m)) ∈ equivocating_nodes
| _,_ => True
end.

(** Every [ELMOComponent] is a validator for [ELMOProtocol]. *)
Theorem ELMOComponents_fixed_equivocation_validating (equivocating_nodes : Ci) :
  forall i : index, i ∉ equivocating_nodes ->
    component_projection_validator_prop ELMOComponent
      (ELMO_fixed_equivocation_global_constraint equivocating_nodes) i.
Proof.
  intros i Hi li si om Hvti.
  apply input_valid_transition_iff in Hvti as [[si' om'] Hvti].
  pose (Hvti' := Hvti); destruct Hvti' as [(_ & _ & Hvi) Hti].
  apply input_valid_transition_destination in Hvti as Hsi'.
  eapply reflecting_composite_for_reachable_component in Hsi'
    as (s' & <- & Hs' & _ & _ & Htransitions); [| done].
  specialize (Htransitions si li).
  exists (state_update ELMOComponent s' i si).
  split; [by state_update_simpl |].
  inversion Hvi; subst; inversion Hti as [Heqs'i]; subst;
    symmetry in Heqs'i; destruct (Htransitions _ Heqs'i) as [Hvs'0 Hvt0];
    inversion Hvt0 as [? ? ? ? Hvt | ? ? ? ? Hvt];
    [ repeat split; [| | by apply Hvt |]
    | repeat split; [| apply option_valid_message_None | apply Hvt]].
Admitted.

Lemma ELMO_fixed_equivocation_subsumption (equivocating_nodes : Ci) :
  weak_input_valid_constraint_subsumption ELMOComponent
    (ELMO_fixed_equivocation_global_constraint equivocating_nodes)
    (fixed_equivocation_constraint ELMOComponent equivocating_nodes).
Admitted.

Lemma ELMO_fixed_equivocation_subsumption_rev (equivocating_nodes : Ci) :
  weak_input_valid_constraint_subsumption ELMOComponent
    (fixed_equivocation_constraint ELMOComponent equivocating_nodes)
    (ELMO_fixed_equivocation_global_constraint equivocating_nodes).
Admitted.

Lemma ELMO_fixed_equivocation_VLSM_eq (equivocating_nodes : Ci) :
  VLSM_eq
    (composite_vlsm ELMOComponent (ELMO_fixed_equivocation_global_constraint equivocating_nodes))
    (composite_vlsm ELMOComponent (fixed_equivocation_constraint ELMOComponent equivocating_nodes)).
Proof.
  apply VLSM_eq_incl_iff; split; apply weak_constraint_subsumption_incl.
  - by apply ELMO_fixed_equivocation_subsumption.
  - by apply ELMO_fixed_equivocation_subsumption_rev.
Qed.

Corollary ELMO_fixed_byzantine_traces_equivocation_char :
  forall (byzantine_nodes : Ci), (sum_weights (set_map (D := Ca) idx byzantine_nodes) <= threshold)%R ->
  forall (bis : composite_state ELMOComponent) (btr : list (composite_transition_item ELMOComponent)),
  fixed_byzantine_trace_alt_prop ELMOComponent byzantine_nodes (ELMO_A idx) Message_sender bis btr
    ->
  exists (eis : VLSM.state) (etr : list transition_item),
    finite_valid_trace (composite_vlsm ELMOComponent (ELMO_fixed_equivocation_global_constraint byzantine_nodes)) eis etr
    ∧ SubProjectionTraces.composite_state_sub_projection ELMOComponent
        (elements (list_to_set (finite.enum index) ∖ byzantine_nodes)) eis =
      SubProjectionTraces.composite_state_sub_projection ELMOComponent
        (elements (list_to_set (finite.enum index) ∖ byzantine_nodes)) bis
      ∧ SubProjectionTraces.finite_trace_sub_projection ELMOComponent
          (elements (list_to_set (finite.enum index) ∖ byzantine_nodes)) etr =
        SubProjectionTraces.finite_trace_sub_projection ELMOComponent
          (elements (list_to_set (finite.enum index) ∖ byzantine_nodes)) btr.
Proof.
  intros ? Hlimited ? ? Hfixed.
  eapply validator_fixed_byzantine_traces_equivocation_char in Hfixed
    as (eis & etr & Hetr & Hpr_eis & Hpr_etr);
    [exists eis, etr; split_and!; [| done..] |..]; cycle 1.
  - by intros ? **; inversion 1.
  - by apply ELMO_channel_authentication_prop.
  - typeclasses eauto.
  - by apply ELMOComponent_message_dependencies_full_node_condition.
  - intros i Hi.
    apply component_projection_validator_is_message_validator,
      component_projection_validator_constraint_subsumption with
        (constraint1 := ELMO_fixed_equivocation_global_constraint byzantine_nodes);
      [| by apply ELMOComponents_fixed_equivocation_validating].
    by apply ELMO_fixed_equivocation_subsumption.
  - revert Hetr.
    by apply VLSM_eq_finite_valid_trace, ELMO_fixed_equivocation_VLSM_eq.
Qed.

End sec_elmo_byzantine.