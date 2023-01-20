From stdpp Require Import prelude.
From Coq Require Import Reals.
From VLSM.Lib Require Import Measurable.
From VLSM.Core Require Import VLSM Composition ProjectionTraces.
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

Corollary ELMO_fixed_byzantine_traces_equivocation_char :
  forall (byzantine_nodes : Ci), (sum_weights (set_map (D := Ca) idx byzantine_nodes) <= threshold)%R ->
  forall (bis : composite_state ELMOComponent) (btr : list (composite_transition_item ELMOComponent)),
  fixed_byzantine_trace_alt_prop ELMOComponent byzantine_nodes (ELMO_A idx) Message_sender bis btr
    ->
  True.
Proof.
  intros ? Hlimited ? ? Hfixed.
  eapply validator_fixed_byzantine_traces_equivocation_char in Hfixed.
  - done.
  - by intros ? **; inversion 1.
  - by apply ELMO_channel_authentication_prop.
  - typeclasses eauto.
  - by apply ELMOComponent_message_dependencies_full_node_condition.
  -

End sec_elmo_byzantine.