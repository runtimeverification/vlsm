From stdpp Require Import prelude.
From Coq Require Import Reals.
From VLSM.Lib Require Import Measurable.
From VLSM.Core Require Import VLSM Composition ProjectionTraces VLSMProjections.
From VLSM.Core Require Import Equivocation MessageDependencies FixedSetEquivocation.
From VLSM.Core Require Import ReachableThreshold Validator.
From VLSM.Core Require Import ByzantineTraces LimitedByzantineTraces.
From VLSM.Examples Require Import BaseELMO ELMO.

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
  (ELMO_component := fun i : index => ELMO_component threshold idx (Ca := Ca) i)
  (ELMOProtocol := ELMOProtocol threshold idx (Ca := Ca))
  `{Set_ (@Message Address) Cm}
  `{Elements Message Cm}
  `{!FinSet (@Message Address) Cm}.

Corollary ELMO_component_byzantine_fault_tolerance :
  forall i : index,
    forall tr, byzantine_trace_prop (ELMO_component i) tr ->
      valid_trace_prop
        (pre_composite_vlsm_induced_projection_validator
          ELMO_component (ELMO_global_constraint threshold idx) i)
        tr.
Proof.
  by intro i; apply validator_component_byzantine_fault_tolerance,
    ELMO_components_validating.
Qed.

Corollary ELMOcomposite_byzantine_traces_are_not_byzantine :
  forall tr, byzantine_trace_prop ELMOProtocol tr -> valid_trace_prop ELMOProtocol tr.
Proof.
  apply composite_validator_byzantine_traces_are_not_byzantine.
  by intro; eapply component_projection_validator_is_message_validator, ELMO_components_validating.
Qed.

Lemma all_is_fine : True.
Proof.
  specialize
    (@msg_dep_validator_limited_non_equivocating_byzantine_traces_are_limited_non_equivocating
      (@Message Address) index Ci _ _ _ _ _ _ _ _ _ _ ELMO_component _ _
      threshold Address Ca _ _ _ _ _ _ _ _ _ _ _
      (listset Message) _ _ _ _ _ _ _ _ _
      Message_dependencies Message_full_dependencies _ _ Message_sender (ELMO_A idx)).
Qed.

End sec_elmo_byzantine.