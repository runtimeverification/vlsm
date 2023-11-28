From stdpp Require Import prelude.
From Coq Require Import Reals Lra.
From VLSM.Lib Require Import Measurable.
From VLSM.Core Require Import VLSM Composition ProjectionTraces VLSMProjections.
From VLSM.Core Require Import Equivocation MessageDependencies FixedSetEquivocation.
From VLSM.Core Require Import ReachableThreshold Validator.
From VLSM.Core Require Import ByzantineTraces LimitedByzantineTraces.
From VLSM.Core Require Import MsgDepLimitedEquivocation.
From VLSM.Examples Require Import BaseELMO ELMO.

Section sec_elmo_byzantine.

Context
  {Address : Type}
  `{EqDecision Address}
  `{Measurable Address}
  (threshold : R)
  `{finite.Finite index}
  `{Inhabited index}
  `(idx : index -> Address)
  `{!Inj (=) (=) idx}
  `{!ReachableThreshold (Message_validator idx) (listset (Message_validator idx)) threshold}
  .

#[local] Instance Address_reachable_threshold :
  ReachableThreshold Address (listset Address) threshold.
Proof.
  destruct ReachableThreshold0 as (Hgt0 & vs & Hvs).
  split; [done |].
  exists (set_map proj1_sig vs).
  replace (sum_weights _) with (sum_weights vs); [done |].
  clear Hvs; revert vs; apply set_ind.
  - intros vs1 vs2 Heqv Hvs1.
    replace (sum_weights vs2) with (sum_weights vs1)
      by (apply sum_weights_proper; done).
    by rewrite Hvs1; apply sum_weights_proper; rewrite Heqv.
  - by rewrite !sum_weights_empty.
  - intros v vs Hv Hvs.
    Search sum_weights union.
    rewrite sum_weights_disj_union, Hvs by set_solver.
    replace (sum_weights (set_map _ ({[v]} ∪ _)))
      with (sum_weights (set_map (C := listset (Message_validator idx)) (D := listset Address) proj1_sig {[v]} ∪ set_map (D := listset Address) proj1_sig vs))
      by (apply sum_weights_proper; rewrite set_map_union; done).
    rewrite sum_weights_disj_union; cycle 1.
    + rewrite set_map_singleton.
      cut (` v ∉ set_map (D := listset Address) proj1_sig vs); [by set_solver |].
      contradict Hv.
      apply elem_of_map in Hv as (v' & Hv' & Hv).
      by apply dsig_eq in Hv' as ->.
    + replace (sum_weights (set_map _ {[v]}))
        with (sum_weights (Cv := listset Address) {[` v]});
        [by rewrite !sum_weights_singleton |].
      by apply sum_weights_proper; rewrite set_map_singleton.
Qed.

Context
  (ELMO_component := fun i : index => ELMO_component threshold idx (Ca := listset Address) i)
  (ELMOProtocol := ELMOProtocol threshold idx (Ca := listset Address))
  .

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

Lemma no_initial_messages_in_ELMO_components :
  no_initial_messages_in_IM_prop ELMO_component.
Proof. by intros ? ? ?. Qed.

Lemma ELMO_msg_dep_limited_equivocation_message_validator_prop (i : index) :
  msg_dep_limited_equivocation_message_validator_prop
    (Cv := listset (Message_validator idx))
    ELMO_component threshold
    Message_full_dependencies
    (Message_sender idx)
    i.
Admitted.

Definition ELMO_msg_dep_validator_limited_non_equivocating_byzantine_traces_are_limited_non_equivocating :=
    (msg_dep_validator_limited_non_equivocating_byzantine_traces_are_limited_non_equivocating
      (Ci := listset index)
      ELMO_component threshold
      Message_dependencies Message_full_dependencies
      (Message_sender idx) (ELMO_A idx)
      no_initial_messages_in_ELMO_components
      (ELMO_channel_authentication_prop threshold idx)
      ELMO_msg_dep_limited_equivocation_message_validator_prop
      (ELMO_component_message_dependencies_full_node_condition threshold idx)).

End sec_elmo_byzantine.