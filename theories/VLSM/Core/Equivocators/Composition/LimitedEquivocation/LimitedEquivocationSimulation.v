From stdpp Require Import prelude.
From Coq Require Import FinFun Reals.
From VLSM Require Import Lib.StdppListSet.
From VLSM Require Import Core.VLSM Core.VLSMProjections Core.Composition Core.ProjectionTraces Core.SubProjectionTraces.
From VLSM Require Import Core.Equivocation Core.EquivocationProjections Core.Equivocation.FixedSetEquivocation Core.Equivocation.NoEquivocation.
From VLSM Require Import Lib.Measurable Core.Equivocation.TraceWiseEquivocation Core.Equivocation.LimitedEquivocation.
From VLSM Require Import MessageDependencies Core.Equivocation.WitnessedEquivocation.
From VLSM Require Import Core.Equivocators.Composition.Common Core.Equivocators.Composition.Projections.
From VLSM Require Import Core.Equivocators.Composition.LimitedEquivocation.LimitedEquivocation.
From VLSM Require Import Core.Equivocators.Composition.LimitedEquivocation.FixedEquivocationSimulation.
From VLSM Require Import Core.Equivocators.Composition.LimitedEquivocation.FixedEquivocation.

(** * VLSM Equivocators Simulating limited message equivocation traces

In this module we show that the composition of equivocators with no-message
equivocation and limited state-equivocation can simulate all traces with the
[fixed_limited_equivocation_prop]erty.

As a corollary we show that any state which is protocol for the composition
of regular nodes using a [limited_equivocation_constraint] can be
obtained as the projection of a protocol state for the composition of
equivocators with no message equivocation and limited state equivocation.
*)

Section fixed_limited_state_equivocation.

Context
  {message : Type}
  {index : Type}
  {IndEqDec : EqDecision index}
  (IM : index -> VLSM message)
  {i0 : Inhabited index}
  (Hbs : forall i, HasBeenSentCapability (IM i))
  (Hbr : forall i, HasBeenReceivedCapability (IM i))
  `{IndThreshold : ReachableThreshold index}
  {index_listing : list index}
  (finite_index : Listing index_listing)
  (Limited : VLSM message := equivocators_limited_equivocations_vlsm IM Hbs finite_index)
  (equivocating : list index)
  (Fixed : VLSM message := equivocators_fixed_equivocations_vlsm IM Hbs index_listing equivocating)
  .

(** If the total weight of the equivocators allowed to state-equivocate is less
than the [threshold], then traces of equivocators which are protocol w.r.t
the fixed state-equivocation constraint are also protocol w.r.t. the
limited state-equivocation constraint.
*)
Lemma equivocators_Fixed_incl_Limited
  (Hlimited : (sum_weights (remove_dups equivocating) <= `threshold)%R)
  : VLSM_incl Fixed Limited.
Proof.
  apply constraint_subsumption_incl.
  apply preloaded_constraint_subsumption_stronger.
  apply strong_constraint_subsumption_strongest.
  intros l (s, om) [Hno_equiv Hfixed].
  split; [assumption|].
  unfold not_heavy.
  transitivity (sum_weights (remove_dups equivocating)); [|assumption].
  remember (composite_transition _ _ _).1. clear Heqc.
  unfold state_has_fixed_equivocation in Hfixed.
  unfold equivocation_fault.
  specialize (equivocating_indices_equivocating_validators IM _ finite_index _ IndThreshold c)
    as Heq.
  apply sum_weights_subseteq.
  - apply equivocating_validators_nodup.
  - apply NoDup_remove_dups.
  - intros i Hi.
    apply elem_of_remove_dups. apply Hfixed. apply Heq. assumption.
Qed.

End fixed_limited_state_equivocation.

Section limited_equivocation_simulation.

Context
  {message : Type}
  {index : Type}
  {IndEqDec : EqDecision index}
  (IM : index -> VLSM message)
  {i0 : Inhabited index}
  (Hbs : forall i, HasBeenSentCapability (IM i))
  (Hbr : forall i, HasBeenReceivedCapability (IM i))
  `{IndThreshold : ReachableThreshold index}
  {index_listing : list index}
  (finite_index : Listing index_listing)
  (XE : VLSM message := equivocators_limited_equivocations_vlsm IM Hbs finite_index)
  .

(** If a trace has the [fixed_limited_equivocation_prop]erty, then it can be
simulated by the composition of equivocators with no message-equivocation and
limited state-equivocation.
*)
Lemma limited_equivocators_finite_protocol_trace_init_to_rev
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  isX trX
  (HtrX : fixed_limited_equivocation_prop IM _ _ isX trX)
  : exists is, equivocators_total_state_project IM is = isX /\
    exists s, equivocators_total_state_project IM s = finite_trace_last isX trX /\
    exists tr, equivocators_total_trace_project IM tr = trX /\
    finite_protocol_trace_init_to XE is s tr /\
    finite_trace_last_output trX = finite_trace_last_output tr.
Proof.
  destruct HtrX as [equivocating [Hlimited HtrX]].
  specialize (Fixed_eq_StrongFixed IM Hbs Hbr finite_index equivocating)
    as Heq.
  apply (VLSM_eq_finite_protocol_trace Heq) in HtrX.
  clear Heq.
  apply ptrace_add_default_last in HtrX.
  specialize
    (fixed_equivocators_finite_protocol_trace_init_to_rev IM Hbs finite_index _
      no_initial_messages_in_IM _ _ _ HtrX)
    as [is [His [s [Hs [tr [Htr [Hptr Houtput]]]]]]].
  exists is. split; [assumption|].
  exists s. split; [assumption|].
  exists tr. split; [assumption|].
  split; [|assumption].
  revert Hptr.
  apply VLSM_incl_finite_protocol_trace_init_to.
  apply equivocators_Fixed_incl_Limited.
  assumption.
Qed.

Context
  (sender : message -> option index)
  {is_equivocating_tracewise_no_has_been_sent_dec : RelDecision (is_equivocating_tracewise_no_has_been_sent IM (fun i => i) sender)}
  (Limited : VLSM message := limited_equivocation_vlsm_composition IM finite_index sender)
  (message_dependencies : message -> set message)
  .

(** Any protocol state for the composition of reqular nodes under a limited
message-equivocation constraint is the projection of a protocol state of
the composition of equivocators under a no message-equivocation and limited
state-equivocation constraint.
*)
Lemma limited_equivocators_protocol_state_rev
  (Hwitnessed_equivocation : WitnessedEquivocationCapability IM Datatypes.id sender finite_index)
  (Hbo := fun i => HasBeenObservedCapability_from_sent_received (IM i))
  (HMsgDep : forall i, MessageDependencies message_dependencies (IM i))
  (Hfull : forall i, message_dependencies_full_node_condition_prop message_dependencies (IM i))
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  (can_emit_signed : channel_authentication_prop IM Datatypes.id sender)
  : forall sX, protocol_state_prop Limited sX ->
    exists s, equivocators_total_state_project IM s = sX /\
    protocol_state_prop XE s.
Proof.
  intros sX HsX.
  apply
    (limited_protocol_state_has_trace_exhibiting_limited_equivocation IM Hbs Hbr finite_index
      sender message_dependencies Hwitnessed_equivocation HMsgDep Hfull
      no_initial_messages_in_IM can_emit_signed)
    in HsX as [isX [trX [HsX HtrX]]].
  apply limited_equivocators_finite_protocol_trace_init_to_rev in HtrX
    as [is [_ [s [Hpr_s [tr [_ [Htr _]]]]]]]
  ; [|assumption].
  exists s.
  subst. split; [assumption|].
  apply ptrace_last_pstate in Htr.
  assumption.
Qed.

End limited_equivocation_simulation.
