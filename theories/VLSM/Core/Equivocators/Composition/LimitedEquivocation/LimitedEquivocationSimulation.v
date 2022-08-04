From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From Coq Require Import Logic.FinFun Reals.Reals.
From VLSM.Lib Require Import StdppListSet.
From VLSM.Core Require Import VLSM VLSMProjections Composition AnnotatedVLSM.
From VLSM.Core Require Import Equivocation Equivocation.FixedSetEquivocation.
From VLSM.Lib Require Import Measurable.
From VLSM.Core Require Import Equivocation.TraceWiseEquivocation Equivocation.LimitedMessageEquivocation Equivocation.MsgDepLimitedEquivocation.
From VLSM.Core Require Import MessageDependencies Equivocation.WitnessedEquivocation.
From VLSM.Core Require Import Equivocators.Composition.EquivocatorsComposition Equivocators.Composition.EquivocatorsCompositionProjections.
From VLSM.Core Require Import Equivocators.Composition.LimitedEquivocation.LimitedStateEquivocation.
From VLSM.Core Require Import Equivocators.Composition.LimitedEquivocation.FixedEquivocationSimulation.
From VLSM.Core Require Import Equivocators.Composition.LimitedEquivocation.FixedEquivocation.

(** * VLSM Equivocators Simulating limited message equivocation traces

In this module we show that the composition of equivocators with no-message
equivocation and limited state-equivocation can simulate all traces with the
[fixed_limited_equivocation_prop]erty.

As a corollary we show that any state which is valid for the composition
of regular nodes using a [limited_equivocation_constraint] can be
obtained as the projection of a valid state for the composition of
equivocators with no message equivocation and limited state equivocation.
*)

Section fixed_limited_state_equivocation.

Context
  {message : Type}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  `{forall i, HasBeenSentCapability (IM i)}
  `{forall i, HasBeenReceivedCapability (IM i)}
  `{IndThreshold : ReachableThreshold index}
  (Limited : VLSM message := equivocators_limited_equivocations_vlsm IM)
  (equivocating : list index)
  (Fixed : VLSM message := equivocators_fixed_equivocations_vlsm IM equivocating)
  .

(** If the total weight of the equivocators allowed to state-equivocate is less
than the [threshold], then traces of equivocators which are valid w.r.t
the fixed state-equivocation constraint are also valid w.r.t. the
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
  split; [done |].
  unfold not_heavy.
  transitivity (sum_weights (remove_dups equivocating)); [| done].
  remember (composite_transition _ _ _).1. clear Heqc.
  unfold state_has_fixed_equivocation in Hfixed.
  unfold equivocation_fault.
  specialize (equivocating_indices_equivocating_validators IM c)
    as Heq.
  apply sum_weights_subseteq.
  - apply equivocating_validators_nodup.
  - apply NoDup_remove_dups.
  - by intros i Hi; apply elem_of_remove_dups, Hfixed, Heq.
Qed.

End fixed_limited_state_equivocation.

Section limited_equivocation_simulation.

Context
  {message : Type}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  `{forall i, HasBeenSentCapability (IM i)}
  `{forall i, HasBeenReceivedCapability (IM i)}
  `{IndThreshold : ReachableThreshold index}
  (XE : VLSM message := equivocators_limited_equivocations_vlsm IM)
  .

(** If a trace has the [fixed_limited_equivocation_prop]erty, then it can be
simulated by the composition of equivocators with no message-equivocation and
limited state-equivocation.
*)
Lemma limited_equivocators_finite_valid_trace_init_to_rev
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  isX trX
  (HtrX : fixed_limited_equivocation_prop IM isX trX)
  : exists is s tr,
      equivocators_total_state_project IM is = isX /\
      equivocators_total_state_project IM s = finite_trace_last isX trX /\
      equivocators_total_trace_project IM tr = trX /\
      finite_valid_trace_init_to XE is s tr /\
      finite_trace_last_output trX = finite_trace_last_output tr.
Proof.
  destruct HtrX as (equivocating & Hlimited & HtrX).
  eapply VLSM_incl_finite_valid_trace, valid_trace_add_default_last in HtrX
  ; [|eapply VLSM_eq_proj1,Fixed_eq_StrongFixed].
  specialize
    (fixed_equivocators_finite_valid_trace_init_to_rev IM _
      no_initial_messages_in_IM _ _ _ HtrX)
    as (is & s & tr & His & Hs & Htr & Hptr & Houtput).
  exists is, s, tr; split_and?; try itauto.
  revert Hptr; apply VLSM_incl_finite_valid_trace_init_to.
  by apply equivocators_Fixed_incl_Limited.
Qed.

Section sec_equivocators_simulating_annotated_limited.

Context
  (message_dependencies : message -> set message)
  (full_message_dependencies : message -> set message)
  `{FullMessageDependencies message message_dependencies full_message_dependencies}
  `{forall i, MessageDependencies (IM i) message_dependencies}
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  (sender : message -> option index)
  (Hchannel : channel_authentication_prop IM Datatypes.id sender)
  .

Lemma equivocators_limited_valid_trace_projects_to_annotated_limited_equivocation_rev
  isX sX trX
  (HtrX : finite_valid_trace_init_to (msg_dep_limited_equivocation_vlsm IM full_message_dependencies sender) isX sX trX)
  : exists is s tr,
      equivocators_total_state_project IM is = original_state isX /\
      equivocators_total_state_project IM s = original_state sX /\
      equivocators_total_trace_project IM tr =
        pre_VLSM_full_projection_finite_trace_project
          (annotated_type (free_composite_vlsm IM) (set index)) (composite_type IM) Datatypes.id original_state
          trX /\
      finite_valid_trace_init_to XE is s tr /\
      finite_trace_last_output trX = finite_trace_last_output tr.
Proof.
  apply valid_trace_get_last in HtrX as HeqsX.
  eapply valid_trace_forget_last, msg_dep_fixed_limited_equivocation in HtrX; [| done ..].
  apply limited_equivocators_finite_valid_trace_init_to_rev in HtrX
     as (is & s & tr & His_pr & Hpr_s & Htr_pr & Htr & Houtput); [| done].
  exists is, s, tr; subst; split_and!; try itauto.
  - by erewrite Hpr_s, <- pre_VLSM_full_projection_finite_trace_last.
  - by rewrite <- Houtput; apply pre_VLSM_full_projection_finite_trace_last_output.
Qed.

End sec_equivocators_simulating_annotated_limited.

Context
  (sender : message -> option index)
  `{RelDecision _ _ (is_equivocating_tracewise_no_has_been_sent IM (fun i => i) sender)}
  (Limited : VLSM message := tracewise_limited_equivocation_vlsm_composition IM sender)
  (message_dependencies : message -> set message)
  .

(** Any valid state for the composition of reqular nodes under a limited
message-equivocation constraint is the projection of a valid state of
the composition of equivocators under a no message-equivocation and limited
state-equivocation constraint.
*)
Lemma limited_equivocators_valid_state_rev
  (Hwitnessed_equivocation : WitnessedEquivocationCapability IM Datatypes.id sender)
  `{!Irreflexive (msg_dep_happens_before message_dependencies)}
  `{forall i, MessageDependencies (IM i) message_dependencies}
  (Hfull : forall i, message_dependencies_full_node_condition_prop (IM i) message_dependencies)
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  (can_emit_signed : channel_authentication_prop IM Datatypes.id sender)
  : forall sX, valid_state_prop Limited sX ->
    exists s, equivocators_total_state_project IM s = sX /\
    valid_state_prop XE s.
Proof.
  intros sX HsX.
  apply
    (limited_valid_state_has_trace_exhibiting_limited_equivocation IM
      sender message_dependencies Hwitnessed_equivocation Hfull
      no_initial_messages_in_IM can_emit_signed)
    in HsX as (isX & trX & HsX & HtrX).
  apply limited_equivocators_finite_valid_trace_init_to_rev in HtrX
    as (is & s & tr & _ & Hpr_s & _ & Htr & _)
  ; [| done].
  exists s.
  subst. split; [done |].
  by apply valid_trace_last_pstate in Htr.
Qed.

End limited_equivocation_simulation.
