From stdpp Require Import prelude finite.
From Coq Require Import FunctionalExtensionality.
From VLSM.Lib Require Import Preamble StdppListSet FinFunExtras ListExtras.
From VLSM Require Import Core.VLSM Core.MessageDependencies Core.VLSMProjections Core.Composition Core.ProjectionTraces Core.SubProjectionTraces Core.ByzantineTraces.
From VLSM Require Import Core.Validating Core.Equivocation Core.EquivocationProjections Core.Equivocation.NoEquivocation Core.Equivocation.FixedSetEquivocation.

(** * VLSM Compositions with a fixed set of byzantine nodes

In this module we study a composition in which a fixed subset of nodes are
replaced by byzantine nodes, i.e., nodes which can send arbitrary
[channel_authenticated_message]s at any time, while the rest are protocol
abiding (non-equivocating) nodes.

We will show that, if the non-byzantine nodes are validating for the
composition with that specific fixed-set of nodes as equivocators, then the
projections of traces to the non-byzantine nodes are precisely the projections
of traces of the composition with that specific fixed-set of nodes as
equivocators to the non-equivocating nodes.

That is, validating non-byzantine nodes do not distinguish between byzantine
nodes and equivocating ones.  Therefore, when analyzing the security of a
protocol it suffices to consider equivocating nodes.
*)

Section emit_any_signed_message_vlsm.

(** ** A machine which can emit any valid message for a given node

This VLSM is similar to the [emit_any_message_vlsm] with the exception of the
validity predicate which requires that the sender of the emitted message
corresponds to the given node.
*)

Context
  {message : Type}
  {index : Type}
  {validator : Type}
  (A : validator -> index)
  (sender : message -> option validator)
  (node_idx : index)
  .

(** The [valid]ity predicate allows sending only signed messages
*)
Definition signed_messages_valid
  (l : @label message all_messages_type)
  (som : @state message all_messages_type * option message)
  : Prop :=
  channel_authenticated_message A sender node_idx l.

Definition emit_any_signed_message_vlsm_machine
  : VLSMClass all_messages_sig
  :=
  {| transition := all_messages_transition
   ; valid := signed_messages_valid
  |}.

Definition emit_any_signed_message_vlsm
    := mk_vlsm emit_any_signed_message_vlsm_machine.

End emit_any_signed_message_vlsm.

Section fixed_byzantine_traces.

Context
  {message : Type}
  `{EqDecision index}
  (IM : index -> VLSM message)
  (Hbs : forall i : index, HasBeenSentCapability (IM i))
  (byzantine : set index)
  {validator : Type}
  (A : validator -> index)
  (sender : message -> option validator)
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  (can_emit_signed : channel_authentication_prop IM A sender)
  (Hsender_safety : sender_safety_alt_prop IM A sender :=
    channel_authentication_sender_safety IM A sender can_emit_signed)
  .

(** Given a collection of nodes indexed by an <<index>>, we define the
associated fixed byzantine collection of nodes by replacing the nodes
corresponding to the indices in a given <<byzantine>> with byzantine nodes,
i.e., nodes which can emit any (signed) message.
*)
Definition fixed_byzantine_IM : index -> VLSM message :=
  update_IM IM byzantine (fun i => emit_any_signed_message_vlsm A sender (` i)).

Lemma fixed_byzantine_IM_no_initial_messages
  : forall i m, ~vinitial_message_prop (fixed_byzantine_IM i) m.
Proof.
  unfold fixed_byzantine_IM, update_IM. simpl.
  intros i m Hm.
  case_decide.
  - cbn in Hm. assumption.
  - elim (no_initial_messages_in_IM i m). assumption.
Qed.

Lemma fixed_byzantine_IM_preserves_channel_authentication
: channel_authentication_prop fixed_byzantine_IM A sender.
Proof.
  unfold fixed_byzantine_IM, update_IM. simpl.
  intros i m Hm.
  case_decide.
  - destruct Hm as [(s0, om) [l [s1 [[_ [_ Hv]] Ht]]]].
    cbn in Hv, Ht.
    unfold signed_messages_valid, channel_authenticated_message in Hv.
    inversion Ht.
    subst; assumption.
  - apply can_emit_signed; assumption.
Qed.

Definition fixed_byzantine_IM_sender_safety
  : sender_safety_alt_prop fixed_byzantine_IM A sender :=
  channel_authentication_sender_safety fixed_byzantine_IM A sender
    fixed_byzantine_IM_preserves_channel_authentication.

Definition message_as_byzantine_label
  (m : message)
  (i : index)
  (Hi : i ∈ byzantine)
  : composite_label fixed_byzantine_IM.
Proof.
  exists i.
  unfold fixed_byzantine_IM, update_IM.
  simpl.
  rewrite decide_True by assumption.
  cbn. exact m.
Defined.

Context
  {finite_index : finite.Finite index}
  (non_byzantine : set index := set_diff (enum index) byzantine)
  .

Definition sub_fixed_byzantine_IM_Hbs
  : forall sub_i : sub_index non_byzantine,
    HasBeenSentCapability (sub_IM fixed_byzantine_IM non_byzantine sub_i)
  := update_IM_complement_Hbs IM byzantine _ Hbs.

(** Constraint requiring only that the non-byzantine nodes are not equivocating.
*)
Definition non_byzantine_not_equivocating_constraint
  : composite_label fixed_byzantine_IM -> composite_state fixed_byzantine_IM * option message -> Prop :=
  sub_IM_not_equivocating_constraint fixed_byzantine_IM non_byzantine A sender sub_fixed_byzantine_IM_Hbs.

(** The first definition of the [fixed_byzantine_trace_prop]erty:

Fixed byzantine traces are projections to the subset of protocol-following nodes
of traces which are protocol for the composition in which a fixed set of nodes
were replaced by byzantine nodes and the rest are protocol-following
(i.e., they are not equivocating).
*)
Definition fixed_byzantine_trace_prop
  (is : composite_state (sub_IM fixed_byzantine_IM non_byzantine))
  (tr : list (composite_transition_item (sub_IM fixed_byzantine_IM non_byzantine)))
  : Prop :=
  exists bis btr,
  finite_protocol_trace (composite_vlsm fixed_byzantine_IM non_byzantine_not_equivocating_constraint) bis btr /\
  composite_state_sub_projection fixed_byzantine_IM non_byzantine bis = is /\
  finite_trace_sub_projection fixed_byzantine_IM non_byzantine btr = tr.

(** ** Byzantine traces characterization as projections. *)

Section fixed_byzantine_traces_as_projections.

Definition fixed_non_byzantine_projection : VLSM message :=
  induced_sub_projection fixed_byzantine_IM non_byzantine non_byzantine_not_equivocating_constraint.

Lemma fixed_non_byzantine_projection_initial_state_preservation
  : forall s, vinitial_state_prop fixed_non_byzantine_projection s <->
    composite_initial_state_prop (sub_IM fixed_byzantine_IM non_byzantine) s.
Proof.
  split.
  - intros Hs sub_i.
    destruct Hs as [sX [HeqsX Hinitial]].
    subst.
    apply Hinitial.
  - intros Hs.
    exists (lift_sub_state fixed_byzantine_IM non_byzantine s).
    split.
    + apply composite_state_sub_projection_lift.
    + apply (lift_sub_state_initial fixed_byzantine_IM non_byzantine); assumption.
Qed.

Lemma fixed_non_byzantine_projection_incl_preloaded
  : VLSM_incl fixed_non_byzantine_projection (pre_loaded_with_all_messages_vlsm (free_composite_vlsm (sub_IM fixed_byzantine_IM non_byzantine))).
Proof.
  apply basic_VLSM_strong_incl; intro; intros.
  - apply fixed_non_byzantine_projection_initial_state_preservation. assumption.
  - exact I.
  - split; [|exact I].
    revert H.
    apply induced_sub_projection_valid_preservation.
  - revert H. apply induced_sub_projection_transition_preservation.
Qed.

Lemma non_byzantine_lift_full_projection
  : VLSM_full_projection fixed_non_byzantine_projection (composite_vlsm fixed_byzantine_IM non_byzantine_not_equivocating_constraint)
    (lift_sub_label fixed_byzantine_IM non_byzantine)
    (lift_sub_state fixed_byzantine_IM non_byzantine).
Proof.
  apply basic_VLSM_full_projection; intro; intros.
  - destruct Hv as [_ [_ [lX [sX [Heql [Heqs [HsX [Hom [Hv Hc]]]]]]]]].
    destruct lX as [i li]. cbn in Hv, Hc.
    unfold composite_label_sub_projection_option in Heql.
    simpl in Heql.
    case_decide; [|congruence].
    inversion Heql. subst l. clear Heql.
    cbn. unfold constrained_composite_valid. cbn.
    unfold lift_sub_state.
    rewrite lift_sub_state_to_eq with (Hi := H).
    subst.
    split; [assumption|].
    destruct om as [m|]; [|exact I].
    destruct (sender m) as [v|]; [|exact I].
    simpl in *.
    case_decide; [|exact I].
    rewrite lift_sub_state_to_eq with (Hi := H0).
    assumption.
  - apply proj2 in H. revert H. cbn.
    destruct (vtransition _ _ _) as (si', _om').
    inversion 1. subst. clear H.
    f_equal.
    extensionality i.
    destruct l as (sub_j, lj).
    destruct_dec_sig sub_j j Hj Heqsub_j.
    subst.
    simpl.
    destruct (decide (i = j)).
    + subst. rewrite state_update_eq.
      unfold lift_sub_state.
      rewrite lift_sub_state_to_eq with (Hi := Hj).
      unfold composite_state_sub_projection.
      simpl.
      rewrite state_update_eq.
      reflexivity.
    + rewrite state_update_neq by congruence.
      destruct (decide (i ∈ non_byzantine)).
      * unfold lift_sub_state.
        rewrite! lift_sub_state_to_eq with (Hi := e).
        unfold composite_state_sub_projection. simpl.
        rewrite state_update_neq by congruence.
        rewrite lift_sub_state_to_eq with (Hi := e).
        reflexivity.
      * unfold lift_sub_state, lift_sub_state_to.
        destruct (decide _); [contradiction|reflexivity].
  - apply (lift_sub_state_initial fixed_byzantine_IM).
    destruct H as [sX [Hs_pr HsX]].
    subst.
    intro sub_i.
    destruct_dec_sig sub_i i Hi Heqsub_i.
    subst. apply HsX.
  - assumption.
Qed.

(** Characterization result for the first definition:
the [fixed_byzantine_trace_prop]erty is equivalent to the
[finite_protocol_trace_prop]erty of the [induced_sub_projection] of the
the composition in which a fixed set of nodes were replaced by byzantine nodes
and the rest are protocol-following to the set of protocol-following nodes.
*)
Lemma fixed_byzantine_trace_char1 is tr
  : fixed_byzantine_trace_prop is tr <->
    finite_protocol_trace fixed_non_byzantine_projection is tr.
Proof.
  split.
  - intros [bis [btr [Hbtr [His Htr]]]].
    subst.
    specialize
      (induced_sub_projection_is_projection
        fixed_byzantine_IM non_byzantine non_byzantine_not_equivocating_constraint)
      as Hproj.
    apply (VLSM_projection_finite_protocol_trace Hproj) in Hbtr.
    replace (finite_trace_sub_projection _ _ _) with (VLSM_projection_trace_project Hproj btr)
    ; [assumption|reflexivity].
  - intro Htr.
    eexists _,_.
    intuition.
    + apply (VLSM_full_projection_finite_protocol_trace non_byzantine_lift_full_projection), Htr.
    + apply composite_state_sub_projection_lift.
    + apply composite_trace_sub_projection_lift.
Qed.

End fixed_byzantine_traces_as_projections.

(** ** Fixed Byzantine traces as traces pre-loaded with signed messages

In this section we'll be showing that byzantine traces correspond to traces of
the composition of nodes in the [non_byzantine], preloaded with messages
signed by the nodes in the <<byzantine>>.
*)

Section fixed_byzantine_traces_as_pre_loaded.

Definition fixed_set_signed_message (m : message) : Prop :=
  non_sub_index_authenticated_message non_byzantine A sender m /\
  (exists i, i ∈ non_byzantine /\ exists l s, protocol_valid (pre_loaded_with_all_messages_vlsm (IM i)) l (s, Some m)).

(**
Given that we're only looking at the composition of nodes in the
[non_byzantine], we can define their subset as either a subset of the
[fixed_byzantine_IM] or of the original <<IM>>.

As it turns out, the first definition is easier to prove equivalent to the
induced [fixed_non_byzantine_projection], while the second is easier to work
with in general because it makes no reference to byzantine nodes.

Therefore we'll first be defining them both below and show that they are
equivalent to each-other using the generic Lemma [same_IM_full_projection].
*)

Definition pre_loaded_fixed_non_byzantine_vlsm' : VLSM message :=
  composite_no_equivocation_vlsm_with_pre_loaded (sub_IM fixed_byzantine_IM non_byzantine) (free_constraint _) sub_fixed_byzantine_IM_Hbs fixed_set_signed_message.

Definition pre_loaded_fixed_non_byzantine_vlsm : VLSM message :=
  composite_no_equivocation_vlsm_with_pre_loaded (sub_IM IM non_byzantine) (free_constraint _) (sub_has_been_sent_capabilities IM non_byzantine Hbs) fixed_set_signed_message.

Lemma non_byzantine_nodes_same
  : forall sub_i, sub_IM fixed_byzantine_IM non_byzantine sub_i = sub_IM IM non_byzantine sub_i.
Proof.
  intro sub_i.
  destruct_dec_sig sub_i i Hi Heqsub_i.
  subst.
  unfold sub_IM, fixed_byzantine_IM, update_IM.
  simpl.
  apply set_diff_elim2 in Hi.
  rewrite decide_False by assumption.
  reflexivity.
Qed.

Lemma non_byzantine_nodes_same_sym
  : forall sub_i, sub_IM IM non_byzantine sub_i = sub_IM fixed_byzantine_IM non_byzantine sub_i.
Proof.
  intro. symmetry. apply non_byzantine_nodes_same.
Qed.

Lemma pre_loaded_fixed_non_byzantine_vlsm_full_projection
  : VLSM_full_projection
    pre_loaded_fixed_non_byzantine_vlsm'
    pre_loaded_fixed_non_byzantine_vlsm
    (same_IM_label_rew non_byzantine_nodes_same)
    (same_IM_state_rew non_byzantine_nodes_same).
Proof.
  apply same_IM_full_projection.
  intros s1 H l1 om H0.
  apply proj1 in H0.
  split; [|exact I].
  destruct om as [m|]; [|exact I].
  destruct H0 as [Hsent | Hseeded]; [|right; assumption].
  cbn. left.
  revert Hsent.
  apply same_IM_composite_has_been_sent_preservation; [|assumption].
  apply stdpp_finite_sub_index; assumption.
Qed.

Lemma pre_loaded_fixed_non_byzantine_vlsm_full_projection'
  : VLSM_full_projection
    pre_loaded_fixed_non_byzantine_vlsm
    pre_loaded_fixed_non_byzantine_vlsm'
    (same_IM_label_rew non_byzantine_nodes_same_sym)
    (same_IM_state_rew non_byzantine_nodes_same_sym).
Proof.
  apply same_IM_full_projection.
  intros s1 H l1 om H0.
  apply proj1 in H0.
  split; [|exact I].
  destruct om as [m|]; [|exact I].
  destruct H0 as [Hsent | Hseeded]; [|right; assumption].
  cbn. left.
  revert Hsent.
  apply same_IM_composite_has_been_sent_preservation; [|assumption].
  apply stdpp_finite_sub_index; assumption.
Qed.

(**
We next show that the [fixed_non_byzantine_projection] and
[pre_loaded_fixed_non_byzantine_vlsm'] are [VLSM_eq]ual.
*)

(** The validity of [fixed_non_byzantine_projection] subsumes
the constraint of [pre_loaded_fixed_non_byzantine_vlsm'].
*)
Lemma fixed_non_byzantine_projection_valid_no_equivocations
  : forall l s om, vvalid fixed_non_byzantine_projection l (s, om) ->
    composite_no_equivocations_except_from
      (sub_IM fixed_byzantine_IM non_byzantine)
      sub_fixed_byzantine_IM_Hbs fixed_set_signed_message
      l (s, om).
Proof.
  intros l s om Hv.
  apply
    (sub_IM_no_equivocation_preservation fixed_byzantine_IM non_byzantine
      A sender fixed_byzantine_IM_sender_safety sub_fixed_byzantine_IM_Hbs
      fixed_byzantine_IM_no_initial_messages fixed_byzantine_IM_preserves_channel_authentication)
    in Hv as Hnoequiv.
  destruct om as [m|]; [|exact I].
  destruct Hnoequiv as [Hsent|Hseeded].
  - left; assumption.
  - right.
    split; [assumption|].
    apply induced_sub_projection_valid_projection in Hv
      as [i [Hi [li [si Hv]]]].
    exists i.
    split; [assumption|].
    revert li si Hv.
    unfold fixed_byzantine_IM, update_IM. simpl.
    apply set_diff_elim2 in Hi.
    rewrite decide_False by assumption.
    intros.
    exists li, si; assumption.
Qed.

Lemma fixed_non_byzantine_pre_loaded_incl
  : VLSM_incl fixed_non_byzantine_projection pre_loaded_fixed_non_byzantine_vlsm'.
Proof.
  apply basic_VLSM_incl; intro; intros.
  - apply fixed_non_byzantine_projection_initial_state_preservation; assumption.
  - destruct Hv as [Hs [_ Hv]].
    apply fixed_non_byzantine_projection_valid_no_equivocations in Hv as
      [Hsent | Hseeded].
    + simpl in Hsent.
      simpl in HsY.
      apply
        (preloaded_composite_sent_protocol (sub_IM fixed_byzantine_IM non_byzantine)
          (finite_sub_index non_byzantine (listing_from_finite index))
          sub_fixed_byzantine_IM_Hbs _ _ _ HsY _ Hsent).
    + apply initial_message_is_protocol. cbn. right. assumption.
  - split.
    + apply proj2,proj2 in Hv.
      revert Hv.
      apply induced_sub_projection_valid_preservation.
    + split; [|exact I].
      apply fixed_non_byzantine_projection_valid_no_equivocations. apply Hv.
  - apply proj2 in H.
    revert H.
    apply induced_sub_projection_transition_preservation.
Qed.

Lemma pre_loaded_fixed_non_byzantine_vlsm_lift_valid
  : weak_full_projection_valid_preservation pre_loaded_fixed_non_byzantine_vlsm'
    (composite_vlsm fixed_byzantine_IM
       non_byzantine_not_equivocating_constraint)
    (lift_sub_label fixed_byzantine_IM non_byzantine)
    (lift_sub_state fixed_byzantine_IM non_byzantine).
Proof.
  intros l s om Hv  HsY HomY.
  destruct l as (sub_i, li).
  destruct_dec_sig sub_i i Hi Heqsub_i.
  subst.
  destruct Hv as [HsX [HomX [Hv [Hc _]]]].
  revert Hv Hc.
  split.
  - revert Hv.
    apply lift_sub_valid.
  - clear -Hsender_safety Hc HsX.
    cbn. destruct om as [m|]; [|exact I].
    destruct (sender m) as [v|] eqn:Hsender; [|exact I].
    simpl.
    case_decide; [|exact I].
    cbn in Hc.
    destruct Hc as [Hsent | Hseeded].
    + unfold lift_sub_state.
      rewrite lift_sub_state_to_eq with (Hi0 := H).
      revert Hsent.
      apply (sub_IM_has_been_sent_iff_by_sender fixed_byzantine_IM non_byzantine
              A sender fixed_byzantine_IM_sender_safety sub_fixed_byzantine_IM_Hbs).
      * apply (VLSM_incl_protocol_state
                (composite_pre_loaded_vlsm_incl_pre_loaded_with_all_messages
                  (sub_IM fixed_byzantine_IM non_byzantine) _ _))
        in HsX. assumption.
      * assumption.
    + exfalso.
      clear -Hseeded Hsender H.
      destruct Hseeded as [[i [Hi Hm]] Hvalid].
      unfold channel_authenticated_message in Hm.
      rewrite Hsender in Hm.
      inversion Hm.
      rewrite H1 in H; contradiction.
Qed.

Lemma pre_loaded_fixed_non_byzantine_vlsm_lift_initial_message
  : weak_full_projection_initial_message_preservation
    pre_loaded_fixed_non_byzantine_vlsm'
    (composite_vlsm fixed_byzantine_IM
       non_byzantine_not_equivocating_constraint)
    (lift_sub_state fixed_byzantine_IM non_byzantine).
Proof.
  intros l s m Hv HsY HmX.
  destruct HmX as [[sub_i [[im Him] Heqm]] | Hseeded].
  - exfalso. clear -no_initial_messages_in_IM Him.
    destruct_dec_sig sub_i i Hi Heqsub_i.
    subst.
    unfold sub_IM, fixed_byzantine_IM, update_IM in Him.
    simpl in Him.
    apply set_diff_elim2 in Hi.
    case_decide; [contradiction|].
    elim (no_initial_messages_in_IM i im).
    assumption.
  - destruct Hseeded as [[i [Hi Hsender]] Hvalid].
    pose (X := (composite_vlsm fixed_byzantine_IM non_byzantine_not_equivocating_constraint)).
    pose (s0 := proj1_sig (composite_s0 fixed_byzantine_IM)).
    assert (Hs0 : protocol_prop X s0 None).
    { apply (protocol_initial X).
      - destruct (composite_s0 fixed_byzantine_IM); assumption.
      - exact I.
    }
    specialize (protocol_generated X _ _ Hs0 _ _ Hs0) as Hgen.
    unfold non_byzantine in Hi.
    rewrite set_diff_iff in Hi.
    apply not_and_r in Hi as [Hi | Hi]; [elim Hi; apply elem_of_enum|].
    apply dec_stable in Hi.
    spec Hgen (message_as_byzantine_label m i Hi).
    spec Hgen.
    { split; [|exact I].
      cbn. unfold fixed_byzantine_IM, update_IM. simpl.
      rewrite @decide_True; assumption.
    }
    cbn in Hgen.
    destruct (vtransition _ _ _) as (si', _om) eqn:Ht.
    specialize (Hgen _ _ eq_refl).
    replace _om with (Some m) in Hgen; [eexists; exact Hgen|].
    clear -Ht.
    revert si' Ht.
    unfold fixed_byzantine_IM, update_IM.
    simpl.
    rewrite @decide_True by assumption.
    cbn. unfold all_messages_transition.
    inversion 1; intuition.
Qed.

(** Since the [fixed_non_byzantine_projection] is an [induced_projection] of
the composition of [fixed_byzantine_IM] with a
[non_byzantine_not_equivocating_constraint], its initial_messages and validity
are derived from protocol messages and protocol validity of the larger
composition; therefore, the following simple result becomes vrey important.
*)
Lemma pre_loaded_fixed_non_byzantine_vlsm_lift
  : VLSM_full_projection pre_loaded_fixed_non_byzantine_vlsm' (composite_vlsm fixed_byzantine_IM non_byzantine_not_equivocating_constraint)
      (lift_sub_label fixed_byzantine_IM non_byzantine)
      (lift_sub_state fixed_byzantine_IM non_byzantine).
Proof.
  apply basic_VLSM_full_projection; intro; intros.
  - apply pre_loaded_fixed_non_byzantine_vlsm_lift_valid; assumption.
  - apply lift_sub_transition. apply H.
  - apply (lift_sub_state_initial fixed_byzantine_IM); assumption.
  - apply (pre_loaded_fixed_non_byzantine_vlsm_lift_initial_message l s m); assumption.
Qed.

Lemma pre_loaded_fixed_non_byzantine_incl
  : VLSM_incl pre_loaded_fixed_non_byzantine_vlsm' fixed_non_byzantine_projection.
Proof.
  apply basic_VLSM_incl; intro; intros.
  - apply fixed_non_byzantine_projection_initial_state_preservation; assumption.
  - apply initial_message_is_protocol.
    apply (pre_loaded_fixed_non_byzantine_vlsm_lift_initial_message l s m).
    + assumption.
    + apply proj1 in Hv. revert Hv.
      apply (VLSM_full_projection_protocol_state pre_loaded_fixed_non_byzantine_vlsm_lift).
    + assumption.
  - exists (lift_sub_label fixed_byzantine_IM non_byzantine l).
    exists (lift_sub_state fixed_byzantine_IM non_byzantine s).
    split; [apply composite_label_sub_projection_option_lift|].
    split; [apply composite_state_sub_projection_lift|].
    revert Hv.
    apply (VLSM_full_projection_protocol_valid pre_loaded_fixed_non_byzantine_vlsm_lift).
  - apply proj2 in H.
    revert H.
    apply induced_sub_projection_transition_preservation.
Qed.

Lemma fixed_non_byzantine_pre_loaded_eq
  : VLSM_eq fixed_non_byzantine_projection pre_loaded_fixed_non_byzantine_vlsm'.
Proof.
  apply VLSM_eq_incl_iff. split.
  - apply fixed_non_byzantine_pre_loaded_incl.
  - apply pre_loaded_fixed_non_byzantine_incl.
Qed.

End fixed_byzantine_traces_as_pre_loaded.

(** The second fixed byzantine trace definition.

Given the equivalence results from Lemmas [fixed_byzantine_trace_char1],
[fixed_non_byzantine_pre_loaded_eq], and
[pre_loaded_fixed_non_byzantine_vlsm_full_projection],
we introduce the following alternate definition to the
[fixed_byzantine_trace_prop]erty, this time defined for (not necessarily valid)
traces of the full composition, accepting any such trace as long as its
projection to the non-byzantine nodes is indistinguishable from a projection
of a valid protocol trace of the composition of [fixed_byzantine_IM] under the
[non_byzantine_not_equivocating_constraint].
*)
Definition fixed_byzantine_trace_alt_prop is tr : Prop :=
  finite_protocol_trace pre_loaded_fixed_non_byzantine_vlsm
    (composite_state_sub_projection IM non_byzantine is)
    (finite_trace_sub_projection IM non_byzantine tr).

End fixed_byzantine_traces.

(** ** Relation between Byzantine nodes and equivocators

In this section we show that while equivocators can always appear as byzantine
to the protocol-abiding nodes, the converse is also true if the protocol-
abiding nodes satisfy the [validating_projection_prop]erty, which basically
allows them to locally verify the authenticity of a received message.
*)

Section fixed_non_equivocating_vs_byzantine.

Context
  {message : Type}
  {index : Type}
  {IndEqDec : EqDecision index}
  (IM : index -> VLSM message)
  (Hbs : forall i : index, HasBeenSentCapability (IM i))
  (Hbr : forall i : index, HasBeenReceivedCapability (IM i))
  (selection : set index)
  {validator : Type}
  (A : validator -> index)
  (sender : message -> option validator)
  {finite_index : finite.Finite index}
  (PreNonByzantine : VLSM message := pre_loaded_fixed_non_byzantine_vlsm IM Hbs selection A sender)
  (Fixed : VLSM message := fixed_equivocation_vlsm_composition IM Hbs Hbr selection)
  (FixedNonEquivocating : VLSM message := induced_sub_projection IM (set_diff (enum index) selection) (fixed_equivocation_constraint IM Hbs Hbr selection))
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  (can_emit_signed : channel_authentication_prop IM A sender)
  (Hsender_safety : sender_safety_alt_prop IM A sender :=
    channel_authentication_sender_safety IM A sender can_emit_signed)
  .

Lemma fixed_non_equivocating_incl_sub_non_equivocating
  : VLSM_incl FixedNonEquivocating
      (induced_sub_projection IM (set_diff (enum index) selection)
        (sub_IM_not_equivocating_constraint IM
          (set_diff (enum index) selection) A sender
          (sub_has_been_sent_capabilities IM
            (set_diff (enum index) selection) Hbs))).
Proof.
  apply induced_sub_projection_constraint_subsumption_incl.
  intros l (s, om) Hv.
  apply (fixed_strong_equivocation_subsumption IM Hbs Hbr (listing_from_finite index) selection)
    in Hv as Hstrong_v.
  destruct Hv as [Hs [Hom [Hv Hc]]].
  destruct om; [|exact I].
  simpl.
  destruct (sender m) as [v|] eqn:Hsender; [|exact I].
  simpl.
  case_decide; [|exact I].
  unfold sub_IM. simpl.
  apply (VLSM_incl_protocol_state (constraint_free_incl IM (fixed_equivocation_constraint IM Hbs Hbr selection))) in Hs.
  apply (VLSM_incl_protocol_state (vlsm_incl_pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM))) in Hs.
  assert (Hpre_si : forall i, protocol_state_prop (pre_loaded_with_all_messages_vlsm (IM i)) (s i)).
  { intro i.
    revert Hs.
    apply protocol_state_project_preloaded_to_preloaded.
  }
  cut (@has_been_sent _ _ (Hbs (A v)) (s (A v)) m).
  { apply has_been_sent_irrelevance; intuition. }
  apply set_diff_elim2 in H.
  destruct Hstrong_v as [Hsent | Hemitted].
  - destruct Hsent as [i [Hi Hsent]].
    apply protocol_state_has_trace in Hs as [is [tr Htr]].
    apply (has_been_sent_iff_by_sender IM Hbs Hsender_safety Htr Hsender).
    exists i; assumption.
  - elim H.
    apply (sub_can_emit_sender IM selection A sender Hsender_safety _ _ _ Hsender Hemitted).
Qed.

Lemma fixed_non_equivocating_incl_fixed_non_byzantine
  : VLSM_incl FixedNonEquivocating PreNonByzantine.
Proof.
  apply basic_VLSM_incl; intro; intros.
  - intros sub_i.
    destruct H as [sX [HeqsX Hinitial]].
    subst.
    apply Hinitial.
  - apply (VLSM_incl_protocol_valid fixed_non_equivocating_incl_sub_non_equivocating) in Hv.
    destruct Hv as [Hs [_ Hv]].
    specialize
      (sub_IM_no_equivocation_preservation IM (set_diff (enum index) selection)
        A sender Hsender_safety (sub_has_been_sent_capabilities IM (set_diff (enum index) selection) Hbs)
        no_initial_messages_in_IM can_emit_signed _ _ _ Hv)
      as [Hsent | Hseeded].
    + simpl in Hsent.
      simpl in HsY.
      apply
        (preloaded_composite_sent_protocol (sub_IM IM (set_diff (enum index) selection))
          (finite_sub_index (set_diff (enum index) selection) (listing_from_finite index))
          (sub_has_been_sent_capabilities IM (set_diff (enum index) selection) Hbs)
          _ _ _ HsY _ Hsent).
    + apply initial_message_is_protocol.
      right.
      split; [assumption|].
      clear -Hv.
      apply induced_sub_projection_valid_projection in Hv; assumption.
  - apply (VLSM_incl_protocol_valid fixed_non_equivocating_incl_sub_non_equivocating),
      proj2, proj2 in Hv.
    split.
    + revert Hv.
      apply induced_sub_projection_valid_preservation.
    + split; [|exact I].
      apply
        (sub_IM_no_equivocation_preservation IM (set_diff (enum index) selection)
          A sender Hsender_safety (sub_has_been_sent_capabilities IM (set_diff (enum index) selection) Hbs)
          no_initial_messages_in_IM can_emit_signed)
        in Hv as Hnoequiv.
      destruct om as [m|]; [|exact I].
      destruct Hnoequiv as [Hsent|Hseeded]; [left; assumption|].
      right.
      split; [assumption|].
      apply induced_sub_projection_valid_projection in Hv; assumption.
  - apply proj2 in H.
    revert H.
    apply induced_sub_projection_transition_preservation.
Qed.

(** As a corollary to the above result, we can conclude that valid protocol
traces for the composition with <<Fixed>> equivocation have the
[fixed_byzantine_trace_alt_prop]erty.
*)
Corollary fixed_equivocating_traces_are_byzantine is tr
  : finite_protocol_trace Fixed is tr ->
    fixed_byzantine_trace_alt_prop IM Hbs selection A sender is tr.
Proof.
  intro Htr.
  apply (VLSM_incl_finite_protocol_trace fixed_non_equivocating_incl_fixed_non_byzantine).
  specialize
    (induced_sub_projection_is_projection
      IM (set_diff (enum index) selection) (fixed_equivocation_constraint IM Hbs Hbr selection))
    as Hproj.
  apply (VLSM_projection_finite_protocol_trace Hproj); assumption.
Qed.

Section validating_fixed_set_byzantine.

Context
  (Hbo := fun i => HasBeenObservedCapability_from_sent_received (IM i))
  (message_dependencies : message -> set message)
  (HMsgDep : forall i, MessageDependencies message_dependencies (IM i))
  (Hfull : forall i, message_dependencies_full_node_condition_prop message_dependencies (IM i))
  .

Lemma fixed_non_byzantine_vlsm_lift_valid
  : weak_full_projection_valid_preservation PreNonByzantine Fixed
    (lift_sub_label IM (set_diff (enum index) selection))
    (lift_sub_state IM (set_diff (enum index) selection)).
Proof.
  intros l s om Hv HsY HomY.
  split.
  - apply lift_sub_valid. apply Hv.
  - destruct om as [m|]; [|exact I].
    apply proj2 in Hv as Hc.
    apply proj2, proj2, proj1 in Hc.
    destruct Hc as [Hsent | Hseeded].
    + left.
      apply composite_has_been_observed_sent_received_iff.
      left.
      simpl in Hsent. clear -Hsent.
      destruct Hsent as [sub_i Hsenti].
      destruct_dec_sig sub_i i Hi Heqsub_i.
      subst.
      exists i.
      unfold lift_sub_state.
      rewrite lift_sub_state_to_eq with (Hi0 := Hi); assumption.
    + right.
      apply can_emit_protocol_iff in HomY.
      destruct HomY as [[_v [[_im Him] Heqim]] | Hiom]
      ; [elim (no_initial_messages_in_IM _v _im); assumption|].
      apply (VLSM_incl_can_emit (vlsm_incl_pre_loaded_with_all_messages_vlsm Fixed))
        in Hiom.
      apply can_emit_composite_project in Hiom as [_v Hiom].
      destruct Hseeded as [[i [Hi Hsigned]] _].
      unfold channel_authenticated_message in Hsigned.
      destruct (sender m) as [v|] eqn:Hsender; simpl in Hsigned; [|congruence].
      apply Some_inj in Hsigned.
      specialize (Hsender_safety _ _ Hsender _ Hiom) as Heq_v.
      rewrite Hsigned in Heq_v. subst _v.
      destruct (HMsgDep i) as [_ Hsufficient].
      apply Hsufficient in Hiom. clear Hsufficient.
      revert Hiom.
      rewrite set_diff_iff in Hi.
      apply not_and_r in Hi as [Hi | Hi]; [elim Hi; apply finite_index|].
      apply dec_stable in Hi.
      apply can_emit_with_more; [assumption|].
      intros dm Hdm.
      apply proj2, proj2, proj1 in Hv.
      destruct l as (sub_j, lj).
      destruct_dec_sig sub_j j Hj Heqsub_j.
      subst sub_j.
      simpl in Hv.
      unfold sub_IM in Hv. simpl in Hv.
      specialize (Hfull j _ _ _ Hv _ Hdm).
      exists j.
      unfold lift_sub_state.
      rewrite lift_sub_state_to_eq with (Hi0 := Hj); assumption.
Qed.

Lemma preloaded_non_byzantine_vlsm_lift
  : VLSM_full_projection PreNonByzantine (pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM))
      (lift_sub_label IM (set_diff (enum index) selection))
      (lift_sub_state IM (set_diff (enum index) selection)).
Proof.
  apply basic_VLSM_strong_full_projection; intro; intros.
  - split; [|exact I].
    apply proj1 in H.
    apply lift_sub_valid; assumption.
  - apply lift_sub_transition; assumption.
  - apply (lift_sub_state_initial IM); assumption.
  - exact I.
Qed.

Section assuming_initial_messages_lift.

Context
  (Hfixed_non_byzantine_vlsm_lift_initial_message
    : weak_full_projection_initial_message_preservation PreNonByzantine Fixed
    (lift_sub_state IM (set_diff (enum index) selection))).

(** Since <<FixedNonEquivocating>> is an [induced_projection] of <<Fixed>>,
its initial_messages and validity are derived from protocol messages and
protocol validity of the larger composition; therefore, the following
result becomes very important.
*)
Lemma fixed_non_byzantine_vlsm_lift_from_initial
  : VLSM_full_projection PreNonByzantine Fixed
      (lift_sub_label IM (set_diff (enum index) selection))
      (lift_sub_state IM (set_diff (enum index) selection)).
Proof.
  apply basic_VLSM_full_projection; intro; intros.
  - apply fixed_non_byzantine_vlsm_lift_valid; assumption.
  - apply lift_sub_transition. apply H.
  - apply (lift_sub_state_initial IM); assumption.
  - apply (Hfixed_non_byzantine_vlsm_lift_initial_message l s m); assumption.
Qed.

Lemma fixed_non_byzantine_incl_fixed_non_equivocating_from_initial
  : VLSM_incl PreNonByzantine FixedNonEquivocating.
Proof.
  apply basic_VLSM_incl; intro; intros.
  - exists (lift_sub_state IM (set_diff (enum index) selection) s).
    split; [apply composite_state_sub_projection_lift|].
    by apply (lift_sub_state_initial IM).
  - apply initial_message_is_protocol.
    apply (Hfixed_non_byzantine_vlsm_lift_initial_message l s m).
    + assumption.
    + apply proj1 in Hv. revert Hv.
      apply (VLSM_full_projection_protocol_state fixed_non_byzantine_vlsm_lift_from_initial).
    + assumption.
  - exists (lift_sub_label IM (set_diff (enum index) selection) l).
    exists (lift_sub_state IM (set_diff (enum index) selection) s).
    split; [apply composite_label_sub_projection_option_lift|].
    split; [apply composite_state_sub_projection_lift|].
    revert Hv.
    apply (VLSM_full_projection_protocol_valid fixed_non_byzantine_vlsm_lift_from_initial).
  - apply proj2 in H.
    revert H.
    apply induced_sub_projection_transition_preservation.
Qed.

Lemma fixed_non_byzantine_eq_fixed_non_equivocating_from_initial
  : VLSM_eq PreNonByzantine FixedNonEquivocating.
Proof.
  apply VLSM_eq_incl_iff.
  split.
  - apply fixed_non_byzantine_incl_fixed_non_equivocating_from_initial.
  - apply fixed_non_equivocating_incl_fixed_non_byzantine.
Qed.

End assuming_initial_messages_lift.

Context
  (Hvalidating:
    forall i : index, i ∉ selection ->
    validating_projection_prop IM (fixed_equivocation_constraint IM Hbs Hbr selection) i)
  .

Lemma validating_fixed_non_byzantine_vlsm_lift_initial_message
  : weak_full_projection_initial_message_preservation PreNonByzantine Fixed
    (lift_sub_state IM (set_diff (enum index) selection)).
Proof.
  intros l s m Hv HsY HmX.
  destruct HmX as [[sub_i [[im Him] Heqm]] | Hseeded].
  - simpl in Heqm. subst.
    destruct_dec_sig sub_i i Hi Heqsub_i.
    subst. unfold sub_IM in Him. simpl in Him.
    clear -Him.
    cbn.
    apply initial_message_is_protocol.
    by exists i, (exist _ m Him).
  - destruct Hseeded as [Hsigned [i [Hi [li [si Hpre_valid]]]]].
    apply set_diff_elim2 in Hi.
    specialize (Hvalidating i Hi _ _ Hpre_valid)
      as [sX [Heqsi [HsX [Hm HvX]]]].
    assumption.
Qed.

(** ** The main result

Assuming that the non-byzantine nodes are validating for the
[fixed_equivocation_constraint] we give the following characterization of traces
with the [fixed_byzantine_trace_alt_prop]erty in terms of equivocation:

A trace has the [fixed_byzantine_trace_alt_prop]erty for a <<selection>> of
byzantine nodes iff there exists a protocol valid trace for the <<Fixed>>
equivocation composition the projections of the two traces to the non-byzantine
nodes, i.e., the nodes in the <<selection_complement>> coincide.
*)
Lemma validating_fixed_byzantine_traces_equivocation_char bis btr
  (selection_complement := set_diff (enum index) selection)
  : fixed_byzantine_trace_alt_prop IM Hbs selection A sender bis btr <->
    exists eis etr,
      finite_protocol_trace Fixed eis etr /\
      composite_state_sub_projection IM selection_complement bis = composite_state_sub_projection IM selection_complement eis /\
      finite_trace_sub_projection IM selection_complement btr = finite_trace_sub_projection IM selection_complement etr.
Proof.
  split.
  - intro Htr.
    specialize (fixed_non_byzantine_vlsm_lift_from_initial validating_fixed_non_byzantine_vlsm_lift_initial_message)
      as Hproj.
    apply (VLSM_full_projection_finite_protocol_trace Hproj) in Htr.
    eexists _,_; split; [exact Htr|].
    unfold lift_sub_state.
    rewrite composite_state_sub_projection_lift.
    split; [reflexivity|].
    symmetry. apply composite_trace_sub_projection_lift.
  - intros [eis [etr [Hetr [Heis_pr Hetr_pr]]]].
    apply fixed_equivocating_traces_are_byzantine in Hetr.
    revert Hetr.
    subst selection_complement.
    unfold fixed_byzantine_trace_alt_prop.
    rewrite Heis_pr, Hetr_pr.
    exact id.
Qed.

(** A characterization at the level of VLSMs: the VLSM corresponding to
the induced projection from a fixed-set byzantine composition to the
non-byzantine components is trace-equivalent to the VLSM corresponding to
the induced projection from the composition of regular nodes under a fixed-set
equivocation constraint to the same components.
*)
Lemma validating_fixed_non_byzantine_eq_fixed_non_equivocating
  : VLSM_eq PreNonByzantine FixedNonEquivocating.
Proof.
  apply fixed_non_byzantine_eq_fixed_non_equivocating_from_initial.
  apply validating_fixed_non_byzantine_vlsm_lift_initial_message.
Qed.

End validating_fixed_set_byzantine.

End fixed_non_equivocating_vs_byzantine.
