From Cdcl Require Import Itauto. Local Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude finite.
From Coq Require Import FunctionalExtensionality.
From VLSM.Lib Require Import Preamble StdppListSet FinFunExtras ListExtras.
From VLSM Require Import Core.VLSM Core.MessageDependencies Core.VLSMProjections Core.Composition Core.ProjectionTraces Core.SubProjectionTraces Core.ByzantineTraces.
From VLSM Require Import Core.Validator Core.Equivocation Core.EquivocationProjections Core.Equivocation.NoEquivocation Core.Equivocation.FixedSetEquivocation.

(** * VLSM Compositions with a fixed set of byzantine nodes

In this module we study a composition in which a fixed subset of nodes are
replaced by byzantine nodes, i.e., nodes which can send arbitrary
[channel_authenticated_message]s at any time, while the rest are protocol
abiding (non-equivocating) nodes.

We will show that, if the non-byzantine nodes are validators for the
composition with that specific fixed-set of nodes as equivocators, then the
projections of traces to the non-byzantine nodes are precisely the projections
of traces of the composition with that specific fixed-set of nodes as
equivocators to the non-equivocating nodes.

That is, non-byzantine validator nodes do not distinguish between byzantine
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
  : VLSMMachine all_messages_type
  :=
  {| initial_state_prop := fun s => True
   ; initial_message_prop := fun m => False
   ; s0 := all_messages_state_inh
   ; transition := all_messages_transition
   ; valid := signed_messages_valid
  |}.

Definition emit_any_signed_message_vlsm
    := mk_vlsm emit_any_signed_message_vlsm_machine.

End emit_any_signed_message_vlsm.

Section fixed_byzantine_traces.

Context
  {message : Type}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  `{forall i : index, HasBeenSentCapability (IM i)}
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
  by case_decide; [|destruct (no_initial_messages_in_IM i m)].
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
    by inversion Ht; subst.
  - by apply can_emit_signed.
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
  by rewrite decide_True.
Defined.

Context
  (non_byzantine : set index := set_diff (enum index) byzantine)
  .

(** Constraint requiring only that the non-byzantine nodes are not equivocating.
*)
Definition non_byzantine_not_equivocating_constraint
  : composite_label fixed_byzantine_IM -> composite_state fixed_byzantine_IM * option message -> Prop :=
  sub_IM_not_equivocating_constraint fixed_byzantine_IM non_byzantine A sender.

(** The first definition of the [fixed_byzantine_trace_prop]erty:

Fixed byzantine traces are projections to the subset of protocol-following nodes
of traces which are valid for the composition in which a fixed set of nodes
were replaced by byzantine nodes and the rest are protocol-following
(i.e., they are not equivocating).
*)
Definition fixed_byzantine_trace_prop
  (is : composite_state (sub_IM fixed_byzantine_IM non_byzantine))
  (tr : list (composite_transition_item (sub_IM fixed_byzantine_IM non_byzantine)))
  : Prop :=
  exists bis btr,
  finite_valid_trace (composite_vlsm fixed_byzantine_IM non_byzantine_not_equivocating_constraint) bis btr /\
  composite_state_sub_projection fixed_byzantine_IM non_byzantine bis = is /\
  finite_trace_sub_projection fixed_byzantine_IM non_byzantine btr = tr.

(** ** Byzantine traces characterization as projections. *)

Section fixed_byzantine_traces_as_projections.

Definition fixed_non_byzantine_projection : VLSM message :=
  pre_induced_sub_projection fixed_byzantine_IM non_byzantine non_byzantine_not_equivocating_constraint.

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
    + apply composite_state_sub_projection_lift_to.
    + by apply (lift_sub_state_initial fixed_byzantine_IM non_byzantine).
Qed.

Lemma fixed_non_byzantine_projection_incl_preloaded
  : VLSM_incl fixed_non_byzantine_projection (pre_loaded_with_all_messages_vlsm (free_composite_vlsm (sub_IM fixed_byzantine_IM non_byzantine))).
Proof.
  apply basic_VLSM_strong_incl.
  - by intros s H1; apply fixed_non_byzantine_projection_initial_state_preservation.
  - by intros m H1; cbv.
  - by split; [eapply induced_sub_projection_valid_preservation|].
  - intros l s om s' om'.
    unfold vtransition, transition, machine.
    cbn [vtransition transition machine vmachine].
    unfold projection_induced_validator_machine.
    unfold pre_loaded_with_all_messages_vlsm_machine.
    (* an ugly trick to get the forward direction from an iff (<->) lemma *)
    by eapply proj1; rapply @induced_sub_projection_transition_preservation.
Qed.

(** The induced projection from the composition of [fixed_byzantine_IM] under
the [non_byzantine_not_equivocating_constraint] to the non-byzantine nodes has
the [projection_friendly_prop]erty.
*)
Lemma fixed_non_byzantine_projection_friendliness
  : projection_friendly_prop
      (induced_sub_projection_is_projection fixed_byzantine_IM non_byzantine
        non_byzantine_not_equivocating_constraint).
Proof.
  apply induced_sub_projection_friendliness.
  apply induced_sub_projection_lift.
  intros s1 s2 Heq l om.
  destruct om as [m|]; [|itauto].
  cbn.
  destruct (sender m) as [v|]; [|itauto].
  simpl.
  case_decide as HAv; [|itauto].
  replace (s2 (A v)) with (s1 (A v)); [itauto|].
  exact (equal_f_dep Heq (dexist (A v) HAv)).
Qed.

(** Characterization result for the first definition:
the [fixed_byzantine_trace_prop]erty is equivalent to the
[finite_valid_trace_prop]erty of the [pre_induced_sub_projection] of the
the composition in which a fixed set of nodes were replaced by byzantine nodes
and the rest are protocol-following to the set of protocol-following nodes.
*)
Lemma fixed_byzantine_trace_char1 is tr
  : fixed_byzantine_trace_prop is tr <->
    finite_valid_trace fixed_non_byzantine_projection is tr.
Proof.
  apply and_comm.
  apply (projection_friendly_trace_char (induced_sub_projection_is_projection _ _ _)).
  apply fixed_non_byzantine_projection_friendliness.
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
  (exists i, i ∈ non_byzantine /\ exists l s, input_valid (pre_loaded_with_all_messages_vlsm (IM i)) l (s, Some m)).

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
  composite_no_equivocation_vlsm_with_pre_loaded (sub_IM fixed_byzantine_IM non_byzantine) (free_constraint _) fixed_set_signed_message.

Definition pre_loaded_fixed_non_byzantine_vlsm : VLSM message :=
  composite_no_equivocation_vlsm_with_pre_loaded (sub_IM IM non_byzantine) (free_constraint _) fixed_set_signed_message.

Lemma non_byzantine_nodes_same
  : forall sub_i, sub_IM fixed_byzantine_IM non_byzantine sub_i = sub_IM IM non_byzantine sub_i.
Proof.
  intro sub_i.
  destruct_dec_sig sub_i i Hi Heqsub_i.
  subst.
  unfold sub_IM, fixed_byzantine_IM, update_IM.
  simpl.
  apply set_diff_elim2 in Hi.
  by rewrite decide_False.
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
  intros s1 Hs1 l1 om [Hom _].
  split; [| done].
  destruct om as [m |]; [| done].
  destruct Hom as [Hsent | Hseeded]; [left | by right].
  by eapply same_IM_composite_has_been_sent_preservation.
Qed.

Lemma pre_loaded_fixed_non_byzantine_vlsm_full_projection'
  : VLSM_full_projection
    pre_loaded_fixed_non_byzantine_vlsm
    pre_loaded_fixed_non_byzantine_vlsm'
    (same_IM_label_rew non_byzantine_nodes_same_sym)
    (same_IM_state_rew non_byzantine_nodes_same_sym).
Proof.
  apply same_IM_full_projection.
  intros s1 Hs1 l1 om [Hom _].
  split; [| done].
  destruct om as [m |]; [| done].
  destruct Hom as [Hsent | Hseeded]; [left | by right].
  by eapply same_IM_composite_has_been_sent_preservation.
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
      fixed_set_signed_message
      l (s, om).
Proof.
  intros l s om Hv.
  apply
    (sub_IM_no_equivocation_preservation fixed_byzantine_IM non_byzantine
      A sender fixed_byzantine_IM_sender_safety
      fixed_byzantine_IM_no_initial_messages fixed_byzantine_IM_preserves_channel_authentication)
    in Hv as Hnoequiv.
  destruct om as [m|]; [| done].
  destruct Hnoequiv as [Hsent|Hseeded].
  - by left.
  - right.
    split; [done |].
    apply induced_sub_projection_valid_projection in Hv
      as [i [Hi [li [si Hv]]]].
    exists i.
    split; [done |].
    revert li si Hv.
    unfold fixed_byzantine_IM, update_IM. simpl.
    apply set_diff_elim2 in Hi.
    rewrite decide_False by done.
    intros.
    by exists li, si.
Qed.

Lemma fixed_non_byzantine_pre_loaded_incl
  : VLSM_incl fixed_non_byzantine_projection pre_loaded_fixed_non_byzantine_vlsm'.
Proof.
  apply basic_VLSM_incl.
  - by intro; intros; apply fixed_non_byzantine_projection_initial_state_preservation.
  - intros l s m (Hs & _ & Hv) HsY _.
    apply fixed_non_byzantine_projection_valid_no_equivocations
       in Hv as [Hsent | Hseeded].
    + simpl in Hsent, HsY.
      by eapply preloaded_composite_sent_valid.
    + by apply initial_message_is_valid; right.
  - intros l s om (_ & _ & Hv) _ _; split.
    + by eapply induced_sub_projection_valid_preservation.
    + split; [| done].
      by apply fixed_non_byzantine_projection_valid_no_equivocations.
  - intros l s om s' om' [_ Ht]; cbn.
    by apply induced_sub_projection_transition_preservation.
Qed.

Lemma pre_loaded_fixed_non_byzantine_vlsm_lift_valid
  : weak_full_projection_valid_preservation pre_loaded_fixed_non_byzantine_vlsm'
    (composite_vlsm fixed_byzantine_IM
       non_byzantine_not_equivocating_constraint)
    (lift_sub_label fixed_byzantine_IM non_byzantine)
    (lift_sub_state fixed_byzantine_IM non_byzantine).
Proof.
  intros (sub_i, li) s om (HsX & HomX & Hv & Hc & _) HsY HomY.
  destruct_dec_sig sub_i i Hi Heqsub_i; subst.
  split.
  - by apply lift_sub_valid.
  - clear -Hsender_safety Hc HsX.
    cbn; destruct om as [m |]; [| done].
    destruct (sender m) as [v |] eqn: Hsender; [| done]; cbn.
    case_decide as HAv; [| done].
    cbn in Hc; destruct Hc as [Hsent | Hseeded].
    + unfold lift_sub_state.
      rewrite (lift_sub_state_to_eq _ _ _ _ _ HAv).
      apply (sub_IM_has_been_sent_iff_by_sender fixed_byzantine_IM non_byzantine
              A sender fixed_byzantine_IM_sender_safety)
      ; [| done | done].
      eapply (VLSM_incl_valid_state); [| done].
      eapply composite_pre_loaded_vlsm_incl_pre_loaded_with_all_messages.
    + contradict HAv; clear -Hseeded Hsender.
      destruct Hseeded as [(i & Hi & Hm) _].
      unfold channel_authenticated_message in Hm.
      rewrite Hsender in Hm.
      by inversion Hm; subst.
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
    by case_decide; [|destruct (no_initial_messages_in_IM i im)].
  - destruct Hseeded as [[i [Hi Hsender]] Hvalid].
    pose (X := (composite_vlsm fixed_byzantine_IM non_byzantine_not_equivocating_constraint)).
    pose (s0 := proj1_sig (composite_s0 fixed_byzantine_IM)).
    assert (Hs0 : valid_state_message_prop X s0 None).
    { apply (valid_initial_state_message X); [| done].
      by destruct (composite_s0 fixed_byzantine_IM).
    }
    specialize (valid_generated_state_message X _ _ Hs0 _ _ Hs0) as Hgen.
    unfold non_byzantine in Hi.
    rewrite set_diff_iff in Hi.
    apply not_and_r in Hi as [Hi | Hi]; [elim Hi; apply elem_of_enum|].
    apply dec_stable in Hi.
    spec Hgen (message_as_byzantine_label m i Hi).
    spec Hgen.
    { split; [| done].
      cbn. unfold fixed_byzantine_IM, update_IM. simpl.
      by rewrite @decide_True.
    }
    cbn in Hgen.
    destruct (vtransition _ _ _) as (si', _om) eqn:Ht.
    specialize (Hgen _ _ eq_refl).
    replace _om with (Some m) in Hgen; [by eexists |].
    clear -Ht.
    revert si' Ht.
    unfold fixed_byzantine_IM, update_IM.
    simpl.
    rewrite @decide_True by done.
    cbn. unfold all_messages_transition.
    inversion 1; itauto.
Qed.

(** Since the [fixed_non_byzantine_projection] is an [induced_validator] of
the composition of [fixed_byzantine_IM] with a
[non_byzantine_not_equivocating_constraint], its initial_messages and validity
are derived from valid messages and protocol validity of the larger
composition; therefore, the following simple result becomes very important.
*)
Lemma pre_loaded_fixed_non_byzantine_vlsm_lift
  : VLSM_full_projection pre_loaded_fixed_non_byzantine_vlsm' (composite_vlsm fixed_byzantine_IM non_byzantine_not_equivocating_constraint)
      (lift_sub_label fixed_byzantine_IM non_byzantine)
      (lift_sub_state fixed_byzantine_IM non_byzantine).
Proof.
  apply basic_VLSM_full_projection.
  - by intro; intros; apply pre_loaded_fixed_non_byzantine_vlsm_lift_valid.
  - by intro; intros * []; rapply lift_sub_transition.
  - by intro; intros; apply (lift_sub_state_initial fixed_byzantine_IM).
  - by intro; intros; apply (pre_loaded_fixed_non_byzantine_vlsm_lift_initial_message l s m).
Qed.

Lemma pre_loaded_fixed_non_byzantine_incl
  : VLSM_incl pre_loaded_fixed_non_byzantine_vlsm' fixed_non_byzantine_projection.
Proof.
  apply basic_VLSM_incl; cbn.
  - by intro; intros; apply fixed_non_byzantine_projection_initial_state_preservation.
  - by intros l s m Hv _ Him; apply initial_message_is_valid.
  - intros l s om Hv.
    exists (lift_sub_label fixed_byzantine_IM non_byzantine l).
    exists (lift_sub_state fixed_byzantine_IM non_byzantine s).
    split; [apply composite_label_sub_projection_option_lift |].
    split; [apply composite_state_sub_projection_lift |].
    by apply (VLSM_full_projection_input_valid pre_loaded_fixed_non_byzantine_vlsm_lift).
  - intros l s om s' om' [_ Ht].
    by apply induced_sub_projection_transition_preservation.
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
of a valid trace of the composition of [fixed_byzantine_IM] under the
[non_byzantine_not_equivocating_constraint].
*)
Definition fixed_byzantine_trace_alt_prop is tr : Prop :=
  finite_valid_trace pre_loaded_fixed_non_byzantine_vlsm
    (composite_state_sub_projection IM non_byzantine is)
    (finite_trace_sub_projection IM non_byzantine tr).

End fixed_byzantine_traces.

(** ** Relation between Byzantine nodes and equivocators

In this section we show that while equivocators can always appear as byzantine
to the protocol-abiding nodes, the converse is also true if the protocol-
abiding nodes satisfy the [projection_message_validator_prop]erty, which basically
allows them to locally verify the authenticity of a received message.
*)

Section fixed_non_equivocating_vs_byzantine.

Context
  {message : Type}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  `{forall i : index, HasBeenSentCapability (IM i)}
  `{forall i : index, HasBeenReceivedCapability (IM i)}
  (selection : set index)
  {validator : Type}
  (A : validator -> index)
  (sender : message -> option validator)
  (selection_complement := set_diff (enum index) selection)
  (PreNonByzantine : VLSM message := pre_loaded_fixed_non_byzantine_vlsm IM selection A sender)
  (Fixed : VLSM message := fixed_equivocation_vlsm_composition IM selection)
  (FixedNonEquivocating : VLSM message := pre_induced_sub_projection IM selection_complement (fixed_equivocation_constraint IM selection))
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  (can_emit_signed : channel_authentication_prop IM A sender)
  (Hsender_safety : sender_safety_alt_prop IM A sender :=
    channel_authentication_sender_safety IM A sender can_emit_signed)
  .

Lemma fixed_non_equivocating_incl_sub_non_equivocating
  : VLSM_incl FixedNonEquivocating
      (pre_induced_sub_projection IM (set_diff (enum index) selection)
        (sub_IM_not_equivocating_constraint IM
          (set_diff (enum index) selection) A sender)).
Proof.
  apply induced_sub_projection_constraint_subsumption_incl.
  intros l (s, om) Hv.
  apply (fixed_strong_equivocation_subsumption IM selection)
    in Hv as Hstrong_v.
  destruct Hv as (Hs & Hom & Hv & Hc).
  destruct om; [| done].
  cbn; destruct (sender m) as [v |] eqn: Hsender; [| done]; cbn.
  case_decide as HAv; [| done].
  unfold sub_IM; cbn.
  apply (VLSM_incl_valid_state (constraint_free_incl IM (fixed_equivocation_constraint IM selection))) in Hs.
  apply (VLSM_incl_valid_state (vlsm_incl_pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM))) in Hs.
  assert (Hpre_si : forall i, valid_state_prop (pre_loaded_with_all_messages_vlsm (IM i)) (s i)).
  {
    intro i.
    revert Hs.
    apply valid_state_project_preloaded_to_preloaded.
  }
  apply set_diff_elim2 in HAv.
  destruct Hstrong_v as [(i & Hi & Hsent) | Hemitted].
  - apply valid_state_has_trace in Hs as (is & tr & Htr).
    by eapply has_been_sent_iff_by_sender; [| | | exists i].
  - by contradict HAv; eapply sub_can_emit_sender.
Qed.

Lemma fixed_non_equivocating_incl_fixed_non_byzantine
  : VLSM_incl FixedNonEquivocating PreNonByzantine.
Proof.
  apply basic_VLSM_incl.
  - intros s (sX & <- & Hinitial) sub_i.
    apply Hinitial.
  - intro; intros.
    apply (VLSM_incl_input_valid fixed_non_equivocating_incl_sub_non_equivocating)
      in Hv as (Hs & _ & Hv).
    apply sub_IM_no_equivocation_preservation in Hv as Hnoeqv.
    2-4: done.
    destruct Hnoeqv as [Hsent | Hseeded].
    + by eapply preloaded_composite_sent_valid.
    + apply initial_message_is_valid.
      by right; split; [|eapply induced_sub_projection_valid_projection; apply Hv].
  - intros l s om Hv.
    apply (VLSM_incl_input_valid fixed_non_equivocating_incl_sub_non_equivocating)
       in Hv as (_ & _ & Hv).
    split.
    + by eapply induced_sub_projection_valid_preservation.
    + split; [| done].
      apply sub_IM_no_equivocation_preservation in Hv as Hnoequiv.
      2-4: done.
      destruct om as [m |]; [| done].
      destruct Hnoequiv as [Hsent|Hseeded]; [by left | right].
      by split; [|eapply induced_sub_projection_valid_projection; apply Hv].
  - intros l s om s' om' [_ Ht].
    revert Ht.
    by apply @induced_sub_projection_transition_preservation.
Qed.

(** As a corollary to the above result, we can conclude that valid
traces for the composition with <<Fixed>> equivocation have the
[fixed_byzantine_trace_alt_prop]erty.
*)
Corollary fixed_equivocating_traces_are_byzantine is tr
  : finite_valid_trace Fixed is tr ->
    fixed_byzantine_trace_alt_prop IM selection A sender is tr.
Proof.
  intro Htr.
  apply (VLSM_incl_finite_valid_trace fixed_non_equivocating_incl_fixed_non_byzantine).
  specialize
    (induced_sub_projection_is_projection
      IM (set_diff (enum index) selection) (fixed_equivocation_constraint IM selection))
    as Hproj.
  by apply (VLSM_projection_finite_valid_trace Hproj).
Qed.

Section validator_fixed_set_byzantine.

Context
  (message_dependencies : message -> set message)
  `{forall i, MessageDependencies message_dependencies (IM i)}
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
  - destruct om as [m|]; [| done].
    apply proj2 in Hv as Hc.
    destruct Hc as [_ [_ [Hc _]]].
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
      by rewrite (lift_sub_state_to_eq _ _ _ _ _ Hi).
    + right.
      apply emitted_messages_are_valid_iff in HomY.
      destruct HomY as [[_v [[_im Him] Heqim]] | Hiom]
      ; [by elim (no_initial_messages_in_IM _v _im) |].
      apply (VLSM_incl_can_emit (vlsm_incl_pre_loaded_with_all_messages_vlsm Fixed))
        in Hiom.
      apply can_emit_composite_project in Hiom as [_v Hiom].
      destruct Hseeded as [[i [Hi Hsigned]] _].
      unfold channel_authenticated_message in Hsigned.
      destruct (sender m) as [v|] eqn:Hsender; simpl in Hsigned; [|congruence].
      apply Some_inj in Hsigned.
      specialize (Hsender_safety _ _ Hsender _ Hiom) as Heq_v.
      rewrite Hsigned in Heq_v. subst _v.
      eapply message_dependencies_are_sufficient in Hiom; [|typeclasses eauto].
      revert Hiom.
      rewrite set_diff_iff in Hi.
      apply not_and_r in Hi as [Hi | Hi]; [elim Hi; apply elem_of_enum|].
      apply dec_stable in Hi.
      apply can_emit_with_more; [done |].
      intros dm Hdm.
      destruct Hv as [_ [_ [Hv _]]].
      destruct l as (sub_j, lj).
      destruct_dec_sig sub_j j Hj Heqsub_j.
      subst sub_j.
      simpl in Hv.
      unfold sub_IM in Hv. simpl in Hv.
      specialize (Hfull j _ _ _ Hv _ Hdm).
      exists j.
      unfold lift_sub_state.
      by rewrite (lift_sub_state_to_eq _ _ _ _ _ Hj).
Qed.

Lemma preloaded_non_byzantine_vlsm_lift
  : VLSM_full_projection PreNonByzantine (pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM))
      (lift_sub_label IM (set_diff (enum index) selection))
      (lift_sub_state IM (set_diff (enum index) selection)).
Proof.
  apply basic_VLSM_strong_full_projection; [| | | done].
  - intros l s om [Hv _].
    by split; [apply lift_sub_valid|].
  - by intro; intros; rapply lift_sub_transition.
  - by intro; intros; apply (lift_sub_state_initial IM).
Qed.

Section assuming_initial_messages_lift.

Context
  (Hfixed_non_byzantine_vlsm_lift_initial_message
    : weak_full_projection_initial_message_preservation PreNonByzantine Fixed
    (lift_sub_state IM (set_diff (enum index) selection))).

(** Since <<FixedNonEquivocating>> is an [induced_validator] of <<Fixed>>,
its initial_messages and validity are derived from valid messages and
protocol validity of the larger composition; therefore, the following
result becomes very important.
*)
Lemma fixed_non_byzantine_vlsm_lift_from_initial
  : VLSM_full_projection PreNonByzantine Fixed
      (lift_sub_label IM (set_diff (enum index) selection))
      (lift_sub_state IM (set_diff (enum index) selection)).
Proof.
  apply basic_VLSM_full_projection.
  - by intro; intros; apply fixed_non_byzantine_vlsm_lift_valid.
  - by intro; intros * []; rapply lift_sub_transition.
  - by intro; intros; apply (lift_sub_state_initial IM).
  - intros; apply Hfixed_non_byzantine_vlsm_lift_initial_message.
Qed.

Lemma fixed_non_byzantine_incl_fixed_non_equivocating_from_initial
  : VLSM_incl PreNonByzantine FixedNonEquivocating.
Proof.
  apply basic_VLSM_incl.
  - intro; intros.
    exists (lift_sub_state IM (set_diff (enum index) selection) s).
    split.
    + apply composite_state_sub_projection_lift_to.
    + by apply (lift_sub_state_initial IM).
  - by intro; intros; apply initial_message_is_valid.
  - intros l s om Hv HsY HomY.
    exists (lift_sub_label IM (set_diff (enum index) selection) l).
    exists (lift_sub_state IM (set_diff (enum index) selection) s).
    split; [apply composite_label_sub_projection_option_lift |].
    split; [apply composite_state_sub_projection_lift |].
    apply @VLSM_full_projection_input_valid; [| done].
    apply fixed_non_byzantine_vlsm_lift_from_initial.
  - intros l s om s' om' [_ Ht].
    by apply induced_sub_projection_transition_preservation.
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
  (Hvalidator:
    forall i : index, i ∉ selection ->
    component_message_validator_prop IM (fixed_equivocation_constraint IM selection) i)
  .

Lemma validator_fixed_non_byzantine_vlsm_lift_initial_message
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
    apply initial_message_is_valid.
    by exists i, (exist _ m Him).
  - destruct Hseeded as [Hsigned [i [Hi [li [si Hpre_valid]]]]].
    apply set_diff_elim2 in Hi.
    by eapply Hvalidator.
Qed.

(** The VLSM corresponding to the induced projection from a fixed-set byzantine
composition to the non-byzantine components is trace-equivalent to the VLSM
corresponding to the induced projection from the composition of regular nodes
under a fixed-set equivocation constraint to the same components.
*)
Lemma validator_fixed_non_byzantine_eq_fixed_non_equivocating
  : VLSM_eq PreNonByzantine FixedNonEquivocating.
Proof.
  apply fixed_non_byzantine_eq_fixed_non_equivocating_from_initial.
  apply validator_fixed_non_byzantine_vlsm_lift_initial_message.
Qed.

(** ** The main result

Assuming that the non-byzantine nodes are validators for the
[fixed_equivocation_constraint] we give the following characterization of traces
with the [fixed_byzantine_trace_alt_prop]erty in terms of equivocation:

A trace has the [fixed_byzantine_trace_alt_prop]erty for a <<selection>> of
byzantine nodes iff there exists a valid trace for the <<Fixed>>
equivocation composition the projections of the two traces to the non-byzantine
nodes, i.e., the nodes in the <<selection_complement>> coincide.
*)
Lemma validator_fixed_byzantine_traces_equivocation_char bis btr
  : fixed_byzantine_trace_alt_prop IM selection A sender bis btr <->
    exists eis etr,
      finite_valid_trace Fixed eis etr /\
      composite_state_sub_projection IM selection_complement eis = composite_state_sub_projection IM selection_complement bis /\
      finite_trace_sub_projection IM selection_complement etr = finite_trace_sub_projection IM selection_complement btr.
Proof.
  unfold fixed_byzantine_trace_alt_prop.
  split; intros Htr.
  - apply fixed_non_equivocating_traces_char.
    by apply (VLSM_eq_finite_valid_trace validator_fixed_non_byzantine_eq_fixed_non_equivocating).
  - apply (VLSM_eq_finite_valid_trace validator_fixed_non_byzantine_eq_fixed_non_equivocating).
    by apply fixed_non_equivocating_traces_char.
Qed.

End validator_fixed_set_byzantine.

End fixed_non_equivocating_vs_byzantine.
