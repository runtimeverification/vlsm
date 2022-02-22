From stdpp Require Import prelude finite.
From Coq Require Import FunctionalExtensionality.
From VLSM.Lib Require Import Preamble StdppListSet FinFunExtras ListExtras.
From VLSM.Core Require Import VLSM MessageDependencies VLSMProjections Composition ProjectionTraces SubProjectionTraces ByzantineTraces Validator Equivocation EquivocationProjections.
From VLSM.Core.Equivocation Require Import NoEquivocation FixedSetEquivocation MsgDepFixedSetEquivocation.

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

Section sec_fixed_byzantine_traces.

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
  (non_byzantine : set index := set_diff (enum index) byzantine)
  .

Section sec_fixed_byzantine_replacements.

Context
  (byzantine_replacements_IM : sub_index byzantine -> VLSM message)
  (no_initial_messages_in_byzantine_IM : no_initial_messages_in_IM_prop byzantine_replacements_IM)
  (can_emit_signed_byzantine : channel_authentication_prop byzantine_replacements_IM (sub_IM_A byzantine A) (sub_IM_sender byzantine A sender))
  .

(** Given a collection of nodes indexed by an <<index>>, we define the
associated fixed byzantine collection of nodes by replacing the nodes
corresponding to the indices in a given <<byzantine>> with byzantine nodes,
i.e., nodes which can emit any (signed) message.
*)
Definition fixed_byzantine_IM
  : index -> VLSM message :=
  update_IM IM byzantine byzantine_replacements_IM.

Lemma fixed_byzantine_IM_no_initial_messages
  : forall i m, ~vinitial_message_prop (fixed_byzantine_IM i) m.
Proof.
  unfold fixed_byzantine_IM, update_IM. simpl.
  intros i m Hm.
  case_decide as Hi.
  - eapply no_initial_messages_in_byzantine_IM; eassumption.
  - eapply no_initial_messages_in_IM; eassumption.
Qed.

Lemma fixed_byzantine_IM_preserves_channel_authentication
: channel_authentication_prop fixed_byzantine_IM A sender.
Proof.
  unfold fixed_byzantine_IM, update_IM. simpl.
  intros i m Hm.
  case_decide.
  - apply can_emit_signed_byzantine in Hm. revert Hm.
    unfold channel_authenticated_message, sub_IM_A, sub_IM_sender.
    destruct (sender m) as [v|]; [|inversion 1].
    case_decide as HAv; [|inversion 1].
    cbn.
    intro Heq; apply Some_inj, dec_sig_eq_iff in Heq; cbn in *.
    congruence.
  - apply can_emit_signed; assumption.
Qed.

Definition fixed_byzantine_IM_sender_safety
  : sender_safety_alt_prop fixed_byzantine_IM A sender :=
  channel_authentication_sender_safety fixed_byzantine_IM A sender
    fixed_byzantine_IM_preserves_channel_authentication.

(** Constraint requiring only that the non-byzantine nodes are not equivocating.
*)
Definition non_byzantine_not_equivocating_constraint
  : composite_label fixed_byzantine_IM -> composite_state fixed_byzantine_IM * option message -> Prop :=
  sub_IM_not_equivocating_constraint fixed_byzantine_IM non_byzantine A sender.

Definition fixed_byzantine_composite_vlsm : VLSM message :=
  composite_vlsm fixed_byzantine_IM non_byzantine_not_equivocating_constraint.

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
  pre_loaded_with_all_messages_vlsm (free_composite_vlsm (sub_IM fixed_byzantine_IM non_byzantine)).

Lemma pre_loaded_fixed_non_byzantine_vlsm'_projection
  : VLSM_projection fixed_byzantine_composite_vlsm pre_loaded_fixed_non_byzantine_vlsm'
    (composite_label_sub_projection_option fixed_byzantine_IM non_byzantine)
    (composite_state_sub_projection fixed_byzantine_IM non_byzantine).
Proof.
  constructor; [apply induced_sub_projection_is_projection|].
  intros sX trX HtrX.
  apply
    (VLSM_projection_finite_valid_trace
      (induced_sub_projection_is_projection fixed_byzantine_IM non_byzantine _))
    in HtrX.
  revert HtrX.
  apply VLSM_incl_finite_valid_trace.
  apply induced_sub_projection_preloaded_free_incl.
Qed.

Definition pre_loaded_fixed_non_byzantine_vlsm : VLSM message :=
  pre_loaded_with_all_messages_vlsm (free_composite_vlsm (sub_IM IM non_byzantine)).

Definition non_byzantine_nodes_same sub_i
  : sub_IM fixed_byzantine_IM non_byzantine sub_i = sub_IM IM non_byzantine sub_i.
Proof.
  unfold sub_IM, fixed_byzantine_IM, update_IM; cbn.
  case_decide as Hi; [|reflexivity].
  exfalso.
  eapply selection_complement_index_not_in_selection; eassumption.
Defined.

Definition non_byzantine_nodes_same_sym := same_IM_sym non_byzantine_nodes_same.

Lemma pre_loaded_fixed_non_byzantine_vlsm_full_projection
  : VLSM_full_projection
    pre_loaded_fixed_non_byzantine_vlsm'
    pre_loaded_fixed_non_byzantine_vlsm
    (same_IM_label_rew non_byzantine_nodes_same)
    (same_IM_state_rew non_byzantine_nodes_same).
Proof.
  apply same_IM_preloaded_free_full_projection.
Qed.

Lemma pre_loaded_fixed_non_byzantine_vlsm_full_projection'
  : VLSM_full_projection
    pre_loaded_fixed_non_byzantine_vlsm
    pre_loaded_fixed_non_byzantine_vlsm'
    (same_IM_label_rew non_byzantine_nodes_same_sym)
    (same_IM_state_rew non_byzantine_nodes_same_sym).
Proof.
  apply same_IM_preloaded_free_full_projection.
Qed.

Definition pre_loaded_fixed_non_byzantine_label_projection :=
  (mbind (Some ∘ (same_IM_label_rew non_byzantine_nodes_same))) ∘
    (composite_label_sub_projection_option fixed_byzantine_IM non_byzantine).

Definition pre_loaded_fixed_non_byzantine_state_projection :=
  (same_IM_state_rew non_byzantine_nodes_same) ∘
    (composite_state_sub_projection fixed_byzantine_IM non_byzantine).

Lemma pre_loaded_fixed_non_byzantine_vlsm_projection
  : VLSM_projection fixed_byzantine_composite_vlsm pre_loaded_fixed_non_byzantine_vlsm
    pre_loaded_fixed_non_byzantine_label_projection
    pre_loaded_fixed_non_byzantine_state_projection.
Proof.
  apply (@VLSM_projection_composition _ _ _ pre_loaded_fixed_non_byzantine_vlsm _ _ pre_loaded_fixed_non_byzantine_vlsm'_projection),
    @VLSM_full_projection_is_projection, pre_loaded_fixed_non_byzantine_vlsm_full_projection.
Qed.

Definition pre_loaded_fixed_non_byzantine_label_component_projection i :=
  (mbind (sub_label_element_project IM non_byzantine i)) ∘
    pre_loaded_fixed_non_byzantine_label_projection.

Definition pre_loaded_fixed_non_byzantine_state_component_projection i (Hi : i ∈ non_byzantine) :=
  sub_state_element_project IM non_byzantine i Hi ∘
    pre_loaded_fixed_non_byzantine_state_projection.

Lemma pre_loaded_fixed_non_byzantine_vlsm_component_projection i (Hi : i ∈ non_byzantine)
  : VLSM_projection fixed_byzantine_composite_vlsm (pre_loaded_with_all_messages_vlsm (IM i))
    (pre_loaded_fixed_non_byzantine_label_component_projection i)
    (pre_loaded_fixed_non_byzantine_state_component_projection i Hi).
Proof.
  apply (VLSM_projection_composition pre_loaded_fixed_non_byzantine_vlsm_projection (sub_preloaded_all_component_projection IM non_byzantine i Hi _)).
Qed.

(** ** Byzantine traces characterization as projections. *)

Section sec_fixed_non_byzantine_projection.

Definition fixed_non_byzantine_projection : VLSM message :=
  induced_sub_projection fixed_byzantine_IM non_byzantine non_byzantine_not_equivocating_constraint.

Lemma fixed_non_byzantine_projection_initial_state_preservation
  : forall s, vinitial_state_prop fixed_non_byzantine_projection s <->
    composite_initial_state_prop (sub_IM fixed_byzantine_IM non_byzantine) s.
Proof.
  split.
  - intros (sX & HeqsX & Hinitial) sub_i; subst.
    apply Hinitial.
  - intros Hs.
    eexists; split.
    + apply composite_state_sub_projection_lift_to.
    + apply (lift_sub_state_initial fixed_byzantine_IM); assumption.
Qed.

Lemma fixed_non_byzantine_projection_incl_preloaded
  : VLSM_incl fixed_non_byzantine_projection (pre_loaded_with_all_messages_vlsm (free_composite_vlsm (sub_IM fixed_byzantine_IM non_byzantine))).
Proof.
  apply basic_VLSM_strong_incl; intros ? *.
  - apply fixed_non_byzantine_projection_initial_state_preservation.
  - intros _; compute; trivial.
  - split; [|exact I].
    eapply induced_sub_projection_valid_preservation; eassumption.
  - intro Ht; apply induced_sub_projection_transition_preservation in Ht; assumption.
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
  apply induced_sub_projection_friendliness, induced_sub_projection_lift.
  intros s1 s2 Heq l [m|]; [|intuition]; cbn.
  destruct (sender m) as [v|]; [|intuition]; cbn.
  case_decide as HAv; [|intuition].
  replace (s2 (A v)) with (s1 (A v)); [intuition|].
  apply (equal_f_dep Heq (dexist (A v) HAv)).
Qed.

End sec_fixed_non_byzantine_projection.

End sec_fixed_byzantine_replacements.


Definition byzantine_replacements : Type :=
  { byzantine_replacements_IM : sub_index byzantine -> VLSM message |
    no_initial_messages_in_IM_prop byzantine_replacements_IM /\
    channel_authentication_prop byzantine_replacements_IM (sub_IM_A byzantine A) (sub_IM_sender byzantine A sender)
  }.

(** The first definition of the [fixed_byzantine_trace_prop]erty:

Fixed byzantine traces are projections to the subset of protocol-following nodes
of traces which are valid for the composition in which a fixed set of nodes
were replaced by byzantine nodes and the rest are protocol-following
(i.e., they are not equivocating).
*)
Definition fixed_byzantine_trace : Type :=
  { byz_IM : byzantine_replacements & { istr |
    finite_valid_trace (fixed_byzantine_composite_vlsm (` byz_IM)) istr.1 istr.2}}.

Definition trace_exposed_to_fixed_byzantine_behavior_prop
  (is : composite_state (sub_IM IM non_byzantine))
  (tr : list (composite_transition_item (sub_IM IM non_byzantine)))
  : Prop :=
  exists byz_tr : fixed_byzantine_trace,
    match byz_tr with
      existT (exist _ byz_IM _) (exist _ (byzantine_is, byzantine_tr) _) =>
      pre_loaded_fixed_non_byzantine_state_projection byz_IM byzantine_is = is /\
      VLSM_projection_trace_project (pre_loaded_fixed_non_byzantine_vlsm_projection byz_IM) byzantine_tr = tr
    end.

End sec_fixed_byzantine_traces.

Section fixed_non_equivocating_vs_byzantine.

Context
  {message : Type}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  `{Hbs : forall i : index, HasBeenSentCapability (IM i)}
  `{Hbr : forall i : index, HasBeenReceivedCapability (IM i)}
  (selection : set index)
  {validator : Type}
  (A : validator -> index)
  (sender : message -> option validator)
  (selection_complement := set_diff (enum index) selection)
  (Fixed : VLSM message := fixed_equivocation_vlsm_composition IM selection)
  (StrongFixed := strong_fixed_equivocation_vlsm_composition IM selection)
  (FixedNonEquivocating : VLSM message := induced_sub_projection IM selection_complement (fixed_equivocation_constraint IM selection))
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  (can_emit_signed : channel_authentication_prop IM A sender)
  (Hsender_safety : sender_safety_alt_prop IM A sender :=
    channel_authentication_sender_safety IM A sender can_emit_signed)
  .

Definition byzantine_id_replacements_same_IM
  : forall i, fixed_byzantine_IM IM selection (fun sub_i => IM (` sub_i)) i = IM i
  := update_IM_id_same_IM IM selection.

Definition byzantine_id_replacements_same_IM_sym := same_IM_sym byzantine_id_replacements_same_IM.

Lemma byzantine_id_replacements_full_projection
  : VLSM_full_projection
    (fixed_byzantine_composite_vlsm IM selection A sender (fun sub_i => IM (` sub_i)))
    (composite_vlsm IM (sub_IM_not_equivocating_constraint IM selection_complement A sender))
    (same_IM_label_rew byzantine_id_replacements_same_IM)
    (same_IM_state_rew byzantine_id_replacements_same_IM).
Proof.
  apply same_IM_full_projection; intros s Hs l [m|]; [|trivial].
  subst selection_complement
  ; unfold non_byzantine_not_equivocating_constraint,
    sub_IM_not_equivocating_constraint.
  destruct (sender m) as [v|]; [|trivial]; cbn.
  case_decide as HAv; [|trivial].
  unfold sub_IM, fixed_byzantine_IM; cbn; intro Hsent.
  eapply VLSM_full_projection_has_been_sent in Hsent
  ; [eassumption|apply same_VLSM_preloaded_full_projection|].
  eapply VLSM_projection_valid_state in Hs
  ; [| apply preloaded_component_projection with (j := A v)].
  assumption.
Qed.

Lemma byzantine_id_replacements_full_projection_rev
  : VLSM_full_projection
    (composite_vlsm IM (sub_IM_not_equivocating_constraint IM selection_complement A sender))
    (fixed_byzantine_composite_vlsm IM selection A sender (fun sub_i => IM (` sub_i)))
    (same_IM_label_rew byzantine_id_replacements_same_IM_sym)
    (same_IM_state_rew byzantine_id_replacements_same_IM_sym).
Proof.
  apply same_IM_full_projection; intros s Hs l [m|]; [|trivial].
  subst selection_complement
  ; unfold non_byzantine_not_equivocating_constraint,
    sub_IM_not_equivocating_constraint.
  destruct (sender m) as [v|]; [|trivial]; cbn.
  case_decide as HAv; [|trivial].
  unfold sub_IM, fixed_byzantine_IM; cbn; intro Hsent.
  eapply VLSM_full_projection_has_been_sent in Hsent
  ; [eassumption|apply same_VLSM_preloaded_full_projection|].
  eapply VLSM_projection_valid_state in Hs
  ; [| apply preloaded_component_projection with (j := A v)].
  assumption.
Qed.

Lemma fixed_sub_IM_non_equivocating_subsumption
  : input_valid_constraint_subsumption IM
    (fixed_equivocation_constraint IM selection)
    (sub_IM_not_equivocating_constraint IM selection_complement A sender).
Proof.
  intros l (s, [m|]) Hv; cbn; [|trivial].
  apply (fixed_strong_equivocation_subsumption IM selection)
    in Hv as Hstrong_v.
  destruct Hv as (Hs & _).
  destruct (sender m) as [v|] eqn:Hsender; cbn; [|trivial].
  case_decide as HAv; [|trivial].
  unfold sub_IM; cbn.
  destruct Hstrong_v as [(i & Hi & Hsent) | Hemitted]; cycle 1.
  - exfalso; apply set_diff_elim2 in HAv; contradict HAv.
    eapply (sub_can_emit_sender IM); eassumption.
  - eapply VLSM_incl_valid_state in Hs; [|apply constraint_free_incl].
    apply
      (VLSM_incl_valid_state
        (vlsm_incl_pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM)))
      in Hs.
    cut (@has_been_sent _ _ (Hbs (A v)) (s (A v)) m).
    { eapply has_been_sent_irrelevance,
       valid_state_project_preloaded_to_preloaded, Hs.
    }
    eapply valid_state_has_trace in Hs as (is & tr & Htr).
    eapply (has_been_sent_iff_by_sender IM). 1-3: eassumption.
    eexists; eassumption.
Qed.

Lemma fixed_non_equivocating_incl_sub_non_equivocating
  : VLSM_incl FixedNonEquivocating
      (induced_sub_projection IM (set_diff (enum index) selection)
        (sub_IM_not_equivocating_constraint IM
          (set_diff (enum index) selection) A sender)).
Proof.
  apply induced_sub_projection_constraint_subsumption_incl,
    fixed_sub_IM_non_equivocating_subsumption.
Qed.

Lemma Fixed_sub_IM_non_equivocating_incl
  : VLSM_incl Fixed (composite_vlsm IM (sub_IM_not_equivocating_constraint IM selection_complement A sender)).
Proof.
  apply constraint_subsumption_incl, fixed_sub_IM_non_equivocating_subsumption.
Qed.

Lemma fixed_equivocating_traces_are_byzantine_component i (Hi : i ∈ set_diff (enum index) selection)
  : byzantine_id_replacements_same_IM_sym i
  =
    non_byzantine_nodes_same_sym IM selection (fun sub_i => IM (`sub_i)) (dexist i Hi).
Proof.
  unfold byzantine_id_replacements_same_IM_sym,
    non_byzantine_nodes_same_sym, same_IM_sym
  ; f_equal.
  unfold byzantine_id_replacements_same_IM, non_byzantine_nodes_same,
    update_IM_id_same_IM, fixed_byzantine_IM, update_IM; cbn.
  apply set_diff_elim2 in Hi as Hni.
  case_decide; [contradiction|reflexivity].
Qed.

Lemma fixed_equivocating_traces_are_byzantine_label l
  : pre_loaded_fixed_non_byzantine_label_projection IM selection (fun sub_i => IM (`sub_i))
    (same_IM_label_rew byzantine_id_replacements_same_IM_sym l)
  =
    composite_label_sub_projection_option IM selection_complement l.
Proof.
  destruct l as (i, li).
  unfold pre_loaded_fixed_non_byzantine_label_projection,
    composite_label_sub_projection_option, composite_label_sub_projection, same_IM_label_rew
  ; subst selection_complement; cbn.
  case_decide as Hi; [|reflexivity]; cbn.
  do 2 f_equal.
  rewrite <- same_VLSM_label_rew_21
    with (Heq := non_byzantine_nodes_same IM selection (fun sub_i => IM (`sub_i)) (dexist i Hi)).
  do 2 f_equal.
  apply fixed_equivocating_traces_are_byzantine_component.
Qed.

Lemma fixed_equivocating_traces_are_byzantine_state s
  : pre_loaded_fixed_non_byzantine_state_projection IM selection (fun sub_i => IM (`sub_i))
    (same_IM_state_rew byzantine_id_replacements_same_IM_sym s)
  =
    composite_state_sub_projection IM selection_complement s.
Proof.
  unfold pre_loaded_fixed_non_byzantine_state_projection,
    composite_state_sub_projection, same_IM_state_rew.
  extensionality sub_i; cbn.
  rewrite <- same_VLSM_state_rew_21
    with (Heq := non_byzantine_nodes_same IM selection (fun sub_i => IM (`sub_i)) sub_i).
  f_equal; destruct_dec_sig sub_i i Hi Heqsub_i; subst; cbn; f_equal.
  apply fixed_equivocating_traces_are_byzantine_component.
Qed.

Lemma fixed_equivocating_traces_are_byzantine_trace tr
: VLSM_projection_trace_project
  (pre_loaded_fixed_non_byzantine_vlsm_projection IM selection A sender (fun sub_i => IM (`sub_i)))
  (VLSM_full_projection_finite_trace_project byzantine_id_replacements_full_projection_rev tr)
=
  finite_trace_sub_projection IM selection_complement tr.
Proof.
  induction tr; [reflexivity|]; cbn; rewrite IHtr.
  replace (pre_VLSM_projection_transition_item_project _ _ _ _ _) with
    (pre_VLSM_projection_transition_item_project (composite_type IM)
    (composite_type (sub_IM IM selection_complement))
    (composite_label_sub_projection_option IM selection_complement)
    (composite_state_sub_projection IM selection_complement) a)
  ; [reflexivity|].
  destruct a; unfold pre_VLSM_projection_transition_item_project; cbn.
  rewrite fixed_equivocating_traces_are_byzantine_state,
    fixed_equivocating_traces_are_byzantine_label.
  reflexivity.
Qed.

Program Definition fixed_equivocating_traces_are_byzantine_replacements
  : byzantine_replacements selection A sender :=
  exist _ (fun sub_i => IM (` sub_i)) _.
Next Obligation.
  split.
  - apply sub_IM_preserves_no_initial_messages; assumption.
  - apply sub_IM_preserves_channel_authentication; assumption.
Qed.

Program Definition fixed_equivocating_traces_are_byzantine_traces eis etr
  (Htr : finite_valid_trace Fixed eis etr)
  : fixed_byzantine_trace IM selection A sender :=
  (existT fixed_equivocating_traces_are_byzantine_replacements
    (exist _
      (same_IM_state_rew byzantine_id_replacements_same_IM_sym eis,
      VLSM_full_projection_finite_trace_project byzantine_id_replacements_full_projection_rev etr)
      _)).
Next Obligation.
  intros; cbn.
  apply (VLSM_full_projection_finite_valid_trace byzantine_id_replacements_full_projection_rev).
  revert Htr; apply VLSM_incl_finite_valid_trace.
  apply Fixed_sub_IM_non_equivocating_incl.
Qed.

Lemma fixed_equivocating_traces_are_byzantine eis etr
  : finite_valid_trace Fixed eis etr ->
    trace_exposed_to_fixed_byzantine_behavior_prop IM selection A sender
      (composite_state_sub_projection IM selection_complement eis)
      (finite_trace_sub_projection IM selection_complement etr).
Proof.
  intros Htr.
  exists (fixed_equivocating_traces_are_byzantine_traces _ _ Htr); cbn; split.
  - apply fixed_equivocating_traces_are_byzantine_state.
  - apply fixed_equivocating_traces_are_byzantine_trace.
Qed.

Context
  (Hvalidator:
    forall i : index, i ∉ selection ->
    component_message_validator_prop IM (fixed_equivocation_constraint IM selection) i)
  .

Lemma fixed_byzantine_traces_are_equivocating
  (byz_tr : fixed_byzantine_trace IM selection A sender)
  : match byz_tr with
      existT (exist _ byz_IM _) (exist _ (byzantine_is, byzantine_tr) _) =>
      exists eis, composite_state_sub_projection IM selection_complement eis = pre_loaded_fixed_non_byzantine_state_projection IM selection byz_IM byzantine_is /\
      exists etr, finite_trace_sub_projection IM selection_complement etr =  VLSM_projection_trace_project (pre_loaded_fixed_non_byzantine_vlsm_projection IM selection A sender byz_IM) byzantine_tr /\
      finite_valid_trace Fixed eis etr
    end.
Proof.
  destruct byz_tr as ((byz_IM & no_initial_byz & can_emit_byz) & (byz_is, byz_tr) & Hbyz_tr); cbn in *.
  eexists; split; [apply composite_state_sub_projection_lift|].
  eexists; split; [apply composite_trace_sub_projection_lift|].
  assert
    (Hinit : composite_initial_state_prop IM
      (lift_sub_state IM selection_complement
        (pre_loaded_fixed_non_byzantine_state_projection IM selection byz_IM byz_is))).
  { destruct Hbyz_tr as [_ Hinit]
    ; eapply VLSM_projection_initial_state in Hinit
    ; [| apply pre_loaded_fixed_non_byzantine_vlsm_projection].
    apply lift_sub_state_initial; assumption.
  }
  split; [|assumption].
  induction Hbyz_tr using finite_valid_trace_rev_ind
  ; [constructor; apply initial_state_is_valid; assumption|].
  specialize (IHHbyz_tr Hinit).
  unfold VLSM_projection_trace_project, pre_VLSM_projection_finite_trace_project;
    rewrite map_option_app.
  unfold pre_VLSM_full_projection_finite_trace_project; rewrite map_app.
  apply finite_valid_trace_from_app_iff; split; [assumption|]; cbn.
  remember (finite_trace_last (lift_sub_state _ _ _) _) as lst.
  assert (Hlst : valid_state_prop Fixed lst)
    by (subst; apply finite_valid_trace_last_pstate; assumption).
  destruct l as (i, li); unfold pre_VLSM_projection_transition_item_project, pre_loaded_fixed_non_byzantine_label_projection, composite_label_sub_projection_option; cbn.
  case_decide as Hi; [|constructor; assumption]; cbn.
  unfold composite_label_sub_projection; cbn.
  apply finite_valid_trace_singleton; cbn.
  repeat split.
  - assumption.
  - destruct iom as [im|]; [|apply option_valid_message_None].
    apply set_diff_elim2 in Hi as Hni.
    specialize (VLSM_projection_input_valid_transition (pre_loaded_fixed_non_byzantine_vlsm_component_projection IM selection A sender byz_IM i Hi) (existT i li)) as Hproj.
    remember (pre_loaded_fixed_non_byzantine_label_component_projection _ _ _ _ _) as somelY.
    unfold pre_loaded_fixed_non_byzantine_label_component_projection, pre_loaded_fixed_non_byzantine_label_projection, composite_label_sub_projection_option in HeqsomelY; cbn in HeqsomelY. 
    case_decide as H_i; [|contradiction]; unfold sub_label_element_project in HeqsomelY; cbn in HeqsomelY.
    rewrite decide_True_pi with eq_refl in HeqsomelY; cbn in HeqsomelY; subst somelY.
    specialize (Hproj _ eq_refl _ _ _ _ Hx) as [Hv _]. 
    eapply (Hvalidator i); [assumption|eassumption].
  - destruct Hx as [(_ & _ & Hv & _) _].
    revert Hv; cbn.
    clear -Heqlst Hi.
    subst lst. revert li.
    unfold same_VLSM_label_rew, non_byzantine_nodes_same, fixed_byzantine_IM, update_IM; cbn.
    
  admit.
Admitted.

(*

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
  apply basic_VLSM_incl.
  - intro; intros; apply fixed_non_byzantine_projection_initial_state_preservation; assumption.
  - intros l s m (Hs & _ & Hv) HsY _.
    apply fixed_non_byzantine_projection_valid_no_equivocations
       in Hv as [Hsent | Hseeded].
    + simpl in Hsent, HsY.
      eapply preloaded_composite_sent_valid; eassumption.
    + apply initial_message_is_valid; right; assumption.
  - intros l s om (_ & _ & Hv) _ _; split.
    + eapply induced_sub_projection_valid_preservation; eassumption.
    + split; [|cbv; trivial].
      apply fixed_non_byzantine_projection_valid_no_equivocations; assumption.
  - intros l s om s' om' [_ Ht].
    apply induced_sub_projection_transition_preservation in Ht; assumption.
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
  - apply lift_sub_valid. assumption.
  - clear -Hsender_safety Hc HsX.
    cbn; destruct om as [m |]; [| trivial].
    destruct (sender m) as [v |] eqn: Hsender; [| exact I]; cbn.
    case_decide as HAv; [| trivial].
    cbn in Hc; destruct Hc as [Hsent | Hseeded].
    + unfold lift_sub_state.
      rewrite lift_sub_state_to_eq with (Hi0 := HAv).
      apply (sub_IM_has_been_sent_iff_by_sender fixed_byzantine_IM non_byzantine
              A sender fixed_byzantine_IM_sender_safety)
      ; [| assumption | assumption].
      eapply (VLSM_incl_valid_state); [| eassumption].
      eapply composite_pre_loaded_vlsm_incl_pre_loaded_with_all_messages.
    + contradict HAv; clear -Hseeded Hsender.
      destruct Hseeded as [(i & Hi & Hm) _].
      unfold channel_authenticated_message in Hm.
      rewrite Hsender in Hm.
      inversion Hm; subst; assumption.
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
    assert (Hs0 : valid_state_message_prop X s0 None).
    { apply (valid_initial_state_message X).
      - destruct (composite_s0 fixed_byzantine_IM); assumption.
      - exact I.
    }
    specialize (valid_generated_state_message X _ _ Hs0 _ _ Hs0) as Hgen.
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
are derived from valid messages and protocol validity of the larger
composition; therefore, the following simple result becomes very important.
*)
Lemma pre_loaded_fixed_non_byzantine_vlsm_lift
  : VLSM_full_projection pre_loaded_fixed_non_byzantine_vlsm' (composite_vlsm fixed_byzantine_IM non_byzantine_not_equivocating_constraint)
      (lift_sub_label fixed_byzantine_IM non_byzantine)
      (lift_sub_state fixed_byzantine_IM non_byzantine).
Proof.
  apply basic_VLSM_full_projection.
  - intro; intros; apply pre_loaded_fixed_non_byzantine_vlsm_lift_valid; assumption.
  - intro; intros * []; rapply lift_sub_transition; assumption.
  - intro; intros; apply (lift_sub_state_initial fixed_byzantine_IM); assumption.
  - intro; intros; apply (pre_loaded_fixed_non_byzantine_vlsm_lift_initial_message l s m); assumption.
Qed.

Lemma pre_loaded_fixed_non_byzantine_incl
  : VLSM_incl pre_loaded_fixed_non_byzantine_vlsm' fixed_non_byzantine_projection.
Proof.
  apply basic_VLSM_incl.
  - intro; intros; apply fixed_non_byzantine_projection_initial_state_preservation; assumption.
  - intros l s m Hv _ Him.
    apply initial_message_is_valid.
    apply (pre_loaded_fixed_non_byzantine_vlsm_lift_initial_message l s m).
    1,3: assumption.
    apply (VLSM_full_projection_valid_state pre_loaded_fixed_non_byzantine_vlsm_lift).
    destruct Hv; assumption.
  - intro; intros.
    exists (lift_sub_label fixed_byzantine_IM non_byzantine l).
    exists (lift_sub_state fixed_byzantine_IM non_byzantine s).
    split; [apply composite_label_sub_projection_option_lift|].
    split; [apply composite_state_sub_projection_lift|].
    revert Hv.
    apply (VLSM_full_projection_input_valid pre_loaded_fixed_non_byzantine_vlsm_lift).
  - intros l s om s' om' [_ Ht].
    revert Ht.
    apply @induced_sub_projection_transition_preservation.
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
  (FixedNonEquivocating : VLSM message := induced_sub_projection IM selection_complement (fixed_equivocation_constraint IM selection))
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  (can_emit_signed : channel_authentication_prop IM A sender)
  (Hsender_safety : sender_safety_alt_prop IM A sender :=
    channel_authentication_sender_safety IM A sender can_emit_signed)
  .

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
    2-4: assumption.
    destruct Hnoeqv as [Hsent | Hseeded].
    + eapply preloaded_composite_sent_valid; eassumption.
    + apply initial_message_is_valid.
      right; split; [assumption|].
      eapply induced_sub_projection_valid_projection. apply Hv.
  - intros l s om Hv.
    apply (VLSM_incl_input_valid fixed_non_equivocating_incl_sub_non_equivocating)
       in Hv as (_ & _ & Hv).
    split.
    + revert Hv.
      apply induced_sub_projection_valid_preservation.
    + split; [| exact I].
      apply sub_IM_no_equivocation_preservation in Hv as Hnoequiv.
      2-4: assumption.
      destruct om as [m |]; [| trivial].
      destruct Hnoequiv as [Hsent|Hseeded]; [left; assumption | right].
      split; [assumption|].
      eapply induced_sub_projection_valid_projection. apply Hv.
  - intros l s om s' om' [_ Ht].
    revert Ht.
    apply @induced_sub_projection_transition_preservation.
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
  apply (VLSM_projection_finite_valid_trace Hproj); assumption.
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
  - destruct om as [m|]; [|exact I].
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
      rewrite lift_sub_state_to_eq with (Hi0 := Hi); assumption.
    + right.
      apply emitted_messages_are_valid_iff in HomY.
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
      eapply message_dependencies_are_sufficient in Hiom; [|typeclasses eauto].
      revert Hiom.
      rewrite set_diff_iff in Hi.
      apply not_and_r in Hi as [Hi | Hi]; [elim Hi; apply elem_of_enum|].
      apply dec_stable in Hi.
      apply can_emit_with_more; [assumption|].
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
      rewrite lift_sub_state_to_eq with (Hi0 := Hj); assumption.
Qed.

Lemma preloaded_non_byzantine_vlsm_lift
  : VLSM_full_projection PreNonByzantine (pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM))
      (lift_sub_label IM (set_diff (enum index) selection))
      (lift_sub_state IM (set_diff (enum index) selection)).
Proof.
  apply basic_VLSM_strong_full_projection.
  - intros l s om [Hv _].
    split; [|exact I].
    apply lift_sub_valid; assumption.
  - intro; intros; rapply lift_sub_transition; assumption.
  - intro; intros; apply (lift_sub_state_initial IM); assumption.
  - intro; intros; cbn; trivial.
Qed.

Section assuming_initial_messages_lift.

Context
  (Hfixed_non_byzantine_vlsm_lift_initial_message
    : weak_full_projection_initial_message_preservation PreNonByzantine Fixed
    (lift_sub_state IM (set_diff (enum index) selection))).

(** Since <<FixedNonEquivocating>> is an [induced_projection] of <<Fixed>>,
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
  - intro; intros; apply fixed_non_byzantine_vlsm_lift_valid; assumption.
  - intro; intros * []; rapply lift_sub_transition; assumption.
  - intro; intros; apply (lift_sub_state_initial IM); assumption.
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
    + apply (lift_sub_state_initial IM); assumption.
  - intro; intros.
    apply initial_message_is_valid.
    eapply Hfixed_non_byzantine_vlsm_lift_initial_message.
    1, 3: eassumption.
    destruct Hv as [Hv _].
    eapply VLSM_full_projection_valid_state in Hv; [eassumption|].
    apply fixed_non_byzantine_vlsm_lift_from_initial.
  - intro; intros.
    exists (lift_sub_label IM (set_diff (enum index) selection) l).
    exists (lift_sub_state IM (set_diff (enum index) selection) s).
    split; [apply composite_label_sub_projection_option_lift|].
    split; [apply composite_state_sub_projection_lift|].
    revert Hv.
    apply VLSM_full_projection_input_valid.
    apply fixed_non_byzantine_vlsm_lift_from_initial.
  - intros l s om s' om' [_ Ht].
    apply induced_sub_projection_transition_preservation; assumption.
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
    component_message_validator_prop IM (fixed_equivocation_constraint IM Hbs Hbr selection) i)
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
    eapply Hvalidator; eassumption.
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
    apply (VLSM_eq_finite_valid_trace validator_fixed_non_byzantine_eq_fixed_non_equivocating).
    assumption.
  - apply (VLSM_eq_finite_valid_trace validator_fixed_non_byzantine_eq_fixed_non_equivocating).
    apply fixed_non_equivocating_traces_char.
    assumption.
Qed.

End validator_fixed_set_byzantine.
*)

End fixed_non_equivocating_vs_byzantine.
