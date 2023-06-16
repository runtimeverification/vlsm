From VLSM.Lib Require Import Itauto.
From Coq Require Import Reals.
From stdpp Require Import prelude.
From VLSM.Lib Require Import Preamble StdppExtras FinSetExtras.
From VLSM.Lib Require Import ListExtras ListSetExtras Measurable.
From VLSM.Core Require Import VLSM AnnotatedVLSM MessageDependencies VLSMProjections Composition.
From VLSM.Core Require Import Validator ProjectionTraces SubProjectionTraces Equivocation.
From VLSM.Core Require Import Equivocation.FixedSetEquivocation.
From VLSM.Core Require Import Equivocation.LimitedMessageEquivocation.
From VLSM.Core Require Import Equivocation.MsgDepFixedSetEquivocation.
From VLSM.Core Require Import Equivocation.TraceWiseEquivocation.

(**
  To allow capturing the two models of limited equivocation described in the
  sections below, we first define a notion of limited equivocation parameterized
  on a function yielding the set of equivocators induced by a received message,
  other that the message sender.
*)

Section sec_coequivocating_senders_limited_equivocation.

Context
  {message : Type}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  (threshold : R)
  `{ReachableThreshold validator Cv threshold}
  (A : validator -> index)
  (sender : message -> option validator)
  (coequivocating_senders : composite_state IM -> message -> Cv)
  `{forall i, HasBeenSentCapability (IM i)}
  `{forall i, HasBeenReceivedCapability (IM i)}
  .

Definition coeqv_message_equivocators (s : composite_state IM) (m : message)
  : Cv :=
  if decide (composite_has_been_directly_observed IM s m)
  then (* no additional equivocation *)
    ∅
  else (* m itself and all its non-observed dependencies are equivocating. *)
    list_to_set (map_option sender [m] ++ (elements (coequivocating_senders s m))).

Definition coeqv_composite_transition_message_equivocators
  (l : composite_label IM)
  (som : annotated_state (free_composite_vlsm IM) Cv * option message)
  : Cv :=
  match som with
  | (sa, None) => state_annotation sa
  | (sa, Some m) =>
    (state_annotation sa) ∪ (coeqv_message_equivocators (original_state sa) m)
  end.

Definition coeqv_limited_equivocation_constraint
  (l : composite_label IM)
  (som : annotated_state (free_composite_vlsm IM) Cv * option message)
  : Prop :=
  (sum_weights (coeqv_composite_transition_message_equivocators l som) <= threshold)%R.

#[export] Program Instance empty_validators_inhabited : Inhabited {s : Cv | s = ∅} :=
  populate (exist _ ∅ _).
Next Obligation.
Proof. done. Defined.

Definition coeqv_limited_equivocation_vlsm : VLSM message :=
  annotated_vlsm (free_composite_vlsm IM) Cv (fun s => s = ∅)
    coeqv_limited_equivocation_constraint coeqv_composite_transition_message_equivocators.

Definition coeqv_annotate_trace_with_equivocators :=
  annotate_trace (free_composite_vlsm IM) Cv (fun s => s = ∅)
    coeqv_composite_transition_message_equivocators.

Lemma coeqv_limited_equivocation_transition_state_annotation_incl [l s iom s' oom]
  : transition coeqv_limited_equivocation_vlsm l (s, iom) = (s', oom) ->
    state_annotation s ⊆ state_annotation s'.
Proof.
  cbn; unfold annotated_transition; destruct (transition _ _ _) as (_s', _om').
  inversion 1; cbn.
  by destruct iom as [m |]; [apply union_subseteq_l |].
Qed.

Lemma coeqv_limited_equivocation_state_annotation_nodup s
  : valid_state_prop coeqv_limited_equivocation_vlsm s ->
    NoDup (elements (state_annotation s)).
Proof.
  induction 1 using valid_state_prop_ind.
  - by destruct s, Hs as [_ ->]; cbn in *; apply NoDup_elements.
  - destruct Ht as [_ Ht]; cbn in Ht.
    unfold annotated_transition in Ht
    ; destruct (transition _ _ _); inversion Ht; apply NoDup_elements.
Qed.

Lemma coeqv_limited_equivocation_state_not_heavy s
  : valid_state_prop coeqv_limited_equivocation_vlsm s ->
    (sum_weights (state_annotation s) <= threshold)%R.
Proof.
  induction 1 using valid_state_prop_ind.
  - destruct s, Hs as [_ ->]; cbn in *.
    rewrite sum_weights_empty; [| done].
    by apply (rt_positive (H6 := H7)).
  - destruct Ht as [(_ & _ & _ & Hc) Ht]
    ; cbn in Ht; unfold annotated_transition in Ht; destruct (transition _ _ _)
    ; inversion_clear Ht.
    by destruct om as [m |].
Qed.

Definition coeqv_limited_equivocation_projection_validator_prop : index -> Prop :=
  annotated_projection_validator_prop IM (fun s => s = ∅)
    coeqv_limited_equivocation_constraint coeqv_composite_transition_message_equivocators.

Definition coeqv_limited_equivocation_message_validator_prop : index -> Prop :=
  annotated_message_validator_prop IM (fun s => s = ∅)
    coeqv_limited_equivocation_constraint coeqv_composite_transition_message_equivocators.

Definition coeqv_limited_equivocation_projection_validator_prop_alt : index -> Prop :=
  annotated_projection_validator_prop_alt IM (fun s => s = ∅)
    coeqv_limited_equivocation_constraint coeqv_composite_transition_message_equivocators.

End sec_coequivocating_senders_limited_equivocation.

Section sec_msg_dep_limited_equivocation.

Context
  {message : Type}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  `{forall i, HasBeenSentCapability (IM i)}
  `{forall i, HasBeenReceivedCapability (IM i)}
  (threshold : R)
  `{ReachableThreshold validator Cv threshold}
  `{FinSet message Cm}
  (full_message_dependencies : message -> Cm)
  (A : validator -> index)
  (sender : message -> option validator)
  .

Definition not_directly_observed_happens_before_dependencies (s : composite_state IM) (m : message)
  : Cm :=
  filter (fun dm => ~ composite_has_been_directly_observed IM s dm) (full_message_dependencies m).

Definition msg_dep_coequivocating_senders (s : composite_state IM) (m : message)
  : Cv :=
  list_to_set (map_option sender (elements (not_directly_observed_happens_before_dependencies s m))).

Definition msg_dep_limited_equivocation_vlsm : VLSM message :=
  coeqv_limited_equivocation_vlsm IM threshold sender msg_dep_coequivocating_senders.

Definition msg_dep_message_equivocators :=
  coeqv_message_equivocators IM sender msg_dep_coequivocating_senders.

Definition msg_dep_annotate_trace_with_equivocators :=
  coeqv_annotate_trace_with_equivocators IM sender msg_dep_coequivocating_senders.

Lemma msg_dep_annotate_trace_with_equivocators_app : forall sa tr1 tr2,
  msg_dep_annotate_trace_with_equivocators sa (tr1 ++ tr2)
    =
  msg_dep_annotate_trace_with_equivocators sa tr1 ++
    annotate_trace_from (free_composite_vlsm IM) Cv
      (coeqv_composite_transition_message_equivocators IM sender msg_dep_coequivocating_senders)
      (@finite_trace_last _ (annotated_type (free_composite_vlsm IM) Cv)
        {| original_state := sa; state_annotation := ` inhabitant |}
        (msg_dep_annotate_trace_with_equivocators sa tr1)) tr2.
Proof. by intros; apply annotate_trace_from_app. Qed.

Lemma msg_dep_annotate_trace_with_equivocators_last_original_state : forall s s' tr,
  original_state (finite_trace_last s (msg_dep_annotate_trace_with_equivocators s' tr))
    =
  finite_trace_last (original_state s) tr.
Proof. by intros; apply annotate_trace_from_last_original_state. Qed.

Definition msg_dep_composite_transition_message_equivocators :=
  coeqv_composite_transition_message_equivocators IM sender msg_dep_coequivocating_senders.

Definition msg_dep_limited_equivocation_projection_validator_prop :=
  coeqv_limited_equivocation_projection_validator_prop IM threshold sender msg_dep_coequivocating_senders.

Definition msg_dep_limited_equivocation_message_validator_prop :=
  coeqv_limited_equivocation_message_validator_prop IM threshold sender msg_dep_coequivocating_senders.

Definition msg_dep_limited_equivocation_projection_validator_prop_alt :=
  coeqv_limited_equivocation_projection_validator_prop_alt IM threshold sender msg_dep_coequivocating_senders.

Lemma msg_dep_annotate_trace_with_equivocators_project s tr
  : pre_VLSM_embedding_finite_trace_project msg_dep_limited_equivocation_vlsm
    (composite_type IM) Datatypes.id original_state
    (msg_dep_annotate_trace_with_equivocators s tr) = tr.
Proof. by apply (annotate_trace_project (free_composite_vlsm IM) Cv). Qed.

End sec_msg_dep_limited_equivocation.

Section sec_full_node_limited_equivocation.

Context
  {message : Type}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  `{forall i, HasBeenSentCapability (IM i)}
  `{forall i, HasBeenReceivedCapability (IM i)}
  (threshold : R)
  `{ReachableThreshold validator Cv threshold}
  (A : validator -> index)
  (sender : message -> option validator)
  .

Definition full_node_coequivocating_senders (s : composite_state IM) (m : message)
  : Cv := ∅.

Definition full_node_limited_equivocation_vlsm : VLSM message :=
  coeqv_limited_equivocation_vlsm IM threshold sender full_node_coequivocating_senders.

End sec_full_node_limited_equivocation.

Section sec_full_node_msg_dep_limited_equivocation_equivalence.

Context
  {message : Type}
  `{FinSet message Cm}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  `{forall i, HasBeenSentCapability (IM i)}
  `{forall i, HasBeenReceivedCapability (IM i)}
  (full_message_dependencies : message -> Cm)
  (threshold : R)
  `{ReachableThreshold validator Cv threshold}
  `{!LeibnizEquiv Cv}
  (A : validator -> index)
  (sender : message -> option validator)
  (message_dependencies : message -> Cm)
  `{!FullMessageDependencies message_dependencies full_message_dependencies}
  `{forall i, MessageDependencies (IM i) message_dependencies}
  (Hfull : forall i, message_dependencies_full_node_condition_prop (IM i) message_dependencies)
  (Limited := msg_dep_limited_equivocation_vlsm IM threshold full_message_dependencies sender (Cv := Cv))
  (FullNodeLimited := full_node_limited_equivocation_vlsm IM threshold sender (Cv := Cv))
  .

Lemma full_node_msg_dep_coequivocating_senders s m i li
  (Hvalid : input_valid (pre_loaded_with_all_messages_vlsm (IM i)) li (s i, Some m))
  : msg_dep_coequivocating_senders IM full_message_dependencies sender s m ≡@{Cv} ∅.
Proof.
  intro; split; intro Hx; [| by contradict Hx; apply not_elem_of_empty].
  exfalso; contradict Hx.
  unfold msg_dep_coequivocating_senders.
  rewrite elem_of_list_to_set, elem_of_map_option.
  setoid_rewrite elem_of_elements; setoid_rewrite elem_of_filter.
  intros (dm & [Hnobs Hdm]  & _).
  contradict Hnobs; exists i.
  eapply msg_dep_full_node_input_valid_happens_before_has_been_directly_observed;
    [by typeclasses eauto | by apply Hfull | done |].
  by apply full_message_dependencies_happens_before.
Qed.

Lemma annotated_free_input_valid_projection
  iprop `{Inhabited (sig iprop)} constr trans
  i li s om
  : input_valid (annotated_vlsm (free_composite_vlsm IM) Cv iprop constr trans)
      (existT i li) (s, om) ->
    input_valid (pre_loaded_with_all_messages_vlsm (IM i)) li (original_state s i, om).
Proof.
  intro Hvalid.
  eapply (VLSM_projection_input_valid (preloaded_component_projection IM i))
  ; [by apply (composite_project_label_eq IM) |].
  by apply
    (VLSM_incl_input_valid (vlsm_incl_pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM))),
    (VLSM_embedding_input_valid (forget_annotations_projection (free_composite_vlsm IM) _ _ _)).
Qed.

Lemma full_node_msg_dep_composite_transition_message_equivocators
  i li (s : state (annotated_type (free_composite_vlsm IM) Cv)) om
  (Hvalid : input_valid (pre_loaded_with_all_messages_vlsm (IM i)) li (original_state s i, om))
  : coeqv_composite_transition_message_equivocators
      IM sender (full_node_coequivocating_senders IM)
      (existT i li) (s, om)
      ≡
    msg_dep_composite_transition_message_equivocators
      IM full_message_dependencies sender
      (existT i li) (s, om).
Proof.
  destruct om as [m |]; cbn; [| done].
  apply sets.union_proper; [done |].
  unfold coeqv_message_equivocators, msg_dep_coequivocating_senders.
  case_decide as Hobs; [done |].
  remember (list_to_set (map_option _ _)) as equivs.
  cut (equivs ≡@{Cv} ∅); [by intros -> |].
  by subst; eapply full_node_msg_dep_coequivocating_senders.
Qed.

Lemma msg_dep_full_node_valid_iff
  l (s : state (annotated_type (free_composite_vlsm IM) Cv)) om
  (Hvi : input_valid (pre_loaded_with_all_messages_vlsm (IM (projT1 l)))
           (projT2 l) (original_state s (projT1 l), om))
  : valid Limited l (s, om) <-> valid FullNodeLimited l (s, om).
Proof.
  cbn; unfold annotated_valid, coeqv_limited_equivocation_constraint; destruct l as [i li].
  replace (sum_weights _) with
    (sum_weights
      (coeqv_composite_transition_message_equivocators IM sender
        (full_node_coequivocating_senders IM) (existT i li)
        (s, om)));
    [done |].
  by apply sum_weights_proper, full_node_msg_dep_composite_transition_message_equivocators.
Qed.

Lemma msg_dep_full_node_transition_iff
  l (s : state (annotated_type (free_composite_vlsm IM) Cv)) om
  (Hvi : input_valid (pre_loaded_with_all_messages_vlsm (IM (projT1 l)))
           (projT2 l) (original_state s (projT1 l), om))
  : transition Limited l (s, om) = transition FullNodeLimited l (s, om).
Proof.
  cbn; unfold annotated_transition;
    destruct (transition _ _ _) as (s', om'), l as (i, li).
  do 2 f_equal.
  destruct om as [m |]; [| done].
  symmetry.
  by apply leibniz_equiv, full_node_msg_dep_composite_transition_message_equivocators.
Qed.

Lemma msg_dep_full_node_limited_equivocation_vlsm_incl :
  VLSM_incl Limited FullNodeLimited.
Proof.
  apply basic_VLSM_incl.
  - by intros s Hs.
  - by intros _ _ m _ _ Hinit; apply initial_message_is_valid.
  - intros [i li] s om HvX _ _.
    apply msg_dep_full_node_valid_iff; [| apply HvX].
    by eapply annotated_free_input_valid_projection.
  - intros [i li] s iom s' oom [Hv Ht]; cbn in Ht |- *; rewrite <- Ht.
    symmetry; rapply msg_dep_full_node_transition_iff.
    by eapply annotated_free_input_valid_projection.
Qed.

Lemma full_node_msg_dep_limited_equivocation_vlsm_incl :
  VLSM_incl FullNodeLimited Limited.
Proof.
  apply basic_VLSM_incl.
  - by intros s Hs.
  - by intros _ _ m _ _ Hinit; apply initial_message_is_valid.
  - intros [i li] s om HvX _ _.
    apply msg_dep_full_node_valid_iff; [| apply HvX].
    by eapply annotated_free_input_valid_projection.
  - intros [i li] s iom s' oom [Hv Ht]; cbn in Ht |- *; rewrite <- Ht.
    rapply msg_dep_full_node_transition_iff.
    by eapply annotated_free_input_valid_projection.
Qed.

Lemma full_node_msg_dep_limited_equivocation_vlsm_eq :
  VLSM_eq FullNodeLimited Limited.
Proof.
  split.
  - by apply full_node_msg_dep_limited_equivocation_vlsm_incl.
  - by apply msg_dep_full_node_limited_equivocation_vlsm_incl.
Qed.

End sec_full_node_msg_dep_limited_equivocation_equivalence.

Section sec_msg_dep_fixed_limited_equivocation.

Context
  {message : Type}
  `{FinSet index Ci}
  `{!finite.Finite index}
  `{FinSet message Cm}
  (IM : index -> VLSM message)
  `{forall i, HasBeenSentCapability (IM i)}
  `{forall i, HasBeenReceivedCapability (IM i)}
  (message_dependencies : message -> Cm)
  (full_message_dependencies : message -> Cm)
  `{!FullMessageDependencies message_dependencies full_message_dependencies}
  `{forall i, MessageDependencies (IM i) message_dependencies}
  (threshold : R)
  `{ReachableThreshold validator Cv threshold}
  (sender : message -> option validator)
  (A : validator -> index)
  `{!Inj (=) (=) A}
  (Limited := msg_dep_limited_equivocation_vlsm IM threshold full_message_dependencies sender (Cv := Cv))
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  (Hchannel : channel_authentication_prop IM A sender)
  (Hsender_safety : sender_safety_alt_prop IM A sender :=
    channel_authentication_sender_safety _ _ _ Hchannel)
  .

Lemma equivocating_messages_are_equivocator_emitted
  s im
  (Him : can_emit (free_composite_vlsm IM) im)
  (Hnobserved : ¬ composite_has_been_directly_observed IM s im) :
    exists v : validator,
      v ∈ msg_dep_message_equivocators IM full_message_dependencies sender s im (Cv := Cv)
        /\
      can_emit (pre_loaded_vlsm (IM (A v)) (fun dm => msg_dep_rel message_dependencies dm im)) im.
Proof.
  eapply (VLSM_incl_can_emit (vlsm_incl_pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM)))
      in Him.
  apply can_emit_free_composite_project in Him as [j Him].
  apply Hchannel in Him as Hsender.
  unfold channel_authenticated_message in Hsender.
  destruct (sender im) as [v |] eqn: Heq_sender; [| by inversion Hsender].
  apply Some_inj in Hsender; cbn in Hsender; subst.
  exists v; subst; cbn.
  unfold msg_dep_message_equivocators, coeqv_message_equivocators,
         msg_dep_coequivocating_senders, not_directly_observed_happens_before_dependencies.
  rewrite decide_False by done; cbn.
  split.
  - by rewrite Heq_sender, elem_of_list_to_set, elem_of_app; left; left.
  - by eapply message_dependencies_are_sufficient.
Qed.

Lemma equivocating_messages_dependencies_are_directly_observed_or_equivocator_emitted
  s im
  (Him : can_emit (free_composite_vlsm IM) im)
  (Hnobserved : ¬ composite_has_been_directly_observed IM s im)
  : forall dm, msg_dep_happens_before message_dependencies dm im ->
    composite_has_been_directly_observed IM s dm \/
    exists v_i, v_i ∈ msg_dep_message_equivocators IM full_message_dependencies sender s im (Cv := Cv) /\
      can_emit (pre_loaded_with_all_messages_vlsm (IM (A v_i))) dm.
Proof.
  intros dm Hdm.
  destruct (decide (composite_has_been_directly_observed IM s dm)) as [Hobs | Hnobs]
  ; [by left | right].
  cut (exists v, sender dm = Some v /\
                 can_emit (pre_loaded_with_all_messages_vlsm (IM (A v))) dm).
  {
    intros (v & Hsender & Hemit).
    exists v; split; [| done].
    unfold msg_dep_message_equivocators, coeqv_message_equivocators,
      msg_dep_coequivocating_senders, not_directly_observed_happens_before_dependencies.
    rewrite decide_False, elem_of_list_to_set, elem_of_app, elem_of_elements,
      elem_of_list_to_set, !elem_of_map_option by done.
    right; exists dm.
    rewrite elem_of_elements, elem_of_filter.
    by setoid_rewrite full_message_dependencies_happens_before.
  }
  apply emitted_messages_are_valid in Him.
  by eapply msg_dep_happens_before_composite_no_initial_valid_messages_emitted_by_sender.
Qed.

Lemma message_equivocators_can_emit (s : state Limited) im
  (Hs : valid_state_prop
          (fixed_equivocation_vlsm_composition IM (Ci := Ci) (fin_sets.set_map A (state_annotation s)))
          (original_state s))
  (Hnobserved : ¬ composite_has_been_directly_observed IM (original_state s) im)
  (HLemit : can_emit (free_composite_vlsm IM) im)
  : can_emit
      (equivocators_composition_for_directly_observed IM (Ci := Ci)
        (fin_sets.set_map A (state_annotation s
            ∪ msg_dep_message_equivocators IM full_message_dependencies sender
                (original_state s) im))
        (original_state s))
      im.
Proof.
  eapply VLSM_embedding_can_emit.
  - unshelve apply equivocators_composition_for_directly_observed_index_incl_embedding with
      (indices1 := fin_sets.set_map A (msg_dep_message_equivocators IM (Cv := Cv)
        full_message_dependencies sender (original_state s) im)).
    intros x; rewrite !elem_of_elements.
    by apply set_map_mono, union_subseteq_r.
  - destruct (equivocating_messages_are_equivocator_emitted _ _ HLemit Hnobserved)
      as (j & Heqv_j & Hemitj).
    eapply sub_valid_preloaded_lifts_can_be_emitted;
      [by apply elem_of_elements, elem_of_map_2 | | done].
    cbn; intros dm H_dm.
    assert (Hdm : msg_dep_happens_before message_dependencies dm im)
        by (apply msg_dep_happens_before_iff_one; left; done).
    clear H_dm; revert dm Hdm.
    induction dm as [dm Hind] using
      (well_founded_ind (msg_dep_happens_before_wf message_dependencies full_message_dependencies _))
    ; intros Hdm.
    apply emitted_messages_are_valid_iff.
    destruct (equivocating_messages_dependencies_are_directly_observed_or_equivocator_emitted
      _ _ HLemit Hnobserved _ Hdm)
      as [Hobs_dm | (dm_i & Hdm_i & Hemit_dm)]
    ; [by left; right | right].
    eapply sub_valid_preloaded_lifts_can_be_emitted;
      [by apply elem_of_elements, elem_of_map_2 | | by eapply message_dependencies_are_sufficient].
    intros dm' Hdm'; apply Hind.
    + by apply msg_dep_happens_before_iff_one; left.
    + transitivity dm; [| done].
      by apply msg_dep_happens_before_iff_one; left.
Qed.

Lemma msg_dep_fixed_limited_equivocation_witnessed
  is tr
  (Htr : finite_valid_trace Limited is tr)
  (equivocators := state_annotation (finite_trace_last is tr))
  (Fixed := fixed_equivocation_vlsm_composition IM (Ci := Ci) (fin_sets.set_map A equivocators))
  : (sum_weights equivocators <= threshold)%R
      /\
    finite_valid_trace Fixed
      (original_state is)
      (pre_VLSM_embedding_finite_trace_project
        Limited (composite_type IM) Datatypes.id original_state
        tr).
Proof.
  repeat split; [.. | by apply Htr].
  - by eapply coeqv_limited_equivocation_state_not_heavy,
            finite_valid_trace_last_pstate, Htr.
  - apply valid_trace_add_default_last in Htr.
    induction Htr using finite_valid_trace_init_to_rev_ind
    ; [constructor; apply initial_state_is_valid; apply Hsi |].
    setoid_rewrite map_app.
    apply finite_valid_trace_from_app_iff; split.
    + revert IHHtr.
      apply VLSM_incl_finite_valid_trace_from,
        fixed_equivocation_vlsm_composition_index_incl.
      intro; rewrite !elem_of_elements.
      apply set_map_mono; [done |].
      by eapply coeqv_limited_equivocation_transition_state_annotation_incl, Ht.
    + apply finite_valid_trace_singleton.
      unfold input_valid_transition, input_valid.
      change (map _ _) with (pre_VLSM_embedding_finite_trace_project Limited
                              (composite_type IM) Datatypes.id original_state tr).
      rewrite <- pre_VLSM_embedding_finite_trace_last.
      assert (Hs : valid_state_prop
                    (fixed_equivocation_vlsm_composition IM (Ci := Ci) (fin_sets.set_map A (state_annotation s)))
                    (original_state s)).
      {
        replace s with (finite_trace_last si tr) at 2
             by (apply valid_trace_get_last in Htr; done).
        rewrite (pre_VLSM_embedding_finite_trace_last
                  Limited (composite_type IM) Datatypes.id original_state si tr).
        by apply finite_valid_trace_last_pstate.
      }
      destruct Ht as [[HLs [HLim HLv]] HLt].
      cbn in HLt |- *; unfold annotated_transition in HLt; cbn in HLt.
      replace (finite_trace_last si _) with s
           by (apply valid_trace_get_last in Htr; congruence).
      destruct l as [i li], (transition _ _ _) as (si', om').
      inversion HLt; subst; clear HLt; cbn.
      repeat split.
      * revert Hs; apply VLSM_incl_valid_state.
        apply fixed_equivocation_vlsm_composition_index_incl.
        intro; rewrite !elem_of_elements.
        apply set_map_mono; [done |].
        by destruct iom as [im |]; [apply union_subseteq_l |].
      * destruct iom as [im |]
        ; [apply option_valid_message_Some | apply option_valid_message_None].
        destruct (decide (composite_has_been_directly_observed IM (original_state s) im))
              as [Hobs | Hnobs].
        -- eapply composite_directly_observed_valid; [| done].
           revert Hs; apply VLSM_incl_valid_state.
           apply fixed_equivocation_vlsm_composition_index_incl.
           intro; rewrite !elem_of_elements.
           by apply set_map_mono, union_subseteq_l.
        -- revert HLim.
           setoid_rewrite emitted_messages_are_valid_iff.
           intros [Hinit | Hemit]; [by left | right].
           eapply VLSM_weak_embedding_can_emit.
           {
             eapply EquivPreloadedBase_Fixed_weak_embedding
               with (base_s := original_state s).
             - revert Hs; apply VLSM_incl_valid_state.
               apply fixed_equivocation_vlsm_composition_index_incl.
               intro; rewrite !elem_of_elements.
               by apply set_map_mono, union_subseteq_l.
             - by intros; apply no_initial_messages_in_IM.
           }
           eapply VLSM_incl_can_emit.
           {
             apply Equivocators_Fixed_Strong_incl.
             revert Hs; apply VLSM_incl_valid_state.
             apply fixed_equivocation_vlsm_composition_index_incl.
             intro; rewrite !elem_of_elements.
             by apply set_map_mono, union_subseteq_l.
           }
           apply message_equivocators_can_emit; [done | done |].
           eapply VLSM_embedding_can_emit; [| done].
           by apply forget_annotations_projection.
      * by apply HLv.
      * destruct iom as [im |]; [| done].
        destruct (decide (composite_has_been_directly_observed IM (original_state s) im))
              as [Hobs | Hnobs]; [by left | right; cbn].
        apply message_equivocators_can_emit; [done | done |].
        apply emitted_messages_are_valid_iff in HLim
          as [[j [[mj Hmj] Heqim]] | Hemit]
        ; [clear Heqim; contradict Hmj; apply no_initial_messages_in_IM |].
        eapply VLSM_embedding_can_emit; [| done].
        by apply forget_annotations_projection.
Qed.

Corollary msg_dep_fixed_limited_equivocation is tr
  : finite_valid_trace Limited is tr ->
    fixed_limited_equivocation_prop IM threshold A
      (original_state is)
      (pre_VLSM_embedding_finite_trace_project
        Limited (composite_type IM) Datatypes.id original_state
        tr) (Ci := Ci) (Cv := Cv).
Proof.
  intro Htr.
  exists (state_annotation (finite_trace_last is tr)).
  by apply msg_dep_fixed_limited_equivocation_witnessed.
Qed.

Lemma fixed_transition_preserves_annotation_equivocators
  (eqv_validators : Cv)
  (equivocators := fin_sets.set_map A eqv_validators : Ci)
  (is : state (free_composite_vlsm IM)) s tr
  (Htr1 :
    finite_valid_trace_init_to (fixed_equivocation_vlsm_composition IM equivocators)
    is s tr)
  l iom sf oom
  (Ht :
    input_valid_transition
      (fixed_equivocation_vlsm_composition IM equivocators) l
      (s, iom) (sf, oom))
  (Hsub_equivocators :
    state_annotation
      (@finite_trace_last _ Limited
        {| original_state := is; state_annotation := `inhabitant |}
        (msg_dep_annotate_trace_with_equivocators IM full_message_dependencies sender is tr))
    ⊆ eqv_validators)
  : msg_dep_composite_transition_message_equivocators IM
      full_message_dependencies sender l
      (@finite_trace_last _ Limited
        {| original_state := is; state_annotation := ∅ |}
        (annotate_trace_from (free_composite_vlsm IM)
          Cv
          (msg_dep_composite_transition_message_equivocators IM full_message_dependencies sender)
          {| original_state := is; state_annotation := ∅ |} tr), iom)
    ⊆ eqv_validators.
Proof.
  destruct iom as [im |]; [| done].
  apply union_subseteq; split; [done | cbn].
  rewrite annotate_trace_from_last_original_state; cbn.
  replace (finite_trace_last _ _) with s
       by (apply valid_trace_get_last in Htr1; congruence).
  unfold coeqv_message_equivocators.
  case_decide as Hnobserved; [by apply empty_subseteq |].
  destruct Ht as [(Hs & Him & Hv & [Hobs | Hemitted]) Ht]
  ; [done | intros eqv Heqv].
  unfold msg_dep_coequivocating_senders,
         not_directly_observed_happens_before_dependencies in Heqv
  ; rewrite elem_of_list_to_set, elem_of_app,
      elem_of_elements, elem_of_list_to_set, !elem_of_map_option in Heqv
  ; setoid_rewrite elem_of_list_singleton in Heqv
  ; setoid_rewrite elem_of_elements in Heqv
  ; setoid_rewrite elem_of_filter in Heqv.
  destruct Heqv as [(msg & Hmsg & Hsender) | (msg & [Hnobserved_msg Hdep_msg] & Hsender)].
  - subst msg.
    eapply VLSM_incl_can_emit in Hemitted
    ; [| apply pre_loaded_vlsm_incl_pre_loaded_with_all_messages].
    apply can_emit_free_composite_project in Hemitted as [sub_eqv Hemitted].
    destruct_dec_sig sub_eqv _eqv H_eqv Heqsub_eqv; subst.
    unfold sub_IM in Hemitted; cbn in Hemitted.
    eapply Hsender_safety in Hemitted; [| done]; subst.
    apply elem_of_elements in H_eqv.
    by revert H_eqv; apply elem_of_set_map_inj.
  - cut (strong_fixed_equivocation IM equivocators s msg).
    {
      intros [Hobserved | Hemitted_msg].
      - contradict Hnobserved_msg.
        by eapply sent_by_non_equivocating_are_directly_observed.
      - eapply VLSM_incl_can_emit in Hemitted_msg
        ; [| apply pre_loaded_vlsm_incl_pre_loaded_with_all_messages].
        apply can_emit_free_composite_project in Hemitted_msg as [sub_i Hemitted_msg].
        destruct_dec_sig sub_i i Hi Heqsub_i; subst.
        eapply Hsender_safety in Hemitted_msg; [| done].
        cbn in Hemitted_msg; subst.
        apply elem_of_elements in Hi.
        by revert Hi; apply elem_of_set_map_inj.
    }
    eapply msg_dep_happens_before_reflect
    ; [| by apply full_message_dependencies_happens_before | right]
    ; cycle 1.
    + eapply VLSM_incl_can_emit; [| done].
      by apply Equivocators_Fixed_Strong_incl.
    + eapply msg_dep_rel_reflects_strong_fixed_equivocation
      ; [done | done |].
      apply VLSM_incl_valid_state; [| done].
      by apply Fixed_incl_StrongFixed.
Qed.

Lemma msg_dep_limited_fixed_equivocation
  (is : state (free_composite_vlsm IM)) (tr : list (composite_transition_item IM))
  : fixed_limited_equivocation_prop (Ci := Ci) (Cv := Cv) IM threshold A is tr ->
    finite_valid_trace Limited
      {| original_state := is; state_annotation := ` inhabitant |}
      (msg_dep_annotate_trace_with_equivocators IM full_message_dependencies sender is tr).
Proof.
  intros (equivocators & Hlimited & Htr).
  split; [| by split; [apply Htr |]].
  apply valid_trace_add_default_last in Htr.
  match goal with
  |- finite_valid_trace_from Limited ?is ?tr =>
    cut
      (finite_valid_trace_from Limited is tr /\
        (state_annotation (@finite_trace_last _ Limited is tr) ⊆ equivocators))
  end
  ; [itauto |].
  induction Htr using finite_valid_trace_init_to_rev_strong_ind.
  - split; [| by apply empty_subseteq].
    by constructor; apply initial_state_is_valid.
  - rewrite @msg_dep_annotate_trace_with_equivocators_app; cbn.
    unfold annotate_trace_item; rewrite !finite_trace_last_is_last; cbn.
    split; cycle 1.
    + by eapply fixed_transition_preserves_annotation_equivocators
      ; [| | apply IHHtr1].
    + apply finite_valid_trace_from_app_iff.
      split; [by apply IHHtr1 |].
      apply finite_valid_trace_singleton.
      repeat split.
      * by apply finite_valid_trace_last_pstate, IHHtr1.
      * clear -Heqiom IHHtr2.
        destruct IHHtr2 as [IHHtr2 _].
        unfold empty_initial_message_or_final_output in Heqiom.
        destruct_list_last iom_tr iom_tr' iom_item Heqiom_tr
        ; [by apply option_initial_message_is_valid |].
        destruct iom as [im |]; [| apply option_valid_message_None].
        eapply valid_trace_output_is_valid; [done |].
        rewrite @msg_dep_annotate_trace_with_equivocators_app.
        apply Exists_app; right.
        destruct iom_item.
        by apply Exists_exists; eexists; split; [left |].
      * destruct l as [i li]; cbn.
        rewrite msg_dep_annotate_trace_with_equivocators_last_original_state; cbn.
        replace (finite_trace_last _ _) with s
             by (apply valid_trace_get_last in Htr1; congruence).
        by apply Ht.
      * apply Rle_trans with (sum_weights equivocators)
        ; [| done].
        apply sum_weights_subseteq.
        by eapply fixed_transition_preserves_annotation_equivocators; [.. | apply IHHtr1].
      * destruct l as [i li]; cbn; unfold annotated_transition; cbn.
        rewrite !msg_dep_annotate_trace_with_equivocators_last_original_state; cbn.
        replace (finite_trace_last _ _) with s
             by (apply valid_trace_get_last in Htr1; congruence).
        by destruct Ht as [_ Ht]; cbn in Ht
        ; destruct (transition _ _ _) as (si', om')
        ; inversion Ht.
Qed.

Lemma annotated_limited_incl_constrained_limited
  `{!finite.Finite validator}
  {is_equivocating_tracewise_no_has_been_sent_dec :
    RelDecision (is_equivocating_tracewise_no_has_been_sent IM A sender)}
  : VLSM_embedding
      Limited
      (tracewise_limited_equivocation_vlsm_composition IM threshold A sender (Cv := Cv))
      Datatypes.id original_state.
Proof.
  constructor; intros sX trX HtrX.
  eapply @traces_exhibiting_limited_equivocation_are_valid; [done.. | |].
  - by apply Hsender_safety.
  - by apply msg_dep_fixed_limited_equivocation.
Qed.

End sec_msg_dep_fixed_limited_equivocation.
