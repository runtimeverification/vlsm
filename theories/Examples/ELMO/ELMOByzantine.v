From stdpp Require Import prelude.
From Coq Require Import Reals Lra.
From VLSM.Lib Require Import Measurable.
From VLSM.Core Require Import VLSM Composition ProjectionTraces VLSMProjections.
From VLSM.Core Require Import Equivocation MessageDependencies FixedSetEquivocation.
From VLSM.Core Require Import ReachableThreshold Validator.
From VLSM.Core Require Import ByzantineTraces LimitedByzantineTraces.
From VLSM.Core Require Import MsgDepLimitedEquivocation.
From VLSM.Examples Require Import BaseELMO UMO ELMO.
From VLSM.Core Require Import AnnotatedVLSM.

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

Corollary ELMOcomposite_byzantine_traces_are_not_byzantine
  (ELMOProtocol := ELMOProtocol threshold idx (Ca := listset Address)) :
  forall tr, byzantine_trace_prop ELMOProtocol tr -> valid_trace_prop ELMOProtocol tr.
Proof.
  apply composite_validator_byzantine_traces_are_not_byzantine.
  by intro; eapply component_projection_validator_is_message_validator, ELMO_components_validating.
Qed.

Lemma no_initial_messages_in_ELMO_components :
  no_initial_messages_in_IM_prop ELMO_component.
Proof. by intros ? ? ?. Qed.

Context
  (Limited := msg_dep_limited_equivocation_vlsm (Cv := listset (Message_validator idx))
    ELMO_component threshold Message_full_dependencies (Message_sender idx))
  .

(**
  The following lemma shows that for any reachable state in an (ELMO_component i)
  there is a valid state in [ELMOProtocol] where component <<i>> meets most of the
  conditions of the previous lemma.
*)
Lemma reflecting_composite_for_reachable_component
  (i : index) (si : VLSM.state (ELMO_component i))
  (Hreachable : constrained_state_prop (ELMO_component i) si) :
  exists s : VLSM.state Limited,
    original_state s i = si
    /\ valid_state_prop Limited s
    /\ component_reflects_composite threshold idx (original_state s) i
    /\ other_components_after_send threshold idx (fun j : index => j = i) (original_state s)
    /\ forall (s_prev : State) (l : Label) (m : Message),
      si = s_prev <+> MkObservation l m ->
      exists s' : VLSM.state Limited,
      original_state s' = state_update ELMO_component (original_state s) i s_prev /\
      valid_state_prop Limited s' /\
      ELMOProtocol_valid_transition threshold idx i l (original_state s') (original_state s) m.
Proof.
  induction Hreachable using valid_state_prop_ind;
    [| destruct IHHreachable as (sigma & <- & Hsigma & Hreflects & Hsend & Hall), l; cycle 1].
  - unfold initial_state_prop in Hs; cbn in Hs.
    apply UMO_component_initial_state_spec in Hs as ->.
    exists (mk_annotated_state (free_composite_vlsm ELMO_component) (listset (Message_validator idx)) (` (composite_s0 ELMO_component)) ∅).
    unfold composite_s0; cbn; split_and!; [done | ..].
    + by apply initial_state_is_valid.
    + repeat split; cbn; [.. | by inversion 1].
      * by intros [j Hj].
      * by inversion 1.
      * intros [? ? [? Hrcv] ?].
        by inversion Hrcv.
    + by left; cbn.
    + by inversion 1.
  - 
    pose (Hti := Ht); destruct Hti as [(_ & _ & Hv) Hti];
      inversion Hv; subst; inversion Hti; subst.
    destruct (transition (VLSMMachine := Limited) (existT i Send) (sigma, None))
      as (sigma', _om') eqn:Ht'.
    cbn in Ht'; unfold annotated_transition in Ht'; cbn in Ht'.
    exists sigma'; split; [by inversion Ht'; subst; cbn; state_update_simpl |].
    assert (Htsigma : input_valid_transition Limited (existT i Send) (sigma, None)
                        (sigma', Some (MkMessage (original_state sigma i)))).
    {
      repeat split;
        [done | by apply option_valid_message_None | done | | by inversion Ht'].
      by eapply coeqv_limited_equivocation_state_not_heavy.
    }
    eapply input_valid_transition_destination in Htsigma as Hsigma'.
    inversion Ht'; subst; cbn.
    split_and!; [done | split | ..]; cycle 2.
    + by intros j Hnj; state_update_simpl; apply Hsend.
    + inversion 1; destruct s_prev; cbn in *; subst.
      rewrite state_update_twice, state_update_id
        by (destruct original_state; done).
      by eexists; split_and!; [..| constructor].
    + intro m; split; [| by eexists]; intros [j Hm].
      destruct (decide (i = j)); [by subst |].
      state_update_simpl.
      apply elem_of_messages_addObservation; right.
      by apply Hreflects; eexists.
    + intros a.
      transitivity (global_equivocators_simple threshold idx (original_state sigma) a);
        [split |]; cycle 2.
      * etransitivity; [by apply Hreflects |].
        state_update_simpl.
        unfold local_equivocators_full; cbn; rewrite lefo_alt; cbn.
        by split; [right | intros [|]; [destruct_and! |]].
      * intros [? <-]; esplit; [done | ..].
        -- destruct ges_recv as [j Hrecv].
           destruct (decide (i = j)); subst; state_update_simpl; [| by eexists].
           cbn in Hrecv; rewrite decide_False in Hrecv by (intro; done).
           by exists j.
        -- intros [j Hsent]; apply ges_not_sent; exists j.
           destruct (decide (i = j)); subst; state_update_simpl; [| done].
           by eapply has_been_sent_step_update; [| right].
      * intros []; esplit; [done | ..].
        -- destruct ges_recv as [j Hrecv]; exists j.
           destruct (decide (i = j)); subst; state_update_simpl; [| done].
           by eapply has_been_received_step_update; [| right].
        -- intros [j Hsnd]; apply ges_not_sent.
           destruct (decide (i = j)); subst; state_update_simpl; [| by eexists].
           cbn in Hsnd; rewrite decide_True in Hsnd by done; cbn in Hsnd.
           apply elem_of_cons in Hsnd as []; subst; [| by exists j].
           exfalso; eapply irreflexivity
             with (R := lt) (x := sizeState (original_state sigma j));
             [typeclasses eauto |].
           change (original_state sigma j) with (state (MkMessage (original_state sigma j))) at 1.
           apply messages_sizeState, Hreflects.
           destruct ges_recv as [j' Hrecv]; exists j'.
           by apply elem_of_messages; right.
  - pose (Hti := Ht); destruct Hti as [(_ & _ & Hv) Hti];
      inversion Hv as [? ? [? ? ? Hlocal_ok] |]; subst; inversion Hti; subst om'.
    apply ELMO_msg_valid_full_has_sender in ELMO_mv_msg_valid_full as Hsender.
    cut (exists gamma,
          in_futures Limited sigma gamma /\
          original_state gamma i = original_state sigma i /\
          component_reflects_composite threshold idx (state_update ELMO_component (original_state gamma) i s') i /\
          other_components_after_send threshold idx  (fun j : index => j = i) (original_state gamma)).
    {
      intros (gamma & Hfutures & Heq_i & [Hsigma'_messages Hsigma'_eqvs] & Hgamma_send).
      destruct (transition (VLSMMachine := Limited) (existT i Receive) (gamma, Some m))
        as (sigma', _om') eqn:Ht'.
      cbn in Ht'; unfold annotated_transition in Ht'; cbn in Ht'.
      exists sigma'; split;
        [by inversion Ht'; subst; cbn; state_update_simpl; rewrite Heq_i |].
      assert (Hvtsigma : valid_transition Limited (existT i Receive) gamma (Some m) sigma' None).
      {
        repeat split; cbn; [by rewrite Heq_i | |];
          [| by inversion Ht'; rewrite Heq_i].
        red.
        unfold coeqv_composite_transition_message_equivocators, coeqv_message_equivocators.
        case_decide.
        - replace (sum_weights _) with (sum_weights (state_annotation gamma));
            [| by apply sum_weights_proper; set_solver].
          eapply coeqv_limited_equivocation_state_not_heavy; [done |].
          by eapply in_futures_valid_snd.
        - destruct Hsender as [idx_m Hidx_m].
          pose (v_m := ELMO_A_inv_fn idx idx_m).
          assert (Hsender : Message_sender idx m = Some v_m)
            by (apply Message_sender_Some_adr_iff; done).
          replace (sum_weights _)
            with (sum_weights (state_annotation gamma ∪ {[v_m]})); cycle 1.
          + apply sum_weights_proper.
            rewrite full_node_msg_dep_coequivocating_senders.
            * by cbn; rewrite Hsender, elements_empty; cbn; set_solver.
            * by typeclasses eauto.
            * by typeclasses eauto.
            * by apply ELMO_component_message_dependencies_full_node_condition.
            * by rewrite <- Heq_i in Ht; apply Ht.
            Unshelve.
            typeclasses eauto.
          + 

(*
        Search coeqv_composite_transition_message_equivocators.
        unfold local_equivocation_limit_ok, not_heavy in Hlocal_ok.
        unfold ELMO_not_heavy, not_heavy.
        etransitivity; [| done].
        apply sum_weights_subseteq; [by apply NoDup_elements.. |].
        intros x.
        unfold equivocating_validators, is_equivocating; cbn.
        apply filter_subprop; intros; rewrite <- Heq_i in *.
        unfold component_reflects_composite_equivocators in Hsigma'_eqvs.
        state_update_simpl.
        apply Hsigma'_eqvs, ELMO_global_equivocators_iff_simple; [| done].
        apply input_valid_transition_destination
          with (l := existT i Receive) (s := gamma) (om := Some m) (om' := None);
          repeat split; [| | done].
        + eapply in_futures_valid_snd.
          by apply (VLSM_incl_in_futures (constrained_preloaded_incl (free_composite_vlsm _)
            ELMO_global_constraint)).
        + by apply any_message_is_valid_in_preloaded.
      }
      split_and!.
      - apply input_valid_transition_destination
          with (l := existT i Receive) (s := gamma) (om := Some m) (om' := None); repeat split.
        + by eapply in_futures_valid_snd.
        + by eapply ELMO_valid_states_only_receive_valid_messages;
            [eapply in_futures_valid_snd | constructor 1].
        + by cbn; rewrite Heq_i.
        + by apply Hvtsigma.
        + by cbn; rewrite Heq_i.
      - done.
      - by intros j Hnj; subst sigma'; state_update_simpl; apply Hgamma_send.
      - inversion 1; destruct s_prev; cbn in *; subst; rewrite <- Heq_i.
        subst sigma'; rewrite state_update_twice, state_update_id by (destruct (gamma i); done).
        by split; [eapply in_futures_valid_snd | constructor].
    }
    destruct (decide (composite_has_been_sent ELMO_component sigma m)) as [| Hnot_sent].
    {
      exists sigma; split_and!; [by apply in_futures_refl | done | split | done].
      - by eapply component_reflects_composite_messages_step_update, Hreflects; constructor 1.
      - unfold component_reflects_composite_messages, component_reflects_composite_equivocators.
        state_update_simpl.
        by eapply receiving_already_sent_global_local_equivocators.
    }
    destruct (decide (adr (state m) = idx i)) as [| Hm_not_by_i].
    {
      contradict Hnot_sent; exists i.
      cbn; apply ELMO_mv_no_self_equiv; [by split |].
      transitivity (idx i); [| done].
      by eapply ELMO_reachable_adr, Ht.
    }
    destruct (decide (local_equivocators_full (sigma i) (adr (state m)))) as [| Hneqv].
    {
      exists sigma; split_and!; [by apply in_futures_refl | done | split | done].
      - by eapply component_reflects_composite_messages_step_update, Hreflects; constructor.
      - unfold component_reflects_composite_messages, component_reflects_composite_equivocators.
        state_update_simpl.
        by eapply receiving_already_equivocating_global_local_equivocators.
    }
    destruct (decide (local_equivocators_full s' (adr (state m)))) as [| Hneqv'].
    {
      exists sigma; split_and!; [by apply in_futures_refl | done | split | done].
      - by eapply component_reflects_composite_messages_step_update, Hreflects; constructor 1.
      - unfold component_reflects_composite_messages, component_reflects_composite_equivocators.
        state_update_simpl.
        by eapply receiving_not_already_equivocating_global_local_equivocators.
    }
    destruct Hsender as [i_m Hsender].
    destruct (special_receivable_messages_emittable_in_future _ _ _ _ Ht
      _ Hsender Hm_not_by_i Hneqv Hneqv' _ Hsigma eq_refl Hreflects Hsend Hnot_sent)
      as (chi & Hfutures & Heqi & [Hchi_messages Hchi_eqvs] & Heqi_m & Hchi_send).
    pose (sigma' := state_update ELMO_component chi i_m (chi i_m <+> MkObservation Send m)); subst s'.
    assert (Hti_m :
      input_valid_transition ELMOProtocol (existT i_m Send) (chi, None) (sigma', Some m)).
    {
      repeat split.
      - by eapply in_futures_valid_snd.
      - by apply option_valid_message_None.
      - by constructor.
      - by subst sigma'; cbn; rewrite Heqi_m; destruct m.
    }
    assert (i <> i_m) by (contradict Hm_not_by_i; subst; done).
    assert (ELMO_component_RAM_transition i Receive (sigma' i) (sigma i <+> MkObservation Receive m) m).
    {
      subst sigma'; state_update_simpl; rewrite Heqi.
      constructor; repeat split; [.. | done].
      - by eapply valid_state_project_preloaded.
      - by apply any_message_is_valid_in_preloaded.
    }
    exists sigma'; split_and!; cycle 3; [.. | split].
    + intros k Hk.
      subst sigma'.
      destruct (decide (k = i_m)); subst; state_update_simpl; [| by apply Hchi_send; itauto].
      by constructor 2; eexists _, _.
    + by etransitivity; [| eapply input_valid_transition_in_futures].
    + by subst sigma'; rewrite <- Heqi; state_update_simpl.
    + split; [| by eexists]; intros [j Hj].
      destruct (decide (i = j)); [by subst |].
      subst sigma'; destruct (decide (i_m = j)); subst; state_update_simpl;
        apply elem_of_messages_addObservation.
      * apply elem_of_messages_addObservation in Hj as []; [by left |].
        by right; rewrite <- Heqi; apply Hchi_messages; eexists.
      * by right; rewrite <- Heqi; apply Hchi_messages; eexists.
    + intros a; state_update_simpl.
      transitivity (global_equivocators_simple chi a).
      * subst sigma'; rewrite global_equivocators_simple_step_update_receive;
          [| by constructor; state_update_simpl; rewrite Heqi].
        rewrite global_equivocators_simple_step_update_send_iff; cycle 1.
        -- by constructor; apply input_valid_transition_project_active in Hti_m; state_update_simpl.
        -- by contradict Hneqv; rewrite Hsender, <- Heqi; apply Hchi_eqvs.
        -- split; [| by left].
           intros [| [_ Hnsnd]]; [done |].
           by contradict Hnsnd; exists i_m; state_update_simpl; left.
      * etransitivity; [by apply Hchi_eqvs |].
        rewrite Heqi; split.
        -- by intros Heqv; eapply local_equivocators_full_step_update; [constructor | left].
        -- intros Heqv.
           destruct (decide (a = adr (state m))); [by subst |].
           eapply local_equivocators_full_step_update in Heqv; [| by constructor].
           by destruct Heqv as [| [->]].
Qed.

Lemma ELMO_msg_dep_limited_equivocation_message_validator_prop (i : index) :
  msg_dep_limited_equivocation_message_validator_prop
    (Cv := listset (Message_validator idx))
    ELMO_component threshold
    Message_full_dependencies
    (Message_sender idx)
    i.
Proof.
  intros li si m Hvti.
  cut (valid_message_prop Limited m); [done |].
  apply input_valid_transition_iff in Hvti as [[si' om'] Hvti].
  pose (Hvti' := Hvti); destruct Hvti' as [(_ & _ & Hvi) Hti].
  assert (Hsi' : valid_state_prop (pre_loaded_with_all_messages_vlsm (ELMO_component i)) si')
    by (eapply input_valid_transition_destination; done).
  unshelve eapply reflecting_composite_for_reachable_component in Hsi'
    as (s' & <- & Hs' & _ & _ & Htransitions); [| done].
  specialize (Htransitions si li).
  exists (state_update ELMO_component s' i si).
  split; [by state_update_simpl |].
  inversion Hvi; subst; inversion Hti as [Heqs'i]; subst;
    symmetry in Heqs'i; destruct (Htransitions _ Heqs'i) as [Hvs'0 Hvt0];
    inversion Hvt0 as [? ? ? ? Hvt | ? ? ? ? Hvt].
  - repeat split; [done | | by apply Hvt..].
    eapply received_valid; [by apply Hs' |].
    by eexists; eapply has_been_received_step_update; [| left].
  - by repeat split; [| apply option_valid_message_None | apply Hvt].

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