From stdpp Require Import prelude.
From Coq Require Import FinFun Relations.Relation_Operators.
From VLSM.Lib Require Import Preamble ListExtras FinFunExtras StdppListSet Measurable.
From VLSM.Core Require Import VLSM VLSMProjections Composition ProjectionTraces SubProjectionTraces Equivocation.

(** * VLSM Message Dependencies

An abstract framework for the full-node condition.
Assumes that each message has an associated set of [message_dependencies].

*)

Section sec_message_dependencies.

Context
  {message : Type}
  (message_dependencies : message -> set message)
  (X : VLSM message)
  {Hbs : HasBeenSentCapability X}
  {Hbr : HasBeenReceivedCapability X}
  (Hbo : HasBeenObservedCapability X := HasBeenObservedCapability_from_sent_received X)
  .

Existing Instance Hbo.

(**
[MessageDependencies] characterize a <<message_dependencies>> function
through two properties:

- Necessity: All dependent messeges for a message <<m>>m are required to be
observed by any state emitting the message <<m>>.

- Sufficiency: A message can be produced by the machine pre-loaded with its
dependencies.

Together with [message_dependencies_full_node_condition_prop], it
constitutes the _full node assumption_.
*)
Class MessageDependencies
  :=
  { message_dependencies_are_necessary (m : message)
      `(can_produce (pre_loaded_with_all_messages_vlsm X) s m)
      : forall (dm : message),
        dm ∈ message_dependencies m ->
        has_been_observed X s dm
  ; message_dependencies_are_sufficient (m : message)
      `(can_emit (pre_loaded_with_all_messages_vlsm X) m)
      : can_emit (pre_loaded_vlsm X (fun msg => msg ∈ message_dependencies m)) m
  }.

(** The (local) full node condition for a given <<message_dependencies>> function
requires that a state (receiving the message) has previously
observed all of <<m>>'s dependencies.
*)
Definition message_dependencies_full_node_condition
  (s : vstate X)
  (m : message)
  : Prop :=
  forall dm, dm ∈ message_dependencies m -> has_been_observed X s dm.

(** A VLSM has the [message_dependencies_full_node_condition_prop]
if the validity of receiving a message in a state implies the
[message_dependencies_full_node_condition] for that state and message
*)
Definition message_dependencies_full_node_condition_prop : Prop :=
  forall l s m,
  vvalid X l (s, Some m) -> message_dependencies_full_node_condition s m.

(** Membership to the message_dependencies of a message induces a dependency
relation.
*)
Definition msg_dep_rel : relation message :=
  fun m1 m2 => m1 ∈ message_dependencies m2.

(** The transitive closure of the [msg_dep_rel]ation is a happens-before
relation.
*)
Definition msg_dep_happens_before : relation message := flip (clos_trans _ (flip msg_dep_rel)).

(** Unrolling one the [msg_dep_happens_before] relation one step. *)
Lemma msg_dep_happens_before_iff_one x z
  : msg_dep_happens_before x z <->
    msg_dep_rel x z \/ exists y, msg_dep_happens_before x y /\ msg_dep_rel y z.
Proof.
  unfold msg_dep_happens_before; simpl.
  setoid_rewrite Operators_Properties.clos_trans_t1n_iff.
  split.
  - inversion 1; subst; eauto.
  - intros [H | [y [H1 H2]]]; econstructor; eassumption.
Qed.

Global Instance msg_dep_happens_before_transitive : Transitive msg_dep_happens_before.
Proof.
  apply flip_Transitive.
  intros m1 m2 m3.
  apply t_trans.
Qed.

(** If the [msg_dep_rel]ation reflects a predicate <<P>> and the induced
[msg_dep_happens_before] is [well_founded], then if <<P>> holds for a message,
it will hold for all its dependencies. *)
Lemma msg_dep_happens_before_reflect
  (P : message -> Prop)
  (Hreflects : forall dm m, msg_dep_rel dm m -> P m -> P dm)
  : forall dm m, msg_dep_happens_before dm m -> P m -> P dm.
Proof.
  intros dm m Hdm.
  apply Operators_Properties.clos_trans_t1n in Hdm.
  clear -Hdm Hreflects.
  induction Hdm; firstorder.
Qed.

(** In the absence of initial messages, and if [msg_dep_rel] reflects the
pre-loaded message property, then it also reflects the [valid_message_prop]erty.
*)
Lemma msg_dep_reflects_validity
  (HMsgDep : MessageDependencies)
  (no_initial_messages_in_X : forall m, ~ vinitial_message_prop X m)
  (P : message -> Prop)
  (Hreflects : forall dm m, msg_dep_rel dm m -> P m -> P dm)
  (Hbr_pre := preloaded_HasBeenReceivedCapability Hbr)
  (Hbs_pre := preloaded_HasBeenSentCapability Hbs)
  (Hbo_pre := HasBeenObservedCapability_from_sent_received (pre_loaded_vlsm X P))
  : forall dm m, msg_dep_rel dm m ->
    valid_message_prop (pre_loaded_vlsm X P) m ->
    valid_message_prop (pre_loaded_vlsm X P) dm.
Proof.
  intros dm m Hdm.
  rewrite emitted_messages_are_valid_iff, can_emit_iff.
  intros [Hinit | [s Hproduce]].
  - rewrite emitted_messages_are_valid_iff.
    left; right.
    apply Hreflects with m; [assumption |].
    destruct Hinit as [Hinit | Hp]; [| assumption].
    elim (no_initial_messages_in_X m).
    assumption.
  - apply (observed_valid (pre_loaded_vlsm X P)) with (s := s).
    + exists (Some m). apply can_produce_valid. assumption.
    + cut (has_been_observed X s dm).
      {
        intros [Hsent | Hreceived]; [left|right]; auto.
      }
      apply message_dependencies_are_necessary with m; [| assumption].
      revert Hproduce.
      apply VLSM_incl_can_produce, pre_loaded_vlsm_incl_pre_loaded_with_all_messages.
Qed.

(** Under [MessageDependencies] assumptions, if a message [has_been_sent]
in a state <<s>>, then any of its direct dependencies [has_been_observed].
*)
Lemma msg_dep_has_been_sent
  (HMsgDep : MessageDependencies)
  s
  (Hs : valid_state_prop (pre_loaded_with_all_messages_vlsm X) s)
  m
  (Hsent : has_been_sent X s m)
  : forall dm, msg_dep_rel dm m -> has_been_observed X s dm.
Proof.
  intros dm Hdm.
  cut (exists item, can_produce (pre_loaded_with_all_messages_vlsm X) (destination item) m /\
                    in_futures (pre_loaded_with_all_messages_vlsm X) (destination item) s).
  {
    intros (s_dm & Hproduce & Hfutures).
    eapply in_futures_preserving_oracle_from_stepwise; [|eassumption|].
    - apply has_been_observed_from_sent_received_stepwise_props.
    - apply message_dependencies_are_necessary with m; assumption.
  }
  apply proper_sent in Hsent; [|assumption].
  apply valid_state_has_trace in Hs as [is [tr Htr]].
  specialize (Hsent _ _ Htr).
  apply Exists_exists in Hsent as [item [Hitem Houtput]].
  exists item.
  split; cycle 1.
  - eapply elem_of_trace_in_futures_left; [|eassumption].
    apply Htr.
  - unfold can_produce.
    replace (Some m) with (output item) by assumption.
    eapply can_produce_from_valid_trace; [|eassumption].
    eapply valid_trace_forget_last.
    apply Htr.
Qed.

(** If the [valid]ity predicate has the [message_dependencies_full_node_condition_prop]erty,
then if a message [has_been_received] in a state <<s>>, any of its direct
dependencies [has_been_observed].
*)
Lemma full_node_has_been_received
  (Hfull : message_dependencies_full_node_condition_prop)
  s
  (Hs : valid_state_prop (pre_loaded_with_all_messages_vlsm X) s)
  m
  (Hreceived : has_been_received X s m)
  : forall dm, msg_dep_rel dm m -> has_been_observed X s dm.
Proof.
  intros dm Hdm.
  apply proper_received in Hreceived; [|assumption].
  apply valid_state_has_trace in Hs as [is [tr Htr]].
  specialize (Hreceived _ _ Htr).
  apply Exists_exists in Hreceived as [item [Hitem Hinput]].
  apply elem_of_list_split in Hitem as [pre [suf Heqtr]].
  eapply in_futures_preserving_oracle_from_stepwise with (s1 := finite_trace_last is pre)
  ; [apply has_been_observed_from_sent_received_stepwise_props|..].
  - exists (item  :: suf).
    eapply finite_valid_trace_from_to_app_split.
    rewrite <- Heqtr.
    apply Htr.
  - eapply Hfull; [|eassumption].
    replace (Some m) with (input item) by assumption.
    clear Hinput.
    eapply (input_valid_transition_is_valid (pre_loaded_with_all_messages_vlsm X)).
    eapply input_valid_transition_to; [|simpl; eassumption].
    eapply valid_trace_forget_last.
    apply Htr.
Qed.

(** By combining Lemmas [msg_dep_has_been_sent] and [full_node_has_been_received],
[msg_dep_rel] reflects the [has_been_observed] predicate.
*)
Lemma msg_dep_full_node_reflects_has_been_observed
  (HMsgDep : MessageDependencies)
  (Hfull : message_dependencies_full_node_condition_prop)
  s
  (Hs : valid_state_prop (pre_loaded_with_all_messages_vlsm X) s)
  : forall dm m, msg_dep_rel dm m ->
    has_been_observed X s m ->
    has_been_observed X s dm.
Proof.
  intros dm m Hdm [Hsent|Hreceived].
  - eapply msg_dep_has_been_sent; eassumption.
  - eapply full_node_has_been_received; eassumption.
Qed.

End sec_message_dependencies.

Section sec_composite_message_dependencies.

Context
  {message : Type}
  (message_dependencies : message -> set message)
  `{finite.Finite index}
  (IM : index -> VLSM message)
  (Hbs : forall i, HasBeenSentCapability (IM i))
  (Hbr : forall i, HasBeenReceivedCapability (IM i))
  (Hbo := fun i => HasBeenObservedCapability_from_sent_received (IM i))
  (HMsgDep : forall i, MessageDependencies message_dependencies (IM i))
  (Free_Hbs := free_composite_HasBeenSentCapability IM (listing_from_finite index) Hbs)
  (Free_Hbr := free_composite_HasBeenReceivedCapability IM (listing_from_finite index) Hbr)
  .

Existing Instance Free_Hbs.
Existing Instance Free_Hbr.

(** If all of the components satisfy the [MessageDependencies] assumptions,
then their free composition will also do so.
*)
Lemma composite_message_dependencies
  : MessageDependencies message_dependencies (free_composite_vlsm IM).
Proof.
  split.
  - intros m s Hproduce dm Hdm.
    destruct Hproduce as [(is, iom) [(i, li) Ht]].
    cut (@has_been_observed _ (IM i) (Hbo i) (s i) dm)
    ; [intros [Hsent | Hreceived]; [left | right]; exists i; assumption|].
    eapply message_dependencies_are_necessary; [apply HMsgDep| |eassumption].
    exists (is i, iom), li.
    revert Ht.
    apply
      (VLSM_projection_input_valid_transition (preloaded_component_projection IM _))
      with (lY := li).
    unfold composite_project_label.
    cbn.
    case_decide as Heqi; [|contradiction].
    replace Heqi with (@eq_refl index i) by (apply Eqdep_dec.UIP_dec; assumption).
    reflexivity.
  - intros m Hemit.
    apply can_emit_composite_project in Hemit as [j Hemitj].
    eapply message_dependencies_are_sufficient in Hemitj; [| apply HMsgDep].
    revert Hemitj.
    eapply VLSM_full_projection_can_emit.
    apply lift_to_composite_generalized_preloaded_vlsm_full_projection.
    intuition.
Qed.

Lemma msg_dep_reflects_free_validity
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  (X := free_composite_vlsm IM)
  : forall dm m, msg_dep_rel message_dependencies dm m ->
    valid_message_prop X m -> valid_message_prop X dm.
Proof.
  intros dm m Hdm.
  rewrite !emitted_messages_are_valid_iff.
  intros [[i [[im Him] Heqm]] | Hemit]
  ; [elim (no_initial_messages_in_IM i im); assumption|].
  right.
  pose proof (vlsm_is_pre_loaded_with_False X) as XeqXFalse.
  apply (VLSM_eq_can_emit XeqXFalse) in Hemit.
  apply (VLSM_eq_can_emit XeqXFalse).
  cut (valid_message_prop (pre_loaded_vlsm X (fun _ => False)) dm).
  {
    clear -no_initial_messages_in_IM.
    rewrite emitted_messages_are_valid_iff.
    intros [[[i [[im Him] Heqm]] | Hpreloaded] | Hemit]
    ; [elim (no_initial_messages_in_IM i im); assumption|contradiction| assumption].
  }
  eapply msg_dep_reflects_validity.
  - apply composite_message_dependencies.
  - clear -no_initial_messages_in_IM.
    intros m [i [[im Him] Heqm]].
    elim (no_initial_messages_in_IM i im).
    assumption.
  - intuition.
  - eassumption.
  - apply emitted_messages_are_valid_iff. auto.
Qed.

Lemma msg_dep_reflects_happens_before_free_validity
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  (X := free_composite_vlsm IM)
  : forall dm m, msg_dep_happens_before message_dependencies dm m ->
    valid_message_prop X m -> valid_message_prop X dm.
Proof.
  apply msg_dep_happens_before_reflect.
  apply msg_dep_reflects_free_validity.
  assumption.
Qed.

Lemma msg_dep_happens_before_composite_no_initial_valid_messages_emitted_by_sender
  {validator : Type}
  (sender : message -> option validator)
  (A : validator -> index)
  (Hchannel : channel_authentication_prop  IM A sender)
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  (X := free_composite_vlsm IM)
  : forall m, valid_message_prop X m ->
    forall dm, msg_dep_happens_before message_dependencies dm m ->
    exists v, sender dm = Some v /\
      can_emit (pre_loaded_with_all_messages_vlsm (IM (A v))) dm.
Proof.
  intros m Hm dm Hdm.
  cut (valid_message_prop X dm).
  {
    clear Hdm.
    revert dm.
    apply composite_no_initial_valid_messages_emitted_by_sender; assumption.
  }
  revert dm m Hdm Hm.
  apply msg_dep_reflects_happens_before_free_validity.
  assumption.
Qed.

End sec_composite_message_dependencies.

Section sec_sub_composite_message_dependencies.

Context
  {message : Type}
  (message_dependencies : message -> set message)
  `{EqDecision index}
  (IM : index -> VLSM message)
  (Hbs : forall i, HasBeenSentCapability (IM i))
  (Hbr : forall i, HasBeenReceivedCapability (IM i))
  (Hbo := fun i => HasBeenObservedCapability_from_sent_received (IM i))
  (HMsgDep : forall i, MessageDependencies message_dependencies (IM i))
  (indices : set index)
  (SubFree_Hbs := free_composite_HasBeenSentCapability (sub_IM IM indices) (listing_from_finite (sub_index indices)) (sub_has_been_sent_capabilities IM indices Hbs))
  (SubFree_Hbr := free_composite_HasBeenReceivedCapability (sub_IM IM indices) (listing_from_finite (sub_index indices)) (sub_has_been_received_capabilities IM indices Hbr))
  .

Existing Instance SubFree_Hbs.
Existing Instance SubFree_Hbr.

Lemma sub_composite_message_dependencies
  : MessageDependencies message_dependencies (free_composite_vlsm (sub_IM IM indices)).
Proof.
  apply composite_message_dependencies.
  intro sub_i.
  destruct_dec_sig sub_i i Hi Heqsub_i.
  subst.
  apply HMsgDep.
Qed.

Lemma msg_dep_reflects_sub_free_validity
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  (P : message -> Prop)
  (Hreflects : forall dm m, msg_dep_rel message_dependencies dm m -> P m -> P dm)
  (X := free_composite_vlsm (sub_IM IM indices))
  : forall dm m, msg_dep_rel message_dependencies dm m ->
    valid_message_prop (pre_loaded_vlsm X P) m ->
    valid_message_prop (pre_loaded_vlsm X P) dm.
Proof.
  eapply msg_dep_reflects_validity; [| |assumption].
  - apply sub_composite_message_dependencies.
  - intros m [sub_i [[im Him] Heqm]].
    destruct_dec_sig sub_i i Hi Heqsub_i.
    subst.
    elim (no_initial_messages_in_IM i im).
    assumption.
Qed.

End sec_sub_composite_message_dependencies.

Section sec_full_message_dependencies.

Context
  {message : Type}
  .

Class FullMessageDependencies
  (message_dependencies : message -> set message)
  (full_message_dependencies : message -> set message)
  :=
  { full_message_dependencies_happens_before
      : forall dm m, dm ∈ full_message_dependencies m <-> msg_dep_happens_before message_dependencies dm m
  ; full_message_dependencies_irreflexive
      : forall m, m ∉ full_message_dependencies m
  ; full_message_dependencies_nodups
      : forall m, NoDup (full_message_dependencies m)
  }.

End sec_full_message_dependencies.

Section full_message_dependencies_happens_before.

Context
  {message : Type}
  (message_dependencies : message -> set message)
  (full_message_dependencies : message -> set message)
  (HFullMsgDep : FullMessageDependencies message_dependencies full_message_dependencies)
  .

Global Instance msg_dep_happens_before_irrefl : Irreflexive (msg_dep_happens_before message_dependencies).
Proof.
  intros m Hm.
  elim (full_message_dependencies_irreflexive m).
  eapply full_message_dependencies_happens_before.
  assumption.
Qed.

Global Instance msg_dep_happens_before_strict : StrictOrder (msg_dep_happens_before message_dependencies) := {}.

Lemma msg_dep_happens_before_wf : well_founded (msg_dep_happens_before message_dependencies).
Proof.
  cut (forall n m, length (full_message_dependencies m) < n -> Acc (msg_dep_happens_before message_dependencies) m).
  {
    intros Hn m.
    apply (Hn (S (length (full_message_dependencies m)))).
    lia.
  }
  induction n as [|n IHn]; [lia|].
  intros m Hm.
  constructor.
  intros dm Hdm.
  apply IHn.
  unfold lt.
  transitivity (length (full_message_dependencies m)); [|lia].
  replace (S _) with (length (dm :: full_message_dependencies dm))
    by reflexivity.
  apply NoDup_subseteq_length.
  - constructor.
    + apply full_message_dependencies_irreflexive.
    + apply full_message_dependencies_nodups.
  - intros m' Hm'.
    inversion Hm'; subst; [apply full_message_dependencies_happens_before; assumption|].
    revert H1.
    setoid_rewrite full_message_dependencies_happens_before.
    intro Hm'dm.
    transitivity dm; assumption.
Qed.

Lemma FullMessageDependencies_ind
  (P : message -> Prop)
  m
  (IHm : forall dm, dm ∈ full_message_dependencies m -> (forall dm0, dm0 ∈ full_message_dependencies dm -> P dm0) -> P dm)
  : forall dm, dm ∈ full_message_dependencies m -> P dm.
Proof.
  induction m using (well_founded_ind msg_dep_happens_before_wf).
  intros dm Hdm.
  apply IHm; [assumption|].
  apply H; [apply full_message_dependencies_happens_before; assumption|].
  intros dm0 Hdm0.
  apply IHm.

  apply full_message_dependencies_happens_before.
  transitivity dm.
  - apply full_message_dependencies_happens_before. assumption.
  - apply full_message_dependencies_happens_before. assumption.
Qed.

End full_message_dependencies_happens_before.
