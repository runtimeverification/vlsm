From Cdcl Require Import Itauto. Local Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From Coq Require Import FinFun Relations.Relation_Operators Program.Equality.
From VLSM.Lib Require Import Preamble ListExtras FinFunExtras StdppListSet Measurable.
From VLSM.Core Require Import VLSM VLSMProjections Composition ProjectionTraces SubProjectionTraces Equivocation EquivocationProjections.

(** * VLSM Message Dependencies

An abstract framework for the full-node condition.
Assumes that each message has an associated set of [message_dependencies].

*)

Section sec_message_dependencies.

Context
  {message : Type}
  (message_dependencies : message -> set message)
  (X : VLSM message)
  `{HasBeenSentCapability message X}
  `{HasBeenReceivedCapability message X}
  .

(** The (local) full node condition for a given <<message_dependencies>> function
requires that a state (receiving the message) has previously
observed all of <<m>>'s dependencies.
*)
Definition message_dependencies_full_node_condition
  (s : vstate X)
  (m : message)
  : Prop :=
  forall dm, dm ∈ message_dependencies m -> has_been_observed X s dm.

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
      : message_dependencies_full_node_condition s m
  ; message_dependencies_are_sufficient (m : message)
      `(can_emit (pre_loaded_with_all_messages_vlsm X) m)
      : can_emit (pre_loaded_vlsm X (fun msg => msg ∈ message_dependencies m)) m
  }.

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

(** The transitive closure ([clos_trans_1n]) of the [msg_dep_rel]ation is a
happens-before relation.
*)
Definition msg_dep_happens_before : relation message := flip (clos_trans_1n _ (flip msg_dep_rel)).

(** Unrolling one the [msg_dep_happens_before] relation one step. *)
Lemma msg_dep_happens_before_iff_one x z
  : msg_dep_happens_before x z <->
    msg_dep_rel x z \/ exists y, msg_dep_happens_before x y /\ msg_dep_rel y z.
Proof.
  split.
  - inversion 1; subst; eauto.
  - by intros [Hxz | [y [Hxy Hyz]]]; econstructor.
Qed.

Global Instance msg_dep_happens_before_transitive : Transitive msg_dep_happens_before.
Proof.
  apply flip_Transitive.
  intros m1 m2 m3 .
  rewrite <- !Relations.Operators_Properties.clos_trans_t1n_iff.
  apply t_trans.
Qed.

(** If the [msg_dep_rel]ation reflects a predicate <<P>>, then
[msg_dep_happens_before] will also reflect it. *)
Lemma msg_dep_happens_before_reflect
  (P : message -> Prop)
  (Hreflects : forall dm m, msg_dep_rel dm m -> P m -> P dm)
  : forall dm m, msg_dep_happens_before dm m -> P m -> P dm.
Proof.
  intros dm m Hdm.
  clear -Hdm Hreflects.
  induction Hdm; firstorder.
Qed.

(** In the absence of initial messages, and if [msg_dep_rel]ation reflects
the pre-loaded message property, then it also reflects the
[valid_message_prop]erty.
*)
Lemma msg_dep_reflects_validity
  `{MessageDependencies}
  (no_initial_messages_in_X : forall m, ~ vinitial_message_prop X m)
  (P : message -> Prop)
  (Hreflects : forall dm m, msg_dep_rel dm m -> P m -> P dm)
  : forall dm m, msg_dep_rel dm m ->
    valid_message_prop (pre_loaded_vlsm X P) m ->
    valid_message_prop (pre_loaded_vlsm X P) dm.
Proof.
  intros dm m Hdm.
  rewrite emitted_messages_are_valid_iff, can_emit_iff.
  intros [Hinit | [s Hproduce]].
  - rewrite emitted_messages_are_valid_iff; left; right.
    apply Hreflects with m; [done |].
    destruct Hinit as [Hinit | Hp]; [| done].
    contradict Hinit; apply no_initial_messages_in_X.
  - apply (observed_valid (pre_loaded_vlsm X P) s).
    + exists (Some m). by apply can_produce_valid.
    + cut (has_been_observed X s dm).
      {
        intros [Hsent | Hreceived]; [left | right]; auto.
      }
      apply message_dependencies_are_necessary with m; [| done].
      revert Hproduce
      ; apply VLSM_incl_can_produce, pre_loaded_vlsm_incl_pre_loaded_with_all_messages.
Qed.

(** Under [MessageDependencies] assumptions, if a message [has_been_sent]
in a state <<s>>, then any of its direct dependencies [has_been_observed].
*)
Lemma msg_dep_has_been_sent
  `{MessageDependencies}
  s
  (Hs : valid_state_prop (pre_loaded_with_all_messages_vlsm X) s)
  m
  (Hsent : has_been_sent X s m)
  : forall dm, msg_dep_rel dm m -> has_been_observed X s dm.
Proof.
  revert m Hsent; induction Hs using valid_state_prop_ind; intro m.
  - intro Hbs; contradict Hbs; eapply oracle_no_inits; [| done].
    apply has_been_sent_stepwise_from_trace.
  - rewrite has_been_sent_step_update by done; intros [-> | Hrcv] dm Hdm.
    + eapply message_dependencies_are_necessary; [by eexists _,_ | done].
    + rewrite has_been_observed_step_update by done; right.
      by eapply IHHs.
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
  revert m Hreceived; induction Hs using valid_state_prop_ind; intro m.
  - intro Hbr; contradict Hbr; eapply oracle_no_inits; [| done].
    apply has_been_received_stepwise_from_trace.
  - rewrite has_been_received_step_update by done; intros [-> | Hrcv] dm Hdm
    ; rewrite has_been_observed_step_update by done; right.
    + by eapply Hfull; [apply Ht|].
    + by eapply IHHs.
Qed.

(** By combining Lemmas [msg_dep_has_been_sent] and [full_node_has_been_received],
the [msg_dep_rel]ation reflects the [has_been_observed] predicate.
*)
Lemma msg_dep_full_node_reflects_has_been_observed
  `{MessageDependencies}
  (Hfull : message_dependencies_full_node_condition_prop)
  s
  (Hs : valid_state_prop (pre_loaded_with_all_messages_vlsm X) s)
  : forall dm m, msg_dep_rel dm m ->
    has_been_observed X s m -> has_been_observed X s dm.
Proof.
  intros dm m Hdm [Hsent|Hreceived].
  - by eapply msg_dep_has_been_sent.
  - by eapply full_node_has_been_received.
Qed.

(** Under full-node assumptions, the [msg_dep_happens_before] relation
reflects the [has_been_observed] predicate.
*)
Lemma msg_dep_full_node_happens_before_reflects_has_been_observed
  `{MessageDependencies}
  (Hfull : message_dependencies_full_node_condition_prop)
  s
  (Hs : valid_state_prop (pre_loaded_with_all_messages_vlsm X) s)
  : forall dm m, msg_dep_happens_before dm m ->
    has_been_observed X s m -> has_been_observed X s dm.
Proof.
  intros dm m Hdm Hobs.
  eapply msg_dep_happens_before_reflect; [|done ..].
  by apply msg_dep_full_node_reflects_has_been_observed.
Qed.

(** Under full-node assumptions, it it is valid to receive a message in a state
then any of its happens-before dependencies [has_been_observed] in that state.
*)
Lemma msg_dep_full_node_input_valid_happens_before_has_been_observed
  `{MessageDependencies}
  (Hfull : message_dependencies_full_node_condition_prop)
  l s m
  (Hvalid : input_valid (pre_loaded_with_all_messages_vlsm X) l (s, Some m))
  : forall dm, msg_dep_happens_before dm m ->
    has_been_observed X s dm.
Proof.
  intro dm; rewrite msg_dep_happens_before_iff_one; intros [Hdm | (dm' & Hdm' & Hdm)].
  - eapply Hfull; [apply Hvalid | done].
  - eapply msg_dep_happens_before_reflect; [| done |].
    + apply msg_dep_full_node_reflects_has_been_observed; [apply Hfull | apply Hvalid].
    + eapply Hfull; [apply Hvalid | done].
Qed.

End sec_message_dependencies.

(* Given the VLSM for which it's defined, the other arguments (message,
message_dependencies function, [HasBeenSentCapability] and
[HasBeenReceivedCapability]) can be inferred from that.
*)
Global Hint Mode MessageDependencies - - ! - - : typeclass_instances.

Section sec_composite_message_dependencies.

Context
  {message : Type}
  (message_dependencies : message -> set message)
  `{finite.Finite index}
  (IM : index -> VLSM message)
  `{forall i, HasBeenSentCapability (IM i)}
  `{forall i, HasBeenReceivedCapability (IM i)}
  `{forall i, MessageDependencies message_dependencies (IM i)}
  .

(** If all of the components satisfy the [MessageDependencies] assumptions,
then their free composition will also do so.
*)
Global Instance composite_message_dependencies
  : MessageDependencies message_dependencies (free_composite_vlsm IM).
Proof.
  split.
  - intros m s ((is, iom) & (i, li) & Ht) dm Hdm.
    apply composite_has_been_observed_free_iff.
    eapply composite_has_been_observed_from_component.
    eapply message_dependencies_are_necessary; [typeclasses eauto | | done].
    exists (is i, iom), li.
    revert Ht.
    apply
      (VLSM_projection_input_valid_transition (preloaded_component_projection IM _))
      with (lY := li).
    unfold composite_project_label; cbn.
    case_decide as Heqi; [| done].
    by replace Heqi with (@eq_refl index i) by (apply Eqdep_dec.UIP_dec; done).
  - intros m Hemit.
    apply can_emit_composite_project in Hemit as [j Hemitj].
    eapply message_dependencies_are_sufficient in Hemitj; [|typeclasses eauto].
    revert Hemitj.
    eapply VLSM_full_projection_can_emit.
    apply lift_to_composite_generalized_preloaded_vlsm_full_projection.
    itauto.
Qed.

Lemma msg_dep_reflects_free_validity
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  (X := free_composite_vlsm IM)
  : forall dm m, msg_dep_rel message_dependencies dm m ->
    valid_message_prop X m -> valid_message_prop X dm.
Proof.
  intros dm m Hdm.
  rewrite !emitted_messages_are_valid_iff.
  intros [[i [[im Him] _]] | Hemit]
  ; [contradict Him; apply no_initial_messages_in_IM | right].
  pose proof (vlsm_is_pre_loaded_with_False X) as XeqXFalse.
  apply (VLSM_eq_can_emit XeqXFalse).
  cut (valid_message_prop (pre_loaded_vlsm X (fun _ => False)) dm).
  {
    clear -no_initial_messages_in_IM.
    rewrite emitted_messages_are_valid_iff.
    intros [[[i [[im Him] _]] | Hpreloaded] | Hemit]; try itauto.
    contradict Him; apply no_initial_messages_in_IM.
  }
  eapply msg_dep_reflects_validity.
  - apply composite_message_dependencies.
  - intros _ [i [[im Him] _]].
    contradict Him; apply no_initial_messages_in_IM.
  - itauto.
  - done.
  - apply emitted_messages_are_valid_iff.
    apply (VLSM_eq_can_emit XeqXFalse) in Hemit.
    auto.
Qed.

Lemma msg_dep_reflects_happens_before_free_validity
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  (X := free_composite_vlsm IM)
  : forall dm m, msg_dep_happens_before message_dependencies dm m ->
    valid_message_prop X m -> valid_message_prop X dm.
Proof.
  by apply msg_dep_happens_before_reflect, msg_dep_reflects_free_validity.
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
  - by apply composite_no_initial_valid_messages_emitted_by_sender.
  - by eapply msg_dep_reflects_happens_before_free_validity.
Qed.

End sec_composite_message_dependencies.

Section sec_sub_composite_message_dependencies.

Context
  {message : Type}
  (message_dependencies : message -> set message)
  `{EqDecision index}
  (IM : index -> VLSM message)
  `{forall i, HasBeenSentCapability (IM i)}
  `{forall i, HasBeenReceivedCapability (IM i)}
  `{forall i, MessageDependencies message_dependencies (IM i)}
  (indices : set index)
  .

Lemma msg_dep_reflects_sub_free_validity
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  (P : message -> Prop)
  (Hreflects : forall dm m, msg_dep_rel message_dependencies dm m -> P m -> P dm)
  (X := free_composite_vlsm (sub_IM IM indices))
  : forall dm m, msg_dep_rel message_dependencies dm m ->
    valid_message_prop (pre_loaded_vlsm X P) m ->
    valid_message_prop (pre_loaded_vlsm X P) dm.
Proof.
  eapply msg_dep_reflects_validity; [| | done].
  - typeclasses eauto.
  - intros m [sub_i [[im Him] Heqm]].
    destruct_dec_sig sub_i i Hi Heqsub_i; subst.
    contradict Him; apply no_initial_messages_in_IM.
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

(* given the message type, we can usually look up the functions for
message dependencies *)
Global Hint Mode FullMessageDependencies ! - - : typeclass_instances.

Section full_message_dependencies_happens_before.

Context
  `{EqDecision message}
  (message_dependencies : message -> set message)
  (full_message_dependencies : message -> set message)
  `{FullMessageDependencies _ message_dependencies full_message_dependencies}
  .

Global Instance msg_dep_happens_before_dec :
 RelDecision (msg_dep_happens_before message_dependencies).
Proof.
 refine
   (fun m1 m2 =>
      match decide (m1 ∈ full_message_dependencies m2) with
      | left Hdec => left _
      | right Hdec => right _
      end);
  by rewrite <- full_message_dependencies_happens_before.
Qed.

Global Instance msg_dep_happens_before_irrefl :
  Irreflexive (msg_dep_happens_before message_dependencies).
Proof.
  intros m Hm.
  contradict Hm.
  rewrite <- full_message_dependencies_happens_before.
  apply full_message_dependencies_irreflexive.
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
  rewrite <- (cons_length dm).
  apply NoDup_subseteq_length.
  - constructor.
    + apply full_message_dependencies_irreflexive.
    + apply full_message_dependencies_nodups.
  - intros m' Hm'. apply elem_of_cons in Hm' as [-> | Hm'].
    + by apply full_message_dependencies_happens_before.
    + revert Hm'.
      setoid_rewrite full_message_dependencies_happens_before.
      intro Hm'dm.
      by transitivity dm.
Qed.

Lemma FullMessageDependencies_ind
  (P : message -> Prop)
  m
  (IHm : forall dm, dm ∈ full_message_dependencies m ->
    (forall dm0, dm0 ∈ full_message_dependencies dm -> P dm0) -> P dm)
  : forall dm, dm ∈ full_message_dependencies m -> P dm.
Proof.
  induction m  as (m & Hm) using (well_founded_ind msg_dep_happens_before_wf).
  intros dm Hdm.
  apply IHm; [done |].
  apply Hm; [by apply full_message_dependencies_happens_before |].
  intros dm0 Hdm0.
  apply IHm, full_message_dependencies_happens_before.
  by transitivity dm; apply full_message_dependencies_happens_before.
Qed.

End full_message_dependencies_happens_before.
