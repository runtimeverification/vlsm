From Cdcl Require Import Itauto. Local Tactic Notation "itauto" := itauto auto.
From Coq Require Import FinFun Relations.Relation_Operators Program.Equality.
From stdpp Require Import prelude.
From VLSM.Lib Require Import Preamble ListExtras FinFunExtras StdppListSet Measurable.
From VLSM.Core Require Import VLSM VLSMProjections Composition Validator ProjectionTraces.
From VLSM.Core Require Import SubProjectionTraces Equivocation EquivocationProjections.

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
Definition msg_dep_happens_before : relation message := tc msg_dep_rel.

(** Unrolling one the [msg_dep_happens_before] relation one step. *)
Lemma msg_dep_happens_before_iff_one x z
  : msg_dep_happens_before x z <->
    msg_dep_rel x z \/ exists y, msg_dep_happens_before x y /\ msg_dep_rel y z.
Proof. apply tc_r_iff. Qed.

(** If the [msg_dep_rel]ation reflects a predicate <<P>>, then
[msg_dep_happens_before] will also reflect it. *)
Lemma msg_dep_happens_before_reflect
  (P : message -> Prop)
  (Hreflects : forall dm m, msg_dep_rel dm m -> P m -> P dm)
  : forall dm m, msg_dep_happens_before dm m -> P m -> P dm.
Proof. by apply tc_reflect. Qed.

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

(** ** Local Equivocation Based on Message Dependencies

Inspired by the definitions of observability and local equivocation given for
the ELMO protocol, we introduce abstract notions for local equivocation based
on message dependencies.
*)
Section sec_message_dependencies_equivocation.

Context
  {message : Type}
  (X : VLSM message)
  `{!HasBeenSentCapability X}
  `{!HasBeenReceivedCapability X}
  (message_dependencies : message -> set message)
  `(sender : message -> option validator)
  (R := pre_loaded_with_all_messages_vlsm X)
  .

(**
A message can be recursively observed in a state if it either has been directly
observed in the state (as sent or received), or it [msg_dep_happens_before]
a directly observed message.
*)
Inductive HasBeenRecursivelyObserved (s : vstate X) (m : message) : Prop :=
| hbro_directly :
    has_been_observed X s m ->
    HasBeenRecursivelyObserved s m
| hbro_indirectly :
    forall m',
      has_been_observed X s m' ->
      msg_dep_happens_before message_dependencies m m' ->
      HasBeenRecursivelyObserved s m.

(**
A pair of messages constitutes a (local) evidence of equivocation for a
validator <<v>> in a state <<s>> is both messages have <<v>> as a sender,
each message [HasBeenRecursivelyObserved] in <<s>>, and the messages are not
comparable through the [msg_dep_happens_before] relation.
*)
Record MsgDepLocalEquivocationEvidence
  (s : vstate X) (v : validator) (m1 m2 : message) : Prop :=
  {
    mdlee_sender1 : sender m1 = Some v;
    mdlee_sender2 : sender m2 = Some v;
    mdlee_observed1 : HasBeenRecursivelyObserved s m1;
    mdlee_observed2 : HasBeenRecursivelyObserved s m2;
    mdlee_incomparable : ~ Comparable (msg_dep_happens_before message_dependencies) m1 m2;
  }.

Definition msg_dep_is_locally_equivocating (s : vstate X) (v : validator) : Prop :=
  exists m1 m2, MsgDepLocalEquivocationEvidence s v m1 m2.

(**
Under the full-node assumptions, due to Lemma [msg_dep_full_node_happens_before_reflects_has_been_observed],
we can give a simpler alternative to [MsgDepLocalEquivocationEvidence] which
only requires that each message [has_been_observed] directly in the state.
*)
Record FullNodeLocalEquivocationEvidence
  (s : vstate X) (v : validator) (m1 m2 : message) : Prop :=
  {
    fnlee_sender1 : sender m1 = Some v;
    fnlee_sender2 : sender m2 = Some v;
    fnlee_observed1 : has_been_observed X s m1;
    fnlee_observed2 : has_been_observed X s m2;
    fnlee_incomparable : ~ Comparable (msg_dep_happens_before message_dependencies) m1 m2;
  }.

Definition full_node_is_locally_equivocating (s : vstate X) (v : validator) : Prop :=
  exists m1 m2, FullNodeLocalEquivocationEvidence s v m1 m2.

(**
If the states and messages are more tightly coupled (e.g., there is a unique 
state from which a given message can be emitted), then the sent messages of
a state would be totally ordered by the [msg_dep_rel]ation.
*)
Definition has_been_sent_msg_dep_comparable_prop : Prop :=
  forall (s : vstate X), valid_state_prop R s ->
  forall (m1 m2 : message),
    has_been_sent X s m1 ->
    has_been_sent X s m2 ->
    Comparable (msg_dep_rel message_dependencies) m1 m2.

(**
We present yet another definition for local evidence of equivocation assuming
both full-node and the [has_been_sent_msg_dep_comparable_prop]erty.
*)
Record FullNodeSentLocalEquivocationEvidence
  (s : vstate X) (v : validator) (m1 m2 : message) : Prop :=
  {
    fnclee_sender1 : sender m1 = Some v;
    fnclee_sender2 : sender m2 = Some v;
    fnclee_observed1 : has_been_observed X s m1;
    fnclee_observed2 : has_been_observed X s m2;
    fnclee_incomparable : ~ Comparable (msg_dep_rel message_dependencies) m1 m2;
  }.

Definition full_node_is_sent_locally_equivocating
  (s : vstate X) (v : validator) : Prop :=
  exists m1 m2, FullNodeSentLocalEquivocationEvidence s v m1 m2.

Lemma full_node_is_sent_locally_equivocating_weaker s v:
  full_node_is_locally_equivocating s v ->
  full_node_is_sent_locally_equivocating s v.
Proof.
  intros (m1 & m2 & [Hsender1 Hsender2 Hobs1 Hobs2 Hncomp]).
  exists m1, m2; constructor; [done.. |].
  by contradict Hncomp; apply tc_Comparable.
Qed.

Lemma full_node_is_locally_equivocating_stronger s v:
  full_node_is_locally_equivocating s v ->
  msg_dep_is_locally_equivocating s v.
Proof.
  intros (m1 & m2 & []).
  by exists m1, m2; constructor; [| | constructor | constructor |].
Qed.

(**
Under [MessageDependencies] and full-node assumptions, any message which
[HasBeenRecursivelyObserved] in a state, [has_been_observed] in that state, too.
*)
Lemma full_node_HasBeenRecursivelyObserved_is_observed
  `{!MessageDependencies message_dependencies X}
  (Hfull : message_dependencies_full_node_condition_prop message_dependencies X)
  : forall s, valid_state_prop R s ->
    forall m, HasBeenRecursivelyObserved s m <-> has_been_observed X s m.
Proof.
  intros s Hs m; split; [| by intros; constructor].
  intros [Hobs | m' Hobs Hhb]; [done |].
  by eapply msg_dep_full_node_happens_before_reflects_has_been_observed.
Qed.

(**
Under [MessageDependencies] and full-node assumptions, the two notions of
local equivocation defined above are equivalent.
*)
Lemma full_node_is_locally_equivocating_iff
  `{!MessageDependencies message_dependencies X}
  (Hfull : message_dependencies_full_node_condition_prop message_dependencies X)
  : forall s, valid_state_prop R s ->
    forall v,
      msg_dep_is_locally_equivocating s v
        <->
      full_node_is_locally_equivocating s v.
Proof.
  intros s Hs v; split; [| apply full_node_is_locally_equivocating_stronger].
  intros (m1 & m2 & [Hsender1 Hsender2 Hobs1 Hobs2 Hncomp]); exists m1, m2;
    split; [done | done | | | done];
    by apply full_node_HasBeenRecursivelyObserved_is_observed.
Qed.

End sec_message_dependencies_equivocation.

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

(** ** Global Equivocation Based on Message Dependencies

Inspired by the definitions of observability and global equivocation given for
the ELMO protocol, we introduce abstract notions for global equivocation based
on message dependencies.
*)

Section sec_composite_message_dependencies_equivocation.

Context
  {message : Type}
  (message_dependencies : message -> set message)
  `{EqDecision index}
  (IM : index -> VLSM message)
  `{forall i, HasBeenSentCapability (IM i)}
  `{forall i, HasBeenReceivedCapability (IM i)}
  `(sender : message -> option validator)
  (Free := free_composite_vlsm IM)
  (RFree := pre_loaded_with_all_messages_vlsm Free)
  .

(**
A message can be recursively observed in a composite state if it either has been
directly observed in the state (as sent or received), or it
[msg_dep_happens_before] a directly observed message.
*)
Inductive CompositeHasBeenRecursivelyObserved
  (s : composite_state IM) (m : message) : Prop :=
| chbro_directly :
    composite_has_been_observed IM s m ->
    CompositeHasBeenRecursivelyObserved s m
| chbro_indirectly :
    forall m',
      composite_has_been_observed IM s m' ->
      msg_dep_happens_before message_dependencies m m' ->
      CompositeHasBeenRecursivelyObserved s m.

Lemma composite_HasBeenRecursivelyObserved_lift : forall s m i,
  HasBeenRecursivelyObserved (IM i) message_dependencies (s i) m ->
  CompositeHasBeenRecursivelyObserved s m.
Proof.
  intros s m i [].
  - by constructor 1; eexists.
  - by econstructor 2; [eexists |].
Qed.

Lemma composite_HasBeenRecursivelyObserved_iff : forall s m,
  CompositeHasBeenRecursivelyObserved s m
    <->
  exists i, HasBeenRecursivelyObserved (IM i) message_dependencies (s i) m.
Proof.
  split; [| by intros []; eapply composite_HasBeenRecursivelyObserved_lift].
  intros [[i Hobsi] |m' [i Hobsi] Hmm'];
    exists i; [by constructor 1 | by econstructor 2].
Qed.

(**
A messages constitutes a (global) evidence of equivocation for a
validator <<v>> in a composite state <<s>> is the messages has <<v>> as a sender,
it [CompositeHasBeenRecursivelyObserved] in <<s>>, but not
[composite_has_been_sent] in <<s>>.
*)
Record MsgDepGlobalEquivocationEvidence
  (s : composite_state IM) (v : validator) (m : message) : Prop :=
  {
    mdgee_sender : sender m = Some v;
    mdgee_rec_observed : CompositeHasBeenRecursivelyObserved s m;
    mdgee_not_sent : ~ composite_has_been_sent IM s m;
  }.

Definition msg_dep_is_globally_equivocating
  (s : composite_state IM) (v : validator) : Prop :=
  exists m : message, MsgDepGlobalEquivocationEvidence s v m.

(**
Under the full-node assumptions, due to Lemma [msg_dep_full_node_happens_before_reflects_has_been_observed],
we can give a simpler alternative to [MsgDepGlobalEquivocationEvidence] which
only requires that the message [composite_has_been_received] in the state.
*)
Record FullNodeGlobalEquivocationEvidence
  (s : composite_state IM) (v : validator) (m : message) : Prop :=
  {
    fngee_sender : sender m = Some v;
    fngee_received : composite_has_been_received IM s m;
    fngee_not_sent : ~ composite_has_been_sent IM s m;
  }.

Definition full_node_is_globally_equivocating
  (s : composite_state IM) (v : validator) : Prop :=
  exists m : message, FullNodeGlobalEquivocationEvidence s v m.

Lemma full_node_is_globally_equivocating_stronger s v:
  full_node_is_globally_equivocating s v ->
  msg_dep_is_globally_equivocating s v.
Proof.
  intros [m []]; exists m; constructor; [done | | done].
  by constructor 1; apply composite_has_been_observed_sent_received_iff; right.
Qed.

Lemma full_node_is_globally_equivocating_iff
  `{forall i, MessageDependencies message_dependencies (IM i)}
  (Hfull : forall i, message_dependencies_full_node_condition_prop message_dependencies (IM i))
  : forall s, valid_state_prop RFree s ->
    forall v,
      msg_dep_is_globally_equivocating s v
        <->
      full_node_is_globally_equivocating s v.
Proof.
  intros s Hs v; split; [| apply full_node_is_globally_equivocating_stronger].
  intros [m [Hsender Hobs Hnsent]]; exists m; split; [done | | done].
  cut (composite_has_been_observed IM s m).
  {
    by rewrite composite_has_been_observed_sent_received_iff; intros [].
  }
  destruct Hobs as [Hobs | m' Hobs Hhb]; [done |].
  destruct Hobs as [i Hobs]; exists i.
  by eapply msg_dep_full_node_happens_before_reflects_has_been_observed
  ; [| | apply valid_state_project_preloaded_to_preloaded | |].
Qed.

Lemma msg_dep_locally_is_globally_equivocating
  (A : validator -> index)
  (Hsafety : sender_safety_alt_prop IM A sender)
  (Hsent_comparable :
    forall i, has_been_sent_msg_dep_comparable_prop (IM i) message_dependencies)
  : forall s, valid_state_prop RFree s ->
    forall i v,
    msg_dep_is_locally_equivocating (IM i) message_dependencies sender (s i) v ->
    msg_dep_is_globally_equivocating s v.
Proof.
  intros s Hs i v (m1 & m2 & [Hsender1 Hsender2 Hobs1 Hobs2 Hncomp]).
  apply valid_state_has_trace in Hs as Htr.
  destruct Htr as (? & ? & ?).
  destruct (decide (has_been_sent (IM (A v)) (s (A v)) m1));
    [destruct (decide (has_been_sent (IM (A v)) (s (A v)) m2)) |]; cycle 1.
  1,2: eexists; split;
      [..| by contradict n; eapply has_been_sent_iff_by_sender];
      [done | by eapply composite_HasBeenRecursivelyObserved_lift].
  contradict Hncomp; eapply tc_Comparable, Hsent_comparable; [| done..].
  by eapply valid_state_project_preloaded_to_preloaded.
Qed.

Lemma full_node_sent_locally_is_globally_equivocating
  (A : validator -> index)
  (Hsafety : sender_safety_alt_prop IM A sender)
  (Hsent_comparable :
    forall i, has_been_sent_msg_dep_comparable_prop (IM i) message_dependencies)
  : forall s, valid_state_prop RFree s ->
    forall i v,
    full_node_is_sent_locally_equivocating (IM i) message_dependencies sender (s i) v ->
    msg_dep_is_globally_equivocating s v.
Proof.
  intros s Hs i v (m1 & m2 & [Hsender1 Hsender2 Hobs1 Hobs2 Hncomp]).
  apply valid_state_has_trace in Hs as Htr.
  destruct Htr as (? & ? & ?).
  destruct (decide (has_been_sent (IM (A v)) (s (A v)) m1));
    [destruct (decide (has_been_sent (IM (A v)) (s (A v)) m2)) |]; cycle 1.
  1,2: eexists; split; cycle 2; 
      [by contradict n; eapply has_been_sent_iff_by_sender | done |];
      by constructor 1; eexists.
  contradict Hncomp; eapply Hsent_comparable; [| done..].
  by eapply valid_state_project_preloaded_to_preloaded.
Qed.

End sec_composite_message_dependencies_equivocation.

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

Lemma msg_dep_rel_full_message_dependecies_subset :
  forall x y : message, msg_dep_rel message_dependencies x y ->
    full_message_dependencies x ⊆ full_message_dependencies y.
Proof.
  intros; intros z Hz.
  apply full_message_dependencies_happens_before.
  transitivity x; [by apply full_message_dependencies_happens_before |].
  by constructor.
Qed.

Lemma msg_dep_happens_before_wf : well_founded (msg_dep_happens_before message_dependencies).
Proof.
  apply tc_wf_projected with (<) (fun m => length (full_message_dependencies m));
    [typeclasses eauto | | apply Wf_nat.lt_wf ].
  intros; unfold lt.
  change (S _) with (length (x :: full_message_dependencies x)).
  apply NoDup_subseteq_length.
  - constructor.
    + apply full_message_dependencies_irreflexive.
    + apply full_message_dependencies_nodups.
  - intros z Hz; inversion Hz; subst;
      [| by eapply msg_dep_rel_full_message_dependecies_subset].
    by apply full_message_dependencies_happens_before; constructor.
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

(** ** Basic validation condition for free composition

In this section we show (Lemma [valid_free_validating_is_message_validating])
that, under [FullMessageDependencies] assumptions, if the validity predicate
ensures that message itself and all of its dependencies can be emitted using
only its dependencies, then the input message is valid for the free composition.
Thus, the node itself is a validator for the free composition.
*)

Section free_composition_validators.

Context
  {message : Type}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  `{forall i, HasBeenSentCapability (IM i)}
  `{forall i, HasBeenReceivedCapability (IM i)}
  `{FullMessageDependencies message message_dependencies full_message_dependencies}
  {validator : Type}
  (A : validator -> index)
  (sender : message -> option validator)
  .

(**
The property of a message of having a sender and being emittable by the
component corresponding to its sender pre-loaded with the dependencies of the
message.
*)
Inductive Emittable_from_dependencies_prop (m : message) : Prop :=
  | efdp : forall (v : validator) (Hsender : sender m = Some v)
              (Hemittable : can_emit
                (pre_loaded_vlsm (IM (A v)) (fun dm => dm ∈ message_dependencies m))
                m),
               Emittable_from_dependencies_prop m.

Definition emittable_from_dependencies_prop (m : message) : Prop :=
  match sender m with
  | None => False
  | Some v => can_emit (pre_loaded_vlsm (IM (A v)) (fun dm => dm ∈ message_dependencies m)) m
  end.

Lemma emittable_from_dependencies_prop_iff m
  : Emittable_from_dependencies_prop m <-> emittable_from_dependencies_prop m.
Proof.
  unfold emittable_from_dependencies_prop; split.
  - by inversion 1; rewrite Hsender.
  - destruct (sender m) eqn: Hsender; [by split with v | inversion 1].
Qed.

(**
The property of a message that both itself and all of its dependencies are
emittable from their dependencies.
*)
Definition all_dependencies_emittable_from_dependencies_prop (m : message) : Prop :=
  forall dm, dm ∈ m :: full_message_dependencies m -> Emittable_from_dependencies_prop dm.

(**
The property of requiring that the validity predicate subsumes the
[all_dependencies_emittable_from_dependencies_prop]erty.
*)
Definition valid_all_dependencies_emittable_from_dependencies_prop (i : index) : Prop :=
  forall l s m, input_valid (pre_loaded_with_all_messages_vlsm (IM i)) l (s, Some m) ->
    all_dependencies_emittable_from_dependencies_prop m.

(**
If a message can be emitted by a node preloaded with the message's direct
dependencies, and if all the dependencies of the message are valid for the
free composition, then the message itself is valid for the free composition.
*)
Lemma free_valid_from_valid_dependencies
  m i
  (Hm : can_emit (pre_loaded_vlsm (IM i) (fun dm => dm ∈ message_dependencies m)) m)
  (Hdeps :
    forall dm, dm ∈ full_message_dependencies m ->
      valid_message_prop (free_composite_vlsm IM) dm)
  : valid_message_prop (free_composite_vlsm IM) m.
Proof.
  eapply emitted_messages_are_valid, free_valid_preloaded_lifts_can_be_emitted; [| done].
  by intros; apply Hdeps, full_message_dependencies_happens_before, msg_dep_happens_before_iff_one;
  left.
Qed.

(**
Any message with the [all_dependencies_emittable_from_dependencies_prop]erty
is valid for the free composition.
*)
Lemma free_valid_from_all_dependencies_emitable_from_dependencies :
  forall m,
    all_dependencies_emittable_from_dependencies_prop m ->
      valid_message_prop (free_composite_vlsm IM) m.
Proof.
  intros m Hm.
  specialize (Hm m) as Hemit; spec Hemit; [left |].
  inversion Hemit as [v _ Hemit']; clear Hemit.
  apply free_valid_from_valid_dependencies with (A v); [done | clear v Hemit'].
  eapply FullMessageDependencies_ind; [done |].
  intros dm Hdm Hdeps.
  specialize (Hm dm); spec Hm; [by right |].
  inversion Hm as [v _ ?]; clear Hm.
  by apply free_valid_from_valid_dependencies with (A v).
Qed.

(**
If a node in a composition satisfies the
[valid_all_dependencies_emittable_from_dependencies_prop]erty, then it also has
the [component_message_validator_prop]erty, that is, it is a validator for the
free composition.
*)
Lemma valid_free_validating_is_message_validating
  : forall i, valid_all_dependencies_emittable_from_dependencies_prop i ->
    component_message_validator_prop IM (free_constraint IM) i.
Proof.
  by intros i Hvalidating l s im Hv
  ; eapply free_valid_from_all_dependencies_emitable_from_dependencies, Hvalidating.
Qed.

(**
Under several additional (but regularly used) assumptions, including the
[MessageDependencies] assumptions, the [channel_authentication_prop]erty and the
[no_initial_messages_in_IM_prop]erty, we can show that the
[component_message_validator_prop]erty is fully equivalent to the
[valid_all_dependencies_emittable_from_dependencies_prop]erty.
*)
Lemma valid_free_validating_equiv_message_validating
  `{forall i, MessageDependencies message_dependencies (IM i)}
  (Hchannel : channel_authentication_prop  IM A sender)
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  : forall i, component_message_validator_prop IM (free_constraint IM) i <->
  valid_all_dependencies_emittable_from_dependencies_prop i.
Proof.
  intros i; split; [| apply valid_free_validating_is_message_validating].
  intros Hvalidator l s m Hv dm Hdm.
  specialize (Hvalidator l s m Hv).
  inversion Hdm as [| ? ? ? Hin]; subst.
  - eapply composite_no_initial_valid_messages_emitted_by_sender in Hvalidator
        as (v & Hsender & Hemit); [| done | done].
    exists v; [done |].
    by eapply message_dependencies_are_sufficient.
  - apply full_message_dependencies_happens_before in Hin.
    eapply msg_dep_happens_before_composite_no_initial_valid_messages_emitted_by_sender in Hin
        as (v & Hsender & Hemit); [| done ..].
    exists v; [done |].
    by eapply message_dependencies_are_sufficient.
Qed.

End free_composition_validators.
