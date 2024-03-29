From VLSM.Lib Require Import Itauto.
From stdpp Require Import prelude.
From VLSM.Lib Require Import Preamble ListExtras FinSetExtras.
From VLSM.Core Require Import VLSM VLSMProjections Composition ProjectionTraces.
From VLSM.Core Require Import SubProjectionTraces Equivocation EquivocationProjections.

(** * Core: VLSM Message Dependencies

  An abstract framework for the full-node condition.
  Assumes that each message has an associated set of <<message_dependencies>>.

  Given a <<message_dependencies>> function, we can define a (direct) message
  dependency relation [msg_dep_rel] as follows:
  message <<m1>> is a (direct) dependency of message <<m2>> if <<m1>> belongs
  to the <<message_dependencies>> of <<m2>>.

  The transitive closure of such a relation is a happens-before relation which
  we denote by [msg_dep_happens_before].
*)
Definition msg_dep_rel
  `{FinSet message Cm} `(message_dependencies : message -> Cm) : relation message :=
  fun m1 m2 => m1 ∈ message_dependencies m2.

Definition msg_dep_happens_before
  `{FinSet message Cm} `(message_dependencies : message -> Cm) : relation message :=
  tc (msg_dep_rel message_dependencies).

(**
  The (local) full node condition for a given <<message_dependencies>> function
  requires that a state (receiving the message) has previously directly observed
  all of <<m>>'s dependencies.
*)
Definition message_dependencies_full_node_condition
  `(X : VLSM message)
  `{FinSet message Cm}
  (message_dependencies : message -> Cm)
  `{HasBeenSentCapability message X}
  `{HasBeenReceivedCapability message X}
  (s : state X)
  (m : message)
  : Prop :=
  forall dm, dm ∈ message_dependencies m -> has_been_directly_observed X s dm.

(**
  [MessageDependencies] characterize a <<message_dependencies>> function
  through two properties:

  - Necessity: All dependent messages for a message <<m>>m are required to be
  directly observed by origin state of a transition emitting the message <<m>>.

  - Sufficiency: A message can be produced by the machine preloaded with its
  dependencies.

  Additionally, we require that the induced [msg_dep_happens_before] relation
  is irreflexive (i.e., a message cannot recursively observe itself).

  [MessageDependencies], together with [message_dependencies_full_node_condition_prop],
  constitute the _strict full node assumption_.
*)
Class MessageDependencies
  `(X : VLSM message)
  `{FinSet message Cm}
  (message_dependencies : message -> Cm)
  `{!HasBeenSentCapability X}
  `{!HasBeenReceivedCapability X}
  `{!Irreflexive (msg_dep_happens_before message_dependencies)}
  : Prop :=
{
  message_dependencies_are_necessary (m : message)
    `(can_produce (preloaded_with_all_messages_vlsm X) s' m)
    : message_dependencies_full_node_condition X message_dependencies s' m;
  message_dependencies_are_sufficient (m : message)
    `(can_emit (preloaded_with_all_messages_vlsm X) m)
    : can_emit (preloaded_vlsm X (fun msg => msg ∈ message_dependencies m)) m
}.

(*
  Given the VLSM for which it's defined, the other arguments (message,
  message_dependencies function, [HasBeenSentCapability] and
  [HasBeenReceivedCapability]) can be inferred from that.
*)
#[global] Hint Mode MessageDependencies - ! - - - - - - - - - - - - - - : typeclass_instances.

Section sec_message_dependencies.

Context
  `(X : VLSM message)
  `{FinSet message Cm}
  (message_dependencies : message -> Cm)
  `{!HasBeenSentCapability X}
  `{!HasBeenReceivedCapability X}
  `{!Irreflexive (msg_dep_happens_before message_dependencies)}
  `{!MessageDependencies X message_dependencies}
  .

(**
  A VLSM has the [message_dependencies_full_node_condition_prop]
  if the validity of receiving a message in a state implies the
  [message_dependencies_full_node_condition] for that state and message
*)
Definition message_dependencies_full_node_condition_prop : Prop :=
  forall l s m,
  valid X l (s, Some m) ->
  message_dependencies_full_node_condition X message_dependencies s m.

(** Unrolling one the [msg_dep_happens_before] relation one step. *)
Lemma msg_dep_happens_before_iff_one x z
  : msg_dep_happens_before message_dependencies x z <->
    msg_dep_rel message_dependencies x z \/
    exists y, msg_dep_happens_before message_dependencies x y /\ msg_dep_rel message_dependencies y z.
Proof. by apply tc_r_iff. Qed.

(**
  If the [msg_dep_rel]ation reflects a predicate <<P>>, then
  [msg_dep_happens_before] will also reflect it.
*)
Lemma msg_dep_happens_before_reflect
  (P : message -> Prop)
  (Hreflects : forall dm m, msg_dep_rel message_dependencies dm m -> P m -> P dm)
  : forall dm m, msg_dep_happens_before message_dependencies dm m -> P m -> P dm.
Proof. by apply tc_reflect. Qed.

(**
  In the absence of initial messages, and if [msg_dep_rel]ation reflects
  the preloaded message property, then it also reflects the
  [valid_message_prop]erty.
*)
Lemma msg_dep_reflects_validity
  (no_initial_messages_in_X : forall m, ~ initial_message_prop X m)
  (P : message -> Prop)
  (Hreflects : forall dm m, msg_dep_rel message_dependencies dm m -> P m -> P dm)
  : forall dm m, msg_dep_rel message_dependencies dm m ->
    valid_message_prop (preloaded_vlsm X P) m ->
    valid_message_prop (preloaded_vlsm X P) dm.
Proof.
  intros dm m Hdm.
  rewrite emitted_messages_are_valid_iff, can_emit_iff.
  intros [Hinit | [s Hproduce]].
  - rewrite emitted_messages_are_valid_iff; left; right.
    apply Hreflects with m; [done |].
    destruct Hinit as [Hinit | Hp]; [| done].
    by contradict Hinit; apply no_initial_messages_in_X.
  - apply (directly_observed_valid (preloaded_vlsm X P) s).
    + by exists (Some m); apply can_produce_valid.
    + destruct X as [T M].
      eapply VLSM_incl_has_been_directly_observed
        with HasBeenSentCapability0 HasBeenReceivedCapability0; cycle 2.
      * eapply @message_dependencies_are_necessary; [done | | done].
        by apply (VLSM_incl_can_produce
          (preloaded_vlsm_incl_preloaded_with_all_messages (mk_vlsm M) P)).
      * by apply basic_VLSM_incl_preloaded; cbv.
      * apply (VLSM_incl_valid_state
          (preloaded_vlsm_incl_preloaded_with_all_messages (mk_vlsm M) P)).
        by eexists; eapply can_produce_valid.
Qed.

(**
  Under [MessageDependencies] assumptions, if a message [has_been_sent]
  in a state <<s>>, then any of its direct dependencies [has_been_directly_observed].
*)
Lemma msg_dep_has_been_sent
  s
  (Hs : constrained_state_prop X s)
  m
  (Hsent : has_been_sent X s m)
  : forall dm, msg_dep_rel message_dependencies dm m -> has_been_directly_observed X s dm.
Proof.
  revert m Hsent; induction Hs using valid_state_prop_ind; intro m.
  - intro Hbs; contradict Hbs.
    by apply has_been_sent_no_inits.
  - rewrite has_been_sent_step_update by done; intros [-> | Hrcv] dm Hdm.
    + by eapply message_dependencies_are_necessary; [eexists _, _ |].
    + by eapply has_been_directly_observed_step_update; [done |]; right; eapply IHHs.
Qed.

Lemma constrained_transition_preserves_message_dependencies_full_node_condition
  `(input_constrained_transition X lX (s, im) (s', om)) :
  forall m, message_dependencies_full_node_condition X message_dependencies s m ->
    message_dependencies_full_node_condition X message_dependencies s' m.
Proof.
  intros m Hm dm Hdm.
  eapply has_been_directly_observed_step_update; [done |].
  by right; apply Hm.
Qed.

(**
  If the [valid]ity predicate has the [message_dependencies_full_node_condition_prop]erty,
  then if a message [has_been_received] in a state <<s>>, any of its direct
  dependencies [has_been_directly_observed].
*)
Lemma full_node_has_been_received
  (Hfull : message_dependencies_full_node_condition_prop)
  s
  (Hs : constrained_state_prop X s)
  m
  (Hreceived : has_been_received X s m)
  : forall dm, msg_dep_rel message_dependencies dm m -> has_been_directly_observed X s dm.
Proof.
  revert m Hreceived; induction Hs using valid_state_prop_ind; intro m.
  - intro Hbr; contradict Hbr.
    by apply has_been_received_no_inits.
  - rewrite has_been_received_step_update by done; intros [-> | Hrcv] dm Hdm
    ; rewrite has_been_directly_observed_step_update by done; right.
    + by eapply Hfull; [apply Ht |].
    + by eapply IHHs.
Qed.

(**
  By combining Lemmas [msg_dep_has_been_sent] and [full_node_has_been_received],
  the [msg_dep_rel]ation reflects the [has_been_directly_observed] predicate.
*)
Lemma msg_dep_full_node_reflects_has_been_directly_observed
  (Hfull : message_dependencies_full_node_condition_prop)
  s
  (Hs : constrained_state_prop X s)
  : forall dm m, msg_dep_rel message_dependencies dm m ->
    has_been_directly_observed X s m -> has_been_directly_observed X s dm.
Proof.
  intros dm m Hdm [Hsent | Hreceived].
  - by eapply msg_dep_has_been_sent.
  - by eapply full_node_has_been_received.
Qed.

(**
  Under full-node assumptions, the [msg_dep_happens_before] relation
  reflects the [has_been_directly_observed] predicate.
*)
Lemma msg_dep_full_node_happens_before_reflects_has_been_directly_observed
  (Hfull : message_dependencies_full_node_condition_prop)
  s
  (Hs : constrained_state_prop X s)
  : forall dm m, msg_dep_happens_before message_dependencies dm m ->
    has_been_directly_observed X s m -> has_been_directly_observed X s dm.
Proof.
  intros dm m Hdm Hobs.
  eapply msg_dep_happens_before_reflect; [| done ..].
  by apply msg_dep_full_node_reflects_has_been_directly_observed.
Qed.

(**
  Under full-node assumptions, it is valid to receive a message in a state
  then any of its happens-before dependencies [has_been_directly_observed] in that state.
*)
Lemma msg_dep_full_node_input_valid_happens_before_has_been_directly_observed
  (Hfull : message_dependencies_full_node_condition_prop)
  l s m
  (Hvalid : input_constrained X l (s, Some m))
  : forall dm, msg_dep_happens_before message_dependencies dm m ->
    has_been_directly_observed X s dm.
Proof.
  intro dm; rewrite msg_dep_happens_before_iff_one; intros [Hdm | (dm' & Hdm' & Hdm)].
  - by eapply Hfull; [apply Hvalid |].
  - eapply msg_dep_happens_before_reflect; [| done |].
    + by apply msg_dep_full_node_reflects_has_been_directly_observed; [apply Hfull | apply Hvalid].
    + by eapply Hfull; [apply Hvalid |].
Qed.

End sec_message_dependencies.

(** ** Equivocation Based on Message Dependencies

  Inspired by the definitions of observability and local equivocation given for
  the ELMO protocol, we introduce abstract notions for local equivocation based
  on message dependencies.
*)

Section sec_message_dependencies_equivocation.

Context
  {message : Type}
  (X : VLSM message)
  `{FinSet message Cm}
  (message_dependencies : message -> Cm)
  `(sender : message -> option validator)
  `{!HasBeenSentCapability X}
  `{!HasBeenReceivedCapability X}
  `{!Irreflexive (msg_dep_happens_before message_dependencies)}
  .

(**
  A message can be (indirectly) observed in a state if it either has been directly
  observed in the state (as sent or received), or it happens before (in the sense
  of the [msg_dep_happens_before] relation) a directly observed message.
*)
Inductive HasBeenObserved (s : state X) (m : message) : Prop :=
| hbo_directly :
    has_been_directly_observed X s m ->
    HasBeenObserved s m
| hbo_indirectly :
    forall m',
      has_been_directly_observed X s m' ->
      msg_dep_happens_before message_dependencies m m' ->
      HasBeenObserved s m.

Lemma transition_preserves_HasBeenObserved :
  forall l s im s' om, input_constrained_transition X l (s, im) (s', om) ->
  forall msg, HasBeenObserved s msg -> HasBeenObserved s' msg.
Proof.
  intros * Ht msg Hbefore; inversion Hbefore as [Hobs | m Hobs Hdep].
  - by constructor; eapply has_been_directly_observed_step_update; [| right].
  - by econstructor 2; [| done]; eapply has_been_directly_observed_step_update; [| right].
Qed.

Lemma HasBeenObserved_step_update :
  forall l s im s' om, input_constrained_transition X l (s, im) (s', om) ->
  forall msg,
    HasBeenObserved s' msg
      <->
    HasBeenObserved s msg \/
    (exists m, (im = Some m \/ om = Some m) /\
      (msg = m \/ msg_dep_happens_before message_dependencies msg m)).
Proof.
  intros * Ht msg; split.
  - inversion 1 as [Hobs' | m' Hobs' Hdep];
      (eapply has_been_directly_observed_step_update in Hobs'; [| done]);
      destruct Hobs' as [Hnow | Hbefore].
    + by right; exists msg; split; [| left].
    + by left; constructor.
    + by right; exists m'; split; [| right].
    + by left; econstructor 2.
  - intros [Hbefore | (m & Hnow & [<- | Hdep])].
    + by eapply transition_preserves_HasBeenObserved.
    + by constructor; eapply has_been_directly_observed_step_update; [| left].
    + by econstructor 2; [| done]; eapply has_been_directly_observed_step_update; [| left].
Qed.

(**
  Message <<m1>> is in relation [ObservedBeforeSendTransition] with message <<m2>>
  if it [HasBeenObserved] in a state from which <<m2>> can be emitted in the next
  step.

  Note that we use [HasBeenObserved] instead of [has_been_directly_observed], which
  extends direct observability in a state (sent or received on a trace leading to
  that state) with the transitive closure of the [msg_dep_rel] (to include any
  message depending on a directly observed one).
*)
Inductive ObservedBeforeStateOrMessage
  : message -> state X -> option message -> Prop :=
| observed_before_state (m : message) (s : state X) (_oim : option message) :
    HasBeenObserved s m ->
    ObservedBeforeStateOrMessage m s _oim
| observed_is_message (m : message) (_s : state X) :
    ObservedBeforeStateOrMessage m _s (Some m)
| observed_before_message (m : message) (_s : state X) (im : message) :
    msg_dep_happens_before message_dependencies m im ->
    ObservedBeforeStateOrMessage m _s (Some im).

Record ObservedBeforeSendTransition
  (s : state X) (item : transition_item X) (m1 m2 : message) : Prop :=
{
  dobst_transition : input_constrained_transition_item X s item;
  dobst_output_m2 : output item = Some m2;
  dobst_observed_m1 : ObservedBeforeStateOrMessage m1 s (input item);
}.

Definition observed_before_send (m1 m2 : message) : Prop :=
  exists s item, ObservedBeforeSendTransition s item m1 m2.

Lemma observed_before_send_subsumes_msg_dep_rel
  `{!MessageDependencies X message_dependencies} :
  forall m, can_emit (preloaded_with_all_messages_vlsm X) m ->
  forall dm, msg_dep_rel message_dependencies dm m ->
    observed_before_send dm m.
Proof.
  intros m ([s im] & l & s' & Ht) dm Hdm.
  exists s, {| l := l; input := im; destination := s'; output := Some m |}.
  constructor; [done.. |].
  eapply @message_dependencies_are_necessary in Hdm as Hobs; [| done | by eexists _, _].
  eapply has_been_directly_observed_step_update in Hobs as [[| Hout] |]; [.. | done]; cycle 2.
  - by do 2 constructor.
  - by subst; cbn; constructor.
  - by contradict Hdm; inversion Hout; apply tc_reflect_irreflexive.
Qed.

(**
  A pair of messages constitutes a (local) evidence of equivocation for a
  validator <<v>> in a state <<s>> if both messages have <<v>> as a sender, have
  been (indirectly) observed in <<s>> (see [HasBeenObserved]), and are
  not comparable according to the [msg_dep_happens_before] relation.
*)
Record MsgDepLocalEquivocationEvidence
  (s : state X) (v : validator) (m1 m2 : message) : Prop :=
{
  mdlee_sender1 : sender m1 = Some v;
  mdlee_sender2 : sender m2 = Some v;
  mdlee_observed1 : HasBeenObserved s m1;
  mdlee_observed2 : HasBeenObserved s m2;
  mdlee_incomparable : ~ comparable (msg_dep_happens_before message_dependencies) m1 m2;
}.

Definition msg_dep_is_locally_equivocating (s : state X) (v : validator) : Prop :=
  exists m1 m2, MsgDepLocalEquivocationEvidence s v m1 m2.

(**
  Under the full-node assumptions, we can give a simpler alternative to
  [MsgDepLocalEquivocationEvidence] which only requires that each message
  [has_been_directly_observed] directly in the state. This relies on Lemma
  [msg_dep_full_node_happens_before_reflects_has_been_directly_observed].
*)
Record FullNodeLocalEquivocationEvidence
  (s : state X) (v : validator) (m1 m2 : message) : Prop :=
{
  fnlee_sender1 : sender m1 = Some v;
  fnlee_sender2 : sender m2 = Some v;
  fnlee_observed1 : has_been_directly_observed X s m1;
  fnlee_observed2 : has_been_directly_observed X s m2;
  fnlee_incomparable : ~ comparable (msg_dep_happens_before message_dependencies) m1 m2;
}.

Definition full_node_is_locally_equivocating (s : state X) (v : validator) : Prop :=
  exists m1 m2, FullNodeLocalEquivocationEvidence s v m1 m2.

(**
  If the states and messages are more tightly coupled (e.g., there is a unique
  state from which a given message can be emitted), then the sent messages of
  a state would be totally ordered by [msg_dep_rel].
*)
Definition has_been_sent_msg_dep_comparable_prop : Prop :=
  forall (s : state X), constrained_state_prop X s ->
  forall (m1 m2 : message),
    has_been_sent X s m1 ->
    has_been_sent X s m2 ->
    comparable (msg_dep_rel message_dependencies) m1 m2.

(**
  We present yet another definition for local evidence of equivocation assuming
  both full-node and [has_been_sent_msg_dep_comparable_prop].
*)
Record FullNodeSentLocalEquivocationEvidence
  (s : state X) (v : validator) (m1 m2 : message) : Prop :=
{
  fnslee_sender1 : sender m1 = Some v;
  fnslee_sender2 : sender m2 = Some v;
  fnslee_observed1 : has_been_directly_observed X s m1;
  fnslee_observed2 : has_been_directly_observed X s m2;
  fnslee_incomparable : ~ comparable (msg_dep_rel message_dependencies) m1 m2;
}.

Definition full_node_is_sent_locally_equivocating
  (s : state X) (v : validator) : Prop :=
  exists m1 m2, FullNodeSentLocalEquivocationEvidence s v m1 m2.

Lemma full_node_is_sent_locally_equivocating_weaker s v :
  full_node_is_locally_equivocating s v ->
  full_node_is_sent_locally_equivocating s v.
Proof.
  intros (m1 & m2 & [Hsender1 Hsender2 Hobs1 Hobs2 Hncomp]).
  exists m1, m2; constructor; [done.. |].
  by contradict Hncomp; apply tc_comparable.
Qed.

Lemma full_node_is_locally_equivocating_stronger s v :
  full_node_is_locally_equivocating s v ->
  msg_dep_is_locally_equivocating s v.
Proof.
  intros (m1 & m2 & []).
  by exists m1, m2; constructor; [| | constructor | constructor |].
Qed.

(**
  Under [MessageDependencies] and full-node assumptions, any message which
  [HasBeenObserved] in a state, [has_been_directly_observed] in that state, too.
*)
Lemma full_node_HasBeenObserved_is_directly_observed
  `{!MessageDependencies X message_dependencies}
  (Hfull : message_dependencies_full_node_condition_prop X message_dependencies)
  : forall s, constrained_state_prop X s ->
    forall m, HasBeenObserved s m <-> has_been_directly_observed X s m.
Proof.
  intros s Hs m; split; [| by intros; constructor].
  intros [Hobs | m' Hobs Hhb]; [done |].
  by eapply msg_dep_full_node_happens_before_reflects_has_been_directly_observed.
Qed.

(**
  Assuming [MessageDependencies] and full-node, the two notions of
  local equivocation defined above are equivalent.
*)
Lemma full_node_is_locally_equivocating_iff
  `{!MessageDependencies X message_dependencies}
  (Hfull : message_dependencies_full_node_condition_prop X message_dependencies)
  : forall s, constrained_state_prop X s ->
    forall v,
      msg_dep_is_locally_equivocating s v
        <->
      full_node_is_locally_equivocating s v.
Proof.
  intros s Hs v; split; [| apply full_node_is_locally_equivocating_stronger].
  intros (m1 & m2 & [Hsender1 Hsender2 Hobs1 Hobs2 Hncomp]).
  by exists m1, m2; split; rewrite <- ?full_node_HasBeenObserved_is_directly_observed.
Qed.

End sec_message_dependencies_equivocation.

Section sec_composite_message_dependencies.

Context
  {message : Type}
  `(IM : index -> VLSM message)
  `{FinSet message Cm}
  (message_dependencies : message -> Cm)
  `{finite.Finite index}
  `{forall i, HasBeenSentCapability (IM i)}
  `{forall i, HasBeenReceivedCapability (IM i)}
  `{!Irreflexive (msg_dep_happens_before message_dependencies)}
  `{forall i, MessageDependencies (IM i) message_dependencies}
  .

(**
  If all of the components satisfy the [MessageDependencies] assumptions,
  then their free composition will also do so.
*)
#[export] Instance composite_message_dependencies
  : MessageDependencies (free_composite_vlsm IM) message_dependencies.
Proof.
  split.
  - intros m s' ((s, iom) & [i li] & Ht) dm Hdm.
    apply composite_has_been_directly_observed_free_iff.
    apply input_valid_transition_preloaded_project_active_free in Ht; cbn in Ht.
    eapply composite_has_been_directly_observed_from_component.
    by eapply message_dependencies_are_necessary; [eexists _, _; cbn |].
  - intros m Hemit.
    apply can_emit_free_composite_project in Hemit as [j Hemitj].
    eapply message_dependencies_are_sufficient in Hemitj.
    eapply VLSM_embedding_can_emit; [| done].
    by apply lift_to_composite_generalized_preloaded_VLSM_embedding.
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
  ; [by contradict Him; apply no_initial_messages_in_IM |].
  right.
  pose proof (vlsm_is_preloaded_with_False X) as XeqXFalse.
  apply (VLSM_eq_can_emit XeqXFalse).
  cut (valid_message_prop (preloaded_vlsm X (fun _ => False)) dm).
  {
    clear -no_initial_messages_in_IM.
    rewrite emitted_messages_are_valid_iff.
    intros [[[i [[im Him] _]] | Hpreloaded] | Hemit]; try itauto.
    by contradict Him; apply no_initial_messages_in_IM.
  }
  eapply msg_dep_reflects_validity.
  - by apply composite_message_dependencies.
  - intros _ [i [[im Him] _]].
    by contradict Him; apply no_initial_messages_in_IM.
  - by itauto.
  - done.
  - apply emitted_messages_are_valid_iff.
    by apply (VLSM_eq_can_emit XeqXFalse) in Hemit; auto.
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
      can_emit (preloaded_with_all_messages_vlsm (IM (A v))) dm.
Proof.
  intros m Hm dm Hdm.
  cut (valid_message_prop X dm).
  - by apply free_composite_no_initial_valid_messages_emitted_by_sender.
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
  `(IM : index -> VLSM message)
  `{FinSet message Cm}
  (message_dependencies : message -> Cm)
  `(sender : message -> option validator)
  `{finite.Finite index}
  `{forall i, HasBeenSentCapability (IM i)}
  `{forall i, HasBeenReceivedCapability (IM i)}
  `{!Irreflexive (msg_dep_happens_before message_dependencies)}
  (Free := free_composite_vlsm IM)
  .

(**
  A message can be (indirectly) observed in a composite state if it either has
  been directly observed in the state (as sent or received), or it
  [msg_dep_happens_before] a directly observed message.
*)
Inductive CompositeHasBeenObserved
  (s : composite_state IM) (m : message) : Prop :=
| chbo_directly :
    composite_has_been_directly_observed IM s m ->
    CompositeHasBeenObserved s m
| chbo_indirectly :
    forall m',
      composite_has_been_directly_observed IM s m' ->
      msg_dep_happens_before message_dependencies m m' ->
      CompositeHasBeenObserved s m.

Lemma composite_HasBeenObserved_lift : forall s m i,
  HasBeenObserved (IM i) message_dependencies (s i) m ->
  CompositeHasBeenObserved s m.
Proof.
  intros s m i [].
  - by constructor 1; eexists.
  - by econstructor 2; [eexists |].
Qed.

Lemma composite_HasBeenObserved_iff : forall s m,
  CompositeHasBeenObserved s m
    <->
  exists i, HasBeenObserved (IM i) message_dependencies (s i) m.
Proof.
  split; [| by intros []; eapply composite_HasBeenObserved_lift].
  by intros [[i Hobsi] | m' [i Hobsi] Hmm'];
    exists i; [by constructor 1 | by econstructor 2].
Qed.

Lemma transition_preserves_CompositeHasBeenObserved :
  forall l s im s' om, input_constrained_transition Free l (s, im) (s', om) ->
  forall msg, CompositeHasBeenObserved s msg -> CompositeHasBeenObserved s' msg.
Proof.
  destruct (free_composite_has_been_directly_observed_stepwise_props IM) as [].
  intros * Ht msg Hbefore; inversion Hbefore as [Hobs | m Hobs Hdep].
  - by constructor; eapply oracle_step_update; [| right].
  - by econstructor 2; [| done]; eapply oracle_step_update; [| right].
Qed.

Lemma CompositeHasBeenObserved_step_update :
  forall l s im s' om, input_constrained_transition Free l (s, im) (s', om) ->
  forall msg,
    CompositeHasBeenObserved s' msg
      <->
    CompositeHasBeenObserved s msg \/
    (exists m, (im = Some m \/ om = Some m) /\
      (msg = m \/ msg_dep_happens_before message_dependencies msg m)).
Proof.
  destruct (free_composite_has_been_directly_observed_stepwise_props IM) as [].
  intros * Ht msg; split.
  - inversion 1 as [Hobs' | m' Hobs' Hdep];
      (eapply oracle_step_update in Hobs'; [| done]);
      destruct Hobs' as [Hnow | Hbefore].
    + by right; exists msg; split; [| left].
    + by left; constructor.
    + by right; exists m'; split; [| right].
    + by left; econstructor 2.
  - intros [Hbefore | (m & Hnow & [<- | Hdep])].
    + by eapply transition_preserves_CompositeHasBeenObserved.
    + by constructor; eapply oracle_step_update; [| left].
    + by econstructor 2; [| done]; eapply oracle_step_update; [| left].
Qed.

(**
  Lifting [DirectlyObservedBeforeSend] to a composition. The advantage of this
  definition is that RHS can be emitted by any of the machines in the composition.
*)
Record CompositeObservedBeforeSendTransition
  (s : composite_state IM) (item : composite_transition_item IM) (m1 m2 : message) : Prop :=
{
  cdobst_transition : input_constrained_transition_item Free s item;
  cdobst_output_m2 : output item = Some m2;
  cdobst_observed_m1 :
    ObservedBeforeStateOrMessage (IM (projT1 (l item))) message_dependencies m1
      (s (projT1 (l item))) (input item);
}.

Definition composite_observed_before_send (m1 m2 : message) : Prop :=
  exists s item, CompositeObservedBeforeSendTransition s item m1 m2.

Lemma composite_ObservedBeforeSendTransition_lift :
  forall (i : index) (s : state (IM i)) (item : transition_item (IM i))
    (m1 m2 : message),
  ObservedBeforeSendTransition (IM i) message_dependencies s item m1 m2 ->
  CompositeObservedBeforeSendTransition
    (lift_to_composite_state' IM i s)
    (lift_to_composite_transition_item' IM i item) m1 m2.
Proof.
  intros * []; constructor; [| done |].
  - by eapply VLSM_embedding_input_valid_transition in dobst_transition0;
      [| apply lift_to_composite_preloaded_VLSM_embedding].
  - by destruct item; cbn in *; state_update_simpl.
Qed.

Lemma composite_observed_before_send_lift :
  forall (i : index) (m1 m2 : message),
    observed_before_send (IM i) message_dependencies m1 m2 ->
    composite_observed_before_send m1 m2.
Proof.
  intros * (s & item & Hobs).
  by eexists _, _; apply composite_ObservedBeforeSendTransition_lift.
Qed.

Lemma composite_ObservedBeforeSendTransition_project :
  forall (s : composite_state IM) (item : composite_transition_item IM)
    (m1 m2 : message) (i := projT1 (l item)),
  CompositeObservedBeforeSendTransition s item m1 m2 ->
  ObservedBeforeSendTransition (IM i) message_dependencies
    (s i) (composite_transition_item_projection IM item) m1 m2.
Proof.
  by intros * []; constructor;
    [eapply input_valid_transition_preloaded_project_active_free | ..].
Qed.

Lemma composite_observed_before_send_iff m1 m2 :
  composite_observed_before_send m1 m2
    <->
  exists i, observed_before_send (IM i) message_dependencies m1 m2.
Proof.
  split.
  - intros (s & item & Hcomp); eexists (projT1 (l item)), _, _.
    by apply composite_ObservedBeforeSendTransition_project.
  - by intros []; eapply composite_observed_before_send_lift.
Qed.

Lemma composite_observed_before_send_subsumes_msg_dep_rel
  `{forall i, MessageDependencies (IM i) message_dependencies} :
  forall m, can_emit (preloaded_with_all_messages_vlsm Free) m ->
  forall dm, msg_dep_rel message_dependencies dm m ->
    composite_observed_before_send dm m.
Proof.
  intros m Hm dm Hdm.
  apply can_emit_free_composite_project in Hm as [j Hjm].
  by eapply composite_observed_before_send_lift,
    observed_before_send_subsumes_msg_dep_rel.
Qed.

(**
  Similarly to the [msg_dep_happens_before], we define the transitive closure
  of the [composite_observed_before_send] relation.
*)
Definition tc_composite_observed_before_send : relation message :=
  tc (composite_observed_before_send).

Lemma tc_composite_observed_before_send_subsumes_msg_dep_rel
  `{forall i, MessageDependencies (IM i) message_dependencies} :
  forall m, can_emit Free m ->
  forall dm, msg_dep_rel message_dependencies dm m ->
    tc_composite_observed_before_send dm m.
Proof.
  intros m Hm dm Hdm; constructor.
  eapply composite_observed_before_send_subsumes_msg_dep_rel; [| done].
  eapply VLSM_incl_can_emit; [| done].
  by apply vlsm_incl_preloaded_with_all_messages_vlsm.
Qed.

Lemma tc_composite_observed_before_send_subsumes_happens_before
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  `{forall i, MessageDependencies (IM i) message_dependencies} :
  forall m, can_emit Free m ->
  forall dm, msg_dep_happens_before message_dependencies dm m ->
    tc_composite_observed_before_send dm m.
Proof.
  intros m Hm dm Hdm.
  induction Hdm; [by eapply tc_composite_observed_before_send_subsumes_msg_dep_rel |].
  transitivity y; [| by apply IHHdm].
  eapply tc_composite_observed_before_send_subsumes_msg_dep_rel; [| done].
  by eapply emitted_messages_are_valid,
    msg_dep_reflects_happens_before_free_validity,
    emitted_messages_are_valid_iff
    in Hm as [(i & [] & <-) |]; [exfalso; eapply no_initial_messages_in_IM | ..].
Qed.

(**
  A messages constitutes a (global) evidence of equivocation for a
  validator <<v>> in a composite state <<s>> if the message has <<v>> as a sender,
  it has been (indirectly) observed in [composite_state] <<s>>, (see
  [CompositeHasBeenObserved]), but it wasn't observed as sent in <<s>>
  (see [composite_has_been_sent]).
*)
Record MsgDepGlobalEquivocationEvidence
  (s : composite_state IM) (v : validator) (m : message) : Prop :=
{
  mdgee_sender : sender m = Some v;
  mdgee_rec_observed : CompositeHasBeenObserved s m;
  mdgee_not_sent : ~ composite_has_been_sent IM s m;
}.

Definition msg_dep_is_globally_equivocating
  (s : composite_state IM) (v : validator) : Prop :=
  exists m : message, MsgDepGlobalEquivocationEvidence s v m.

(**
  Under the full-node assumption, we can give a simpler alternative to
  [MsgDepGlobalEquivocationEvidence] which only requires that the message has been
  received in the [composite_state] (see [composite_has_been_received]) (due to
  the Lemma [msg_dep_full_node_happens_before_reflects_has_been_directly_observed]).
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

Lemma full_node_is_globally_equivocating_stronger s v :
  full_node_is_globally_equivocating s v ->
  msg_dep_is_globally_equivocating s v.
Proof.
  intros [m []]; exists m; constructor; [done | | done].
  by constructor 1; apply composite_has_been_directly_observed_sent_received_iff; right.
Qed.

Lemma full_node_is_globally_equivocating_iff
  `{forall i, MessageDependencies (IM i) message_dependencies}
  (Hfull : forall i, message_dependencies_full_node_condition_prop (IM i) message_dependencies)
  : forall s, constrained_state_prop Free s ->
    forall v,
      msg_dep_is_globally_equivocating s v
        <->
      full_node_is_globally_equivocating s v.
Proof.
  intros s Hs v; split; [| apply full_node_is_globally_equivocating_stronger].
  intros [m [Hsender Hobs Hnsent]]; exists m; split; [done | | done].
  cut (composite_has_been_directly_observed IM s m).
  {
    by rewrite composite_has_been_directly_observed_sent_received_iff; intros [].
  }
  destruct Hobs as [Hobs | m' [i Hobs] Hhb]; [done | exists i].
  eapply msg_dep_full_node_happens_before_reflects_has_been_directly_observed;
    [done | done | | done..].
  by eapply composite_constrained_state_project.
Qed.

Lemma msg_dep_locally_is_globally_equivocating
  (A : validator -> index)
  (Hsafety : sender_safety_alt_prop IM A sender)
  (Hsent_comparable :
    forall i, has_been_sent_msg_dep_comparable_prop (IM i) message_dependencies)
  : forall s, constrained_state_prop Free s ->
    forall i v,
    msg_dep_is_locally_equivocating (IM i) message_dependencies sender (s i) v ->
    msg_dep_is_globally_equivocating s v.
Proof.
  intros s Hs i v (m1 & m2 & [Hsender1 Hsender2 Hobs1 Hobs2 Hncomp]).
  apply valid_state_has_trace in Hs as Htr.
  destruct Htr as (? & ? & ?).
  destruct (decide (has_been_sent (IM (A v)) (s (A v)) m1));
    [destruct (decide (has_been_sent (IM (A v)) (s (A v)) m2)) |]; cycle 1.
  1, 2: eexists; split;
      [.. | by contradict n; eapply has_been_sent_iff_by_sender];
      [done | by eapply composite_HasBeenObserved_lift].
  contradict Hncomp; eapply tc_comparable, Hsent_comparable; [| done..].
  by eapply composite_constrained_state_project.
Qed.

Lemma full_node_sent_locally_is_globally_equivocating
  (A : validator -> index)
  (Hsafety : sender_safety_alt_prop IM A sender)
  (Hsent_comparable :
    forall i, has_been_sent_msg_dep_comparable_prop (IM i) message_dependencies)
  : forall s, constrained_state_prop Free s ->
    forall i v,
    full_node_is_sent_locally_equivocating (IM i) message_dependencies sender (s i) v ->
    msg_dep_is_globally_equivocating s v.
Proof.
  intros s Hs i v (m1 & m2 & [Hsender1 Hsender2 Hobs1 Hobs2 Hncomp]).
  apply valid_state_has_trace in Hs as Htr.
  destruct Htr as (? & ? & ?).
  destruct (decide (has_been_sent (IM (A v)) (s (A v)) m1));
    [destruct (decide (has_been_sent (IM (A v)) (s (A v)) m2)) |]; cycle 1.
  1, 2: eexists; split; cycle 2;
      [by contradict n; eapply has_been_sent_iff_by_sender | done |];
      by constructor 1; eexists.
  contradict Hncomp; eapply Hsent_comparable; [| done..].
  by eapply composite_constrained_state_project.
Qed.

End sec_composite_message_dependencies_equivocation.

Section sec_sub_composite_message_dependencies.

Context
  {message : Type}
  `(IM : index -> VLSM message)
  `{FinSet message Cm}
  (message_dependencies : message -> Cm)
  `{FinSet index Ci}
  (indices : Ci)
  `{forall i, HasBeenSentCapability (IM i)}
  `{forall i, HasBeenReceivedCapability (IM i)}
  `{!Irreflexive (msg_dep_happens_before message_dependencies)}
  `{forall i, MessageDependencies (IM i) message_dependencies}
  .

Lemma msg_dep_reflects_sub_free_validity
  (no_initial_messages_in_IM : no_initial_messages_in_IM_prop IM)
  (P : message -> Prop)
  (Hreflects : forall dm m, msg_dep_rel message_dependencies dm m -> P m -> P dm)
  (X := free_composite_vlsm (sub_IM IM (elements indices)))
  : forall dm m, msg_dep_rel message_dependencies dm m ->
    valid_message_prop (preloaded_vlsm X P) m ->
    valid_message_prop (preloaded_vlsm X P) dm.
Proof.
  eapply msg_dep_reflects_validity; [| | done].
  - by typeclasses eauto.
  - intros m [sub_i [[im Him] Heqm]].
    destruct_dec_sig sub_i i Hi Heqsub_i; subst.
    by contradict Him; apply no_initial_messages_in_IM.
Qed.

End sec_sub_composite_message_dependencies.

Section sec_FullMessageDependencies.

Context
  {message : Type}
  `{FinSet message Cm}
  .

Class FullMessageDependencies
  (message_dependencies : message -> Cm)
  (full_message_dependencies : message -> Cm)
  : Prop :=
{
  full_message_dependencies_happens_before :
    forall dm m,
      dm ∈ full_message_dependencies m <->
      msg_dep_happens_before message_dependencies dm m;
  full_message_dependencies_irreflexive :
    forall m, m ∉ full_message_dependencies m;
}.

End sec_FullMessageDependencies.

(* given the message type, we can usually look up the functions for message dependencies *)
#[global] Hint Mode FullMessageDependencies ! - - - - - - - - - - - - : typeclass_instances.

Section sec_FullMessageDependencies_happens_before.

Context
  `{FinSet message Cm}
  (message_dependencies : message -> Cm)
  (full_message_dependencies : message -> Cm)
  (HFullMsgDep : FullMessageDependencies message_dependencies full_message_dependencies)
  .

#[export] Instance msg_dep_happens_before_dec :
 RelDecision (msg_dep_happens_before message_dependencies).
Proof.
 refine
   (fun m1 m2 =>
      match decide (m1 ∈ full_message_dependencies m2) with
      | left Hdec => left _
      | right Hdec => right _
      end).
  - by rewrite <- full_message_dependencies_happens_before.
  - by rewrite <- full_message_dependencies_happens_before.
Qed.

#[export] Instance msg_dep_happens_before_irrefl :
  Irreflexive (msg_dep_happens_before message_dependencies).
Proof.
  intros m Hm.
  contradict Hm.
  rewrite <- full_message_dependencies_happens_before.
  by apply full_message_dependencies_irreflexive.
Qed.

#[export] Instance msg_dep_happens_before_strict :
  StrictOrder (msg_dep_happens_before message_dependencies) := {}.

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
  apply tc_wf_projected with (<) (fun m => length (elements (full_message_dependencies m)));
    [by typeclasses eauto | | by apply Wf_nat.lt_wf].
  intros; unfold lt.
  change (S _) with (length (x :: elements (full_message_dependencies x))).
  apply NoDup_subseteq_length.
  - constructor.
    + by rewrite elem_of_elements; apply full_message_dependencies_irreflexive.
    + by apply NoDup_elements.
  - intros z Hz; inversion Hz; subst; rewrite elem_of_elements in *.
    + by apply full_message_dependencies_happens_before; constructor.
    + by eapply msg_dep_rel_full_message_dependecies_subset.
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

End sec_FullMessageDependencies_happens_before.

(** ** Basic validation condition for free composition

  In this section we show (Lemma [valid_free_validating_is_message_validating])
  that, under [FullMessageDependencies] assumptions, if the validity predicate
  ensures that message itself and all of its dependencies can be emitted using
  only its dependencies, then the input message is valid for the free composition.
  Thus, the component itself is a validator for the free composition.
*)

Section sec_free_composition_validators.

Context
  {message : Type}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  `{forall i, HasBeenSentCapability (IM i)}
  `{forall i, HasBeenReceivedCapability (IM i)}
  {validator : Type}
  (A : validator -> index)
  (sender : message -> option validator)
  `(message_dependencies : message -> Cm)
  `(full_message_dependencies : message -> Cm)
  `{FullMessageDependencies message Cm message_dependencies full_message_dependencies}
  .

(**
  The property of a message of having a sender and being emittable by the
  component corresponding to its sender preloaded with the dependencies of the
  message.
*)
Inductive Emittable_from_dependencies_prop (m : message) : Prop :=
| efdp : forall (v : validator) (Hsender : sender m = Some v)
            (Hemittable : can_emit
              (preloaded_vlsm (IM (A v)) (fun dm => dm ∈ message_dependencies m))
              m),
             Emittable_from_dependencies_prop m.

Definition emittable_from_dependencies_prop (m : message) : Prop :=
  match sender m with
  | None => False
  | Some v => can_emit (preloaded_vlsm (IM (A v)) (fun dm => dm ∈ message_dependencies m)) m
  end.

Lemma emittable_from_dependencies_prop_iff m
  : Emittable_from_dependencies_prop m <-> emittable_from_dependencies_prop m.
Proof.
  unfold emittable_from_dependencies_prop; split.
  - by inversion 1; rewrite Hsender.
  - by destruct (sender m) eqn: Hsender; [exists v | inversion 1].
Qed.

(**
  The property of a message that both itself and all of its dependencies are
  emittable from their dependencies.
*)
Definition all_dependencies_emittable_from_dependencies_prop (m : message) : Prop :=
  forall dm, dm ∈ m :: elements (full_message_dependencies m) -> Emittable_from_dependencies_prop dm.

(**
  The property of requiring that the validity predicate subsumes the
  [all_dependencies_emittable_from_dependencies_prop]erty.
*)
Definition valid_all_dependencies_emittable_from_dependencies_prop (i : index) : Prop :=
  forall l s m, input_constrained (IM i) l (s, Some m) ->
    all_dependencies_emittable_from_dependencies_prop m.

(**
  If a message can be emitted by a component preloaded with the message's direct
  dependencies, and if all the dependencies of the message are valid for the
  free composition, then the message itself is valid for the free composition.
*)
Lemma free_valid_from_valid_dependencies
  m i
  (Hm : can_emit (preloaded_vlsm (IM i) (fun dm => dm ∈ message_dependencies m)) m)
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
  apply free_valid_from_valid_dependencies with (A v); [done |].
  clear v Hemit'.
  eapply FullMessageDependencies_ind; [done |].
  intros dm Hdm Hdeps.
  specialize (Hm dm); spec Hm; [by right; apply elem_of_elements |].
  inversion Hm as [v _ ?]; clear Hm.
  by apply free_valid_from_valid_dependencies with (A v).
Qed.

(**
  If a component in a composition satisfies the
  [valid_all_dependencies_emittable_from_dependencies_prop]erty, then it also has
  the [component_message_validator_prop]erty, that is, it is a validator for the
  free composition.
*)
Lemma valid_free_validating_is_message_validating
  : forall i, valid_all_dependencies_emittable_from_dependencies_prop i ->
    component_message_validator_prop IM (free_constraint IM) i.
Proof.
  intros i Hvalidating l s im Hv.
  eapply VLSM_incl_valid_message.
  - by apply free_composite_vlsm_spec.
  - by do 2 red.
  - by eapply free_valid_from_all_dependencies_emitable_from_dependencies, Hvalidating.
Qed.

(**
  Under several additional (but regularly used) assumptions, including the
  [MessageDependencies] assumptions, the [channel_authentication_prop]erty and the
  [no_initial_messages_in_IM_prop]erty, we can show that the
  [component_message_validator_prop]erty is fully equivalent to the
  [valid_all_dependencies_emittable_from_dependencies_prop]erty.
*)
Lemma valid_free_validating_equiv_message_validating
  `{forall i, MessageDependencies (IM i) message_dependencies}
  (Hchannel : channel_authentication_prop IM A sender)
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
  - apply elem_of_elements, full_message_dependencies_happens_before in Hin.
    eapply msg_dep_happens_before_composite_no_initial_valid_messages_emitted_by_sender in Hin
        as (v & Hsender & Hemit); [| done.. |].
    + exists v; [done |].
      by eapply message_dependencies_are_sufficient.
    + eapply VLSM_incl_valid_message; [| | done].
      * by apply free_composite_vlsm_spec.
      * by do 2 red.
Qed.

End sec_free_composition_validators.

Section sec_CompositeHasBeenObserved_dec.

Context
  `{FinSet message Cm}
  `{finite.Finite index}
  (message_dependencies : message -> Cm)
  (IM : index -> VLSM message)
  `{forall i, ComputableSentMessages (IM i)}
  `{forall i, ComputableReceivedMessages (IM i)}
  .

#[export] Instance CompositeHasBeenObserved_dec
  `{FullMessageDependencies message Cm message_dependencies full_message_dependencies}
  : RelDecision (CompositeHasBeenObserved IM message_dependencies).
Proof.
  intros s m.
  destruct (decide (composite_has_been_directly_observed IM s m));
    [by left; constructor |].
  destruct (decide (Exists (fun m' => m ∈ elements (full_message_dependencies m'))
                      (composite_observed_messages_set IM s))).
  - left.
    apply Exists_exists in e as (m' & Hobsm' & Hmm').
    constructor 2 with m'.
    + by apply elem_of_composite_observed_messages_set.
    + by apply full_message_dependencies_happens_before; apply elem_of_elements in Hmm'.
  - right; inversion 1; [by contradict n |].
    contradict n0; apply Exists_exists; exists m'; split.
    + by apply elem_of_composite_observed_messages_set.
    + by apply elem_of_elements; apply full_message_dependencies_happens_before.
Qed.

End sec_CompositeHasBeenObserved_dec.

Section sec_msg_dep_is_globally_equivocating_props.

Context
  {message : Type}
  `{EqDecision index}
  (IM : index -> VLSM message)
  `{forall i, HasBeenSentCapability (IM i)}
  `{forall i, HasBeenReceivedCapability (IM i)}
  `{FinSet message Cm}
  (message_dependencies : message -> Cm)
  `(sender : message -> option validator)
  (A : validator -> index)
  (Hauth : channel_authentication_prop IM A sender)
  (Hsender_safety := channel_authentication_sender_safety _ _ _ Hauth)
  (Free := free_composite_vlsm IM)
  .

(**
  Input valid transitions preserve (global) evidence of equivocation on
  components not touched by the transitions.
*)
Lemma input_valid_transition_preserves_msg_dep_is_globally_equivocating :
  forall (s : composite_state IM) (item : composite_transition_item IM),
    input_constrained_transition_item Free s item ->
    forall j, destination item j = s j ->
    forall v, A v = j ->
      msg_dep_is_globally_equivocating IM message_dependencies sender s v ->
      msg_dep_is_globally_equivocating IM message_dependencies sender (destination item) v.
Proof.
  intros s item Ht j Hsj v Hv [m []].
  exists m; constructor; [done | ..].
  - by eapply transition_preserves_CompositeHasBeenObserved.
  - contradict mdgee_not_sent0.
    apply exists_right_finite_trace_from in Ht as (is & tr & Htr & _).
    eapply has_been_sent_iff_by_sender in mdgee_not_sent0; [| done..].
    rewrite Hv, Hsj in mdgee_not_sent0.
    by eexists.
Qed.

(** We also define the case in which a transition doesn't forget equivocation. *)
Definition transition_preserves_global_equivocation
  (s : composite_state IM) (item : composite_transition_item IM) : Prop :=
  forall (v : validator),
    msg_dep_is_globally_equivocating IM message_dependencies sender s v ->
    msg_dep_is_globally_equivocating IM message_dependencies sender (destination item) v.

Inductive TraceMonotoneGlobalEquivocation :
  composite_state IM -> list (composite_transition_item IM) -> Prop :=
| tpge_initial :
    forall (s : composite_state IM), TraceMonotoneGlobalEquivocation s []
| tpge_step :
    forall (s : composite_state IM) (item : composite_transition_item IM)
      (tr : list (composite_transition_item IM)),
      transition_preserves_global_equivocation s item ->
      TraceMonotoneGlobalEquivocation (destination item) tr ->
      TraceMonotoneGlobalEquivocation s (item :: tr).

Definition trace_monotone_global_equivocation
  (s : composite_state IM) (tr : list (composite_transition_item IM)) : Prop :=
    forall (pre suf : list (composite_transition_item IM)) (item : composite_transition_item IM),
      tr = pre ++ [item] ++ suf ->
      transition_preserves_global_equivocation (finite_trace_last s pre) item.

Lemma trace_monotone_global_equivocation_def_equiv :
  forall (s : composite_state IM) (tr : list (composite_transition_item IM)),
    trace_monotone_global_equivocation s tr
      <->
    TraceMonotoneGlobalEquivocation s tr.
Proof.
  split.
  - remember (length tr) as n; revert s tr Heqn.
    induction n as [n IHn] using (well_founded_ind lt_wf).
    intros s [| item tr]; [by constructor |].
    cbn; intros -> Hall; constructor; [by apply (Hall [] tr) |].
    eapply IHn; cycle 1; [done | | by lia].
    intros pre suf item' ->.
    specialize (Hall (item :: pre) suf item').
    rewrite finite_trace_last_cons in Hall; apply Hall.
    by simplify_list_eq.
  - induction 1; intros pre suf item1 Heq; [by destruct pre |].
    destruct pre as [| _item pre]; simplify_list_eq; [done |].
    rewrite finite_trace_last_cons.
    by eapply IHTraceMonotoneGlobalEquivocation.
Qed.

End sec_msg_dep_is_globally_equivocating_props.
