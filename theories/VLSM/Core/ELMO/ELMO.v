From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From Coq Require Import FunctionalExtensionality Reals.
From stdpp Require Import prelude finite.
From VLSM.Lib Require Import Preamble Measurable FinSetExtras RealsExtras ListExtras.
From VLSM.Core Require Import VLSM VLSMProjections Composition Equivocation.
From VLSM.Core Require Import Validator ProjectionTraces MessageDependencies.
From VLSM.Core Require Import TraceableVLSM MinimalEquivocationTrace.
From VLSM.Core Require Import BaseELMO UMO MO.

Create HintDb ELMO_hints.

#[local]
Hint Resolve submseteq_tail_l : ELMO_hints.

(** * ELMO Protocol Definitions and Properties

  This module contains definitions and properties of ELMO components and
  the ELMO protocol.
*)

Section sec_ELMO.

Context
  {Address : Type}
  (State := @State Address)
  (Observation := @Observation Address)
  (Message := @Message Address).

Context
  {measurable_Address : Measurable Address}
  `{FinSet Address Ca}
  (threshold : R)
  `{!ReachableThreshold Address Ca threshold}
  `{finite.Finite index}
  (idx : index -> Address)
  `{!Inj (=) (=) idx}.

Definition immediate_dependency (m1 m2 : Message) : Prop :=
  m1 ∈ messages (state m2).

Lemma immediate_dependency_msg_dep_rel :
  forall dm m : Message,
    immediate_dependency dm m <-> msg_dep_rel Message_dependencies dm m.
Proof.
  unfold immediate_dependency, messages, messages',
    msg_dep_rel, Message_dependencies; cbn.
  by setoid_rewrite elem_of_list_to_set.
Qed.

#[local] Notation happensBefore := (tc immediate_dependency).

#[local] Infix "<hb" := happensBefore (at level 70).

Lemma happensBefore_msg_dep :
  forall dm m : Message,
    dm <hb m <-> msg_dep_happens_before Message_dependencies dm m.
Proof.
  by split;
    (induction 1; [by constructor 1; apply immediate_dependency_msg_dep_rel |]);
    (etransitivity; [| done]);
    constructor 1; apply immediate_dependency_msg_dep_rel.
Qed.

(**
  The full node condition says that a node can receive a message
  only if the direct observations of that node already include
  all messages from the direct observations of the state inside
  the message (not necessarily with the same [Send]/[Receive] label).

  This will let us define validity predicates without needing
  to recurse into the states inside observations in a state,
  because a correctly-operating node would have checked the
  shallow condition for those messages when their observations
  were added to the state.
*)

Definition full_node (s : State) (m : Message) : Prop :=
  messages (state m) ⊆+ messages s.

Lemma full_node_reachable_messages_ind
  (P : State -> Message -> Prop)
  (Hnew : forall s l msg
                 (Hfull : full_node s msg)
                 (IH : forall m, m ∈ messages s -> P s m),
    P (s <+> MkObservation l msg) msg)
  (Hprev : forall s ob m (IH: P s m), P (s <+> ob) m)
  :
  forall s, UMO_reachable full_node s ->
  forall m, m ∈ messages s -> P s m.
Proof.
  unfold full_node in Hnew.
  by apply UMO_reachable_elem_of_messages_ind; auto.
Qed.

Lemma messages_hb_transitive :
  forall s,
    UMO_reachable full_node s ->
  forall m,
    m ∈ messages s ->
  forall m',
    m' <hb m ->
    m' ∈ messages s.
Proof.
  refine (UMO_reachable_elem_of_messages_ind _ _ _ _ _);
    [intros | intros s Hs IH m' Hm'%tc_r_iff
    | intros s Hs mr Hmr%submseteq_list_subseteq IH m' Hm'%tc_r_iff];
    apply elem_of_messages_addObservation; right.
  - by itauto.
  - by destruct Hm' as [| (m & ? & ?)]; [| eapply IH].
  - destruct Hm' as [| (m & ? & ?)]; [by apply Hmr |].
    by eapply IH; [apply Hmr |].
Qed.

(**
  Some claims about the full node condition hold for any UMO-based VLSM
  whose validity predicate implies the full node condition. By UMO-based we
  mean a [VLSM] built over the [UMOComponentType] which also has the same
  transition function as UMO/MO, an initial state predicate that ensures
  [obs] of an initial state is empty, and a validity predicate that
  implies [UMOComponentValid].
  If that's all we know about the VLSM, knowing that a [State] is reachable
  in that VLSM is only as informative as knowing that the state is
  [UMO_reachable full_node].
  (This lemma needs no assumption about [UMOComponentValid] because
  reachability is the same anyway, because [UMOComponentValid]
  returns the state unchanged on invalid input.)
*)
Lemma full_node_VLSM_reachable
  (VM : VLSMMachine ELMOComponentType)
  (V := mk_vlsm VM)
  (VM_transition_is_UMO :
    forall (l : Label) (s : State) (om : option Message),
      vtransition V l (s, om) = UMOComponent_transition l s om)
  (VM_init_empty :
    forall s : State, vinitial_state_prop V s -> obs s = [])
  (VM_enforces_full_node :
    forall (l : Label) (s : State) (m : Message),
      vvalid V l (s, Some m) -> full_node s m) :
  forall (s : State),
    ram_state_prop V s ->
    UMO_reachable full_node s.
Proof.
  intro s.
  induction 1 using valid_state_prop_ind.
  - destruct s as [obs adr].
    apply VM_init_empty in Hs; cbn in Hs; subst.
    by apply reach_init.
  - destruct Ht as [(_ & _ & Hvalid) Ht]; cbn in Ht, Hvalid.
    rewrite VM_transition_is_UMO in Ht.
    destruct l, om; injection Ht as [= <- <-]; [| done.. |].
    + apply VM_enforces_full_node in Hvalid.
      by apply reach_recv.
    + by apply reach_send.
Qed.

(**
  A simplified version of [local_equivocators] that only checks for
  incompatible messages among the immediate observations of the state.
  This relies on the full node condition.
*)
Set Warnings "-cannot-define-projection".
Record local_equivocators_simple (s : State) (i : Address) : Prop :=
{
  les_m1 : Message;
  les_m2 : Message;
  les_adr1 : adr (state les_m1) = i;
  les_adr2 : adr (state les_m2) = i;
  les_obs_m1 : les_m1 ∈ messages s;
  les_obs_m2 : les_m2 ∈ messages s;
  les_incomparable : incomparable les_m1 les_m2;
}.
Set Warnings "cannot-define-projection".

(**
  A variant of [local equivocators] that relies more on the full node condition
  and directly shows how the set of equivocators can grow.

  Only a newly received message needs to be checked against previous messages,
  other addresses are equivocating if they are equivocating in the previous
  state.
*)
Inductive local_equivocators_full_obs : list Observation -> Address -> Prop :=
| lefo_last :
    forall (ol : list Observation) (m1 m2 : Message),
      m2 ∈ receivedMessages' ol ->
      incomparable m1 m2 ->
      local_equivocators_full_obs (addObservation' (MkObservation Receive m1) ol) (adr (state m1))
| lefo_prev :
    forall (ol : list Observation) (l : Label) (m : Message) (i : Address),
      local_equivocators_full_obs ol i ->
      local_equivocators_full_obs (addObservation' (MkObservation l m) ol) i.

Lemma lefo_alt (ol : list Observation) (o : Observation) (a : Address) :
  local_equivocators_full_obs (addObservation' o ol) a <->
    (a = adr (state (message o))
      /\ label o = Receive
      /\ exists m2, m2 ∈ receivedMessages' ol
      /\ incomparable (message o) m2)
    \/ local_equivocators_full_obs ol a.
Proof.
  split.
  - by inversion 1; subst; [left; split_and!; [.. | eexists] | right].
  - destruct o as [l m1]; cbn.
    by intros [(-> & -> & m2 & Hrecv & Hadr & Hincomp) |]; econstructor.
Qed.

#[local] Existing Instance list_exist_dec.

#[export]
Instance local_equivocators_full_obs_dec : RelDecision local_equivocators_full_obs.
Proof.
  intros ol a.
  induction ol using addObservation'_rec.
  - by right; inversion 1.
  - apply (Decision_iff (iff_Symmetric _ _ (lefo_alt _ _ _))).
    by typeclasses eauto.
Defined.

Definition local_equivocators_full (s : State) : Address -> Prop :=
  local_equivocators_full_obs (obs s).

#[export]
Instance local_equivocators_full_dec : RelDecision local_equivocators_full :=
  fun s a => local_equivocators_full_obs_dec (obs s) a.

(**
  An ELMO component has the same elements as a MO component
  except for the validity predicate, which:

  - checks message validity
  - enforces the full-node condition
  - only allows receiving a message if it will not bring the total [weight]
    of the locally-visible equivocation above [equivocation_threshold]
*)

Definition no_self_equiv (s : State) (m : Message) : Prop :=
  adr s = adr (state m) -> m ∈ sentMessages s.

Inductive MessageHasSender (m : Message) : Prop :=
| message_has_sender : forall i, adr (state m) = idx i -> MessageHasSender m.

Inductive ELMO_msg_valid_full : Message -> Prop :=
| MVF_nil :
    forall m : Message,
      obs (state m) = [] -> MessageHasSender m -> ELMO_msg_valid_full m
| MVF_send:
    forall m,
      ELMO_msg_valid_full m ->
      ELMO_msg_valid_full (m <*> MkObservation Send m)
| MVF_recv:
    forall m mo,
      full_node (state m) mo ->
      no_self_equiv (state m) mo ->
      ELMO_msg_valid_full m ->
      ELMO_msg_valid_full (m <*> MkObservation Receive mo).

Lemma ELMO_msg_valid_full_to_reach (m : Message) :
  ELMO_msg_valid_full m ->
  UMO_reachable (fun s m => full_node s m /\ no_self_equiv s m) (state m).
Proof.
  by induction 1; destruct m as [ms]; cbn in *;
    [replace ms with (MkState [] (adr ms)) by (apply eq_State; done) | ..];
    constructor.
Qed.

Lemma ELMO_msg_valid_full_has_sender (m : Message) :
  ELMO_msg_valid_full m -> MessageHasSender m.
Proof.
  by induction 1; [done | ..]; destruct IHELMO_msg_valid_full; econstructor.
Qed.

#[local] Instance ELMO_local_equivocation : BasicEquivocation State Address Ca threshold :=
{
  is_equivocating := local_equivocators_full;
  is_equivocating_dec := local_equivocators_full_dec;
  state_validators := const (list_to_set (map idx (enum index)));
}.

Definition local_equivocation_limit_ok (s : State) : Prop := not_heavy s.

Record ELMO_recv_valid (s : State) (m : Message) : Prop :=
{
  ELMO_mv_full_node : full_node s m;
  ELMO_mv_no_self_equiv : no_self_equiv  s m;
  ELMO_mv_msg_valid_full : ELMO_msg_valid_full m;
  ELMO_mv_local_equivocation_limit_ok :
    local_equivocation_limit_ok (s <+> MkObservation Receive m);
}.

Inductive ELMOComponentValid : Label -> State -> option Message -> Prop :=
| ELMOCV_Receive :
    forall (s : State) (m : Message),
      ELMO_recv_valid s m ->
      ELMOComponentValid Receive s (Some m)
| ELMOCV_Send :
    forall s : State,
      ELMOComponentValid Send s None.

(**
  This definition is closer to the way the validity condition
  might be defined by hand, but is probably less convenient than
  the inductive definition of [ELMOComponentValid]. So we prove
  that they are equivalent.
*)
Definition ELMOComponentValid_alt (l : Label) (s : State) (om : option Message) : Prop :=
  UMOComponentValid l s om /\ (l = Receive -> from_option (ELMO_recv_valid s) False om).

Definition ELMOComponentValid_alt_iff :
  forall (l : Label) (s : State) (om : option Message),
    ELMOComponentValid l s om <-> ELMOComponentValid_alt l s om.
Proof.
  split.
  - by destruct 1; split; [constructor | auto | constructor | auto].
  - by intros [[] Hfo]; constructor; apply Hfo.
Qed.

Definition ELMOComponentMachine (i : index) : VLSMMachine ELMOComponentType :=
{|
  initial_state_prop := UMOComponent_initial_state_prop (idx i);
  initial_message_prop := const False;
  s0 := Inhabited_UMOComponent_initial_state_type (idx i);
  transition := fun l '(st, om) => UMOComponent_transition l st om;
  valid := fun l '(st, om) => ELMOComponentValid l st om;
|}.

Definition ELMOComponent (i : index) : VLSM Message :=
{|
  vtype := ELMOComponentType;
  vmachine := ELMOComponentMachine i;
|}.

#[export]
Instance ComputableSentMessages_ELMOComponent
  (i : index) : ComputableSentMessages (ELMOComponent i).
Proof.
  constructor 1 with sentMessages; constructor.
  - by intros [] []; cbn in *; subst; cbn; apply not_elem_of_nil.
  - intros l s im s' om [(Hvsp & Hovmp & Hv) Ht] m; cbn in *.
    destruct l, im; cbn in *; [| by exfalso; inversion Hv.. |];
    inversion_clear Ht; destruct s; cbn.
    + by rewrite decide_False; cbn; firstorder congruence.
    + rewrite decide_True by done; cbn.
      unfold Message; rewrite elem_of_cons.
      by firstorder congruence.
Defined.

#[export]
Instance ComputableReceivedMessages_ELMOComponent
  (i : index) : ComputableReceivedMessages (ELMOComponent i).
Proof.
  constructor 1 with receivedMessages; constructor.
  - by intros [] []; cbn in *; subst; cbn; apply not_elem_of_nil.
  - intros l s im s' om [(Hvsp & Hovmp & Hv) Ht] m; cbn in *.
    destruct l, im; cbn in *; [| by exfalso; inversion Hv.. |];
    inversion_clear Ht; destruct s; cbn.
    + rewrite decide_True by done; cbn.
      unfold Message; rewrite elem_of_cons.
      by firstorder congruence.
    + by rewrite decide_False; cbn; firstorder congruence.
Defined.

#[export]
Instance HasBeenDirectlyObservedCapability_ELMOComponent
  (i : index) : HasBeenDirectlyObservedCapability (ELMOComponent i) :=
    HasBeenDirectlyObservedCapability_from_sent_received (ELMOComponent i).

Lemma ELMO_reachable_view (s : State) i :
  ram_state_prop (ELMOComponent i) s
    <->
  UMO_reachable ELMO_recv_valid s /\ adr s = idx i.
Proof.
  eapply iff_trans.
  - apply UMO_based_valid_reachable; [| | done].
    + by inversion 1.
    + by cbn; split; inversion 1; [| constructor].
  - apply Morphisms_Prop.and_iff_morphism.
    + by split; apply UMO_reachable_impl; inversion 1; subst; [| constructor].
    + by firstorder.
Qed.

Lemma ELMOComponent_message_dependencies_full_node_condition :
  forall i : index,
    message_dependencies_full_node_condition_prop
      (ELMOComponent i) Message_dependencies.
Proof.
  intros i [] s m Hv; inversion Hv as [? ? [Hfull] |]; subst.
  intros dm Hdm; cbn in Hdm.
  apply elem_of_list_to_set in Hdm.
  eapply elem_of_submseteq, elem_of_messages in Hdm; [| done].
  by destruct Hdm as []; [left | right].
Qed.

Lemma ELMO_full_node_reachable i s :
  ram_state_prop (ELMOComponent i) s -> UMO_reachable full_node s.
Proof.
  intro Hs; apply ELMO_reachable_view in Hs as [? _].
  eapply UMO_reachable_impl; [| done].
  by inversion 1.
Qed.

Lemma ELMO_no_self_equiv_reachable i s :
  ram_state_prop (ELMOComponent i) s -> UMO_reachable no_self_equiv s.
Proof.
  intro Hs; apply ELMO_reachable_view in Hs as [? _].
  eapply UMO_reachable_impl; [| done].
  by inversion 1.
Qed.

Section sec_ELMOComponent_lemmas.

(** ** Component lemmas *)

Context
  (i : index)
  (Ei : VLSM Message := ELMOComponent i)
  (Ri : VLSM Message := pre_loaded_with_all_messages_vlsm Ei).

Lemma ELMO_reachable_adr (s : State) :
  ram_state_prop Ei s -> adr s = idx i.
Proof.
  by intros [_ Hadr]%ELMO_reachable_view.
Qed.

Lemma ELMO_transition_output_not_initial :
  forall l (s : State) (om : option Message) (s' : State) (om' : option Message),
    input_valid_transition Ri l (s, om) (s', om') ->
    ~ vinitial_state_prop Ri s'.
Proof.
  intros l s om [ol a] om' [(_ & _ & Hv) Ht]; compute; intros [-> _].
  by inversion Hv; subst; inversion Ht.
Qed.

Lemma ELMO_transition_inj:
  forall l (s : State) (om : option Message) (s' : State) (om' : option Message),
    input_valid_transition Ri l (s, om) (s', om') ->
  forall l0 s0 om0 om'0,
    input_valid_transition Ri l0 (s0, om0) (s', om'0) ->
      l0 = l /\ s0 = s /\ om0 = om /\ om'0 = om'.
Proof.
  intros l s om s' om' [(_ & _ & Hvalid) Ht] l0 s0 om0 om'0 [(_ & _ & Hvalid0) Ht0].
  by inversion Hvalid; subst; cbn in Ht;
    injection Ht as [= <- <-];
    inversion Hvalid0; subst; inversion Ht0;
    replace s0 with s by (apply eq_State; done).
Qed.

Lemma ELMOComponent_valid_transition_size :
  forall (s1 s2 : State) (iom oom : option Message) (lbl : Label),
    ELMOComponentValid lbl s1 iom ->
    UMOComponent_transition lbl s1 iom = (s2, oom) ->
      sizeState s1 < sizeState s2.
Proof. by intros [] s2 [im |] oom []; do 2 inversion_clear 1; cbn; lia. Qed.

#[export] Instance ELMOTransitionMonotoneVLSM : TransitionMonotoneVLSM Ei sizeState.
Proof.
  constructor; intros s1 s2 [? ? ? [Hv Ht]].
  by eapply ELMOComponent_valid_transition_size; cbn in *.
Qed.

Lemma state_suffix_addObservation_inv :
  forall (s1 s2 : State) (ob : Observation),
    state_suffix s1 (s2 <+> ob) ->
      s1 = s2 \/ state_suffix s1 s2.
Proof.
  intros s1 s2 ob (Hadr & [[| _o os] Hsuf] & Hstrict);
    [by contradict Hstrict; exists [] |].
  destruct s2; cbn in *.
  inversion Hsuf; subst _o obs.
  destruct os; [left; apply eq_State; cbn in *; congruence |].
  right; constructor; [done |].
  split; [by eexists | destruct s1; cbn; clear].
  intros [os' Heqos].
  apply f_equal with (f := length) in Heqos.
  rewrite app_length in Heqos; cbn in Heqos; rewrite app_length in Heqos.
  by lia.
Qed.

(** There is a unique trace from any prefix of a reachable state to that state. *)
Lemma ELMO_unique_trace_segments (s sf : State) :
  ram_state_prop Ei sf -> (s = sf \/ state_suffix s sf) ->
  exists! (tr : list transition_item),
    finite_valid_trace_from_to Ri s sf tr.
Proof.
  intros Hsf [-> | Hsuf];
    [by exists []; split; [by constructor |]; intros;
      symmetry; eapply transition_monotone_empty_trace; [typeclasses eauto |]
    |].
  induction Hsf using valid_state_prop_ind.
  - unfold initial_state_prop in Hs; cbn in Hs.
    eapply UMOComponent_initial_state_spec in Hs as ->.
    by contradict Hsuf; apply state_suffix_empty_minimal.
  - assert (s = s0 \/ state_suffix s s0) as [-> | Hss0].
    {
      assert (exists o, s' = s0 <+> o) as [o ->]
        by (destruct Ht as [(_ & _ & Hv) Ht]; inversion Hv; subst;
            inversion Ht; eexists; done).
      by apply state_suffix_addObservation_inv in Hsuf.
    }
    + exists [Build_transition_item l om s' om'].
      split; [by apply finite_valid_trace_from_to_singleton |].
      intros tr' Htr'.
      induction Htr' using finite_valid_trace_from_to_rev_ind;
        [by contradict Hsuf; apply Irreflexive_state_suffix | clear IHHtr'].
      pose proof (ELMO_transition_inj _ _ _ _ _ Ht _ _ _ _ Ht0) as (-> & -> & -> & ->).
      eapply transition_monotone_empty_trace in Htr'; [| typeclasses eauto].
      by subst.
    + destruct (IHHsf Hss0) as (tr & Htr & Htr_unique).
      exists (tr ++ [Build_transition_item l om s' om']).
      split; [by apply extend_right_finite_trace_from_to with (s2 := s0) |].
      intros tr' Htr'.
      induction Htr' using finite_valid_trace_from_to_rev_ind;
        [by contradict Hsuf; apply Irreflexive_state_suffix | clear IHHtr'].
      pose proof (ELMO_transition_inj _ _ _ _ _ Ht _ _ _ _ Ht0) as (-> & -> & -> & ->).
      by f_equal; apply Htr_unique.
Qed.

(**
  From every reachable state of an [ELMOComponent] we can extract a unique
  trace reaching that state from the initial state.
*)
Lemma ELMO_unique_traces (sf : State) :
  ram_state_prop Ei sf ->
    exists! tr : list transition_item, exists si : State,
      finite_valid_trace_init_to Ri si sf tr.
Proof.
  intros Hsf.
  pose (si := MkState [] (idx i)).
  cut (exists! (tr : list transition_item), finite_valid_trace_from_to Ri si sf tr).
  {
    intros (tr & Htr & Htr_unique).
    exists tr; split; [by exists si; split |].
    by intros _tr [[] [H_tr []]]; cbn in *; subst; apply Htr_unique.
  }
  apply ELMO_unique_trace_segments; [done |].
  destruct (decide (si = sf)) as [| Hneq]; [by left | right].
  subst si; constructor; cbn; [by rewrite ELMO_reachable_adr |].
  split; [by eexists; rewrite app_nil_r |].
  intros [os Hos].
  symmetry in Hos; apply app_nil in Hos as [_ Hosf].
  by contradict Hneq; apply eq_State; [| symmetry; apply ELMO_reachable_adr].
Qed.

Lemma full_node_rebase_rec_obs :
  forall (s s' : State) (m : Message),
    UMO_reachable full_node s ->
    full_node s (MkMessage s') ->
    forall l, rec_obs s' (MkObservation l m) ->
      exists l, rec_obs s (MkObservation l m).
Proof.
  intros s s' m Hs Hfull l Hm.
  remember (MkObservation l m) as ob eqn: Heq_ob.
  revert l m Heq_ob; induction Hm; intros l0 m0 ->.
  - assert (Hm : m0 ∈ messages s) by (revert Hfull; apply elem_of_submseteq; constructor).
    by apply elem_of_list_fmap in Hm as [[l' m'] [-> Hm]]; exists l'; apply obs_rec_obs.
  - eapply IHHm; [| done].
    by revert Hfull; apply submseteq_tail_l.
  - assert (m ∈ messages s) by (revert Hfull; apply elem_of_submseteq; constructor).
    by exists l0; apply (unfold_robs _ _ Hs); right; exists m.
Qed.

Lemma full_node_messages_iff_rec_obs:
  forall (s : State), UMO_reachable full_node s ->
  forall (m : Message),
    m ∈ messages s <-> (exists l, rec_obs s (MkObservation l m)).
Proof.
  intros s Hs; induction Hs using UMO_reachable_ind'.
  - by split; [intros Hm | intros [? Hm]]; inversion Hm.
  - intros m.
    setoid_rewrite elem_of_messages_addObservation; rewrite (IHHs m);
      setoid_rewrite rec_obs_addObservation_iff; cbn.
    split.
    + by intros [<- | [l0]]; eauto.
    + by intros [l0 [ | [[= _] | [->]]]]; eauto using full_node_rebase_rec_obs.
Qed.

(**
  Because of the [no_self_equiv] assumption,
  a component might have received its own messages,
  but only messages it also sent.
*)
Lemma self_messages_sent (s : State) :
  UMO_reachable no_self_equiv s ->
  forall m, adr (state m) = adr s -> m ∈ messages s -> m ∈ sentMessages s.
Proof.
  intros Hs m Hadr Hm; revert s Hs m Hm Hadr.
  by apply (UMO_reachable_elem_of_messages_ind no_self_equiv
    (fun s m => adr (state m) = adr s -> m ∈ sentMessages s));
    intros; apply elem_of_sentMessages_addObservation; constructor; auto.
Qed.

Lemma local_equivocators_simple_addObservation :
  forall (s : State) (ob : Observation) (a : Address),
    local_equivocators_simple (s <+> ob) a ->
      local_equivocators_simple s a
        \/
      adr (state (message ob)) = a /\
      message ob ∉ messages s /\
      exists m, m ∈ messages s /\ incomparable (message ob) m.
Proof.
  intros s ob a [].
  apply elem_of_messages_addObservation in les_obs_m1 as [-> | Hm1], les_obs_m2 as [-> | Hm2].
  - by destruct les_incomparable as [? []]; constructor.
  - destruct (decide (message ob ∈ messages s)).
    + by left; exists (message ob) les_m2.
    + by firstorder.
  - symmetry in les_incomparable.
    destruct (decide (message ob ∈ messages s)).
    + by left; exists les_m1 (message ob).
    + by firstorder.
  - by left; eauto using local_equivocators_simple.
Qed.

Lemma local_equivocators_simple_add_Send (s : State) :
  UMO_reachable no_self_equiv s ->
  forall a, local_equivocators_simple (s <+> MkObservation Send (MkMessage s)) a ->
            local_equivocators_simple s a.
Proof.
  intros Hs a Ha.
  apply local_equivocators_simple_addObservation
    in Ha as [| (<- & _ & m & Hm & Hincomp)]; [done |]; cbn in *.
  destruct Hincomp as [Hadr []].
  by apply self_messages_sent in Hm; [constructor | ..].
Qed.

(**
  This lemma is convenient to prove for [local_equivocators_simple],
  and our assumption is slightly weaker than [ram_state_prop Ei].
*)
Lemma local_equivocators_simple_no_self (s : State) :
  UMO_reachable no_self_equiv s ->
    ~ local_equivocators_simple s (adr s).
Proof.
  intros Hs; induction Hs as [| | ? ? Hno_self_eqv].
  - by destruct 1; inversion les_obs_m1.
  - by contradict IHHs; apply local_equivocators_simple_add_Send in IHHs.
  - contradict IHHs.
    unfold no_self_equiv in Hno_self_eqv.
    cbn in IHHs; destruct IHHs.
    assert (adr (state msg) = adr s -> msg ∈ messages s).
    {
      intro Hmsg; symmetry in Hmsg.
      apply Hno_self_eqv, elem_of_list_fmap in Hmsg as (ob & Hmsg & Hob).
      apply elem_of_list_fmap.
      exists ob.
      by apply list_filter_subseteq in Hob.
    }
    assert (les_m1 ∈ messages s)
      by (apply elem_of_messages_addObservation in les_obs_m1 as [-> | l]; auto).
    assert (les_m2 ∈ messages s)
      by (apply elem_of_messages_addObservation in les_obs_m2 as [-> | l]; auto).
    by exists les_m1 les_m2.
Qed.

Lemma local_equivocators_full_nondecreasing (s : State) l om s' om' :
  vtransition Ri l (s, om) = (s', om') ->
  (forall a, local_equivocators_full s a ->
             local_equivocators_full s' a).
Proof.
  by destruct l, om; cbn; injection 1; intros; subst; try constructor.
Qed.

Lemma local_equivocators_full_increase_only_received_adr (s : State) m s' om' :
  vtransition Ri Receive (s, Some m) = (s', om') ->
  forall a, local_equivocators_full s' a ->
            local_equivocators_full s a \/ a = adr (state m).
Proof.
  by inversion 1; subst; inversion 1; subst; [right | left].
Qed.

Lemma local_equivocators_simple_add_Receive (s : State) (msg : Message) :
  UMO_reachable no_self_equiv s -> no_self_equiv s msg ->
  forall i, local_equivocators_simple (s <+> MkObservation Receive msg) i ->
            local_equivocators_simple s i
     \/ adr (state msg) = i /\ i <> adr s /\
          exists m, m ∈ messages s /\ incomparable msg m.
Proof.
  intros Hs Hno_equiv a Ha.
  assert (a <> adr (s <+> MkObservation Receive msg))
    by (contradict Ha; subst; apply local_equivocators_simple_no_self; constructor; done).
  apply local_equivocators_simple_addObservation in Ha; cbn in *.
  by itauto.
Qed.

(**
  Any message in <<messages s>> which does not have the same address as <<s>>
  must be found in [receivedMessages].
*)
Lemma not_adr_received (s : State) :
  UMO_reachable no_self_equiv s ->
  forall msg,
    adr (state msg) <> adr s ->
      msg ∈ messages s -> msg ∈ receivedMessages s.
Proof.
  intros Hs msg Hadr Hmsg; revert s Hs msg Hmsg Hadr.
  by apply (UMO_reachable_elem_of_messages_ind _
    (fun s m => adr (state m) <> adr s -> m ∈ receivedMessages s));
    simpl; intros; apply elem_of_receivedMessages_addObservation; constructor; auto.
Qed.

(**
  Little lemmas used while proving equivalence between
  [local_equivocators], [local_equivocators_simple],
  and [local_equivocators_full].
*)
Lemma received_in_messages (s : State) :
  forall msg, msg ∈ receivedMessages s -> msg ∈ messages s.
Proof.
  intros msg Hmsg.
  apply elem_of_list_fmap in Hmsg as (ob & Hmsg & Hob).
  apply elem_of_list_fmap.
  exists ob; split; [done |].
  by eapply list_filter_subseteq.
Qed.

Lemma local_equivocators_simple_prev (s : State) (ob : Observation) (a : Address) :
  local_equivocators_simple s a ->
  local_equivocators_simple (s <+> ob) a.
Proof.
  by destruct 1; exists les_m1 les_m2; try (apply elem_of_messages_addObservation; right).
Qed.

Lemma reachable_msg_obs :
  forall P (s : State),
    UMO_reachable P s ->
  forall (m : Message) (ob : Observation),
    rec_obs (state m) ob ->
    m ∈ messages s ->
    rec_obs s ob.
Proof.
  intros P s Hs m ob Hob Hm;
  revert s Hs m Hm ob Hob.
  by refine (UMO_reachable_elem_of_messages_ind _ _ _ _ _); auto using @rec_obs.
Qed.

Lemma reachable_obs_msg (s : State) :
  UMO_reachable full_node s ->
  forall ob, rec_obs s ob -> message ob ∈ messages s.
Proof.
  intros Hs ob; induction Hs as [| | ? ? Hfull]; intros Hob.
  - by inversion Hob.
  - by inversion Hob using rec_obs_send_inv; intros; apply elem_of_messages_addObservation; auto.
  - apply elem_of_messages_addObservation; cbn.
    inversion Hob using rec_obs_recv_inv; [by auto.. |].
    pose proof (fun m H => elem_of_submseteq _ _ m H Hfull) as Hmsg.
    intros [Hm | (m & Hm & Hob')]%unfold_rec_obs.
    + by right; apply Hmsg, elem_of_list_fmap_1.
    + apply (elem_of_list_fmap_1 message) in Hm.
      by right; apply IHHs, (unfold_robs full_node); eauto.
Qed.

Lemma local_equivocators_simple_iff_full (s : State) :
  UMO_reachable no_self_equiv s ->
  forall a, local_equivocators_simple s a <-> local_equivocators_full s a.
Proof.
  intros Hs a; split.
  - induction Hs.
    + by destruct 1; inversion les_obs_m1.
    + intros Ha.
      apply lefo_prev, IHHs.
      revert Ha; apply local_equivocators_simple_add_Send.
      by eapply UMO_reachable_impl.
    + intros Ha.
      apply local_equivocators_simple_add_Receive in Ha; [| done..].
      destruct Ha as [| (<- & Hnot_s & m & Hm & Hincomp)]; [by apply lefo_prev, IHHs |].
      assert (adr (state m) <> adr s) by (destruct Hincomp; congruence).
      by revert Hincomp; apply lefo_last, not_adr_received.
  - destruct s as [s_obs s_a].
    unfold local_equivocators_full; cbn.
    intro Hlefo; induction Hlefo as [? ? ? ? Hm12 |].
    + exists m1 m2; [done | .. | done].
      * by symmetry; apply Hm12.
      * by apply elem_of_cons; left.
      * apply elem_of_cons; right; change (m2 ∈ messages (MkState ol s_a)).
        by apply received_in_messages.
    + change (MkState _ _) with (MkState ol s_a <+> MkObservation l m) in Hs |- *.
      apply local_equivocators_simple_prev, IHHlefo.
      by inversion Hs; destruct s.
Qed.

Lemma local_equivocators_iff_simple (s : State) :
  UMO_reachable full_node s ->
  forall a, local_equivocators s a <-> local_equivocators_simple s a.
Proof.
  intro Hs; split; destruct 1.
  - by exists (message lceqv_ob1) (message lceqv_ob2); auto using reachable_obs_msg.
  - apply (full_node_messages_iff_rec_obs s Hs) in les_obs_m1 as [l1 Hm1], les_obs_m2 as [l2 Hm2].
    by exists (MkObservation l1 les_m1) (MkObservation l2 les_m2); auto using reachable_obs_msg.
Qed.

Lemma local_equivocators_iff_full (s : State) :
  UMO_reachable (fun s m => full_node s m /\ no_self_equiv s m) s ->
  forall a, local_equivocators s a <-> local_equivocators_full s a.
Proof.
  intros Hs a.
  by rewrite local_equivocators_iff_simple;
    [apply local_equivocators_simple_iff_full |];
    revert Hs; apply UMO_reachable_impl; itauto.
Qed.

(**
  The [msg_valid_full] predicate holds for any reachable state,
  even though it is only explicitly checked when receiving messages.
*)

Lemma ELMO_reachable_msg_valid_full :
  forall s : State,
    ram_state_prop Ei s -> ELMO_msg_valid_full (MkMessage s).
Proof.
  intros s [Hs Hi]%ELMO_reachable_view.
  induction Hs as [| | ? ? Hvalid]; [| specialize (IHHs Hi)..].
  - by constructor; [| eexists].
  - by constructor.
  - by eapply MVF_recv in IHHs; [| apply Hvalid..].
Qed.

Lemma reachable_full_node_for_all_messages i' (s : State) :
  ram_state_prop (ELMOComponent i') s ->
  forall m, m ∈ messages s -> full_node s m.
Proof.
  intros [Hs _]%ELMO_reachable_view.
  induction Hs as [| | ? ? Hvalid].
  - by inversion 1.
  - by intros m [-> | Hm%IHHs]%elem_of_messages_addObservation; apply submseteq_cons.
  - intros m Hm.
    apply submseteq_cons; change (full_node s m).
    apply elem_of_messages_addObservation in Hm as [-> | Hm].
    + by apply Hvalid.
    + by apply IHHs in Hm.
Qed.

Lemma reachable_sent_messages_reachable i' (s ms : State) :
  ram_state_prop (ELMOComponent i') s ->
  MkMessage ms ∈ sentMessages s ->
  ram_state_prop (ELMOComponent i') ms.
Proof.
  intros [Hs Hadr]%ELMO_reachable_view Hms.
  apply ELMO_reachable_view.
  induction Hs; [| | by auto].
  - by apply not_elem_of_nil in Hms.
  - by apply elem_of_sentMessages_addObservation in Hms as [[[= ->] _] | Hms]; auto.
Qed.

Lemma reachable_sent_messages_adr (s : State) (m : Message) :
  ram_state_prop Ei s ->
  m ∈ sentMessages s ->
  adr (state m) = idx i.
Proof.
  intros Hs Hm; destruct m.
  by eapply ELMO_reachable_adr, reachable_sent_messages_reachable.
Qed.

Lemma reachable_messages_are_msg_valid (s : State) (m : Message) :
  ram_state_prop Ei s ->
  m ∈ messages s ->
  ELMO_msg_valid_full m.
Proof.
  intros [Hs Hadr]%ELMO_reachable_view Hm.
  revert s Hs m Hm Hadr.
  refine (UMO_reachable_elem_of_messages_ind _ _ _ _ _); [done | | by destruct 2].
  by intros; apply ELMO_reachable_msg_valid_full, ELMO_reachable_view.
Qed.

Lemma equivocators_of_msg_subset_of_recv (s : State) (m : Message) :
  full_node s m ->
  forall a,
    local_equivocators_simple (state m) a
    -> local_equivocators_simple (s <+> MkObservation Receive m) a.
Proof.
  intros Hfull a []; destruct m as [ms]; cbn in *.
  assert (forall x, x ∈ messages ms -> x ∈ messages (s <+> MkObservation Receive (MkMessage ms)))
    by (intros; apply elem_of_messages_addObservation; right; eapply elem_of_submseteq; done).
  by eauto using local_equivocators_simple.
Qed.

Lemma equivocation_limit_recv_ok_msg_ok (s : State) (m : Message) :
  full_node s m ->
  no_self_equiv s m ->
  UMO_reachable no_self_equiv s ->
  UMO_reachable no_self_equiv (state m) ->
  local_equivocation_limit_ok (s <+> MkObservation Receive m) ->
  local_equivocation_limit_ok (state m).
Proof.
  intros Hfull Hno_self Hs Hms Hs'.
  eapply Rle_trans; [| done].
  apply incl_equivocating_validators_equivocation_fault, filter_subprop; cbn; intros a Ha.
  rewrite <- local_equivocators_simple_iff_full in Ha by done.
  rewrite <- local_equivocators_simple_iff_full by (constructor; done).
  by apply equivocators_of_msg_subset_of_recv.
Qed.

Lemma ELMO_msg_valid_prefix (m : Message) (ob : Observation) :
  ELMO_msg_valid_full (m <*> ob) ->
  ELMO_msg_valid_full m.
Proof.
  inversion 1 as [? Hobs | |].
  - by inversion Hobs.
  - by replace m with m0 by (apply eq_Message; done).
  - by replace m with m0 by (apply eq_Message; done).
Qed.

Lemma adr_neq_no_self_equiv (s : State) (m : Message) :
  adr s <> adr (state m) ->
  no_self_equiv s m.
Proof. by unfold no_self_equiv. Qed.

Lemma full_node_prefix s m ob :
  full_node s (m <*> ob) ->
  full_node s m.
Proof. by apply submseteq_tail_l. Qed.

Lemma ELMO_msg_valid_full_Send_inv
  (P : Message -> Message -> Prop) :
  (forall m om, m = om -> P m om) ->
  forall (m om : Message),
  ELMO_msg_valid_full (m <*> MkObservation Send om) ->
  P m om.
Proof.
  intros Hm m om.
  inversion 1 as [? Hobs | |].
  - by inversion Hobs.
  - by apply Hm, eq_Message.
Qed.

Lemma incomparable_iff (m1 m2 : Message) :
  incomparable m1 m2
    <->
  adr (state m1) = adr (state m2)
  /\ m1 <> m2
  /\ m1 ∉ sentMessages (state m2)
  /\ m2 ∉ sentMessages (state m1).
Proof.
  split.
  - intros [Hadr Hnot]; split; [done |].
    by repeat split; contradict Hnot; subst; constructor.
  - intros (Hadr & Hneq & Hnot_m12 & Hnot_m21).
    split; [done |].
    by destruct 1 as [| m1 m2 [] | m1 m2 []].
Qed.

Lemma equivocation_limit_recv_msg_prefix_ok (v : State) (m : Message) ob
  (m' := m <*> ob)
  (v' := v <+> MkObservation Receive m')
  (v'' := v <+> MkObservation Receive m)
  :
  adr (state m) <> adr v ->
  ram_state_prop Ei v ->
  m' ∉ receivedMessages v ->
  m ∉ receivedMessages v ->
  ELMO_recv_valid v m' ->
  local_equivocation_limit_ok (v <+> MkObservation Receive (m <*> ob)) ->
  local_equivocation_limit_ok (v <+> MkObservation Receive m).
Proof.
  intros Hadrs Hv Hfresh_m' Hfresh_m Hvalid Hs'.
  eapply Rle_trans; [| done].
  apply incl_equivocating_validators_equivocation_fault, filter_subprop; cbn.
  fold v'' m' v'.
  intros k Hk; cbn in *.
  apply lefo_alt in Hk as [(-> & _ & u & Hu & Hincomp) |]; [| by apply lefo_prev].
  apply (lefo_last _ m' u Hu).
  apply incomparable_iff in Hincomp as (Hadr & Hneq & H_m1_m2 & H_m2_m1).
  apply incomparable_iff; repeat split; [done | by intros <- | |].
  - intro Hm'.
    contradict Hfresh_m'.
    apply not_adr_received; [| done |].
    + apply UMO_reachable_impl with (1 := ELMO_mv_no_self_equiv).
      by apply ELMO_reachable_view in Hv as [].
    + eapply elem_of_submseteq.
      * by apply elem_of_messages; left.
      * apply reachable_full_node_for_all_messages with (1 := Hv).
        by apply elem_of_messages; right.
  - intros [[-> Hob] |]%elem_of_sentMessages_addObservation; [| done].
    destruct ob as [[] om], Hob, Hneq; cbn in *.
    assert (ELMO_msg_valid_full m') as Hmv by apply Hvalid.
    by inversion Hmv; [| apply eq_Message].
Qed.

Hint Resolve
  equivocation_limit_recv_msg_prefix_ok
  : ELMO_hints.

Hint Resolve
  full_node_prefix
  adr_neq_no_self_equiv
  ELMO_msg_valid_prefix
  : ELMO_hints.

Lemma ELMO_recv_valid_prefix s (m : Message) (ob : Observation) :
  ram_state_prop Ei s ->
  m <*> ob ∉ receivedMessages s ->
  m ∉ receivedMessages s ->
  adr s <> adr (state m) ->
  ELMO_recv_valid s (m <*> ob) ->
  ELMO_recv_valid s m.
Proof.
  intros until 4; intros Hrecv.
  destruct (Hrecv) as [Hfull Hno_self Hmsg Hlimit].
  by constructor; eauto with ELMO_hints.
Qed.

Hint Resolve ELMO_recv_valid_prefix : ELMO_hints.

Lemma reachable_received_messages_reachable (s : State) :
  ram_state_prop Ei s ->
  forall m,
    m ∈ receivedMessages s ->
  forall i',
    adr (state m) = idx i' ->
    ram_state_prop (ELMOComponent i') (state m).
Proof.
  intros Hs m Hm.
  destruct (decide (adr (state m) = adr s)).
  {
    intros i' Hi'.
    cut (m ∈ sentMessages s).
    - destruct m.
      apply reachable_sent_messages_reachable.
      assert (i = i') as ->; [| done].
      by (apply ELMO_reachable_view in Hs as []; apply (inj idx); congruence).
    - apply self_messages_sent; [| done |].
      + apply ELMO_reachable_view in Hs as [Hs ?].
        revert Hs; apply UMO_reachable_impl.
        by intros ? ? [].
      + by apply elem_of_messages; auto.
  }
  revert m Hm n.
  apply ELMO_reachable_view in Hs as [Hs Hadr].
  induction Hs as [| | ? ? Hvalid]; [by inversion 1 | by apply IHHs |].
  intros m Hm%elem_of_receivedMessages_addObservation; cbn in Hm, Hadr.
  destruct Hm as [[<- []] |]; [| by eauto].
  destruct (decide (m ∈ receivedMessages s)); [by eauto |].
  clear IHHs; revert s Hs Hadr Hvalid n.
  destruct m as [ms]; cbn.
  induction ms using addObservation_ind.
  - by intros; apply initial_state_is_valid; constructor.
  - set (m' := ms <+> ob); cbn.
    intros s Hs Hadr Hrecv_m' Hfresh' Hadr_neq i' Hadr_ms.
    assert (Hrecv_if_fresh : MkMessage ms ∉ receivedMessages s -> ELMO_recv_valid s (MkMessage ms)).
    {
      by intro; apply (ELMO_recv_valid_prefix s (MkMessage ms) ob); [apply ELMO_reachable_view | ..].
    }
    assert (Hms : ram_state_prop (ELMOComponent i') ms).
    {
      destruct (decide (MkMessage ms ∈ receivedMessages s)); [| by eauto].
      revert e; clear -Hs IHms Hadr Hadr_ms Hadr_neq.
      induction Hs; [by inversion 1 | by eapply IHHs |].
      destruct (decide (MkMessage ms ∈ receivedMessages s)).
      - by intros; eapply IHHs.
      - intros [[Hms _] |]%elem_of_receivedMessages_addObservation; cbn in *; subst; eauto.
    }
    apply ELMO_reachable_view; split; [| done].
    apply ELMO_reachable_view in Hms as [Hms _].
    destruct ob as [[] [os]].
    + apply reach_recv; [| done].
      destruct Hrecv_m' as [Hfull_s_m' Hself Hmvf_m' Hlimit].
      inversion Hmvf_m' as [| | ? ? Hfull_m_os Hself_os Hvalid Heqmo]; [done |].
      assert (m = MkMessage ms)
        by (destruct m; f_equal; apply eq_State; done).
      subst m; clear mo Heqmo; cbn in *.
      constructor; [done | done | |].
      * apply reachable_messages_are_msg_valid with (s := s).
        -- by apply ELMO_reachable_view.
        -- by revert Hfull_s_m'; apply elem_of_submseteq, elem_of_list_here.
      * apply equivocation_limit_recv_ok_msg_ok in Hlimit; try done.
        -- by revert Hs; apply UMO_reachable_impl; intros ? ? [].
        -- apply reach_recv; [done |].
           by revert Hms; apply UMO_reachable_impl; intros ? ? [].
    + destruct Hrecv_m' as [_ _ Hmvf _]; inversion Hmvf; [done |].
      unfold m'.
      replace os with ms by (apply eq_State; done).
      by apply reach_send.
Qed.

Lemma receivable_messages_reachable (ms s : State) i' :
  adr ms = idx i' ->
  ram_state_prop Ei s ->
  ELMO_recv_valid s (MkMessage ms) ->
  ram_state_prop (ELMOComponent i') ms.
Proof.
  intros Heq Hram Hrv.
  change ms with (state (MkMessage ms)).
  apply reachable_received_messages_reachable
    with (s := s <+> MkObservation Receive (MkMessage ms))
  ; [| constructor | done].
  apply ELMO_reachable_view in Hram as [].
  apply ELMO_reachable_view; cbn.
  by split; [apply reach_recv |].
Qed.

Inductive ELMOComponentRAMTransition : Label -> State -> State -> Message -> Prop :=
| ecr_valid_receive : forall (s1 s2 : State) (m : Message),
    input_valid_transition Ri Receive (s1, Some m) (s2, None) ->
    ELMOComponentRAMTransition Receive s1 s2 m
| ecr_valid_send : forall (s1 s2 : State) (m : Message),
    input_valid_transition Ri Send (s1, None) (s2, Some m) ->
    ELMOComponentRAMTransition Send s1 s2 m.

Lemma ELMOComponent_input_valid_transition_iff
  (l : Label) (s : State) (om : option Message) (s' : State) (om' : option Message) :
  input_valid_transition Ri l (s, om) (s', om')
    <->
  (l = Receive /\ exists m, om = Some m /\ om' = None /\ ELMOComponentRAMTransition l s s' m)
    \/
  (l = Send /\ exists m, om' = Some m /\ om = None /\ ELMOComponentRAMTransition Send s s' m).
Proof.
  split; cycle 1.
  - by intros [(-> & ? & -> & -> & Hm) | (-> & ? & -> & -> & Hm)]; inversion Hm.
  - intros Ht; pose (Hti := Ht);  destruct Hti as [(_ & _ & Hvi) Hti];
      inversion Hvi; subst; inversion Hti; subst; [left | right].
    + by split; [done |]; eexists; split_and!; [done.. |]; constructor.
    + by split; [done |]; eexists; split_and!; [done.. |]; constructor.
Qed.

Lemma ELMOComponent_elem_of_ram_trace
  [s tr] (Htr : finite_valid_trace_from Ri s tr) :
  forall item, item ∈ tr ->
    exists (s : State) (m : Message),
      destination item = s <+> MkObservation (l item) m /\
      input_valid_transition_item Ri s item.
Proof.
  induction Htr; [by inversion 1 |].
  intro item; rewrite elem_of_cons; intros [-> | Hitem]; [| by apply IHHtr].
  by pose (Hti := Ht); destruct Hti as [(_ & _ & Hvi) Hti];
    inversion Hvi; subst; inversion Hti; subst; eexists _, _; split.
Qed.

Lemma ELMOComponent_receivedMessages_of_ram_trace
  [s s' tr] (Htr : finite_valid_trace_from_to Ri s s' tr) :
  forall item, item ∈ tr ->
  forall m, (field_selector input) m item -> m ∈ receivedMessages s'.
Proof.
  induction Htr using finite_valid_trace_from_to_rev_ind; [by inversion 1 |].
  intros item Hitem m Hm.
  change (has_been_received Ei sf m).
  eapply has_been_received_step_update; [done |].
  rewrite elem_of_app, elem_of_list_singleton in Hitem.
  by destruct Hitem as [Hitem | ->]; [right; cbn; eapply IHHtr | left].
Qed.

Lemma ELMOComponent_sentMessages_of_ram_trace
  [s s' tr] (Htr : finite_valid_trace_from_to Ri s s' tr) :
  forall item, item ∈ tr ->
  forall m, (field_selector output) m item -> m ∈ sentMessages s'.
Proof.
  induction Htr using finite_valid_trace_from_to_rev_ind; [by inversion 1 |].
  intros item Hitem m Hm.
  change (has_been_sent Ei sf m).
  eapply has_been_sent_step_update; [done |].
  rewrite elem_of_app, elem_of_list_singleton in Hitem.
  by destruct Hitem as [Hitem | ->]; [right; cbn; eapply IHHtr | left].
Qed.

Lemma ELMOComponent_sizeState_of_ram_trace_output
  [s tr] (Htr : finite_valid_trace_from Ri s tr) :
  forall item, item ∈ tr ->
  forall m, (field_selector output) m item ->
  sizeState s <= sizeState (state m).
Proof.
  induction Htr; [by inversion 1 |].
  intros item Hitem m Hm.
  apply elem_of_cons in Hitem as [-> | Hitem]; cbn in Hm;
    destruct Ht as [(_ & _ & Hv) Ht]; inversion Hv; subst; inversion Ht; subst; [done | ..].
  all: by etransitivity; [| eapply IHHtr]; [rewrite addObservation_size; lia | ..].
Qed.

Lemma ELMOComponent_messages_of_ram_trace
  [s s' tr] (Htr : finite_valid_trace_from_to Ri s s' tr) :
  forall item, item ∈ tr ->
  forall m, item_sends_or_receives m item -> m ∈ messages s'.
Proof.
  intros ? ? ? [|]; apply elem_of_messages.
  - by right; eapply ELMOComponent_receivedMessages_of_ram_trace.
  - by left; eapply ELMOComponent_sentMessages_of_ram_trace.
Qed.

End sec_ELMOComponent_lemmas.

Section sec_TraceableVLSM_ELMOComponent.

Context
  (i : index)
  (Ei : VLSM Message := ELMOComponent i)
  (Ri : VLSM Message := pre_loaded_with_all_messages_vlsm Ei)
  .

Definition ELMOComponent_state_destructor (s : State)
  : list (@transition_item Message ELMOComponentType * State) :=
  let adr := adr s in
match obs s with
| [] => []
| MkObservation Send msg as ob :: obs =>
    let source := MkState obs adr in
      [(Build_transition_item Send None s (Some msg), source)]
| MkObservation Receive msg as ob :: obs =>
    let source := MkState obs adr in
      [(Build_transition_item Receive (Some msg) s None, source)]
end.

Lemma ELMOComponent_state_destructor_initial :
  forall (s' : vstate Ei), ram_state_prop Ei s' ->
    vinitial_state_prop Ei s' <-> ELMOComponent_state_destructor s' = [].
Proof.
  intros s' Hs'; split; intro Hs''.
  - by cbn in Hs''; apply UMOComponent_initial_state_spec in Hs'' as ->.
  - apply ELMO_reachable_adr in Hs'.
    by destruct s' as [[| [[] ]] adr]; cbn in *; [| done..].
Qed.

Lemma ELMOComponent_state_destructor_input_valid_transition :
  forall (s' : vstate Ei), ram_state_prop Ei s' ->
  forall (s : vstate Ei) (item : vtransition_item Ei),
    (item, s) ∈ ELMOComponent_state_destructor s' ->
    input_valid_transition_item Ri s item.
Proof.
  intros s' Hs'; apply valid_state_prop_iff in Hs' as [[[is His] ->] | (l & (s, om) & om' & Hpt)].
  - by cbn in *; apply UMOComponent_initial_state_spec in His as ->; inversion 1.
  - by pose (Hpt' := Hpt); destruct l, s, om, Hpt' as [(_ & _ & Hv) Ht];
      inversion Hv; subst; inversion Ht; subst;
      intros _s item Hitem; apply elem_of_list_singleton in Hitem; inversion Hitem.
Qed.

#[export] Instance TraceableVLSM_ELMOComponent :
  TraceableVLSM Ei ELMOComponent_state_destructor sizeState.
Proof.
  constructor.
  - by typeclasses eauto.
  - by intros [[| [[] ?] ?] ?] *; [inversion 1 | ..];
      intro Hitem; apply elem_of_list_singleton in Hitem;
      inversion_clear Hitem.
  - by apply ELMOComponent_state_destructor_input_valid_transition.
  - by apply ELMOComponent_state_destructor_initial.
Qed.

Lemma ELMO_latest_observation_Send_state :
  forall s' : State, ram_state_prop Ei s' ->
  forall (s : State) (m : Message), s' = s <+> MkObservation Send m ->
    s = state m.
Proof.
  intros s' Hs' s m ->.
  edestruct (ELMOComponent_state_destructor_input_valid_transition _ Hs') as [(_ & _ & Hv) Ht];
    [by apply elem_of_list_singleton |]; cbn in *.
  by inversion Hv; subst; inversion Ht; subst; destruct s.
Qed.

End sec_TraceableVLSM_ELMOComponent.

Section sec_MessageDependencies_ELMOComponent.

Context
  (i : index)
  (Ei : VLSM Message := ELMOComponent i)
  (Ri : VLSM Message := pre_loaded_with_all_messages_vlsm Ei)
  .

Lemma cannot_resend_message_stepwise_ELMOComponent :
  cannot_resend_message_stepwise_prop Ei.
Proof.
  intros ? * [(Hs & _ & Hv) Ht];
    inversion Hv; subst; inversion Ht; subst;
    simpl; split; intro Hobs.
  - by apply elem_of_sentMessages, obs_sizeState in Hobs; cbn in Hobs; lia.
  - rewrite receivedMessages_addObservation, decide_False in Hobs by (intro; done).
    by apply elem_of_receivedMessages, obs_sizeState in Hobs; cbn in Hobs; lia.
Qed.

#[export] Instance MessageDependencies_ELMOComponent :
  MessageDependencies Ei Message_dependencies.
Proof.
  constructor.
  - intros m s' ((s, iom) & l & [(_ & _ & Hv) Ht]) dm Hdm; cbn in *.
    apply elem_of_list_to_set, elem_of_list_fmap in Hdm
      as (o & -> & Hy).
    inversion Hv; subst; inversion Ht; subst; cbn in *; clear Ht.
    red; unfold Message; simpl.
    rewrite elem_of_sentMessages_addObservation, elem_of_receivedMessages_addObservation,
      elem_of_sentMessages, elem_of_receivedMessages; cbn.
    by destruct o as [[] ?]; cbn; firstorder.
  - intros m Hm.
    apply can_emit_has_trace in Hm as (is & tr & item & Htr & Houtput).
    apply (can_emit_from_valid_trace
            (pre_loaded_vlsm Ei (fun msg : Message => msg ∈ Message_dependencies m)))
      with is (tr ++ [item]); cycle 1.
    + apply Exists_exists; eexists.
      by split; [apply elem_of_app; right; left |].
    + eapply lift_preloaded_trace_to_seeded;
        [by apply cannot_resend_message_stepwise_ELMOComponent | | done].
      intros dm [Hrcv Hnsnd].
      apply elem_of_list_to_set, elem_of_list_fmap.
      exists (MkObservation Receive dm); split; [done |].
      apply elem_of_receivedMessages.
      destruct Htr as [Htr His].
      apply finite_valid_trace_from_app_iff in Htr as [Htr Hitem].
      apply valid_trace_add_default_last in Htr.
      apply first_transition_valid in Hitem as [(_ & _ & Hv) Ht].
      destruct item, l, input; cbn in *; inversion Hv; subst; inversion Ht; subst.
      clear Hv Ht Hnsnd; cbn.
      assert (Hrcv' : trace_has_message (field_selector input) dm tr).
      {
        apply Exists_exists in Hrcv as (dm_item & Hdm_item & Hdm).
        rewrite elem_of_app, elem_of_list_singleton in Hdm_item.
        destruct Hdm_item as [Hdm_item | ->]; cbn in Hdm; [| done].
        by apply Exists_exists; eexists.
      }
      by eapply @has_been_received_examine_one_trace with (vlsm := Ei) in Hrcv'; cycle 1.
Qed.

End sec_MessageDependencies_ELMOComponent.

Section sec_ELMOProtocol.

Context `{Inhabited index}.

(** ** Protocol

  An ELMO protocol is defined as the constrained composition of a collection
  of ELMO components, under a composition constraint that checks that the
  weight of the globally-detectable equivocation is under the threshold.
*)

(** *** Equivocators *)

Definition ELMO_global_equivocators (s : composite_state ELMOComponent) (a : Address) : Prop :=
  exists m : Message,
    adr (state m) = a /\
    (exists (k : index) (l : Label), rec_obs (s k) (MkObservation l m)) /\
    ~ composite_has_been_sent ELMOComponent s m.

Definition rec_obs_exists_dec
  (P : Observation -> Prop)
  (P_dec : forall o, Decision (P o))
  (s : State)
  : Decision (exists o, rec_obs s o /\ P o).
Proof.
  revert s; fix rec 1; destruct s as [ol a].
  induction ol as [| ob ol]
  ; [| specialize (rec (state (message ob))) as IHob]; clear rec.
  - by right; intros (? & Hrec & ?); inversion Hrec.
  - change (MkState _ _) with (MkState ol a <+> ob);
      remember (MkState ol a) as s; clear Heqs ol a.
    destruct (P_dec ob) as [| Hnot_new];
      [by left; eexists; split; [constructor |] |].
    destruct IHol as [| Hnot_prev];
      [by left; destruct e as (o & Ho & HPo); exists o; split; [constructor 2 |] |].
    destruct ob as [[] [os]]; cbn in IHob.
    + destruct IHob as [| Hnot_recv];
        [by left; destruct e as (o & Ho & HPo); exists o; split; [constructor 3 |] |].
      by right; intros (? & Hrec & ?); inversion Hrec; subst;
        replace s0 with s in * by (apply eq_State; done); eauto.
    + by right; intros (? & Hrec & ?); inversion Hrec; subst;
        replace s0 with s in * by (apply eq_State; done); eauto.
Defined.

#[export]
Instance ELMO_global_equivocators_dec : RelDecision ELMO_global_equivocators.
Proof.
  intros s a.
  apply (@Decision_iff
    (exists k o, rec_obs (s k) o
      /\ adr (state (message o)) = a
      /\ not (composite_has_been_sent ELMOComponent s (message o)))).
  {
    unfold ELMO_global_equivocators.
    split; intros Hequ.
    - by destruct Hequ as (k & [l m] & Hk & [Hadr Hsuff]); eauto 6.
    - by destruct Hequ as (m & Hadr & (k & l & Hrec_obs) & Hnot_sent); eauto.
  }
  pose proof @rec_obs_exists_dec.
  by typeclasses eauto.
Defined.

Set Warnings "-cannot-define-projection".
Record global_equivocators_simple (s : composite_state ELMOComponent) (a : Address) : Prop :=
{
  ges_m : Message;
  ges_adr : adr (state ges_m) = a;
  ges_recv : composite_has_been_received ELMOComponent s ges_m;
  ges_not_sent : not (composite_has_been_sent ELMOComponent s ges_m);
}.
Set Warnings "cannot-define-projection".

Definition ELMO_global_equivocation : BasicEquivocation (composite_state ELMOComponent) Address Ca threshold :=
{|
  is_equivocating := ELMO_global_equivocators;
  is_equivocating_dec := ELMO_global_equivocators_dec;
  state_validators := const (list_to_set (map idx (enum index)));
|}.

Definition ELMO_not_heavy : composite_state ELMOComponent -> Prop :=
  not_heavy (1 := ELMO_global_equivocation).

Definition ELMO_equivocating_validators : composite_state ELMOComponent -> Ca :=
  equivocating_validators (1 := ELMO_global_equivocation).

Definition ELMO_global_constraint
  (l : composite_label ELMOComponent)
  (som : composite_state ELMOComponent * option Message) : Prop :=
match l with
| existT _ Receive =>
  let (s', _) := composite_transition ELMOComponent l som in
    ELMO_not_heavy s'
| existT _ Send => True
end.

Definition ELMOProtocol : VLSM Message :=
  composite_vlsm ELMOComponent ELMO_global_constraint.

Definition FreeELMO : VLSM Message :=
  free_composite_vlsm ELMOComponent.

(**
  To talk about reachabile composite states for the ELMOProtocol we also name
  the [pre_loaded_with_all_messages_vlsm] version of the [free_composition].
*)

Definition ReachELMO : VLSM Message :=
  pre_loaded_with_all_messages_vlsm FreeELMO.

Definition composite_ram_state_prop
  {message : Type} `{EqDecision index}
  (IM : index -> VLSM message) (s : composite_state IM) : Prop :=
    ram_state_prop (free_composite_vlsm IM) s.

Lemma ELMO_initial_state_equivocating_validators :
  forall s : composite_state ELMOComponent,
    composite_initial_state_prop ELMOComponent s ->
      ELMO_equivocating_validators s ≡ ∅.
Proof.
  intros s Hs; rewrite elem_of_equiv_empty; intros v.
  setoid_rewrite elem_of_filter; intros [(m & _ & [(k & l & Hobs) _]) _].
  replace (s k) with (MkState [] (idx k)) in Hobs
    by (symmetry; apply UMOComponent_initial_state_spec, Hs).
  by inversion Hobs.
Qed.

Lemma ELMO_initial_state_not_heavy :
  forall s : composite_state ELMOComponent,
    composite_initial_state_prop ELMOComponent s -> ELMO_not_heavy s.
Proof.
  intros s Hs.
  unfold ELMO_not_heavy, not_heavy.
  replace (equivocation_fault s) with 0%R.
  - by apply (rt_positive (H6 := H6)).
  - by symmetry; apply sum_weights_empty, ELMO_initial_state_equivocating_validators.
Qed.

Lemma ELMO_not_heavy_send_message :
  forall (sigma : composite_state ELMOComponent) (i : index),
    ELMO_not_heavy sigma ->
    ELMO_not_heavy
      (state_update ELMOComponent sigma i
        (sigma i <+> MkObservation Send (MkMessage (sigma i)))).
Proof.
  unfold ELMO_not_heavy, not_heavy; etransitivity; [| done].
  apply sum_weights_subseteq; [by apply NoDup_elements.. |].
  intro a.
  unfold equivocating_validators; rewrite !elem_of_filter; cbn.
  intros [(msg & ? & (k & l & Hmsh) & Hnsent) Hx].
  split; [| done]; clear Hx.
  exists msg; split; [done |].
  split.
  - exists k, l; destruct (decide (k = i)); subst; state_update_simpl; [| done].
    by destruct (sigma i); inversion Hmsh; cbn in *; subst;
      [contradict Hnsent; exists i; cbn; state_update_simpl; left | destruct s].
  - contradict Hnsent; destruct Hnsent as [j Hsnd]; exists j; cbn.
    by destruct (decide (j = i)); subst; state_update_simpl; [right |].
Qed.

Lemma ELMO_not_heavy_receive_observed_message :
  forall (sigma : composite_state ELMOComponent) (m : Message) (i i_m : index),
    UMO_reachable full_node (sigma i_m) ->
    has_been_directly_observed (ELMOComponent i_m) (sigma i_m) m ->
    ELMO_not_heavy sigma ->
      ELMO_not_heavy (state_update ELMOComponent sigma i (sigma i <+> MkObservation Receive m)).
Proof.
  intros * Hfull Hobs.
  unfold ELMO_not_heavy, not_heavy; etransitivity; [| done].
  apply sum_weights_subseteq; [by apply NoDup_elements.. |].
  intro a.
  unfold equivocating_validators; rewrite !elem_of_filter; cbn.
  intros [(msg & ? & (k & l & Hmsh) & Hnsent) Hx].
  split; [| done]; clear Hx.
  exists msg; split; [done |].
  split; cycle 1.
  - contradict Hnsent; destruct Hnsent as [j Hsnd]; exists j; cbn.
    by destruct (decide (j = i)); subst; state_update_simpl.
  - destruct (decide (k = i)); subst; state_update_simpl; [| by eexists _, _].
    apply rec_obs_addObservation_iff in Hmsh as [Hprev | Hmsh]; [by eexists _, _ |].
    assert (m ∈ messages (sigma i_m)) by (apply elem_of_messages; done).
    exists i_m.
    apply full_node_messages_iff_rec_obs; [done |].
    destruct Hmsh as [[= _ ->] | [_ Hmsh]]; [done |].
    apply messages_hb_transitive with m; [done.. |].
    apply happensBefore_msg_dep, full_message_dependencies_happens_before.
    apply elem_of_rec_obs_fn_1 in Hmsh.
    by apply elem_of_map; eexists; split; cycle 1.
Qed.

Lemma ELMO_valid_state_not_heavy :
  forall s : composite_state ELMOComponent,
    valid_state_prop ELMOProtocol s -> ELMO_not_heavy s.
Proof.
  induction 1 using valid_state_prop_ind; [by apply ELMO_initial_state_not_heavy |].
  apply input_valid_transition_destination in Ht as Hs'.
  destruct Ht as [(Hs & _ & [Hv Hc]) Ht].
  unfold ELMO_global_constraint in Hc; destruct l as [i []];
    [by replace (composite_transition _ _ _) with (s', om') in Hc |].
  inversion Hv; subst; inversion Ht; subst.
  by apply ELMO_not_heavy_send_message.
Qed.

Definition ELMO_state_to_minimal_equivocation_trace
  (s : composite_state ELMOComponent) (Hs : composite_ram_state_prop ELMOComponent s)
  : composite_state ELMOComponent * list (composite_transition_item ELMOComponent) :=
  state_to_minimal_equivocation_trace ELMOComponent
    (fun _ : index => ELMOComponent_state_destructor) (fun _ : index => sizeState) s Hs.

Lemma ELMO_state_to_minimal_equivocation_trace_reachable
  (s : composite_state ELMOComponent) (Hs : composite_ram_state_prop ELMOComponent s)
  (is : composite_state ELMOComponent) (tr : list (composite_transition_item ELMOComponent)) :
    ELMO_state_to_minimal_equivocation_trace s Hs = (is, tr) ->
      finite_valid_trace_init_to ReachELMO is s tr.
Proof.
  by apply reachable_composite_state_to_trace,
    minimal_equivocation_choice_is_choosing_well.
Qed.

Lemma ELMO_has_been_directly_observed_sizeState :
  forall i si m,
  has_been_directly_observed (ELMOComponent i) si m ->
  sizeState (state m) < sizeState si.
Proof.
  intros * [Hsent | Hreceived]; cbn in *.
  - by apply elem_of_sentMessages, obs_sizeState in Hsent.
  - by apply elem_of_receivedMessages, obs_sizeState in Hreceived.
Qed.

Lemma ELMO_composite_observed_before_send_sizeState_Proper :
  Proper
    (composite_observed_before_send ELMOComponent Message_dependencies ==> lt)
    (sizeState ∘ state).
Proof.
  intros x y Hxy; cbn.
  apply composite_observed_before_send_iff in Hxy
    as (i & si & itemi & [[(Hsi & _ & Hv) Ht] Hy Hobsxitem]).
  destruct itemi, l, input; cbn in *;
    inversion Hv; subst; inversion Ht; subst; clear Hv Ht.
  inversion Hobsxitem as [? ? ? Hobsx | |]; subst; clear Hobsxitem; cbn.
  inversion Hobsx; [by eapply ELMO_has_been_directly_observed_sizeState |].
  etransitivity; [| by eapply ELMO_has_been_directly_observed_sizeState].
  by apply Message_full_dependencies_sizeState,
    full_message_dependencies_happens_before.
Qed.

#[local] Instance ELMOComponent_tc_composite_observed_before_send_irreflexive :
  Irreflexive (tc_composite_observed_before_send ELMOComponent Message_dependencies).
Proof.
  apply (Proper_reflects_Irreflexive _ (<) (sizeState ∘ state));
    [| typeclasses eauto].
  apply Proper_tc; [typeclasses eauto |].
  by apply ELMO_composite_observed_before_send_sizeState_Proper.
Qed.

Lemma ELMO_channel_authentication_prop :
  channel_authentication_prop ELMOComponent (ELMO_A idx) Message_sender.
Proof.
  intros i m ((s, []) & [] & s' & [(Hs & _ & Hv) Ht]);
    inversion Hv; subst; inversion Ht; subst.
  unfold channel_authenticated_message; cbn; f_equal.
  by erewrite ELMO_reachable_adr, ELMO_A_inv.
Qed.

Lemma ELMO_state_to_minimal_equivocation_trace_equivocation_monotonic :
  forall (s : composite_state ELMOComponent) (Hs : composite_ram_state_prop ELMOComponent s),
  forall (is : composite_state ELMOComponent) (tr :list (composite_transition_item ELMOComponent)),
  ELMO_state_to_minimal_equivocation_trace s Hs = (is, tr) ->
  forall (pre suf : list (composite_transition_item ELMOComponent))
    (item : composite_transition_item ELMOComponent),
    tr = pre ++ [item] ++ suf ->
    forall v : Address,
      msg_dep_is_globally_equivocating ELMOComponent Message_dependencies Message_sender
        (finite_trace_last is pre) v ->
      msg_dep_is_globally_equivocating ELMOComponent Message_dependencies Message_sender
        (destination item) v.
Proof.
  eapply state_to_minimal_equivocation_trace_equivocation_monotonic.
  - by intro; apply MessageDependencies_ELMOComponent.
  - by typeclasses eauto.
  - by apply ELMO_channel_authentication_prop.
Qed.

(**
  The shallow and deeper version of [global_equivocators] agree on
  states which are reachable in [ELMOProtocol].
*)

Lemma ELMO_global_equivocators_iff_simple :
  forall (s : vstate ELMOProtocol) (a : Address),
    composite_ram_state_prop ELMOComponent s ->
      ELMO_global_equivocators s a <-> global_equivocators_simple s a.
Proof.
  intros s a Hs.
  assert (forall k, UMO_reachable full_node (s k)) as Hsi;
    [by intro; apply ELMO_full_node_reachable, preloaded_valid_state_projection |].
  clear Hs; split; intros Hequiv.
  - destruct Hequiv as (m & Hadr & (k & l & Hrobs) & Hnot_sent).
    enough (composite_has_been_received _ s m) by (econstructor; done).
    assert (m ∈ messages (s k)) as Hm.
    + by apply full_node_messages_iff_rec_obs; [| eexists].
    + by apply elem_of_messages in Hm as [|];
        [contradict Hnot_sent |]; exists k.
  - destruct Hequiv as [m Hadr [i_rec Hrecv] Hnot_sent].
    unfold ELMO_global_equivocators.
    exists m; split; [done |].
    split; [| done].
    exists i_rec.
    by apply full_node_messages_iff_rec_obs, received_in_messages.
Qed.

(**
   [global_equivocators_simple] is equivalent to an instance
   of the generic definition [full_node_is_globally_equivocating].
*)
Lemma global_equivocators_simple_iff_full_node_equivocation :
  forall (s : vstate ELMOProtocol) (a : Address),
    full_node_is_globally_equivocating ELMOComponent Message_sender s a
    <->
    global_equivocators_simple s a.
Proof.
  split.
  - by intros [? [?%Some_inj]]; econstructor.
  - by intros [? <- ]; econstructor.
Qed.

(**
  [ELMO_global_equivocators] can be related to
  [msg_dep_is_globally_equivocating],
  but the proof is more complicated because
  it also needs to translate between [rec_obs]
  and [CompositeHasBeenObserved]

  We use a [full_node] hypothesis so we can convert
  through claims about [m ∈ messages (s k)] rather
  than directly relating [rec_obs] and
  [CompositeHasBeenObserved].

  It might be possible to use something weaker than [UMO_reachable full_node]
  to prove
  [CompositeHasBeenObserved ELMOComponent (elements ∘ Message_dependencies) s m
  <-> exists (k : index) (l : label), rec_obs (s k) (MkObservation l m)]
  but [CompositeHasBeenObserved] can recurse into sent or received messages
  and [rec_obs] only into received messages so we need some deep structural
  assumption about what [Send] observations are allowed, even recursively
  within observations of observations.
*)
Lemma ELMO_CHBO_in_messages :
  forall s,
    (forall k, UMO_reachable full_node (s k)) ->
  forall m,
    CompositeHasBeenObserved ELMOComponent Message_dependencies s m
      <->
    exists (k : index), m ∈ messages (s k).
Proof.
  intros s Hs m; split.
  - intros [Hobs | m' Hobs Hdepth];
      destruct Hobs as [k Hobs]; exists k.
    + by apply elem_of_messages.
    + assert (m' ∈ messages (s k)) by (eapply elem_of_messages; done).
      enough (m <hb m') by (eapply messages_hb_transitive; done).
      revert Hdepth; apply (tc_congruence (fun m=>m)).
      unfold msg_dep_rel, compose, immediate_dependency.
      by intros x y Hdep; apply elem_of_list_to_set in Hdep.
  - by intros [k Hm%elem_of_messages]; constructor; exists k.
Qed.

Lemma ELMO_global_equivocators_iff_msg_dep_equivocation :
  forall (s : vstate ELMOProtocol) (a : Address),
    composite_ram_state_prop ELMOComponent s ->
  ELMO_global_equivocators s a
    <->
  msg_dep_is_globally_equivocating ELMOComponent
    Message_dependencies Message_sender s a.
Proof.
  intros s a Hs.
  apply Morphisms_Prop.ex_iff_morphism; intro m.
  assert (forall k : index, UMO_reachable full_node (s k))
    by (intro; eapply ELMO_full_node_reachable, valid_state_project_preloaded_to_preloaded; done).
  setoid_rewrite <- full_node_messages_iff_rec_obs; [| done].
  setoid_rewrite <- ELMO_CHBO_in_messages; [| done].
  (* firstorder works here but is slow *)
  by split; intros []; constructor; [cbv; f_equal | .. | apply Some_inj |]; itauto.
Qed.

Lemma ELMO_global_equivocators_iff_simple_by_generic :
  forall (s : vstate ELMOProtocol) (a : Address),
    composite_ram_state_prop ELMOComponent s ->
      ELMO_global_equivocators s a <-> global_equivocators_simple s a.
Proof.
  intros s a Hs.
  rewrite ELMO_global_equivocators_iff_msg_dep_equivocation by done.
  rewrite <- global_equivocators_simple_iff_full_node_equivocation by done.
  pose proof @ELMOComponent_message_dependencies_full_node_condition.
  by rewrite full_node_is_globally_equivocating_iff; [| typeclasses eauto | ..].
Qed.

(**
  If [s] is a reachable state in E where the state of component [i] has the form [si' <+> (l, m)],
  let [s'] be the composite state which has component [i] equal to [si'] and the other components
  the same as those of [s]. If all global equivocators of [s'] are also
  global equivocators in [s] then [s'] is also reachable in E and also
  it is a valid transition in E to go from [s] to [s'] with
  label [l] from the new observation and either sending or receiving [m]
  as [l] says.
*)

Lemma ELMO_state_to_minimal_equivocation_equivocating_validators
  (s : composite_state ELMOComponent)
  (Hs_pre :  composite_ram_state_prop ELMOComponent s)
  (is : composite_state ELMOComponent)
  (tr : list (composite_transition_item ELMOComponent))
  (Heqtr_min : ELMO_state_to_minimal_equivocation_trace s Hs_pre = (is, tr)) :
    Forall (fun item =>
      ELMO_equivocating_validators (destination item) ⊆ ELMO_equivocating_validators s) tr.
Proof.
  assert (Hall := ELMO_state_to_minimal_equivocation_trace_equivocation_monotonic _ _ _ _ Heqtr_min).
  apply ELMO_state_to_minimal_equivocation_trace_reachable in Heqtr_min as Htr_min; clear Heqtr_min.
  induction Htr_min using finite_valid_trace_init_to_rev_ind; [by constructor |].
  apply Forall_app; split; [| by apply Forall_singleton].
  apply input_valid_transition_origin in Ht as Hs.
  apply input_valid_transition_destination in Ht as Hsf.
  eapply Forall_impl.
  - by apply IHHtr_min; [| intros * ->; eapply Hall; simplify_list_eq].
  - intros x ->.
    apply filter_subprop.
    setoid_rewrite ELMO_global_equivocators_iff_msg_dep_equivocation; [| done..].
    apply valid_trace_get_last in Htr_min as <-.
    by apply (Hall tr [] _ eq_refl).
Qed.

Lemma ELMO_state_to_minimal_equivocation_trace_valid
  (s : composite_state ELMOComponent)
  (Hs : valid_state_prop ELMOProtocol s)
  (Hs_pre := VLSM_incl_valid_state (constraint_preloaded_free_incl _ ELMO_global_constraint) _ Hs
    : composite_ram_state_prop ELMOComponent s)
  (is : composite_state ELMOComponent)
  (tr : list (composite_transition_item ELMOComponent)) :
    ELMO_state_to_minimal_equivocation_trace s Hs_pre = (is, tr) ->
      finite_valid_trace_init_to ELMOProtocol is s tr.
Proof.
  intros Heqtr_min.
  assert (Hall_not_heavy : Forall (fun item => ELMO_not_heavy (destination item)) tr).
  {
    apply ELMO_state_to_minimal_equivocation_equivocating_validators in Heqtr_min.
    eapply Forall_impl; cbn; [done |].
    apply ELMO_valid_state_not_heavy in Hs as Hheavy.
    intros item Hitem; unfold ELMO_not_heavy, not_heavy.
    etransitivity; [| done].
    apply sum_weights_subseteq; [by apply NoDup_elements.. |].
    by intro a; apply Hitem.
  }
  apply ELMO_state_to_minimal_equivocation_trace_reachable in Heqtr_min as Htr_min; clear Heqtr_min.
  assert (Hall_input_valid :
    Forall (fun item => forall m, input item = Some m -> valid_message_prop ELMOProtocol m) tr).
  {
    apply Forall_forall; intros item Hitem m Hobs.
    eapply directly_observed_valid; [done |].
    unshelve eapply EquivocationProjections.VLSM_incl_has_been_directly_observed_reflect; cycle 3;
      [by apply preloaded_constraint_free_incl | .. | by typeclasses eauto | by typeclasses eauto].
    - by generalize Hs; apply VLSM_incl_valid_state, vlsm_incl_pre_loaded_with_all_messages_vlsm.
    - eapply has_been_directly_observed_examine_one_trace; [done |].
      by apply Exists_exists; eexists; cbn; eauto.
  }
  clear -Htr_min Hall_input_valid Hall_not_heavy.
  induction Htr_min using finite_valid_trace_init_to_rev_ind.
  - by split; [rapply @finite_valid_trace_from_to_empty; apply initial_state_is_valid |].
  - rewrite !Forall_app, !Forall_singleton in Hall_not_heavy, Hall_input_valid.
    destruct Hall_not_heavy as [Hall_not_heavy Hsf_not_heavy],
             Hall_input_valid as [Hall_input_valid Hmsg_valid].
    destruct (IHHtr_min Hall_not_heavy Hall_input_valid) as [IHHtr _];
      clear Hall_not_heavy Hall_input_valid.
    split; [| by apply Htr_min]; clear Htr_min.
    apply (extend_right_finite_trace_from_to _ IHHtr).
    destruct Ht as [(Hs_pre & _ & [Hv _]) Ht].
    repeat split; [| | done | | done ].
    + by apply valid_trace_last_pstate in IHHtr.
    + by destruct iom; [apply Hmsg_valid | apply option_valid_message_None].
    + destruct l as [i []]; [| done].
      by hnf; replace (composite_transition _ _ _) with (sf, oom).
Qed.

(** *** Validators

  Due to the validity predicate, a transition must have either a non-empty
  input or a non-empty output, the distinction being made by the label.
*)
Inductive ELMOProtocolValidTransition
  : index -> Label -> vstate ELMOProtocol -> vstate ELMOProtocol -> Message -> Prop :=
| ep_valid_receive : forall (i : index) (s1 s2 : vstate ELMOProtocol) (m : Message),
    ValidTransition ELMOProtocol (existT i Receive) s1 (Some m) s2 None ->
    ELMOProtocolValidTransition i Receive s1 s2 m
| ep_valid_send : forall (i : index) (s1 s2 : vstate ELMOProtocol) (m : Message),
    ValidTransition ELMOProtocol (existT i Send) s1 None s2 (Some m) ->
    ELMOProtocolValidTransition i Send s1 s2 m.

Lemma local_equivocators_full_step_update
  (i : index) (l : Label) (s1 s2 : State) (m : Message) :
    ELMOComponentRAMTransition i l s1 s2 m ->
    forall a : Address,
      local_equivocators_full s2 a
        <->
      local_equivocators_full s1 a \/
      a = adr (state m) /\ l = Receive /\
        exists m', m' ∈ receivedMessages s1 /\ incomparable m m'.
Proof.
  by inversion 1 as [? ? ? [_ Ht] | ? ? ? [_ Ht]]; inversion Ht;
    setoid_rewrite lefo_alt; itauto.
Qed.

Lemma global_equivocators_simple_step_update_send
  (i : index) (sigma : composite_state ELMOComponent) (s' : State) (m : Message) :
  ELMOComponentRAMTransition i Send (sigma i) s' m ->
  forall a : Address,
    global_equivocators_simple (state_update ELMOComponent sigma i s') a
      ->
    global_equivocators_simple sigma a.
Proof.
  inversion 1 as [| ? ? ? [(Hsi & _ & Hvi) Hti]]; inversion Hvi; inversion Hti; subst.
  intros a [ges_m ges_adr [j Hrcv] ges_not_sent].
  destruct (decide (j = i)); subst; state_update_simpl.
  - cbn in Hrcv; rewrite decide_False in Hrcv by auto.
    econstructor; [done | by exists i |].
    intros [j Hsnd]; apply ges_not_sent; exists j.
    destruct (decide (j = i)); subst; state_update_simpl; cbn; [| done].
    by rewrite decide_True by done; right.
  - econstructor; [done | by exists j |].
    intros[k Hsnd]; apply ges_not_sent.
    destruct (decide (k = i)); subst; [| by exists k; state_update_simpl].
    exists i; state_update_simpl; unfold has_been_sent; cbn.
    by rewrite decide_True by done; right.
Qed.

Lemma global_equivocators_simple_step_update_send_iff
  (i : index) (sigma : composite_state ELMOComponent) (s' : State) (m : Message) :
  ELMOComponentRAMTransition i Send (sigma i) s' m ->
  ~ global_equivocators_simple sigma (idx i) ->
  forall a : Address,
    global_equivocators_simple (state_update ELMOComponent sigma i s') a
      <->
    global_equivocators_simple sigma a.
Proof.
  intros Ht Hneqvi; split; [by eapply global_equivocators_simple_step_update_send |].
  inversion Ht as [| ? ? ? [(Hsi & _ & Hvi) Hti]]; inversion Hvi; inversion Hti; subst.
  destruct (decide (a = idx i)); subst; [done |].
  intros [ges_m ges_adr ges_recv ges_not_sent].
  econstructor; [done | ..].
  - destruct ges_recv as [j Hrcv]; exists j.
    destruct (decide (j = i)); subst; state_update_simpl; [| done].
    by cbn; rewrite decide_False by auto.
  - intros [j Hsnd]; apply ges_not_sent; exists j.
    destruct (decide (j = i)); subst; state_update_simpl; [| done].
    cbn in Hsnd; rewrite decide_True, map_cons in Hsnd by done.
    inversion Hsnd; subst; [| done].
    by contradict n; apply ELMO_reachable_adr.
Qed.

Lemma global_equivocators_simple_step_update_receive
  (i : index) (sigma : composite_state ELMOComponent) (s' : State) (m : Message) :
    ELMOComponentRAMTransition i Receive (sigma i) s' m ->
      forall a : Address,
        global_equivocators_simple (state_update ELMOComponent sigma i s') a
          <->
        global_equivocators_simple sigma a
          \/
        a = adr (state m) /\ ~ composite_has_been_sent ELMOComponent sigma m.
Proof.
  intros Ht a; inversion Ht as [? ? ? [(_ & _ & Hvi) Hti] |];
    inversion Hvi; inversion Hti; subst; clear Ht Hvi Hti; split.
  - intros [ges_m ges_adr [j Hrcv] ges_not_sent].
    destruct (decide (j = i)); subst; state_update_simpl; cycle 1.
    + left; econstructor; [done | by exists j |].
      intros [k Hsnd]; apply ges_not_sent.
      destruct (decide (k = i)); subst; [| by exists k; state_update_simpl].
      exists i; state_update_simpl; unfold has_been_sent; cbn.
      by rewrite decide_False by auto.
    + cbn in Hrcv; rewrite decide_True, map_cons in Hrcv by done.
      apply elem_of_cons in Hrcv as [-> | Hrcv].
      * right; split; [done |].
        intros [j Hsnd]; apply ges_not_sent; exists j.
        destruct (decide (j = i)); subst; state_update_simpl; [| done].
        by cbn; rewrite decide_False by auto.
      * left; econstructor; [done | by exists i |].
        intros [j Hsnd]; apply ges_not_sent; exists j.
        destruct (decide (j = i)); subst; state_update_simpl; [| done].
        by cbn; rewrite decide_False by auto.
  - intros [[ges_m ges_adr ges_recv ges_not_sent] | [-> Hnsnd]].
    + econstructor; [done | ..].
      * destruct ges_recv as [j Hrcv]; exists j.
        destruct (decide (j = i)); subst; state_update_simpl; [| done].
        by cbn; rewrite decide_True, map_cons by done; right.
      * intros [j Hsnd]; apply ges_not_sent; exists j.
        by destruct (decide (j = i)); subst; state_update_simpl.
    + econstructor; [done | ..].
      * by exists i; state_update_simpl; left.
      * intros [j Hsnd]; apply Hnsnd; exists j.
        destruct (decide (j = i)); subst; state_update_simpl; [| done].
        by cbn in Hsnd; rewrite decide_False in Hsnd by auto.
Qed.

Lemma global_equivocators_simple_step_update_receive_already_observed
  (i : index) (sigma : composite_state ELMOComponent) (s' : State) (m : Message) :
    composite_ram_state_prop ELMOComponent sigma ->
    ELMOComponentRAMTransition i Receive (sigma i) s' m ->
    composite_has_been_directly_observed ELMOComponent sigma m ->
      forall a : Address,
        global_equivocators_simple (state_update ELMOComponent sigma i s') a
          <->
        global_equivocators_simple sigma a.
Proof.
  intros Hsigma Ht Hobs a.
  rewrite global_equivocators_simple_step_update_receive by done.
  split; [| by left]; intros [| [-> Hnsend]]; [done |].
  apply ELMO_global_equivocators_iff_simple; [done |].
  exists m; repeat split; [| done].
  destruct Hobs as [k Hobs]; exists k.
  apply full_node_messages_iff_rec_obs; [| by apply elem_of_messages].
  by eapply ELMO_full_node_reachable, valid_state_project_preloaded_to_preloaded.
Qed.

Lemma ELMO_equivocating_validators_step_update_Send
  (i : index) (sigma : composite_state ELMOComponent) (s' : State) (m : Message) :
  composite_ram_state_prop ELMOComponent sigma ->
  ELMOComponentRAMTransition i Send (sigma i) s' m ->
    ELMO_equivocating_validators (state_update ELMOComponent sigma i s')
      ⊆
    ELMO_equivocating_validators sigma.
Proof.
  intros Hsigma Ht.
  assert (Hte : input_valid_transition ReachELMO
    (existT i Send) (sigma, None) (state_update ELMOComponent sigma i s', Some m)).
  {
    inversion Ht as [| ? ? ? [(_ & _ & Hvi) Hti]]; inversion Hvi; inversion Hti.
    by repeat split; [| apply option_valid_message_None | constructor].
  }
  apply input_valid_transition_destination in Hte.
  intro a; setoid_rewrite elem_of_filter; unfold is_equivocating; cbn.
  rewrite !ELMO_global_equivocators_iff_simple by done.
  intros [Heqv]; split; [| done].
  by eapply global_equivocators_simple_step_update_send.
Qed.

Lemma ELMO_equivocating_validators_step_update_Receive
  (i : index) (sigma : composite_state ELMOComponent) (s' : State) (m : Message) :
  composite_ram_state_prop ELMOComponent sigma ->
  ELMOComponentRAMTransition i Receive (sigma i) s' m ->
    ELMO_equivocating_validators (state_update ELMOComponent sigma i s')
      ⊆
    ELMO_equivocating_validators sigma ∪ {[adr (state m)]}.
Proof.
  intros Hsigma Ht.
  assert (Hte : input_valid_transition ReachELMO
    (existT i Receive) (sigma, Some m) (state_update ELMOComponent sigma i s', None)).
  {
    inversion Ht as [? ? ? [(_ & _ & Hvi) Hti] |]; inversion Hvi; inversion Hti.
    by repeat split; [| apply any_message_is_valid_in_preloaded | constructor].
  }
  apply input_valid_transition_destination in Hte.
  intro a; rewrite elem_of_union, elem_of_singleton.
  setoid_rewrite elem_of_filter; unfold is_equivocating; cbn.
  rewrite !ELMO_global_equivocators_iff_simple by done.
  intros [Heqv Hin].
  by eapply global_equivocators_simple_step_update_receive in Heqv as [Heqv | []];
    [left; split | right |].
Qed.

Lemma ELMO_equivocating_validators_step_update_Receive_already_Observed
  (i : index) (sigma : composite_state ELMOComponent) (s' : State) (m : Message) :
  composite_ram_state_prop ELMOComponent sigma ->
  composite_has_been_directly_observed ELMOComponent sigma m ->
  ELMOComponentRAMTransition i Receive (sigma i) s' m ->
    ELMO_equivocating_validators (state_update ELMOComponent sigma i s')
      ⊆
    ELMO_equivocating_validators sigma.
Proof.
  intros Hsigma Hsent Ht.
  assert (Hte : input_valid_transition ReachELMO
    (existT i Receive) (sigma, Some m) (state_update ELMOComponent sigma i s', None)).
  {
    inversion Ht as [? ? ? [(_ & _ & Hvi) Hti] |]; inversion Hvi; inversion Hti.
    by repeat split; [| apply any_message_is_valid_in_preloaded | constructor].
  }
  apply input_valid_transition_destination in Hte.
  intro a; setoid_rewrite elem_of_filter; unfold is_equivocating; cbn.
  rewrite !ELMO_global_equivocators_iff_simple by done.
  intros [Heqv]; split; [| done].
  by eapply global_equivocators_simple_step_update_receive_already_observed.
Qed.

(**
  The following lemmas build towards proving that ELMO components are validating
  for the ELMO protocol.

  If the state <<s>> is valid in the ELMO protocol, and <<s>> can take a valid transition
  involving a message <<m>>, then <<m>> is a valid message in the ELMO protocol.
*)

Lemma ELMO_update_state_with_initial
  (s : composite_state ELMOComponent)
  (Hs : valid_state_prop ELMOProtocol s)
  (i : index)
  (Heqv : (sum_weights (ELMO_equivocating_validators s ∪ {[idx i]}) <= threshold)%R)
  (si : State)
  (Hsi : vinitial_state_prop (ELMOComponent i) si) :
    valid_state_prop ELMOProtocol (state_update ELMOComponent s i si) /\
    ELMO_equivocating_validators (state_update ELMOComponent s i si)
      ⊆
    ELMO_equivocating_validators s ∪ {[idx i]}.
Proof.
  assert (Hincl : VLSM_incl ELMOProtocol ReachELMO) by apply constraint_preloaded_free_incl.
  assert (Htr_min := ELMO_state_to_minimal_equivocation_trace_valid _ Hs).
  cbn in Htr_min; destruct (ELMO_state_to_minimal_equivocation_trace _ _)
    as [is_min tr_min] eqn: Heqtr_min; specialize (Htr_min _ _ eq_refl).
  apply ELMO_state_to_minimal_equivocation_equivocating_validators in Heqtr_min
    as Hall; clear Hs Heqtr_min.
  set (s_eqvs := ELMO_equivocating_validators s) in *; clearbody s_eqvs.
  induction Htr_min using finite_valid_trace_init_to_rev_ind.
  {
    rewrite !state_update_id by (destruct (Hsi0 i), Hsi; apply eq_State; congruence).
    split; [by apply initial_state_is_valid |].
    rewrite ELMO_initial_state_equivocating_validators by done.
    by apply empty_subseteq.
  }
  rewrite Forall_app, Forall_singleton in Hall.
  destruct Hall as [Hall Hsf_eqvs].
  destruct (IHHtr_min Hall) as [Hsisi Heqvs].
  apply input_valid_transition_origin in Ht as Hs.
  apply input_valid_transition_destination in Ht as Hsf.
  apply (VLSM_incl_valid_state Hincl) in Hs, Hsf.
  destruct l as [j lj].
  destruct (decide (j = i)); subst; [by destruct Ht as [(_ & _ & [Hv _]) Ht];
    inversion Hv; subst; inversion Ht; subst; rewrite state_update_twice |].
  apply (VLSM_incl_input_valid_transition Hincl) in Ht as Ht_pre.
  destruct Ht as [(_ & Hm & Hv & Hc) Ht].
  assert (Ht' :
    composite_transition ELMOComponent (existT j lj) (state_update ELMOComponent s i si, iom)
    = (state_update ELMOComponent sf i si, oom)).
  {
    cbn in *; state_update_simpl; destruct UMOComponent_transition; inversion Ht; subst.
    by rewrite state_update_twice_neq.
  }
  cut (ELMO_equivocating_validators (state_update ELMOComponent sf i si) ⊆
        ELMO_equivocating_validators sf ∪ {[idx i]}).
  {
    intro Hsfisi_eqvs'.
    assert (Hsfisi_eqvs :
      ELMO_equivocating_validators (state_update ELMOComponent sf i si) ⊆ s_eqvs ∪ {[idx i]}).
    {
      etransitivity; [done |].
      by apply union_subseteq; split; [apply union_subseteq_l' | apply union_subseteq_r'].
    }
    split; [| done].
    cut (input_valid_transition ELMOProtocol (existT j lj)
      (state_update ELMOComponent s i si, iom) (state_update ELMOComponent sf i si, oom));
      [by intro; eapply input_valid_transition_destination |].
    repeat split; [done | done | by cbn; state_update_simpl | | done].
    destruct lj; [| done].
    unfold ELMO_global_constraint.
    replace (composite_transition _ _ _) with (state_update ELMOComponent sf i si, oom).
    unfold ELMO_not_heavy, not_heavy; etransitivity; [| done].
    apply sum_weights_subseteq; [by apply NoDup_elements.. |].
    by intro; apply Hsfisi_eqvs.
  }
  apply (VLSM_incl_finite_valid_trace_init_to Hincl) in Htr_min as Htr_min_pre.
  apply (VLSM_incl_valid_state Hincl) in Hsisi as Hsisi_pre.
  assert (finite_valid_trace_init_to ReachELMO si0 sf
    (tr ++ [@Build_transition_item _ (composite_type ELMOComponent) (existT j lj) iom sf oom])).
  {
    split; [| by apply Htr_min].
    apply valid_trace_add_last; [| by apply finite_trace_last_is_last].
    eapply (extend_right_finite_trace_from ReachELMO);
      [by eapply valid_trace_forget_last, Htr_min_pre |].
    replace (finite_trace_last _ _) with s; [done |].
    by apply valid_trace_get_last in Htr_min.
  }
  assert (Hpre_tisi : input_valid_transition ReachELMO (existT j lj)
    (state_update ELMOComponent s i si, iom) (state_update ELMOComponent sf i si, oom)).
  {
    repeat split; [done | .. | done].
    - by apply any_message_is_valid_in_preloaded.
    - by cbn; state_update_simpl.
  }
  apply input_valid_transition_destination in Hpre_tisi as Hpre_sfisi.
  unfold ELMO_equivocating_validators, equivocating_validators.
  intro a; rewrite elem_of_union, elem_of_singleton, !elem_of_filter.
  unfold is_equivocating; cbn; rewrite !ELMO_global_equivocators_iff_simple by done.
  intros [[ges_m ges_adr [k Hrcv] ges_not_sent] Ha].
  assert (k <> i); [intros -> |]; state_update_simpl.
  {
    by cbn in Hrcv; replace si with (MkState [] (idx i)) in Hrcv;
      [inversion Hrcv | apply eq_State; symmetry; apply Hsi].
  }
  cut (~ composite_has_been_sent ELMOComponent sf ges_m \/ a = idx i).
  {
    intros []; [| by right].
    left; split; [| done].
    by econstructor; [| eexists |].
  }
  apply elem_of_list_to_set, elem_of_list_fmap in Ha as (i_a & -> & _).
  destruct (decide (i_a = i)); [by subst; right | left].
  contradict ges_not_sent.
  eapply has_been_sent_iff_by_sender in ges_not_sent; cycle 1.
  - by apply channel_authentication_sender_safety, ELMO_channel_authentication_prop.
  - done.
  - done.
  - rewrite ges_adr, ELMO_A_inv in ges_not_sent by done.
    by exists i_a; state_update_simpl.
Qed.

Lemma ELMO_valid_states_only_receive_valid_messages :
  forall s : vstate ELMOProtocol,
    valid_state_prop ELMOProtocol s ->
  forall (i : index) (l : Label) (s' : vstate ELMOProtocol) (m : Message),
    ELMOProtocolValidTransition i l s s' m ->
    valid_message_prop ELMOProtocol m.
Proof.
  intros s Hs i l s' m Hvalid.
  inversion Hvalid as [? ? ? ? Hreceive | ? ? ? ? Hsend]; subst; cycle 1.
  {
    apply emitted_messages_are_valid.
    exists (s, None), (existT i Send), s'.
    by repeat split; [| apply option_valid_message_None | apply Hsend..].
  }
  assert (Hincl : VLSM_incl ELMOProtocol ReachELMO) by apply constraint_preloaded_free_incl.
  destruct (decide (composite_has_been_sent ELMOComponent s m)) as [| Hnsnd];
    [by eapply composite_sent_valid |].
  destruct Hreceive as [[Hv Hc] Ht]; inversion Hv as [? ? Hrcv |]; subst; inversion Ht.
  assert (Hm_eqv : global_equivocators_simple s' (adr (state m))).
  {
    subst; constructor 1 with m; [done | |].
    - by exists i; cbn; state_update_simpl; left.
    - intros [i_m Hsnd]; apply Hnsnd; exists i_m.
      by destruct (decide (i_m = i)); subst; state_update_simpl.
  }
  assert (Hs'_eqv : forall a,
    global_equivocators_simple s' a
      <->
    a = adr (state m) \/ global_equivocators_simple s a).
  {
    intro a; subst.
    erewrite global_equivocators_simple_step_update_receive with (m := m); [by itauto |].
    constructor; repeat split; [| | done].
    - by eapply valid_state_project_preloaded.
    - by apply any_message_is_valid_in_preloaded.
  }
  apply (VLSM_incl_valid_state Hincl) in Hs as Hs_pre.
  assert (Hs' : composite_ram_state_prop ELMOComponent s').
  {
    apply valid_state_prop_iff; right.
    by exists (existT i Receive), (s, Some m), None; repeat split;
      [| apply any_message_is_valid_in_preloaded | ..].
  }
  pose (H_rcv := Hrcv); destruct H_rcv.
  apply ELMO_msg_valid_full_has_sender in ELMO_mv_msg_valid_full0 as Hsender.
  destruct Hsender as [i_m Hsender].
  assert (Heqv :
    (sum_weights (ELMO_equivocating_validators s ∪ {[idx i_m]}) <= threshold)%R).
  {
    etransitivity; [| apply Hc].
    apply sum_weights_subseteq; [by apply NoDup_elements.. |].
    intro a; rewrite elem_of_union, elem_of_singleton.
    unfold ELMO_equivocating_validators, equivocating_validators.
    rewrite !elem_of_filter.
    destruct (decide (a = adr (state m))).
    - subst; split; cbn.
      + by apply ELMO_global_equivocators_iff_simple.
      + by apply elem_of_list_to_set, elem_of_list_fmap; eexists; split; [| apply elem_of_enum].
    - intros [[] |]; [| by congruence]; split; [| done].
      subst; apply ELMO_global_equivocators_iff_simple, Hs'_eqv; [done |].
      by right; apply ELMO_global_equivocators_iff_simple.
  }
  assert (His : vinitial_state_prop (ELMOComponent i_m) (MkState [] (idx i_m))) by done.
  destruct (ELMO_update_state_with_initial _ Hs _ Heqv _ His) as [Hsimis Hsimis_eqvs].
  eapply valid_state_project_preloaded with (i := i) in Hs as Hsi_pre.
  replace m with (MkMessage (state m)) in Hrcv by (destruct m; done).
  pose proof (Hm := receivable_messages_reachable _ _ _ _ Hsender Hsi_pre Hrcv).
  apply valid_state_has_trace in Hm as (is_m & tr_m & Htr_m).
  assert (Hall_messages_observed :
    Forall (fun item => forall m, item_sends_or_receives m item -> m ∈ messages (s i)) tr_m).
  {
    apply Forall_forall; intros item Hitem dm Hobs.
    eapply elem_of_submseteq; [| done].
    apply elem_of_messages.
    change (has_been_directly_observed (ELMOComponent i_m) (state m) dm).
    eapply has_been_directly_observed_examine_one_trace; [done |].
    by apply Exists_exists; eexists.
  }
  assert (Hall_messages_valid :
    Forall (fun item => forall m, item_sends_or_receives m item ->
      valid_message_prop ELMOProtocol m) tr_m).
  {
    eapply Forall_impl; cbn; [by apply Hall_messages_observed |].
    intros item Hobs dm Hdm.
    eapply directly_observed_valid; [by apply Hs |].
    by apply Hobs, elem_of_messages in Hdm as []; [left | right]; eexists i.
  }
  assert (Heqis_m : is_m = MkState [] (idx i_m))
    by (destruct is_m, Htr_m as [_ []]; cbn in *; subst; done).
  assert (Hall_bounded_eqv :
    Forall (fun item =>
      ELMO_equivocating_validators (lift_to_composite_state ELMOComponent s i_m (destination item))
        ⊆
      ELMO_equivocating_validators s ∪ {[idx i_m]}
      ) tr_m).
  {
    assert (Hall_reachable :
      Forall (fun item =>
        composite_ram_state_prop ELMOComponent
          ((state_update ELMOComponent s i_m item))) (is_m :: map destination tr_m)).
    {
      apply (VLSM_incl_valid_state Hincl) in Hsimis as Hsimis_pre.
      destruct Htr_m as [Htr_m _].
      apply (VLSM_weak_embedding_finite_valid_trace_from_to
        (lift_to_preloaded_free_weak_embedding ELMOComponent i_m _ Hs_pre)) in Htr_m.
      state_update_simpl.
      apply Forall_forall; intros d Hd.
      apply elem_of_cons in Hd as [-> | Hd]; [by subst |].
      apply elem_of_list_fmap in Hd as (item & -> & Hitem).
      apply elem_of_list_split in Hitem as (pre & suf & ->).
      setoid_rewrite map_app in Htr_m; cbn in Htr_m.
      by eapply elem_of_trace_in_futures_left, in_futures_valid_fst in Htr_m;
        [| by apply elem_of_app; right; left].
    }
    rewrite <- Heqis_m in Hsimis_eqvs, Hsimis.
    remember (state m) as state_m; rewrite <- Hsender in Hsimis_eqvs |- *;
      rewrite Heqstate_m in Hsender, Hsimis_eqvs |- *.
    clear -Htr_m Hsimis_eqvs Hall_reachable Hall_messages_observed Hs Hs_pre Hsender.
    induction Htr_m using finite_valid_trace_init_to_rev_ind; [by constructor |].
    rewrite map_app in Hall_reachable; cbn in Hall_reachable.
    rewrite app_comm_cons in Hall_reachable.
    apply Forall_app in Hall_reachable as [Hall_reachable Hsf_reachable].
    rewrite Forall_singleton in Hsf_reachable.
    apply Forall_app in Hall_messages_observed as [Hall_messages_observed Hlast_obs].
    rewrite Forall_singleton in Hlast_obs.
    specialize (IHHtr_m Hsimis_eqvs Hall_messages_observed Hall_reachable).
    assert (Hsis0_pre : composite_ram_state_prop ELMOComponent (state_update ELMOComponent s i_m s0)).
    {
      apply valid_trace_get_last in Htr_m as <-.
      rewrite Forall_forall in Hall_reachable.
      apply Hall_reachable; apply last_Some_elem_of.
      by rewrite <- StdppExtras.last_last_error, unlock_finite_trace_last.
    }
    clear Hall_reachable Hall_messages_observed.
    apply Forall_app; split; [done |].
    constructor; [| by constructor].
    assert (Hsis0_eqvs :
      ELMO_equivocating_validators (state_update ELMOComponent s i_m s0)
        ⊆ ELMO_equivocating_validators s ∪ {[adr (state m)]}).
    {
      apply valid_trace_get_last in Htr_m as <-.
      destruct_list_last tr tr' lst Heq; [done |].
      rewrite finite_trace_last_is_last.
      rewrite Forall_forall in IHHtr_m; eapply IHHtr_m.
      by apply elem_of_app; right; left.
    }
    cbn; replace (lift_to_composite_state _ _ _ _)
      with (state_update ELMOComponent (state_update ELMOComponent s i_m s0) i_m sf)
      by (apply state_update_twice; done).
    destruct (Ht) as [(_ & _ & H_v) H_t];
      inversion H_v as [? ? [] |]; subst; inversion H_t; subst; cycle 1.
    - transitivity (ELMO_equivocating_validators (state_update ELMOComponent s i_m s0)
        ∪ {[adr (state m)]}).
      + by eapply union_subseteq_l', ELMO_equivocating_validators_step_update_Send;
          [| by constructor; state_update_simpl].
      + by apply union_subseteq; split; [| apply union_subseteq_r'].
    - destruct (decide (adr (state m) = adr (state m0))) as [Hmm0 | Hnmm0].
      {
        transitivity (ELMO_equivocating_validators (state_update ELMOComponent s i_m s0)
          ∪ {[adr (state m)]}).
        - rewrite Hmm0.
          by eapply ELMO_equivocating_validators_step_update_Receive;
            [| constructor; state_update_simpl].
        - by apply union_subseteq; split; [| apply union_subseteq_r'].
      }
      assert (Hm0_obs : m0 ∈ messages (s i)) by (apply Hlast_obs; left; done).
      destruct (decide (i_m = i)); cycle 1.
      + transitivity (ELMO_equivocating_validators (state_update ELMOComponent s i_m s0)
          ∪ {[adr (state m)]});
          [| by apply union_subseteq; split; [| by apply union_subseteq_r']].
        eapply union_subseteq_l', ELMO_equivocating_validators_step_update_Receive_already_Observed;
          [done | | by constructor; state_update_simpl].
        exists i; state_update_simpl.
        by apply elem_of_messages in Hm0_obs.
      + subst; intro a; setoid_rewrite elem_of_filter.
        unfold is_equivocating; cbn.
        rewrite ELMO_global_equivocators_iff_simple by (rewrite state_update_twice; done).
        intros [Heqv].
        eapply global_equivocators_simple_step_update_receive in Heqv;
          [| by constructor; state_update_simpl].
        assert (Hm0_not_sent : m0 ∉ sentMessages (s i)).
        {
          intro Hm0; eapply adr_of_sentMessages in Hm0;
            [| by eapply ELMO_full_node_reachable, valid_state_project_preloaded].
          rewrite Hsender in *.
          rewrite Hm0 in Hnmm0; contradict Hnmm0; symmetry.
          by apply ELMO_reachable_adr, valid_state_project_preloaded.
        }
        destruct Heqv as [Heqv | [-> Hnsent]]; cycle 1.
        * unfold ELMO_equivocating_validators, equivocating_validators, is_equivocating; cbn.
          rewrite elem_of_union, elem_of_singleton, elem_of_filter,
            ELMO_global_equivocators_iff_simple by done.
          left; split; [| done].
          econstructor; [done | exists i; by apply elem_of_messages in Hm0_obs as [] |].
          intros [i_m0 Hsent].
          assert (i <> i_m0) by (intros ->; contradict Hm0_not_sent; done).
          by apply Hnsent; exists i_m0; state_update_simpl.
        * apply Hsis0_eqvs.
          unfold ELMO_equivocating_validators, equivocating_validators, is_equivocating; cbn.
          by rewrite elem_of_filter, ELMO_global_equivocators_iff_simple.
  }
  assert (Htr_m_lift :
    finite_valid_trace_from_to ELMOProtocol
      (lift_to_composite_state ELMOComponent s i_m is_m)
      (lift_to_composite_state ELMOComponent s i_m (state m))
      (pre_VLSM_embedding_finite_trace_project
      _ _ (lift_to_composite_label ELMOComponent i_m) (lift_to_composite_state ELMOComponent s i_m)
      tr_m)).
  {
    remember (state m) as sm.
    clear Heqsm Hrcv Hm_eqv Hs'_eqv Hsender Heqis_m Hall_messages_observed.
    induction Htr_m using  finite_valid_trace_init_to_rev_ind;
      [by constructor; destruct si, Hsi; cbn in *; subst |].
    apply Forall_app in Hall_messages_valid as [Hall_messages_valid H_lst_msg_valid].
    apply Forall_app in Hall_bounded_eqv as [Hall_bounded_eqv Hsf_bounded_eqv].
    rewrite Forall_singleton in H_lst_msg_valid.
    rewrite Forall_singleton in Hsf_bounded_eqv.
    setoid_rewrite map_app; cbn.
    eapply extend_right_finite_trace_from_to; [by apply IHHtr_m | cbn].
    destruct Ht0 as [(Hs0 &  _ & Hv0) Ht0].
    repeat split.
    - by eapply finite_valid_trace_from_to_last_pstate, IHHtr_m.
    - destruct iom; [| apply option_valid_message_None].
      by apply H_lst_msg_valid; left.
    - by cbn; state_update_simpl.
    - destruct l as []; [| done].
      unfold ELMO_global_constraint, lift_to_composite_label, composite_transition.
      rewrite state_update_eq.
      cbn in Ht0 |- *; rewrite Ht0, state_update_twice.
      unfold ELMO_not_heavy, not_heavy.
      etransitivity; [| done].
      apply sum_weights_subseteq; [by apply NoDup_elements.. |].
      by intro; apply Hsf_bounded_eqv.
    - cbn; state_update_simpl.
      replace (UMOComponent_transition _ _ _) with (sf, oom).
      by rewrite state_update_twice.
  }
  cut
    (input_valid_transition ELMOProtocol (existT i_m Send)
      (lift_to_composite_state ELMOComponent s i_m (state m), None)
      (lift_to_composite_state ELMOComponent s i_m (state m <+> MkObservation Send m), Some m)
    ); [by apply input_valid_transition_out |].
  repeat split.
  - by apply finite_valid_trace_from_to_last_pstate in Htr_m_lift.
  - by apply option_valid_message_None.
  - by constructor.
  - by cbn; state_update_simpl; rewrite state_update_twice; destruct m.
Qed.

(**
  Let si be a reachable state in (ELMOComponent i) and
  m a message such that
  ELMOComponentValid Receive si (Some m) in (ELMOComponent i),
  adr m <> i and adr m ∉ local_equivocators_full si, and
  also there is no message m' ∈ received_messages(si) with m' ⊥ m.

  Suppose σ is a valid state in ELMOProtocol such that σ i = si,
  having messages(si) = messages(σ),
  local_equivocators_full(si) = global_equivocators(σ),
  and components of σ other than i may only have a
  Send observation as their latest observation,
  and also m ∉ sent_messages(σ).

  Then there exists a state σ' in the future of σ such that
  σ' i = si, messages(σ') = messages(si), and
  global_equivocators(σ') = global_equivocators(σ),
  components of σ' other than i and adr(m) may only
  have a Send observation as their latest observation.
  Finally, σ'(adr(m)) = m
  (So m can be emitted immediately from σ').

  This is stronger than the previous message by showing,
  at least in these conditions, that a message that
  can be validly received by a component in a valid
  ELMOProtocol state can be validly emitted not just
  in some unrelated ELMOProtocol trace, but also
  in a trace continuing from the current state.
  (We will build from this towards proving ELMOComponents
  are validating for ELMOProtocol by showing how to
  construct such an ELMOProtocol state embedding
  given an ELMOComponent state and receivable message)
*)

Definition latest_observation_Send (s : State) : Prop :=
  obs s = []
    \/
  exists (s' : State) (m : Message),
    s = s' <+> MkObservation Send m.

Definition component_reflects_composite_messages (s : vstate ELMOProtocol) (i : index) : Prop :=
  forall m : Message, (exists j, m ∈ messages (s j)) <-> m ∈ messages (s i).

Definition component_reflects_composite_equivocators (s : vstate ELMOProtocol) (i : index) : Prop :=
  forall a : Address, global_equivocators_simple s a <-> local_equivocators_full (s i) a.

Record component_reflects_composite (s : vstate ELMOProtocol) (i : index) : Prop :=
{
  component_sees_messages : component_reflects_composite_messages s i;
  component_sees_equivocators : component_reflects_composite_equivocators s i;
}.

Definition other_components_after_send
  (P_allowed : index -> Prop) (s : vstate ELMOProtocol) : Prop :=
    forall i : index, ~ P_allowed i -> latest_observation_Send (s i).

Lemma non_equivocating_received_message_continues_trace
  (i : index) (si si' : vstate (ELMOComponent i))
  (m : Message)
  (Ht : input_valid_transition (pre_loaded_with_all_messages_vlsm (ELMOComponent i))
    Receive (si, Some m) (si', None))
  (Hnot_local_equivocator' : ~ local_equivocators_full si' (adr (state m)))
  (i_m : index)
  (Hi_m : adr (state m) = idx i_m)
  (Hadr_neq : adr (state m) <> idx i)
  (sigma : composite_state ELMOComponent)
  (Hcomponent : sigma i = si)
  (Hsigma : valid_state_prop ELMOProtocol sigma)
  (Hm_not_sent_yet : ~ composite_has_been_sent ELMOComponent sigma m)
  (Hspecial : component_reflects_composite sigma i)
  (H_not_i_paused : other_components_after_send (fun j : index => j = i) sigma)
  : exists tr_m,
      finite_valid_trace_from_to (pre_loaded_with_all_messages_vlsm (ELMOComponent i_m))
        (sigma i_m) (state m) tr_m.
Proof.
  assert (Hsigma_no_junk :
    forall j, j <> i ->
    forall mj, mj ∈ sentMessages (sigma j) ->
    mj ∈ receivedMessages si).
  {
    intros j Hni mj Hmj.
    eapply reachable_sent_messages_adr in Hmj as Hmj_adr;
      [subst | by eapply valid_state_project_preloaded].
    cut (mj ∈ messages (sigma i)).
    {
      rewrite elem_of_messages; intros [Hmji |]; [| done].
      eapply reachable_sent_messages_adr in Hmji; [| by eapply valid_state_project_preloaded].
      by contradict Hni; eapply inj with idx; [done | congruence].
    }
    by apply Hspecial; exists j; apply elem_of_messages; left.
  }
  assert (i <> i_m) by (contradict Hadr_neq; congruence).
  apply valid_state_project_preloaded with (i := i_m) in Hsigma as Hsi_m.
  assert (adr (sigma i_m) = idx i_m) by (apply ELMO_reachable_adr; done).
  destruct (ELMO_unique_trace_segments i_m (sigma i_m) (state m)) as [tr []]; [.. | by eexists].
  - destruct Ht as [(Hsi & _ & Hv) _]; inversion Hv; subst.
    by clear Hsi_m; destruct m; eapply receivable_messages_reachable.
  - destruct (H_not_i_paused i_m) as [Hinit | (sim & lst_im & Hsnd)]; [done | ..].
    + replace (sigma i_m) with (MkState [] (adr (state m)));
        [by specialize (state_suffix_empty_minimum (state m)); itauto |].
      by apply eq_State; [| cbn; congruence].
    + apply ELMO_latest_observation_Send_state with (i := i_m) in Hsnd as Hsim; [| done].
      subst sim.
      assert (Hcmp : sent_comparable m lst_im).
      {
        destruct (decide (sent_comparable m lst_im)); [done |].
        contradict Hnot_local_equivocator'.
        eapply local_equivocators_full_step_update; [by constructor 1 |].
        right; split_and!; [done.. |].
        exists lst_im; split; [| split; [| done]].
        - by eapply Hsigma_no_junk with (j := i_m); [| rewrite Hsnd; left].
        - by transitivity (adr (sigma i_m)); [congruence | rewrite Hsnd].
      }
      inversion Hcmp as [| ? ? [] | ? ? Hbefore]; subst.
      * by contradict Hm_not_sent_yet; exists i_m; rewrite Hsnd; left.
      * contradict Hm_not_sent_yet; exists i_m; cbn.
        apply self_messages_sent;
          [by eapply ELMO_no_self_equiv_reachable, valid_state_project_preloaded | by congruence |].
        apply messages_hb_transitive with lst_im.
        -- by eapply ELMO_full_node_reachable, valid_state_project_preloaded.
        -- by rewrite Hsnd; left.
        -- by constructor 1; apply elem_of_messages; left.
      * eapply was_sent_before_characterization_1 in Hbefore; [by rewrite Hsnd; itauto |].
        eapply ELMO_reachable_view with (i := i_m).
        destruct Ht as [(Hsi & _ & Hv) _]; inversion Hv; subst.
        by clear Hsi_m; destruct m; eapply receivable_messages_reachable; [congruence | ..].
Qed.

Lemma all_intermediary_transitions_are_receive
  (i : index) (si si' : vstate (ELMOComponent i))
  (m : Message)
  (Ht : input_valid_transition (pre_loaded_with_all_messages_vlsm (ELMOComponent i))
    Receive (si, Some m) (si', None))
  (i_m : index)
  (Hi_m : adr (state m) = idx i_m)
  (Hadr_neq : adr (state m) <> idx i)
  (Hnot_local_equivocator : ~ local_equivocators_full si (adr (state m)))
  (sigma : composite_state ELMOComponent)
  (Hsigma : composite_ram_state_prop ELMOComponent sigma)
  (Hcomponent : sigma i = si)
  (Hspecial : component_reflects_composite sigma i)
  (tr_m: list transition_item)
  (Htr_m: finite_valid_trace_from_to
          (pre_loaded_with_all_messages_vlsm (ELMOComponent i_m))
          (sigma i_m) (state m) tr_m)
  : Forall (fun item : transition_item => l item = Receive) tr_m.
Proof.
  apply Forall_forall; intros item Hitem.
  eapply ELMOComponent_elem_of_ram_trace in Hitem as H_item;
    [| by eapply valid_trace_forget_last].
  destruct H_item as (s_m0 & m0 & Hs_m0 & H_item).
  destruct item; apply ELMOComponent_input_valid_transition_iff in H_item
    as [[] | (Hl & m_0 & Houtput & Hinput & H_item)]; [done | cbn in *; subst].
  inversion H_item as [| ? ? ? [(_ & _ & Hvi) Hti]]; subst;
    inversion Hvi; subst; inversion Hti; subst; clear H_item Hvi Hti.
  contradict Hnot_local_equivocator; apply Hspecial.
  eapply ELMOComponent_sentMessages_of_ram_trace in Hitem as Hm0; [| done..].
  eapply reachable_sent_messages_adr in Hm0 as Hm0_adr;
    [| by eapply finite_valid_trace_from_to_last_pstate].
  exists (MkMessage s_m0); [by congruence | ..].
  - exists i.
    assert (Hm : MkMessage s_m0 ∈ messages (sigma i)).
    {
      destruct Ht as [(_ & _ & Hv) _]; inversion Hv as [? ? [] |]; subst.
      eapply elem_of_submseteq; [| done].
      by apply elem_of_messages; left.
    }
    apply elem_of_messages in Hm as [Hsnd |]; [| done].
    cbn in Hsnd; eapply reachable_sent_messages_adr in Hsnd; cycle 1.
    + by eapply valid_state_project_preloaded_to_preloaded.
    + by congruence.
  - intros [j Hsnd].
    cbn in Hsnd; eapply reachable_sent_messages_adr in Hsnd as Hsnd_adr;
      [| by eapply valid_state_project_preloaded_to_preloaded].
    rewrite Hm0_adr in Hsnd_adr.
    eapply inj in Hsnd_adr; [| done]; subst j.
    eapply ELMOComponent_sizeState_of_ram_trace_output in Hitem;
      [| by eapply valid_trace_forget_last | done].
    assert (sizeState s_m0 < sizeState (sigma i_m)).
    {
      change s_m0 with (state (MkMessage s_m0)).
      by apply messages_sizeState, elem_of_messages; left.
    }
    by cbn in Hitem; lia.
Qed.

Lemma lift_receive_trace
  (sigma: composite_state ELMOComponent)
  (Hsigma: valid_state_prop ELMOProtocol sigma)
  (m: Message)
  (i_m: index)
  (tr_m: list transition_item)
  (Htr_m:
    finite_valid_trace_from_to (pre_loaded_with_all_messages_vlsm (ELMOComponent i_m))
      (sigma i_m) (state m) tr_m)
  (Htr_m_receive: Forall (fun item : transition_item => l item = Receive) tr_m)
  (Htr_m_inputs_in_sigma:
    forall (item : transition_item) (msg : Message),
      item ∈ tr_m -> input item = Some msg ->
      composite_has_been_directly_observed ELMOComponent sigma msg) :
  finite_valid_trace_from_to ELMOProtocol
    sigma (lift_to_composite_state ELMOComponent sigma i_m (state m))
    (pre_VLSM_embedding_finite_trace_project
      _ _ (lift_to_composite_label ELMOComponent i_m)
      (lift_to_composite_state ELMOComponent sigma i_m)
      tr_m)
    /\
  forall a : Address,
    global_equivocators_simple
      (lift_to_composite_state ELMOComponent sigma i_m (state m)) a
      <->
    global_equivocators_simple sigma a.
Proof.
  remember (pre_VLSM_embedding_finite_trace_project _ _ _ _ _) as tr.
  remember (sigma i_m) as si_m.
  remember (state m) as sm; clear Heqsm.
  revert Heqsi_m Htr_m_inputs_in_sigma Htr_m_receive tr Heqtr.
  induction Htr_m using finite_valid_trace_from_to_rev_ind; intros; subst;
    [by unfold lift_to_composite_state; rewrite state_update_id; split; constructor |].
  apply Forall_app in Htr_m_receive as [Htr_m_receive Hl].
  inversion Hl as [| ? ? H_l _]; cbn in H_l; subst; clear Hl.
  pose (Hti := Ht); destruct Hti as [(_ & _ & Hv) Hti];
    inversion Hv; subst; inversion Hti; subst.
  setoid_rewrite map_app; cbn.
  assert (Hm0 : composite_has_been_directly_observed ELMOComponent sigma m0)
    by (eapply Htr_m_inputs_in_sigma;
      [apply elem_of_app; right; apply elem_of_list_singleton |]; done).
  edestruct IHHtr_m as [Htr Hall];
    [.. | split; [eapply finite_valid_trace_from_to_app; [by apply Htr |] |]].
  - done.
  - intros item msg Hitem Hmsg.
    by eapply Htr_m_inputs_in_sigma; [apply elem_of_app; left |].
  - done.
  - done.
  - apply finite_valid_trace_from_add_last; [| done].
    apply first_transition_valid; cbn.
    apply finite_valid_trace_from_to_last_pstate in Htr as Hsigma'.
    repeat split; cbn; [done | ..].
    + by eapply composite_directly_observed_valid; cycle 1.
    + by constructor; state_update_simpl.
    + eapply
        (in_futures_preserving_oracle_from_stepwise _ _ _ _
          (composite_has_been_directly_observed_stepwise_props ELMOComponent
            ELMO_global_constraint)) in Hm0;
        [| by eapply (VLSM_incl_in_futures (vlsm_incl_pre_loaded_with_all_messages_vlsm
          ELMOProtocol)); eexists].
      destruct Hm0 as [i_m0 Hm0].
      eapply ELMO_not_heavy_receive_observed_message; [| done |].
      * by eapply ELMO_full_node_reachable, valid_state_project_preloaded.
      * by apply ELMO_valid_state_not_heavy.
    + by state_update_simpl; rewrite state_update_twice.
  - apply finite_valid_trace_from_to_last_pstate in Htr as Hsigma'.
    eapply
      (in_futures_preserving_oracle_from_stepwise _ _ _ _
        (composite_has_been_directly_observed_stepwise_props ELMOComponent
          ELMO_global_constraint)) in Hm0;
      [| by eapply (VLSM_incl_in_futures (vlsm_incl_pre_loaded_with_all_messages_vlsm
        ELMOProtocol)); eexists].
    intro a; cbn.
    transitivity (global_equivocators_simple (lift_to_composite_state ELMOComponent sigma i_m s) a);
      [| apply Hall].
    remember (lift_to_composite_state ELMOComponent sigma i_m s) as sigma_s.
    replace s with (sigma_s i_m) by (subst; state_update_simpl; done).
    replace (lift_to_composite_state ELMOComponent sigma i_m _) with
      (state_update ELMOComponent sigma_s i_m (sigma_s i_m <+> MkObservation Receive m0))
      by (subst; rewrite state_update_twice; done).
    rewrite global_equivocators_simple_step_update_receive
      by (subst; state_update_simpl; constructor; done).
    split; [| by left].
    intros [| [-> Hnsnd]]; [done |].
    econstructor; [done | | done].
    by apply composite_has_been_directly_observed_sent_received_iff in Hm0 as [].
Qed.

Lemma special_receivable_messages_emittable_in_future
  (i : index) (si si' : vstate (ELMOComponent i))
  (m : Message)
  (Ht : input_valid_transition (pre_loaded_with_all_messages_vlsm (ELMOComponent i))
    Receive (si, Some m) (si', None))
  (i_m : index)
  (Hi_m : adr (state m) = idx i_m)
  (Hadr_neq : adr (state m) <> idx i)
  (Hnot_local_equivocator : ~ local_equivocators_full si (adr (state m)))
  (Hnot_local_equivocator' : ~ local_equivocators_full si' (adr (state m)))
  (sigma : composite_state ELMOComponent)
  (Hsigma : valid_state_prop ELMOProtocol sigma)
  (Hcomponent : sigma i = si)
  (Hspecial : component_reflects_composite sigma i)
  (H_not_i_paused : other_components_after_send (fun j : index => j = i) sigma)
  (Hm_not_sent_yet : ~ composite_has_been_sent ELMOComponent sigma m) :
    exists sigma' : vstate ELMOProtocol,
      in_futures ELMOProtocol sigma sigma' /\
      sigma' i = si /\
      component_reflects_composite sigma' i /\
      sigma' i_m = state m /\
      other_components_after_send (fun j : index => j = i \/ j = i_m) sigma'.
Proof.
  assert (Hiim : i <> i_m) by (contradict Hadr_neq; congruence).
  assert (Hai_m : adr (sigma i_m) = idx i_m)
    by (apply ELMO_reachable_adr; eapply valid_state_project_preloaded; done).
  edestruct non_equivocating_received_message_continues_trace as [tr_m Htr_m]; [done.. |].
  assert (Htr_m_receive : Forall (fun item => l item = Receive) tr_m).
  {
    eapply all_intermediary_transitions_are_receive.
    1-4, 6-8: done.
    eapply VLSM_incl_valid_state; [| done].
    by apply constraint_preloaded_free_incl with (constraint := ELMO_global_constraint).
  }
  assert (Htr_m_inputs_in_sigma :
    forall item msg, item ∈ tr_m -> input item = Some msg ->
    composite_has_been_directly_observed ELMOComponent sigma msg).
  {
    intros item msg Hitem Hinput.
    destruct Ht as [(Hsi & _ & Hv) _]; inversion Hv as [? ? [] |]; subst.
    cut (has_been_received (ELMOComponent i_m) (state m) msg).
    {
      cbn; intro Hmsg.
      exists i; cbn; unfold has_been_directly_observed_from_sent_received; cbn.
      eapply elem_of_messages, elem_of_submseteq; [| done].
      by apply elem_of_messages; right.
    }
    apply finite_valid_trace_from_to_complete_left in Htr_m as (is & tr & Htr & Hlst).
    eapply has_been_received_examine_one_trace; [done |].
    apply Exists_app; right.
    by apply Exists_exists; eexists.
  }
  edestruct lift_receive_trace as [Htrsigma_m' Heqv]; [done.. |].
  exists (lift_to_composite_state ELMOComponent sigma i_m (state m)).
  split_and!.
  - by eexists.
  - by subst; apply state_update_neq.
  - unfold lift_to_composite_state; split.
    + intros m0; split; [| by eexists].
      intros [j Hm0]; destruct (decide (i_m = j)); subst; state_update_simpl;
        [| by apply Hspecial; eexists].
      destruct Ht as [(_ & _ & Hv) _]; inversion Hv as [? ? [] |]; subst.
      by eapply elem_of_submseteq; [| done].
    + intros a; state_update_simpl.
      by transitivity (global_equivocators_simple sigma a); [apply Heqv | apply Hspecial].
  - by state_update_simpl.
  - intros k Hnk.
    apply Decidable.not_or in Hnk as [].
    state_update_simpl.
    by apply H_not_i_paused.
Qed.

Lemma component_reflects_composite_messages_step_update
  (i : index) (l : Label) (sigma : composite_state ELMOComponent) (s' : State) (m : Message ) :
  ELMOComponentRAMTransition i l (sigma i) s' m ->
  component_reflects_composite_messages sigma i ->
  component_reflects_composite_messages (state_update ELMOComponent sigma i s') i.
Proof.
  intros Ht Hmsgs m'; state_update_simpl.
  replace s' with (sigma i <+> MkObservation l m).
  - split; [| by exists i; state_update_simpl].
    intros [j Hj]; destruct (decide (j = i)); subst; state_update_simpl; [done |].
    by apply elem_of_messages_addObservation; right; apply Hmsgs; eexists.
  - by inversion Ht as [? ? ? [(_ & _ & Hvi) Hti] | ? ? ? [(_ & _ & Hvi) Hti]];
      inversion Hvi; inversion Hti; done.
Qed.

Lemma receiving_already_sent_global_local_equivocators
  (i : index) (sigma : composite_state ELMOComponent) (m : Message) (s' : State)
  (Ht : input_valid_transition (pre_loaded_with_all_messages_vlsm (ELMOComponent i))
    Receive (sigma i, Some m) (s', None))
  (Hreflects : component_reflects_composite sigma i)
  (Hm : composite_has_been_sent ELMOComponent sigma m)
  : forall a : Address,
    global_equivocators_simple (state_update ELMOComponent sigma i s') a
      <->
    local_equivocators_full s' a.
Proof.
  destruct Hreflects as [Hmessages Heqvs].
  assert (m ∈ messages (sigma i))
    by (destruct Hm as [j]; apply Hmessages; exists j; apply elem_of_messages; left; done).
  pose (Hti := Ht); destruct Hti as [(_ & _ & Hvi) Hti];
    inversion Hvi; subst; inversion Hti; subst.
  intros a; rewrite global_equivocators_simple_step_update_receive,
    local_equivocators_full_step_update, (Heqvs a) by (constructor; subst; done).
  split; intros [| [-> Hsome]]; [by left | done | by left | left].
  eapply local_equivocators_simple_iff_full; [done | |].
  - by eapply UMO_reachable_impl, ELMO_reachable_view;
      [intros ? ? [] | apply Ht].
  - destruct Hsome as (_ & m' & Hm' & [Heqadr Hcmp]).
    constructor 1 with m' m; [done | done | | | by split].
    + by apply elem_of_messages; right.
    + apply Hmessages.
      destruct Hm as [j Hj]; exists j.
      by apply elem_of_messages; left.
Qed.

Lemma receiving_already_equivocating_global_local_equivocators
  (i : index) (sigma : composite_state ELMOComponent) (m : Message) (s' : State)
  (Ht : input_valid_transition (pre_loaded_with_all_messages_vlsm (ELMOComponent i))
    Receive (sigma i, Some m) (s', None))
  (Hreflects : component_reflects_composite sigma i)
  (Heqv : local_equivocators_full (sigma i) (adr (state m)))
  : forall a : Address,
    global_equivocators_simple (state_update ELMOComponent sigma i s') a
      <->
    local_equivocators_full s' a.
Proof.
  destruct Hreflects as [Hmessages Heqvs].
  pose (Hti := Ht); destruct Hti as [(_ & _ & Hvi) Hti];
    inversion Hvi; subst; inversion Hti; subst.
  intros a; rewrite global_equivocators_simple_step_update_receive,
    local_equivocators_full_step_update, (Heqvs a) by (constructor; subst; done).
  by split; intros []; [by left | | by left |]; destruct_and!; subst; left.
Qed.

Lemma receiving_not_already_equivocating_global_local_equivocators
  (i : index) (sigma : composite_state ELMOComponent) (m : Message) (s' : State)
  (Ht : input_valid_transition (pre_loaded_with_all_messages_vlsm (ELMOComponent i))
    Receive (sigma i, Some m) (s', None))
  (Hreflects : component_reflects_composite sigma i)
  (Hneqv : ~ local_equivocators_full (sigma i) (adr (state m)))
  (Heqv : local_equivocators_full s' (adr (state m)))
  : forall a : Address,
    global_equivocators_simple (state_update ELMOComponent sigma i s') a
      <->
    local_equivocators_full s' a.
Proof.
  destruct Hreflects as [Hmessages Heqvs].
  pose (Hti := Ht); destruct Hti as [(_ & _ & Hvi) Hti];
    inversion Hvi; subst; inversion Hti.
  assert (Hm' : exists m', m' ∈ receivedMessages (sigma i) /\ incomparable m m')
    by (eapply local_equivocators_full_step_update in Heqv as [| (_ & _ & Hrcv)];
        [| | constructor 1]; done).
  intros a; rewrite global_equivocators_simple_step_update_receive,
    local_equivocators_full_step_update, (Heqvs a) by (constructor; subst; done).
  split; intros []; [by left | by itauto | by left |].
  destruct_and!; subst; right; split; [done |].
  contradict Hneqv.
  eapply local_equivocators_simple_iff_full; [done | |].
  - by eapply UMO_reachable_impl, ELMO_reachable_view;
      [intros ? ? [] | apply Ht].
  - destruct Hm' as (m' & Hm' & Heqadr & Hcmp).
    constructor 1 with m' m; [done | done | | | by split].
    + by apply elem_of_messages; right.
    + apply Hmessages.
      destruct Hneqv as [j Hj]; exists j.
      by apply elem_of_messages; left.
Qed.

(**
  The following lemma shows that for any reachable state in an (ELMOComponent i)
  there is a valid state in [ELMOProtocol] where component <<i>> meets most of the
  conditions of the previous lemma.
*)
Lemma reflecting_composite_for_reachable_component
  (i : index) (si : vstate (ELMOComponent i))
  (Hreachable : ram_state_prop (ELMOComponent i) si):
  exists s : vstate ELMOProtocol,
    s i = si
    /\ valid_state_prop ELMOProtocol s
    /\ component_reflects_composite s i
    /\ other_components_after_send (fun j : index => j = i) s
    /\ forall (s_prev : State) (l : Label) (m : Message),
      si = s_prev <+> MkObservation l m ->
      let s' := state_update ELMOComponent s i s_prev in
      valid_state_prop ELMOProtocol s' /\
      ELMOProtocolValidTransition i l s' s m.
Proof.
  induction Hreachable using valid_state_prop_ind;
    [| destruct IHHreachable as (sigma & <- & Hsigma & Hreflects & Hsend & Hall), l; cycle 1].
  - unfold initial_state_prop in Hs; cbn in Hs.
    apply UMOComponent_initial_state_spec in Hs as ->.
    exists (` (composite_s0 ELMOComponent)).
    unfold composite_s0; cbn; split_and!; [done | ..].
    + by apply initial_state_is_valid.
    + repeat split; cbn; [.. | by inversion 1].
      * by intros [j Hj].
      * by inversion 1.
      * by intros []; itauto.
    + by left; cbn.
    + by inversion 1.
  - pose (sigma' := state_update ELMOComponent sigma i s').
    exists sigma'; split; [by subst sigma'; state_update_simpl |].
    pose (Hti := Ht); destruct Hti as [(_ & _ & Hv) Hti];
      inversion Hv; subst; inversion Hti; subst.
    assert (Htsigma : input_valid_transition ELMOProtocol (existT i Send) (sigma, None)
                        (sigma', Some (MkMessage (sigma i))))
      by (repeat split; [| apply option_valid_message_None |]; done).
    eapply input_valid_transition_destination in Htsigma as Hsigma'.
    split_and!; [done | split | ..]; cycle 2.
    + by intros j Hnj; subst sigma'; state_update_simpl; apply Hsend.
    + inversion 1; destruct s_prev; cbn in *; subst.
      replace (state_update _ _ _ _) with sigma; [by split; [| constructor] |].
      by subst sigma'; extensionality j; destruct (decide (i = j)); subst;
        state_update_simpl; [destruct (sigma j) |].
    + intro m; split; [| by eexists]; intros [j Hm].
      destruct (decide (i = j)); [by subst |].
      subst sigma'; state_update_simpl.
      apply elem_of_messages_addObservation; right.
      by apply Hreflects; eexists.
    + intros a; transitivity (global_equivocators_simple sigma a); [split |]; cycle 2.
      * etransitivity; [by apply Hreflects |].
        subst sigma'; state_update_simpl.
        unfold local_equivocators_full; cbn; rewrite lefo_alt; cbn.
        by split; [right | intros [|]; [destruct_and! |]].
      * intros [? <- ]; esplit; [done | ..].
        -- destruct ges_recv as [j Hrecv].
           destruct (decide (i = j)); subst; subst sigma'; state_update_simpl; [| by eexists].
           by cbn in Hrecv; rewrite decide_False in Hrecv by itauto; exists j.
        -- intros [j Hsent]; apply ges_not_sent; exists j.
           destruct (decide (i = j)); subst; subst sigma'; state_update_simpl; [| done].
           by eapply has_been_sent_step_update; [| right].
      * intros []; esplit; [done | ..].
        -- destruct ges_recv as [j Hrecv]; exists j.
           destruct (decide (i = j)); subst; subst sigma'; state_update_simpl; [| done].
           by eapply has_been_received_step_update; [| right].
        -- intros [j Hsnd]; apply ges_not_sent.
           destruct (decide (i = j)); subst; subst sigma'; state_update_simpl; [| by eexists].
           cbn in Hsnd; rewrite decide_True in Hsnd by done; cbn in Hsnd.
           apply elem_of_cons in Hsnd as []; subst; [| by exists j].
           exfalso; eapply irreflexivity with (R := lt) (x := sizeState (sigma j));
             [typeclasses eauto |].
           change (sigma j) with (state (MkMessage (sigma j))) at 1.
           apply messages_sizeState, Hreflects.
           destruct ges_recv as [j' Hrecv]; exists j'.
           by apply elem_of_messages; right.
  - pose (Hti := Ht); destruct Hti as [(_ & _ & Hv) Hti];
      inversion Hv as [? ? [? ? ? Hlocal_ok] |]; subst; inversion Hti; subst om'.
    apply ELMO_msg_valid_full_has_sender in ELMO_mv_msg_valid_full0 as Hsender.
    cut (exists gamma,
          in_futures ELMOProtocol sigma gamma /\
          gamma i = sigma i /\
          component_reflects_composite (state_update ELMOComponent gamma i s') i /\
          other_components_after_send (fun j : index => j = i) gamma).
    {
      intros (gamma & Hfutures & Heq_i & [Hsigma'_messages Hsigma'_eqvs] & Hgamma_send).
      pose (sigma' := state_update ELMOComponent gamma i s'); subst s'.
      exists sigma'; split; [by subst sigma'; state_update_simpl |].
      assert (Hvtsigma : ValidTransition ELMOProtocol (existT i Receive) gamma (Some m) sigma' None).
      {
        repeat split; cbn; [by rewrite Heq_i | | by rewrite Heq_i].
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
        - eapply in_futures_valid_snd.
          by apply (VLSM_incl_in_futures (constraint_preloaded_free_incl _ ELMO_global_constraint)).
        - by apply any_message_is_valid_in_preloaded.
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
    destruct (decide (composite_has_been_sent ELMOComponent sigma m)) as [| Hnot_sent].
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
    pose (sigma' := state_update ELMOComponent chi i_m (chi i_m <+> MkObservation Send m)); subst s'.
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
    assert (ELMOComponentRAMTransition i Receive (sigma' i) (sigma i <+> MkObservation Receive m) m).
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
           by destruct Heqv as [| [-> ]].
Qed.

(** Every [ELMOComponent] is a validator for [ELMOProtocol]. *)
Theorem ELMOComponents_validating :
  forall i : index,
    component_projection_validator_prop ELMOComponent ELMO_global_constraint i.
Proof.
  intros i li si om Hvti.
  apply input_valid_transition_iff in Hvti as [[si' om'] Hvti].
  pose (Hvti' := Hvti); destruct Hvti' as [(_ & _ & Hvi) Hti].
  apply input_valid_transition_destination in Hvti as Hsi'.
  apply reflecting_composite_for_reachable_component in Hsi'
    as (s' & <- & Hs' & _ & _ & Htransitions).
  specialize (Htransitions si li).
  exists (state_update ELMOComponent s' i si).
  split; [by state_update_simpl |].
  inversion Hvi; subst; inversion Hti as [Heqs'i]; subst;
    symmetry in Heqs'i; destruct (Htransitions _ Heqs'i) as [Hvs'0 Hvt0];
    inversion Hvt0 as [? ? ? ? Hvt | ? ? ? ? Hvt].
  - repeat split; [done | | by apply Hvt..].
    eapply composite_received_valid; [by apply Hs' |].
    by eexists; eapply has_been_received_step_update; [| left].
  - by repeat split; [| apply option_valid_message_None | apply Hvt].
Qed.

End sec_ELMOProtocol.

End sec_ELMO.
