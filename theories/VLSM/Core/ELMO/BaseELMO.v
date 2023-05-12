From VLSM.Lib Require Import Itauto.
From stdpp Require Import prelude finite.
From VLSM.Lib Require Import EquationsExtras.
From VLSM.Lib Require Import Preamble StdppExtras.
From VLSM.Core Require Import VLSM MessageDependencies.

(** * Basic Definitions and Lemmas for UMO, MO and ELMO

  This module contains basic definitions and lemmas needed for the UMO, MO and
  ELMO protocols. In contrast to the paper, which uses natural numbers,
  we abstract over the implementation of an [Address] by making it an arbitrary
  type with decidable equality.
*)

Section sec_base_ELMO.

Context
  {Address : Type}
  `{EqDecision Address}.

(** ** Labels, States, Observations and Messages *)

(** Messages can be labeled as either sent or received. *)
Inductive Label : Type :=
| Receive
| Send.

Inductive State : Type := MkState
{
  obs : list Observation;
  adr  : Address;
}
with Observation : Type := MkObservation
{
  label   : Label;
  message : Message;
}
(** A [Message] is a wrapper for [State]. *)
with Message : Type := MkMessage
{
  state : State;
}.

(**
  [State]s, [Observation]s and [Message]s are printed like ordinary inductive
  types, using their constructor names, instead of as records with the
  {| ... |} notation.
*)
#[export] Unset Printing Records.

(** Two states are equal when they have equal observations and equal addresses. *)
Lemma eq_State :
  forall s1 s2 : State,
    obs s1 = obs s2 -> adr s1 = adr s2 -> s1 = s2.
Proof.
  by intros [] []; cbn; congruence.
Qed.

Lemma eq_Message :
  forall m1 m2 : Message,
    obs (state m1) = obs (state m2) -> adr (state m1) = adr (state m2) -> m1 = m2.
Proof.
  by intros [[]] [[]]; cbn; congruence.
Qed.

Lemma eq_Observation :
  forall ob1 ob2 : Observation,
    label ob1 = label ob2 -> message ob1 = message ob2 -> ob1 = ob2.
Proof.
  by intros [] []; cbn; congruence.
Qed.

(** [Label]s, [State]s, [Observation]s and [Message]s have decidable equality. *)
#[export] Instance EqDecision_Label : EqDecision Label.
Proof. by intros x y; unfold Decision; decide equality. Defined.

#[local] Lemma State_eq_dec : forall x y : State, {x = y} + {x <> y}
with Observation_eq_dec : forall x y : Observation, {x = y} + {x <> y}
with Message_eq_dec : forall x y : Message, {x = y} + {x <> y}.
Proof.
  - intros x y; decide equality.
    + by apply EqDecision0.
    + by decide equality.
  - by do 2 decide equality.
  - by intros x y; decide equality.
Defined.

#[export] Instance EqDecision_State : EqDecision State := State_eq_dec.
#[export] Instance EqDecision_Observation : EqDecision Observation := Observation_eq_dec.
#[export] Instance EqDecision_Message : EqDecision Message := Message_eq_dec.

(** A notion of size for [State]s, [Observation]s and [Message]s. *)
Fixpoint sizeState (s : State) : nat :=
  1 + fold_right (fun ob sizeObs => sizeObservation ob + sizeObs) 0 (obs s)

with sizeObservation (ob : Observation) : nat :=
  1 + sizeMessage (message ob)

with sizeMessage (msg : Message) : nat :=
  1 + sizeState (state msg).

Lemma sizeObservation_unfold (ob : Observation) :
  sizeObservation ob = 2 + sizeState (state (message ob)).
Proof. by destruct ob as [? []]. Qed.

(** ** Extending States with new Observations

  We want to abstract over from the "direction" of the [list] of [Observation]s,
  so that we can [cons] new observations at the beginning, whereas in the paper
  they are [app]ended to the end. We will use the function [addObservation] to
  extend a state with a new observations and [addObservations] to extend a state
  with a list of new observations.
*)

Definition addObservation' (ob : Observation) (obs : list Observation) : list Observation :=
  ob :: obs.

Lemma addObservation'_ind (P : list Observation -> Prop)
  (Hempty : P [])
  (Hadd : forall ob obs, P obs -> P (addObservation' ob obs)) :
  forall obs, P obs.
Proof.
  exact (list_ind P Hempty Hadd).
Qed.

Lemma addObservation'_rec (P : list Observation -> Set)
  (Hempty : P [])
  (Hadd : forall ob obs, P obs -> P (addObservation' ob obs)) :
  forall obs, P obs.
Proof.
  exact (list_rec P Hempty Hadd).
Defined.

Lemma addObservation'_rect (P : list Observation -> Type)
  (Hempty : P [])
  (Hadd : forall ob obs, P obs -> P (addObservation' ob obs)) :
  forall obs, P obs.
Proof.
  exact (list_rect P Hempty Hadd).
Defined.

Definition addObservation (ob : Observation) (s : State) : State :=
  MkState (addObservation' ob (obs s)) (adr s).

Notation "s <+> ob" := (addObservation ob s) (left associativity, at level 50).

(**
  The induction principle [addObservation_ind] considers a [State]
  as built up using [addObservation] from an initial state.
*)
Lemma addObservation_ind (P : State -> Prop)
  (Hempty : forall a, P (MkState [] a))
  (Hadd : forall ob s, P s -> P (addObservation ob s)) :
  forall obs, P obs.
Proof.
  intros [obs a].
  induction obs using addObservation'_ind; [done |].
  by apply (Hadd ob) in IHobs.
Qed.

Lemma addObservation_rec (P : State -> Set)
  (Hempty : forall a, P (MkState [] a))
  (Hadd : forall ob s, P s -> P (s <+> ob)) :
  forall obs, P obs.
Proof.
  intros [obs a].
  induction obs using addObservation'_rec; [done |].
  by apply (Hadd ob) in IHobs.
Defined.

Lemma addObservation_rect (P : State -> Type)
  (Hempty : forall a, P (MkState [] a))
  (Hadd : forall ob s, P s -> P (addObservation ob s)) :
  forall obs, P obs.
Proof.
  intros [obs a].
  induction obs using addObservation'_rect; [done |].
  by apply (Hadd ob) in IHobs.
Defined.

(**
  This induction principle is like [addObservation_ind], but
  also provides an induction hypothesis for the [State] contained
  in the message of the added observation.
*)
Definition addObservation_both_ind
  (P : State -> Prop)
  (Hinit : forall a, P (MkState [] a))
  (Hadd : forall [s l ms], P s -> P ms -> P (s <+> MkObservation l (MkMessage ms))) :
  forall s, P s :=
  fix rec s :=
    let '(MkState ol a) := s in
    let Hcons := fun '(MkObservation _ (MkMessage ms)) _ IHol' => Hadd IHol' (rec ms)
    in list_ind _ (Hinit a) Hcons ol.

(**
  A property on [sizeState] of [addObservation].
  Useful because a [Fixpoint] can't be unfolded unless
  the argument is in the form of a constructor application.
*)
Lemma addObservation_size s ob :
  sizeState (s <+> ob) = sizeState s + sizeObservation ob.
Proof. by destruct s; cbn; lia. Qed.

Definition addObservations (obs' : list Observation) (s : State) : State :=
  MkState (obs' ++ (obs s)) (adr s).

Notation "s <++> obs" := (addObservations obs s) (left associativity, at level 50).

Definition addObservationToMessage (ob : Observation) (m : Message) : Message :=
  MkMessage (state m <+> ob).

Notation "m <*> ob" := (addObservationToMessage ob m) (left associativity, at level 50).

Definition addObservationsToMessage (obs' : list Observation) (m : Message) : Message :=
  MkMessage (state m <++> obs').

Notation "m <**> obs" := (addObservationsToMessage obs m) (left associativity, at level 50).

(** [<+>] is injective in both arguments. *)
Lemma addObservation_inj :
  forall (ob1 ob2 : Observation) (s1 s2 : State),
    s1 <+> ob1 = s2 <+> ob2 -> ob1 = ob2 /\ s1 = s2.
Proof.
  intros ob1 ob2 s1 s2 [= ->].
  by split; [| apply eq_State].
Qed.

(** Adding an observation to a state results in a different state. *)
Lemma addObservation_acyclic :
  forall (ob : Observation) (s : State),
    s <+> ob <> s.
Proof.
  intros ob [obs adr] [= Heq].
  unfold addObservation' in Heq.
  by apply (app_inv_tail _ [ob] []) in Heq.
Qed.

(** Adding no observations does not change the state. *)
Lemma addObservations_nil :
  forall s : State,
    s <++> [] = s.
Proof.
  by intros [].
Qed.

(**
  Adding a single observation is compatible with adding many observations at
  once, in the obvious way.
*)
Lemma addObservations_app :
  forall (s : State) (ob : Observation) (obs' : list Observation),
    s <+> ob <++> obs' = s <++> (obs' ++ [ob]).
Proof.
  intros s ob obs'.
  by apply eq_State; cbn; [rewrite <- app_assoc |].
Qed.

Lemma addObservation_cons :
  forall (s : State) (ob : Observation) (obs' : list Observation),
    s <++> obs' <+> ob = s <++> (ob :: obs').
Proof.
  intros s ob obs'.
  by apply eq_State; cbn.
Qed.

(**
  An observation in [s <+> ob] is either the added observation [ob]
  or an observation in the original state.
*)
Lemma elem_of_addObservation :
  forall (s : State) (ob ob' : Observation),
    ob' ∈ obs (s <+> ob) <-> ob' = ob \/ ob' ∈ obs s.
Proof.
  intros [s_obs a] ob ob'.
  cbn; unfold addObservation'.
  by apply elem_of_cons.
Qed.

(**
  The immediate substate relation. May be used to prove that
  a [State] does not contain itself.
*)
Inductive immediate_substate : State -> State -> Prop :=
| substate_prev : forall s ob, immediate_substate s (s <+> ob)
| substate_new : forall s ob, immediate_substate (state (message ob)) (s <+> ob).

Lemma immediate_substate_wf : wf immediate_substate.
Proof.
  intro s; induction s using addObservation_both_ind; constructor.
  - by inversion 1.
  - by inversion 1; [rewrite (eq_State y s1) | subst y].
Qed.

(** *** Messages sent and received by a State *)

Definition isSend (ob : Observation) : Prop :=
match label ob with
| Send => True
| Receive => False
end.

Definition isReceive (ob : Observation) : Prop :=
match label ob with
| Send => False
| Receive => True
end.

#[export] Instance isSend_dec (ob : Observation) : Decision (isSend ob).
Proof.
  by destruct ob as [[] m]; cbn; typeclasses eauto.
Defined.

#[export] Instance isReceive_dec (ob : Observation) : Decision (isReceive ob).
Proof.
  by destruct ob as [[] m]; cbn; typeclasses eauto.
Defined.

Definition messages' (obs : list Observation) : list Message :=
  map message obs.

Definition messages (st : State) : list Message :=
  messages' (obs st).

Definition sentMessages' (obs : list Observation) : list Message :=
  map message (filter isSend obs).

Definition sentMessages (st : State) : list Message :=
  sentMessages' (obs st).

Definition receivedMessages' (obs : list Observation) : list Message :=
  map message (filter isReceive obs).

Definition receivedMessages (st : State) : list Message :=
  receivedMessages' (obs st).

Definition receivedAddresses (st : State) : list Address :=
  map (fun m => adr (state m)) (receivedMessages st).

Lemma elem_of_map_filter_addObservation
  [B] (f : Observation -> B)
  (P : Observation -> Prop) {P_dec : forall a, Decision (P a)} :
  forall s ob v,
    v ∈ map f (filter P (obs (s <+> ob)))
      <->
    v = f ob /\ P ob \/ v ∈ map f (filter P (obs s)).
Proof.
  intros s ob v.
  rewrite !elem_of_list_fmap.
  setoid_rewrite elem_of_list_filter.
  cbn; unfold addObservation'.
  setoid_rewrite elem_of_cons.
  by split; intros H; decompose [and or ex] H; subst; eauto.
Qed.

(**
  When a message belongs to the [sentMessages] of some state, then the state
  contains a corresponding observation which was sent. The converse also holds.
*)
Lemma elem_of_sentMessages :
  forall (s : State) (m : Message),
    m ∈ sentMessages s <-> MkObservation Send m ∈ obs s.
Proof.
  intros; unfold sentMessages, sentMessages'.
  rewrite elem_of_list_fmap; setoid_rewrite elem_of_list_filter.
  split; [| by firstorder].
  by intros ([[] ?] & -> & []); cbn in *.
Qed.

(**
  A message in [sentMessages (s <+> ob)] is either in
  [sentMessages s] or is the message in the new observation [ob],
  and can only be the message from [ob] if that is a [Send] observation.
*)
Lemma elem_of_sentMessages_addObservation :
  forall (s : State) (ob : Observation) (m : Message),
    m ∈ sentMessages (s <+> ob)
      <->
    m = message ob /\ isSend ob \/ m ∈ sentMessages s.
Proof.
  by apply elem_of_map_filter_addObservation.
Qed.

Lemma sentMessages_addObservation :
  forall (s : State) (ob : Observation),
    sentMessages (s <+> ob)
      =
    if decide (isSend ob) then message ob :: sentMessages s else sentMessages s.
Proof.
  intros s ob.
  unfold sentMessages, sentMessages'; cbn.
  by destruct (decide (isSend ob)).
Qed.

(**
  When a message belongs to the [receivedMessages] of some state, then the state
  contains a corresponding observation which was received. The converse also holds.
*)
Lemma elem_of_receivedMessages :
  forall (s : State) (m : Message),
    m ∈ receivedMessages s <-> MkObservation Receive m ∈ obs s.
Proof.
  intros; unfold receivedMessages, receivedMessages'.
  rewrite elem_of_list_fmap; setoid_rewrite elem_of_list_filter.
  split; [| by firstorder].
  by intros ([[] ?] & -> & []); cbn in *.
Qed.

(**
  A message in [receivedMessages (s <+> ob)] is either in
  [receivedMessages s] or is the message in the new observation [ob],
  and can only be the message from [ob] if that is a [Receive] observation.
*)
Lemma elem_of_receivedMessages_addObservation :
  forall (s : State) (ob : Observation) (m : Message),
    m ∈ receivedMessages (s <+> ob)
      <->
    m = message ob /\ isReceive ob \/ m ∈ receivedMessages s.
Proof.
  by apply elem_of_map_filter_addObservation.
Qed.

Lemma receivedMessages_addObservation :
  forall (s : State) (ob : Observation),
    receivedMessages (s <+> ob)
      =
    if decide (isReceive ob) then message ob :: receivedMessages s else receivedMessages s.
Proof.
  intros s ob.
  unfold receivedMessages, receivedMessages'; cbn.
  by destruct (decide (isReceive ob)).
Qed.

Lemma elem_of_messages :
  forall (s : State) (m : Message),
    m ∈ messages s <-> m ∈ sentMessages s \/ m ∈ receivedMessages s.
Proof.
  intros; unfold messages, messages'.
  rewrite elem_of_sentMessages, elem_of_receivedMessages, elem_of_list_fmap.
  split.
  - by intros [[[]] [-> Hm]]; auto.
  - by intros []; (eexists; split; [| eauto]).
Qed.

(**
  A message in [s <+> ob] is either the message of the added
  observation [ob] or a message in the original state.
*)
Lemma elem_of_messages_addObservation :
  forall (s : State) (ob : Observation) (m : Message),
    m ∈ messages (s <+> ob) <-> m = message ob \/ m ∈ messages s.
Proof.
  by intros; apply elem_of_cons.
Qed.

Lemma messages_addObservation :
  forall (s : State) (ob : Observation),
    messages (s <+> ob) = message ob :: messages s.
Proof. done. Qed.

(**
  An address in [receivedAddresses (s <+> ob)] is either in
  [receivedAddresses s] or is the address from the message in the
  new observation [ob], and can only be from [ob] if that is
  a [Receive] observation.
*)
Lemma elem_of_receivedAddresses :
  forall (s : State) (ob : Observation) (a : Address),
    a ∈ receivedAddresses (s <+> ob)
      <->
    a = adr (state (message ob)) /\ isReceive ob \/ a ∈ receivedAddresses s.
Proof.
  intros s ob a.
  unfold receivedAddresses, receivedMessages, receivedMessages'.
  by rewrite !map_map, elem_of_map_filter_addObservation.
Qed.

Lemma receivedAddresses_addObservation :
  forall (s : State) (ob : Observation),
    receivedAddresses (s <+> ob)
      =
    if decide (isReceive ob)
    then adr (state (message ob)) :: receivedAddresses s
    else receivedAddresses s.
Proof.
  intros s ob.
  unfold receivedAddresses; cbn.
  by destruct (decide (isReceive ob)).
Qed.

End sec_base_ELMO.

Notation "s <+> ob" := (addObservation ob s) (left associativity, at level 50).
Notation "s <++> obs" := (addObservations obs s) (left associativity, at level 50).
Notation "m <*> ob" := (addObservationToMessage ob m) (left associativity, at level 50).
Notation "m <**> obs" := (addObservationsToMessage obs m) (left associativity, at level 50).

(** [ram_state_prop] defines the "reachable by any means" or ram states of a VLSM. *)
Definition ram_state_prop {message} (V : VLSM message) (s : VLSM.state V) : Prop :=
  valid_state_prop (pre_loaded_with_all_messages_vlsm V) s.

Section sec_BaseELMO_Observations.

Context
  {Address : Type}
  `{EqDecision Address}
  (State := @State Address)
  (Observation := @Observation Address)
  (Message := @Message Address)
  .

#[export] Instance ELMOComponentType : VLSMType Message :=
{
  state := State;
  label := Label;
}.

(** We can extract a trace from a [list] of [Observation]s. *)
Fixpoint observations2trace (obs : list Observation) (adr : Address)
  : list transition_item :=
match obs with
| [] => []
| MkObservation Send msg as ob :: obs =>
    let s'   := MkState obs adr in
    let msg' := MkMessage s' in
    let ob'  := MkObservation Send msg' in
    let obs' := addObservation' ob' obs in
    let dest := MkState obs' adr in
      observations2trace obs adr ++ [Build_transition_item Send None dest (Some msg')]
| MkObservation Receive msg as ob :: obs =>
    let dest := MkState (ob :: obs) adr in
      observations2trace obs adr ++ [Build_transition_item Receive (Some msg) dest None]
end.

(** A state contains a list of observations, so we can extract a trace from a state. *)
Definition state2trace (s : State) : list transition_item :=
  observations2trace (obs s) (adr s).

(** ** Observations and message dependencies *)

Lemma obs_sizeState :
  forall (s : State) (ob : Observation), ob ∈ obs s ->
    sizeState (state (message ob)) < sizeState s.
Proof.
  induction s using addObservation_ind; inversion 1; subst.
  - by destruct ob as [? []]; unfold sizeState; cbn; lia.
  - etransitivity; [by apply IHs |].
    by destruct s, ob as [? []]; unfold sizeState; cbn; lia.
Qed.

Lemma messages_sizeState :
  forall (s : State) (m : Message), m ∈ messages s ->
    sizeState (state m) < sizeState s.
Proof.
  intros s m Hm.
  apply elem_of_list_fmap in Hm as (o & -> & Hobs).
  by apply obs_sizeState.
Qed.

Inductive rec_obs : State -> Observation -> Prop :=
| rec_new :
    forall (s : State) (ob : Observation),
      rec_obs (s <+> ob) ob
| rec_prev :
    forall (s : State) (ob' ob : Observation),
      rec_obs s ob -> rec_obs (s <+> ob') ob
| rec_recv :
    forall (s : State) (m : Message) (ob : Observation),
      rec_obs (state m) ob -> rec_obs (s <+> MkObservation Receive m) ob.

Equations rec_obs_fn (s : State) : listset Observation by wf (sizeState s) lt :=
| {| obs := [] |} => ∅
| {| obs := o :: os; adr := a |} =>
  {[ o ]} ∪ rec_obs_fn (state (message o)) ∪ rec_obs_fn {| obs := os; adr := a |}.
Next Obligation.
Proof. by intros [? []] os a _; unfold sizeState; cbn; lia. Qed.
Next Obligation.
Proof. by intros [? []] os a _; unfold sizeState; cbn; lia. Qed.

Lemma elem_of_rec_obs_fn_1 :
  forall (s : State) (o : Observation),
    rec_obs s o -> o ∈ rec_obs_fn s.
Proof.
  intro s; apply_funelim (rec_obs_fn s); clear s; [by inversion 1 |].
  by intros [] os a Hindm Hindos o; inversion 1 as [[] ? | [] ? | [] ?]; subst;
    cbn in *; unfold Observation; rewrite !elem_of_union, ?elem_of_singleton; itauto.
Qed.

Lemma rec_obs_fn_sizeState :
  forall (s : State) (o : Observation), o ∈ rec_obs_fn s ->
    sizeState (state (message o)) < sizeState s.
Proof.
  intro s; apply_funelim (rec_obs_fn s); clear s;
    [intros * Ho; contradict Ho; apply not_elem_of_empty |].
  intros o os a Hindo Hindos o0; rewrite !elem_of_union; intros [[Heq | Ho] | Hos].
  - apply elem_of_singleton in Heq as ->.
    by unfold sizeState; destruct o as [? []]; cbn; lia.
  - transitivity (sizeState (state (message o))); [by apply Hindo |].
    by unfold sizeState; destruct o as [? []]; cbn; lia.
  - transitivity (sizeState (MkState os a)); [by apply Hindos |].
    by unfold sizeState; destruct o as [? []]; cbn; lia.
Qed.

Definition Message_dependencies (m : Message) : listset Message :=
  list_to_set (map message (obs (state m))).

Definition Message_full_dependencies (m : Message) : listset Message :=
  fin_sets.set_map message (rec_obs_fn (state m)).

Lemma Message_full_dependencies_sizeState (dm m : Message) :
  dm ∈ Message_full_dependencies m -> sizeState (state dm) < sizeState (state m).
Proof.
  unfold Message_full_dependencies; intro Hdm.
  apply elem_of_map in Hdm as (o & -> & Ho).
  by apply rec_obs_fn_sizeState.
Qed.

#[export] Instance Message_FullMessageDependencies :
  FullMessageDependencies Message_dependencies Message_full_dependencies.
Proof.
  constructor; cycle 1.
  - by intros m Hm; apply Message_full_dependencies_sizeState in Hm; lia.
  - intros dm [s]; revert dm; unfold Message_full_dependencies; cbn.
    apply_funelim (rec_obs_fn s);
      [intros adr dm; split | intros [l m] os a Hindm Hindos dm; split].
    + by rewrite set_map_empty, elem_of_empty.
    + rewrite msg_dep_happens_before_iff_one; unfold msg_dep_rel; cbn.
      rewrite set_map_empty; setoid_rewrite elem_of_empty.
      by firstorder.
    + intros Hdm; apply elem_of_map in Hdm as (o & -> & Hdm).
      unfold Message in Hdm; rewrite !elem_of_union, !elem_of_singleton in Hdm; cbn in Hdm.
      destruct Hdm as [[-> | Hm] | Hos].
      * apply msg_dep_happens_before_iff_one; left.
        unfold msg_dep_rel, compose; cbn; unfold Message.
        by rewrite elem_of_union, elem_of_singleton; left.
      * transitivity m; cbn in *.
        -- by destruct m; apply Hindm, elem_of_map; cbn; eexists; split.
        -- apply msg_dep_happens_before_iff_one; left.
           unfold msg_dep_rel, compose; cbn; unfold Message.
           by rewrite elem_of_union, elem_of_singleton; left.
      * assert (Hmos : message o ∈@{listset Message} set_map message (rec_obs_fn (MkState os a)))
          by (apply elem_of_map; eexists; split; done).
        apply Hindos in Hmos.
        cut (forall dm,
              msg_dep_rel Message_dependencies
                dm (MkMessage (MkState os a)) ->
              msg_dep_rel Message_dependencies
                dm (MkMessage (MkState (MkObservation l m :: os) a))).
        {
          intro Hext; apply msg_dep_happens_before_iff_one.
          apply msg_dep_happens_before_iff_one in Hmos as [Hdep | (dm & Hhb & Hdep)].
          - by left; apply Hext.
          - by right; eexists; split; [| apply Hext].
        }
        unfold msg_dep_rel; cbn.
        by intros dm; rewrite elem_of_union; right.
    + intros Hb; apply elem_of_map.
      do 2 setoid_rewrite elem_of_union; setoid_rewrite elem_of_singleton; cbn.
      apply msg_dep_happens_before_iff_one in Hb.
      unfold msg_dep_rel, compose in Hb; cbn in Hb; unfold Message in Hb.
      setoid_rewrite elem_of_union in Hb;
        setoid_rewrite elem_of_singleton in Hb.
      destruct Hb as [[-> | Hdm] | Hos].
      * by eexists; split; [| by left; left].
      * cut (msg_dep_happens_before Message_dependencies dm (MkMessage (MkState os a))).
        {
          intro Hb; apply Hindos, elem_of_map in Hb as (y & -> & Hy).
          by eexists; split; [| right].
        }
        by apply msg_dep_happens_before_iff_one; left.
      * destruct Hos as (y & Hb & [-> | Hos]).
        -- destruct m as [state_m].
           apply Hindm, elem_of_map in Hb as (y & -> & Hy).
           by eexists; split; [| left; right].
        -- cut (msg_dep_happens_before Message_dependencies dm
                (MkMessage (MkState os a))).
           {
             intros (z & -> & Hz)%Hindos%elem_of_map.
             by eexists; split; [| right].
           }
           transitivity y; [done |].
           by apply msg_dep_happens_before_iff_one; left.
Qed.

Definition Message_sender (m : Message) : option Address :=
  Some (adr (state m)).

Context
  `{finite.Finite index}
  `{Inhabited index}
  (idx : index -> Address)
  `{!Inj (=) (=) idx}
  .

Definition ELMO_A (a : Address) : index :=
  hd inhabitant (filter (fun i => idx i = a) (enum index)).

Lemma ELMO_A_inv : forall i, ELMO_A (idx i) = i.
Proof.
  intro i; unfold ELMO_A; cbn.
  replace (filter _ _) with [i]; [done |].
  generalize (enum index), (NoDup_enum index) as Hnodup, (elem_of_enum i) as Hi.
  induction l; intros; [by inversion Hi |].
  inversion Hnodup; subst.
  assert (Hnil : forall i, i ∉ l -> filter (fun i0 : index => idx i0 = idx i) l = []).
  {
    intros; apply Forall_filter_nil, Forall_forall.
    intros j Hj; contradict Hj.
    by eapply inj in Hj; [| done]; subst.
  }
  inversion Hi; subst; cbn.
  - by rewrite decide_True, Hnil.
  - rewrite decide_False, IHl; [done.. |].
    by intro Hcontra; eapply inj in Hcontra; [| done]; subst.
Qed.

End sec_BaseELMO_Observations.
