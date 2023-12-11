From VLSM.Lib Require Import Itauto.
From Coq Require Import FunctionalExtensionality.
From stdpp Require Import prelude finite.
From VLSM.Lib Require Import Preamble ListExtras StdppExtras.
From VLSM.Core Require Import VLSM PreloadedVLSM VLSMProjections Composition.
From VLSM.Core Require Import Equivocation Validator ProjectionTraces.
From VLSM.Examples Require Import BaseELMO UMO.

(** * ELMO: Protocol Definitions and Properties for MO

  This module contains definitions and properties of MO components and
  the MO protocol.
*)

Section sec_MO.

Context
  {Address : Type}
  `{EqDecision Address}
  (State := @State Address)
  (Observation := @Observation Address)
  (Message := @Message Address).

(**
  A message is valid for MO if one of the following is the case:

  - it has no observations and its address belongs to the set of allowed
    addresses (as determined by the predicate <<P>>)
  - its last observation was another valid message which was sent
  - its last observation was another valid message which was received
    and the messages observed previously are also valid
*)
Inductive MO_msg_valid (P : Address -> Prop) : Message -> Prop :=
| MO_mv_nil :
    forall m : Message,
      obs (state m) = [] -> P (adr (state m)) -> MO_msg_valid P m
| MO_mv_send :
    forall m : Message,
      MO_msg_valid P m -> MO_msg_valid P (m <*> MkObservation Send m)
| MO_mv_recv :
    forall m mr : Message,
      MO_msg_valid P m -> MO_msg_valid P mr -> MO_msg_valid P (m <*> MkObservation Receive mr).

Section sec_alternative_definition_of_validity.

(** ** Alternative definition of validity

  The above constructors of [MO_msg_valid] may not be the most readable,
  so we will provide an alternative version of this inductive
  definition (called [MO_msg_valid_alt]) and prove them equivalent.

  If [MO_msg_valid_alt_sends] holds for <<m>>, then every possible suffix of
  observations from <<m>> is the same as the observations from a message <<m'>>
  which was the next message that was sent after the suffix. Also, the addresses
  of <<m>> and <<m'>> have to agree.
*)
Definition MO_msg_valid_alt_sends (m : Message) : Prop :=
  forall (k : nat) (suffix : list Observation) (m' : Message),
    lastn k (obs (state m)) = addObservation' (MkObservation Send m') suffix ->
      obs (state m') = suffix /\ adr (state m') = adr (state m).

(**
  If [MO_msg_valid_alt_recvs'] holds for <<valid>> and <<m>>, this means
  that for every suffix of observations from <<m>>, the message <<m'>>, which
  was the next message received after the suffix, is valid.

  Here, validity is determined by an arbitrary predicate. Ultimately, we want
  to replace this arbitrary predicate with [MO_msg_valid_alt], the alternative
  definition of message validity for MO.
*)
Definition MO_msg_valid_alt_recvs' (valid : Message -> Prop) (m : Message) : Prop :=
  forall (k : nat) (suffix : list Observation) (m' : Message),
    lastn k (obs (state m)) = addObservation' (MkObservation Receive m') suffix ->
      valid m'.

(**
  A message is valid for MO (according to the alternative definition) if one
  of the following holds:

  - its address belongs to the set of allowed addresses (as determined by <<P>>)
  - it satisfies [MO_msg_valid_alt_sends]
  - it satisfies [MO_msg_valid_alt_recvs'], with [MO_msg_valid_alt] applied to
    <<P>> used as the validity predicate
*)
Inductive MO_msg_valid_alt (P : Address -> Prop) (m : Message) : Prop :=
{
  P_adr_state : P (adr (state m));
  MO_msg_valid_alt_sends' : MO_msg_valid_alt_sends m;
  MO_msg_valid_alt_recvs'' : MO_msg_valid_alt_recvs' (MO_msg_valid_alt P) m;
}.

(**
  Now we just need to define the final version of [MO_msg_valid_alt_recvs],
  in which the validity predicate is set to [MO_msg_valid_alt].
*)
Definition MO_msg_valid_alt_recvs (P : Address -> Prop) (m : Message) : Prop :=
  MO_msg_valid_alt_recvs' (MO_msg_valid_alt P) m.

(**
  For some proofs to go through, we will need "bounded" versions of the
  [Send] and [Receive] parts of the alternative definition.

  By bounded, we mean that we will only look for suffixes at most as long
  as the whole list of observations of the given message (the suffix can't
  be any longer than that of course; this matters for purely technical
  reasons).
*)

Definition MO_msg_valid_alt_sends_bounded (m : Message) : Prop :=
  forall (k : nat) (suffix : list Observation) (m' : Message),
    k <= length (obs (state m)) ->
    lastn k (obs (state m)) = addObservation' (MkObservation Send m') suffix ->
      obs (state m') = suffix /\ adr (state m') = adr (state m).

Definition MO_msg_valid_alt_recvs_bounded (P : Address -> Prop) (m : Message) : Prop :=
  forall (k : nat) (suffix : list Observation) (m' : Message),
    k <= length (obs (state m)) ->
    lastn k (obs (state m)) = addObservation' (MkObservation Receive m') suffix ->
      MO_msg_valid_alt P m'.

(** The bounded versions are equivalent to the original ones. *)

Lemma MO_msg_valid_alt_sends_shorten :
  forall (m : Message),
    MO_msg_valid_alt_sends m <-> MO_msg_valid_alt_sends_bounded m.
Proof.
  split.
  - unfold MO_msg_valid_alt_sends, MO_msg_valid_alt_sends_bounded.
    by intros Hs k suffix m' _ Hlast; eapply Hs.
  - unfold MO_msg_valid_alt_sends, MO_msg_valid_alt_sends_bounded.
    intros Hs k suffix m' Hlast.
    destruct (decide (k <= length (obs (state m)))).
    + by eapply Hs.
    + apply (Hs (length (obs (state m)))); [lia |].
      by rewrite lastn_ge in *; [| lia | lia].
Qed.

Lemma MO_msg_valid_alt_recvs_shorten :
  forall (P : Address -> Prop) (m : Message),
    MO_msg_valid_alt_recvs P m <-> MO_msg_valid_alt_recvs_bounded P m.
Proof.
  split.
  - unfold MO_msg_valid_alt_recvs, MO_msg_valid_alt_recvs', MO_msg_valid_alt_recvs_bounded.
    by intros Hr k suffix m' _ Hlast; eapply Hr.
  - unfold MO_msg_valid_alt_recvs, MO_msg_valid_alt_recvs', MO_msg_valid_alt_recvs_bounded.
    intros Hr k suffix m' Hlast.
    destruct (decide (k <= length (obs (state m)))).
    + by eapply Hr.
    + apply (Hr (length (obs (state m))) suffix); [lia |].
      by rewrite lastn_ge in *; [| lia | lia].
Qed.

(**
  Now we need a collection of lemmas that tell us what happens when we extend
  a message with a new observation of a sent message. We need to do this
  separately for both the "sends" and the "recvs" parts of the alternative
  definition.
*)

Lemma MO_msg_valid_alt_sends_Send :
  forall m : Message,
    MO_msg_valid_alt_sends m -> MO_msg_valid_alt_sends (m <*> MkObservation Send m).
Proof.
  unfold MO_msg_valid_alt_sends; cbn; unfold addObservation'.
  intros m Hvalid k suffix m' Hlast.
  rewrite lastn_cons in Hlast; case_decide.
  - by inversion Hlast.
  - by eapply Hvalid.
Qed.

Lemma MO_msg_valid_alt_recvs_Send :
  forall (P : Address -> Prop) (m : Message),
    MO_msg_valid_alt_recvs P m -> MO_msg_valid_alt_recvs P (m <*> MkObservation Send m).
Proof.
  unfold MO_msg_valid_alt_recvs, MO_msg_valid_alt_recvs'; cbn; unfold addObservation'.
  intros P m Hvalid k suffix m' Hlast.
  rewrite lastn_cons in Hlast; case_decide.
  - by inversion Hlast.
  - by eapply Hvalid.
Qed.

(**
  When we put the above lemmas together, we get a lemma for [MO_msg_valid_alt]
  which corresponds to one of the constructors of [MO_msg_valid].
*)

Lemma MO_msg_valid_alt_Send :
  forall (P : Address -> Prop) (m : Message),
    MO_msg_valid_alt P m -> MO_msg_valid_alt P (m <*> MkObservation Send m).
Proof.
  intros P m [Hs Hr]; constructor; cbn; [done | |].
  - by apply MO_msg_valid_alt_sends_Send.
  - by apply MO_msg_valid_alt_recvs_Send.
Qed.

(** We will also need the converses of all these lemmas. *)

Lemma MO_msg_valid_alt_sends_Send_conv :
  forall m : Message,
    MO_msg_valid_alt_sends (m <*> MkObservation Send m) -> MO_msg_valid_alt_sends m.
Proof.
  intros m.
  rewrite (MO_msg_valid_alt_sends_shorten m).
  unfold MO_msg_valid_alt_sends; cbn; unfold addObservation'.
  intros Hv k suffix m' Hlen Hlast.
  destruct (decide (1 + length (obs (state m)) <= k)); [lia |].
  apply Hv with k. rewrite lastn_cons. by case_decide; [lia |].
Qed.

Lemma MO_msg_valid_alt_recvs_Send_conv :
  forall (P : Address -> Prop) (m : Message),
    MO_msg_valid_alt_recvs P (m <*> MkObservation Send m) -> MO_msg_valid_alt_recvs P m.
Proof.
  intros P m.
  rewrite (MO_msg_valid_alt_recvs_shorten P m).
  unfold MO_msg_valid_alt_recvs, MO_msg_valid_alt_recvs'; cbn; unfold addObservation'.
  intros Hv k suffix m' Hlen Hlast.
  destruct (decide (1 + length (obs (state m)) <= k)); [lia |].
  apply (Hv k suffix). rewrite lastn_cons.
  by case_decide; [lia |].
Qed.

Lemma MO_msg_valid_alt_Send_conv :
  forall (P : Address -> Prop) (m : Message),
    MO_msg_valid_alt P (m <*> MkObservation Send m) -> MO_msg_valid_alt P m.
Proof.
  intros P m [Hvs Hvr]; split; [done | |].
  - by apply MO_msg_valid_alt_sends_Send_conv.
  - by apply MO_msg_valid_alt_recvs_Send_conv.
Qed.

(**
  We need another collection of lemmas, but this time for the case when a new
  observation was a received message.
*)

Lemma MO_msg_valid_alt_sends_Receive :
  forall m mr : Message,
    MO_msg_valid_alt_sends m ->
      MO_msg_valid_alt_sends (m <*> MkObservation Receive mr).
Proof.
  unfold MO_msg_valid_alt_sends; cbn; unfold addObservation'.
  intros m mr Hm k suffix m' Hlast.
  rewrite lastn_cons in Hlast; case_decide.
  - by inversion Hlast.
  - by apply Hm with k.
Qed.

Lemma MO_msg_valid_alt_recvs_Receive :
  forall (P : Address -> Prop) (m mr : Message),
    MO_msg_valid_alt_recvs P m -> MO_msg_valid_alt P mr ->
      MO_msg_valid_alt_recvs P (m <*> MkObservation Receive mr).
Proof.
  unfold MO_msg_valid_alt_recvs, MO_msg_valid_alt_recvs'; cbn; unfold addObservation'.
  intros P m mr Hm Hmr k suffix m' Hlast.
  rewrite lastn_cons in Hlast; case_decide.
  - by inversion Hlast; subst; clear Hlast.
  - by apply (Hm k suffix).
Qed.

Lemma MO_msg_valid_alt_Receive :
  forall (P : Address -> Prop) (m mr : Message),
    MO_msg_valid_alt P m -> MO_msg_valid_alt P mr ->
      MO_msg_valid_alt P (m <*> MkObservation Receive mr).
Proof.
  intros P m mr [Hs Hr] Hmr; split; cbn; [done | |].
  - by apply MO_msg_valid_alt_sends_Receive.
  - by apply MO_msg_valid_alt_recvs_Receive.
Qed.

(** We need the converses of these lemmas too. *)

Lemma MO_msg_valid_alt_sends_Receive_conv :
  forall m mr : Message,
    MO_msg_valid_alt_sends (m <*> MkObservation Receive mr) ->
      MO_msg_valid_alt_sends m.
Proof.
  intros m mr.
  rewrite (MO_msg_valid_alt_sends_shorten m).
  unfold MO_msg_valid_alt_sends; cbn; unfold addObservation'.
  intros Hv k suffix m' Hlen Hlast.
  destruct (decide (1 + length (obs (state m)) <= k)); [lia |].
  apply Hv with k.
  by rewrite lastn_cons; case_decide; [lia |].
Qed.

Lemma MO_msg_valid_alt_recvs_Receive_conv :
  forall (P : Address -> Prop) (m mr : Message),
    MO_msg_valid_alt_recvs P (m <*> MkObservation Receive mr) ->
      MO_msg_valid_alt_recvs P m /\ MO_msg_valid_alt P mr.
Proof.
  intros P m mr.
  rewrite (MO_msg_valid_alt_recvs_shorten P m).
  unfold MO_msg_valid_alt_recvs, MO_msg_valid_alt_recvs'; cbn; unfold addObservation'.
  intros Hv; split.
  - intros k suffix m' Hlen Hlast.
    destruct (decide (1 + length (obs (state m)) <= k)); [lia |].
    apply (Hv k suffix). rewrite lastn_cons.
    by case_decide; [lia |].
  - apply (Hv (1 + length (obs (state m))) (obs (state m))).
    by rewrite lastn_ge; cbn; [| lia].
Qed.

Lemma MO_msg_valid_alt_Receive_conv :
  forall (P : Address -> Prop) (m mr : Message),
    MO_msg_valid_alt P (m <*> MkObservation Receive mr) ->
      MO_msg_valid_alt P m /\ MO_msg_valid_alt P mr.
Proof.
  intros P m mr [HP Hms Hmr]; cbn in *.
  apply MO_msg_valid_alt_sends_Receive_conv in Hms.
  apply MO_msg_valid_alt_recvs_Receive_conv in Hmr as [].
  by split; [constructor |].
Qed.

(**
  Last but not least, we need an inversion lemma which tells us that,
  if from the state of a message <<m1>> we sent the message <<m2>>, then
  <<m1>> must be equal to <<m2>>.
*)
Lemma MO_msg_valid_alt_Send_inv :
  forall (P : Address -> Prop) (m1 m2 : Message),
    MO_msg_valid_alt P (m1 <*> MkObservation Send m2) -> m1 = m2.
Proof.
  intros P m1 m2 [_ Hvs _].
  unfold MO_msg_valid_alt_sends in Hvs; cbn in *; unfold addObservation' in Hvs.
  specialize (Hvs (1 + length (obs (state m1))) (obs (state m1)) m2).
  rewrite lastn_cons in Hvs; case_decide; [| lia].
  destruct (Hvs eq_refl) as [].
  by destruct m1 as [[]], m2 as [[]]; cbn in *; congruence.
Qed.

(**
  We now have, by previous lemmas, that [MO_msg_valid] and [MO_msg_valid_alt]
  are equivalent. The proof of the equivalence lemma is structured as follows:

  - the [MO_msg_valid] to [MO_msg_valid_alt] direction is by induction on
    [MO_msg_valid] for <<P>> and <<m>>
  - the [MO_msg_valid_alt] to [MO_msg_valid] direction is by well-founded
    induction on the size of the message <<m>>
*)
Lemma MO_msg_valid__MO_msg_valid_alt :
  forall (P : Address -> Prop) (m : Message),
    MO_msg_valid P m <-> MO_msg_valid_alt P m.
Proof.
  split; [| revert m].
  - induction 1 as [m Hobs | m Hm IH | m mr Hm IHm Hmr IHmr].
    + by constructor; [done | |]
      ; intros k suffix m' Hlast
      ; rewrite Hobs, lastn_nil in Hlast; inversion Hlast.
    + by apply MO_msg_valid_alt_Send.
    + by apply MO_msg_valid_alt_Receive.
  - assert (Hwf := well_founded_lt_compat _ (fun m => @sizeMessage Address m)
      (fun m1 m2 => sizeMessage m1 < sizeMessage m2) (fun _ _ H => H)).
    apply (@well_founded_induction _ (fun m1 m2 => sizeMessage m1 < sizeMessage m2) Hwf
      (fun m => MO_msg_valid_alt P m -> MO_msg_valid P m)).
    intros [[[| [[] m'] obs'] adr']] IH Hvalid.
    + by constructor; [| inversion Hvalid].
    + change (MkMessage _) with (MkMessage (MkState obs' adr') <*> MkObservation Receive m') in *.
      apply MO_msg_valid_alt_Receive_conv in Hvalid as [].
      by constructor 3; (apply IH; [unfold sizeMessage; cbn; lia |]).
    + change (MkMessage _) with (MkMessage (MkState obs' adr') <*> MkObservation Send m') in *.
      replace (MkMessage (MkState obs' adr')) with m' in *
        by (apply MO_msg_valid_alt_Send_inv in Hvalid; done).
      apply MO_msg_valid_alt_Send_conv in Hvalid.
      by constructor 2; apply IH; [unfold sizeMessage; cbn; lia |].
Qed.

End sec_alternative_definition_of_validity.

Inductive MO_component_valid (P : Address -> Prop) : Label -> State -> option Message -> Prop :=
| MOCV_Receive :
    forall (s : State) (m : Message),
      MO_msg_valid P m -> MO_component_valid P Receive s (Some m)
| MOCV_Send :
    forall s : State,
      MO_component_valid P Send s None.

Ltac invert_MO_component_valid :=
repeat match goal with
| H : MO_component_valid _ Receive _ None  |- _ => inversion H; subst; clear H
| H : MO_component_valid _ Send _ (Some _) |- _ => inversion H; subst; clear H
end.

Definition MO_component_machine (P : Address -> Prop) (i : Address) : VLSMMachine ELMO_component_type :=
{|
  initial_state_prop := UMO_component_initial_state_prop i;
  initial_message_prop := const False;
  s0 := Inhabited_UMO_component_initial_state_type i;
  transition := fun l '(st, om) => UMO_component_transition l st om;
  valid := fun l '(st, om) => MO_component_valid P l st om;
|}.

Definition MO_component (P : Address -> Prop) (i : Address) : VLSM Message :=
{|
  vlsm_type := ELMO_component_type;
  vlsm_machine := MO_component_machine P i;
|}.

Section sec_MO_component_lemmas.

(** ** Component lemmas

  We will use the notation [Mi] for a [MO_component] of address [i].

  We will use [RMi] to denote the corresponding pre-loaded VLSM, which is
  used to model reachability.

  There is a VLSM inclusion from [Mi] to [RMi].
*)

Context
  {i : Address}
  {P : Address -> Prop}
  (Mi : VLSM Message := MO_component P i)
  (RMi : VLSM Message := pre_loaded_with_all_messages_vlsm Mi).

(** The VLSM [Mi] embeds into [RMi]. *)
Lemma VLSM_incl_MO_component_preloaded :
  VLSM_incl_part Mi RMi.
Proof.
  by apply vlsm_incl_pre_loaded_with_all_messages_vlsm.
Qed.

Lemma VLSM_incl_UMO_MOComponent : VLSM_incl Mi (UMO_component i).
Proof.
  intros; apply basic_VLSM_strong_incl.
  - by intro.
  - by intro.
  - by inversion 1; subst; constructor.
  - by intro.
Qed.

#[export] Instance HasBeenSentCapability_MOComponent : HasBeenSentCapability Mi.
Proof.
  constructor 1 with (fun s m => m ∈ sentMessages s);
    [by intros s m; typeclasses eauto |].
  split; [by intros [] []; cbn in *; subst; cbn; apply not_elem_of_nil |].
  intros l s im s' om [(Hvsp & Hovmp & Hv) Ht] m; cbn in *.
  destruct l, im; cbn in *; invert_MO_component_valid;
    inversion Ht; subst; clear Ht; cbn.
  - by rewrite decide_False; cbn; firstorder congruence.
  - rewrite decide_True by done; cbn.
    unfold Message; rewrite elem_of_cons.
    by firstorder congruence.
Defined.

#[export] Instance HasBeenReceivedCapability_MOComponent : HasBeenReceivedCapability Mi.
Proof.
  constructor 1 with (fun s m => m ∈ receivedMessages s);
    [by intros s m; typeclasses eauto |].
  split; [by intros [] []; cbn in *; subst; cbn; apply not_elem_of_nil |].
  intros l s im s' om [(Hvsp & Hovmp & Hv) Ht] m; cbn in *.
  destruct l, im; cbn in *; invert_MO_component_valid;
    inversion Ht; subst; clear Ht; cbn.
  - rewrite decide_True by done; cbn.
    unfold Message; rewrite elem_of_cons.
    by firstorder congruence.
  - by rewrite decide_False; cbn; firstorder congruence.
Defined.

#[export] Instance HasBeenDirectlyObservedCapability_MOComponent :
  HasBeenDirectlyObservedCapability Mi :=
    HasBeenDirectlyObservedCapability_from_sent_received Mi.

(** The initial state of [RMi] is unique. *)
Lemma vs0_uniqueness :
  forall is : State,
    UMO_component_initial_state_prop i is ->
      is = ``(vs0 RMi).
Proof.
  by intros []; inversion 1; cbv in *; subst.
Qed.

(** *** Properties of transitions and traces *)

(** In a valid state <<s>>, we can send a message containing this state. *)
Lemma input_constrained_transition_Send :
  forall s : State,
    constrained_state_prop Mi s ->
      input_constrained_transition Mi Send
        (s, None)
        (s <+> MkObservation Send (MkMessage s), Some (MkMessage s)).
Proof.
  intros s Hvsp.
  do 2 red; cbn; split_and!; [done | | | done].
  - by exists (MkState [] i); constructor.
  - by do 2 constructor.
Qed.

(** In a valid state <<s>>, we can receive any valid message. *)
Lemma input_constrained_transition_Receive :
  forall (s : State) (m : Message),
    constrained_state_prop Mi s -> MO_msg_valid P m ->
      input_constrained_transition Mi Receive
        (s, Some m)
        (s <+> MkObservation Receive m, None).
Proof.
  intros s m Hvsp Hvalid.
  do 2 red; cbn; split_and!; [done | | | done].
  - by exists (MkState [] i); constructor; cbn; [| right].
  - by constructor.
Qed.

(** If a message <<m>> is valid, its [state] is reachable. *)
Lemma constrained_state_prop_MO_msg_valid :
  forall m : Message,
    MO_msg_valid P m -> adr (state m) = i ->
      constrained_state_prop Mi (state m).
Proof.
  induction 1 as [m Hobs | m Hm IH | m mr Hm IHm Hmr IHmr]; cbn; intros Hadr.
  - by exists None; constructor.
  - apply (@input_valid_transition_destination _ RMi Send (state m) _ None (Some m)).
    destruct m as [s]; cbn in *.
    by apply input_constrained_transition_Send, IH.
  - apply (@input_valid_transition_destination _ RMi Receive (state m) _ (Some mr) None).
    destruct m as [s]; cbn in *.
    by apply input_constrained_transition_Receive; itauto.
Qed.

(** Valid transitions and valid traces lead to bigger states. *)

Lemma MO_component_valid_transition_size :
  forall (s1 s2 : State) (iom oom : option Message) (lbl : Label),
    MO_component_valid P lbl s1 iom ->
    UMO_component_transition lbl s1 iom = (s2, oom) ->
      sizeState s1 < sizeState s2.
Proof.
  by intros [] s2 [im |] oom []; do 2 inversion_clear 1; cbn; lia.
Qed.

Lemma input_constrained_transition_size :
  forall (s1 s2 : State) (iom oom : option Message) (lbl : Label),
    input_constrained_transition Mi lbl (s1, iom) (s2, oom) ->
      sizeState s1 < sizeState s2.
Proof.
  by intros s1 s2 iom oom lbl [(_ & _ & ?) Ht]; cbn in *
  ; eapply MO_component_valid_transition_size.
Qed.

Lemma finite_constrained_trace_from_to_size :
  forall (s1 s2 : State) (tr : list transition_item),
    finite_constrained_trace_from_to Mi s1 s2 tr ->
      s1 = s2 /\ tr = []
        \/
      sizeState s1 < sizeState s2.
Proof.
  induction 1; [by left |].
  assert (sizeState s' < sizeState s)
      by (eapply input_constrained_transition_size; done).
  by destruct IHfinite_valid_trace_from_to; [itauto congruence | itauto lia].
Qed.

(**
  The final state of a valid transition determines the label, initial state,
  input message and output message.
*)
Lemma input_constrained_transition_deterministic_conv :
  forall (s1 s2 f : State) (iom1 iom2 oom1 oom2 : option Message) (lbl1 lbl2 : Label),
    input_constrained_transition Mi lbl1 (s1, iom1) (f, oom1) ->
    input_constrained_transition Mi lbl2 (s2, iom2) (f, oom2) ->
      lbl1 = lbl2 /\ s1 = s2 /\ iom1 = iom2 /\ oom1 = oom2.
Proof.
  intros s1 s2 f iom1 iom2 oom1 oom2 lbl1 lbl2 Hivt1 Hivt2
  ; inversion Hivt1 as [(_ & _ & Hvalid1) Ht1]; subst
  ; inversion Hivt2 as [(_ & _ & Hvalid2) Ht2]; subst.
  destruct lbl1, lbl2, iom1, iom2; cbn in *
  ; inversion Ht1; subst; clear Ht1
  ; inversion Ht2; subst; clear Ht2
  ; inversion Hvalid1; inversion Hvalid2; invert_MO_component_valid; auto.
  by destruct s1, s2; cbn in *; subst; itauto.
Qed.

(** Trace segments between any two states are unique. *)
Lemma finite_constrained_trace_from_to_unique :
  forall (s1 s2 : State) (tr1 tr2 : list transition_item),
    finite_constrained_trace_from_to Mi s1 s2 tr1 ->
    finite_constrained_trace_from_to Mi s1 s2 tr2 ->
      tr1 = tr2.
Proof.
  intros s1 s2 tr1 tr2 Hfvt1 Hfvt2; revert tr2 Hfvt2.
  induction Hfvt1 using finite_valid_trace_from_to_rev_ind; intros.
  - by apply finite_constrained_trace_from_to_size in Hfvt2; itauto (congruence + lia).
  - destruct Hfvt2 using finite_valid_trace_from_to_rev_ind; [| clear IHHfvt2].
    + apply finite_constrained_trace_from_to_size in Hfvt1.
      apply input_constrained_transition_size in Ht.
      by decompose [and or] Hfvt1; subst; clear Hfvt1; lia.
    + assert (l = l0 /\ s = s0 /\ iom = iom0 /\ oom = oom0)
          by (eapply input_constrained_transition_deterministic_conv; done).
      decompose [and] H; subst; clear H.
      by f_equal; apply IHHfvt1.
Qed.

(** Traces between any two states are unique. *)

Lemma finite_constrained_trace_init_to_unique :
  forall (s1 s2 s : State) (tr1 tr2 : list transition_item),
    finite_constrained_trace_init_to Mi s1 s tr1 ->
    finite_constrained_trace_init_to Mi s2 s tr2 ->
      tr1 = tr2.
Proof.
  intros [] [] s tr1 tr2 [Ht1 []] [Ht2 []]; cbn in *; subst.
  by eapply finite_constrained_trace_from_to_unique.
Qed.

(** All above properties also hold for [Mi]. *)

Lemma input_valid_transition_Send :
  forall s : State,
    valid_state_prop Mi s ->
      input_valid_transition Mi Send
        (s, None)
        (s <+> MkObservation Send (MkMessage s), Some (MkMessage s)).
Proof.
  intros s Hvsp.
  red; cbn; split_and!; [done | | | done].
  - by exists (MkState [] i); constructor.
  - by do 2 constructor.
Qed.

Lemma input_valid_transition_size :
  forall (s1 s2 : State) (iom oom : option Message) (lbl : Label),
    input_valid_transition Mi lbl (s1, iom) (s2, oom) ->
      sizeState s1 < sizeState s2.
Proof.
  intros s1 s2 iom oom lbl Hivt.
  eapply input_constrained_transition_size.
  by apply (@VLSM_incl_input_valid_transition _ Mi Mi RMi)
  ; eauto using VLSM_incl_MO_component_preloaded.
Qed.

Lemma finite_valid_trace_from_to_size :
  forall (s1 s2 : State) (tr : list transition_item),
    finite_valid_trace_from_to Mi s1 s2 tr ->
      s1 = s2 /\ tr = []
        \/
      sizeState s1 < sizeState s2.
Proof.
  intros s1 s2 tr Hfvt.
  eapply finite_constrained_trace_from_to_size.
  by apply (@VLSM_incl_finite_valid_trace_from_to _ Mi Mi RMi)
  ; eauto using VLSM_incl_MO_component_preloaded.
Qed.

Lemma input_valid_transition_deterministic_conv :
  forall (s1 s2 f : State) (iom1 iom2 oom1 oom2 : option Message) (lbl1 lbl2 : Label),
    input_valid_transition Mi lbl1 (s1, iom1) (f, oom1) ->
    input_valid_transition Mi lbl2 (s2, iom2) (f, oom2) ->
      lbl1 = lbl2 /\ s1 = s2 /\ iom1 = iom2 /\ oom1 = oom2.
Proof.
  intros s1 s2 f iom1 iom2 oom1 oom2 lbl1 lbl2 Hivt1 Hivt2.
  by eapply input_constrained_transition_deterministic_conv
  ; apply (@VLSM_incl_input_valid_transition _ Mi Mi RMi)
  ; eauto using VLSM_incl_MO_component_preloaded.
Qed.

Lemma finite_valid_trace_from_to_unique :
  forall (s1 s2 : State) (l1 l2 : list transition_item),
    finite_valid_trace_from_to Mi s1 s2 l1 ->
    finite_valid_trace_from_to Mi s1 s2 l2 ->
      l1 = l2.
Proof.
  by intros s1 s2 l1 l2 Hfvt1 Hfvt2
  ; eapply finite_constrained_trace_from_to_unique
  ; apply VLSM_incl_finite_valid_trace_from_to
  ; eauto using VLSM_incl_MO_component_preloaded.
Qed.

Lemma finite_valid_trace_init_to_unique :
  forall (s f : State) (l1 l2 : list transition_item),
    finite_valid_trace_init_to Mi s f l1 ->
    finite_valid_trace_init_to Mi s f l2 ->
      l1 = l2.
Proof.
  by intros s f l1 l2 Hfvit1 Hfvit2
  ; eapply finite_constrained_trace_init_to_unique
  ; apply VLSM_incl_finite_valid_trace_init_to
  ; eauto using VLSM_incl_MO_component_preloaded.
Qed.

(** *** Extracting a trace from a state *)

(** If a valid trace leads to state s, the trace extracted from s also leads to s. *)

Lemma finite_constrained_trace_init_to_state2trace :
  forall (is s : State) (tr : list transition_item),
    finite_constrained_trace_init_to Mi is s tr ->
      finite_constrained_trace_init_to Mi is s (state2trace s).
Proof.
  intros is s tr [Hfv Hinit]; cbn in *; revert Hinit.
  induction Hfv using finite_valid_trace_from_to_rev_ind; intros.
  - inversion Hinit; clear Hinit.
    destruct si; cbn in *; subst; cbn.
    repeat constructor. exists None.
    by repeat constructor.
  - specialize (IHHfv Hinit).
    destruct Ht as [Hvalid Ht]; cbn in Ht.
    destruct s as [obs adr], l, iom as [im |]
    ; inversion Ht; subst; clear Ht; cbn in *
    ; cycle 1; [done | done | |].
    + constructor; [| done].
      by eapply extend_right_finite_trace_from_to; [apply IHHfv |]; auto.
    + constructor; [| done].
      by eapply extend_right_finite_trace_from_to; [apply IHHfv |]; auto.
Qed.

(** The trace extracted from the final state of another trace is equal to that trace. *)

Lemma finite_constrained_trace_init_to_state2trace_inv :
  forall (is s : State) (tr : list transition_item),
    finite_constrained_trace_init_to Mi is s tr ->
      state2trace s = tr.
Proof.
  intros is s tr Hfvti.
  assert (Hfvti' : finite_constrained_trace_init_to Mi is s (state2trace s))
      by (eapply finite_constrained_trace_init_to_state2trace; done).
  by eapply finite_constrained_trace_init_to_unique.
Qed.

(** The trace extracted from a constrained state <<s>> leads to <<s>>. *)

Lemma finite_constrained_trace_init_to_state2trace' :
  forall (s : State),
    constrained_state_prop Mi s ->
      finite_constrained_trace_init_to Mi (``(vs0 RMi)) s (state2trace s).
Proof.
  intros s Hs.
  apply valid_state_has_trace in Hs as (is & tr & Htr).
  apply finite_constrained_trace_init_to_state2trace_inv in Htr as Heqtr; subst.
  replace (``(vs0 RMi)) with is; [done |].
  by apply vs0_uniqueness, Htr.
Qed.

Lemma constrained_state_contains_unique_constrained_trace :
  forall s : State,
    constrained_state_prop Mi s ->
      exists tr : list transition_item,
        finite_constrained_trace_init_to Mi (``(vs0 RMi)) s tr
          /\
        forall tr' : list transition_item,
          finite_constrained_trace_init_to Mi (``(vs0 RMi)) s tr' -> tr' = tr.
Proof.
  intros s Hvsp.
  exists (state2trace s); split.
  - by eapply finite_constrained_trace_init_to_state2trace'.
  - intros tr' Hfvt. symmetry.
    by eapply finite_constrained_trace_init_to_state2trace_inv.
Qed.

(** *** State and message suffix relations *)

Lemma state_suffix_totally_orders_valid_sent_messages :
  forall (m m1 m2 : Message) (obs1 obs2 obs3 : list Observation),
    m = MkMessage (MkState [] i) <**>
      obs1 <*> MkObservation Send m1 <**> obs2 <*> MkObservation Send m2 <**> obs3 ->
    MO_msg_valid_alt_sends m ->
      state_suffix (state m1) (state m2) /\ state_suffix (state m2) (state m).
Proof.
  intros m m1 m2 obs1 obs2 obs3 Heq Hvalid.
  red in Hvalid.
  assert (H2 :
    obs (state m2) =
    obs (state (MkMessage (MkState [] i) <**> obs1 <*> MkObservation Send m1 <**> obs2))
    /\ adr (state m2) = i).
  {
    replace i with (adr (state m)) at 2 by (subst; done).
    apply (Hvalid (1 + length
      (obs (state (MkMessage (MkState [] i) <**> obs1 <*> MkObservation Send m1 <**> obs2))))).
    rewrite Heq; simpl.
    rewrite lastn_app_le by (cbn; lia).
    by rewrite lastn_ge; [| cbn; lia].
  }
  assert (H1 :
    obs (state m1) = obs (state (MkMessage (MkState [] i) <**> obs1))
    /\ adr (state m1) = i).
  {
    replace i with (adr (state m)) at 2 by (subst; done).
    apply (Hvalid (1 + length (obs (state (MkMessage (MkState [] i) <**> obs1))))).
    rewrite Heq; simpl.
    unfold addObservation'.
    rewrite <- (app_cons (MkObservation Send m2)),
            <- (app_cons (MkObservation Send m1)), 2!app_assoc.
    rewrite lastn_app_le by (cbn; lia).
    by rewrite lastn_ge; [| cbn; lia].
  }
  destruct H1 as [H11 H12], H2 as [H21 H22].
  split.
  - constructor; [by congruence |].
    rewrite H11, H21; cbn.
    split.
    + by apply suffix_app_r, suffix_cons_r.
    + intros []. apply (f_equal length) in H.
      rewrite !app_length in H; cbn in H; rewrite app_length in H; cbn in H.
      by lia.
  - constructor; [by subst |].
    rewrite H21, Heq; cbn.
    split.
    + by apply suffix_app_r, suffix_cons_r.
    + intros []. apply (f_equal length) in H.
      unfold addObservation' in H.
      by rewrite <- (app_cons (MkObservation _ m1)),
                 <- (app_cons (MkObservation _ m2)), !app_length in H
      ; cbn in H; lia.
Qed.

Definition MO_msg_suffix (m : Message) : Prop :=
  forall k1 k2 : nat, k1 < k2 ->
  forall ob1 ob2 : Observation,
    obs (state m) !! k1 = Some ob1 -> label ob1 = Send ->
    obs (state m) !! k2 = Some ob2 -> label ob2 = Send ->
      state_suffix (state (message ob2)) (state (message ob1)).

Lemma state_suffix_totally_orders_valid_sent_messages' :
  forall m : Message, MO_msg_valid_alt_sends m -> MO_msg_suffix m.
Proof.
  unfold MO_msg_valid_alt_sends, MO_msg_suffix.
  intros m H k1 k2 Hlt ob1 ob2 Heq1 Hlbl1 Heq2 Hlbl2.
  remember (length (obs (state m))) as K.
  destruct (H (K - k1) (lastn (K - S k1) (obs (state m))) (message ob1)) as [Hobs1 Hadr1]
  ; [by destruct ob1; cbn in *; subst; apply lastn_length_cons |].
  destruct (H (K - k2) (lastn (K - S k2) (obs (state m))) (message ob2)) as [Hobs2 Hadr2]
  ; [by destruct ob2; cbn in *; subst; apply lastn_length_cons |].
  constructor; [by congruence |].
  constructor; rewrite Hobs1, Hobs2.
  - by apply suffix_lastn; lia.
  - intros Hsuf. apply suffix_length in Hsuf.
    rewrite 2!length_lastn in Hsuf.
    apply lookup_lt_Some in Heq1, Heq2.
    unfold Observation in *.
    by destruct (Nat.min_spec (K - S k1) (length (obs (state m)))) as [[H11 H12] | [H11 H12]],
             (Nat.min_spec (K - S k2) (length (obs (state m)))) as [[H21 H22] | [H21 H22]]
    ; rewrite ?H12, ?H22 in Hsuf; lia.
Qed.

End sec_MO_component_lemmas.

Section sec_MOProtocol.

Context
  (index : Type)
  `{finite.Finite index}
  (idx : index -> Address)
  `{!Inj (=) (=) idx}
  (P : Address -> Prop)
  (P' := fun adr => P adr /\ exists i : index, idx i = adr)
  (M : index -> VLSM Message := fun i => MO_component P' (idx i))
  (RM : index -> VLSM Message := fun i => pre_loaded_with_all_messages_vlsm (M i)).

(** ** Protocol

  The MO protocol is a free composition of finitely many MO components (each
  with the same predicate <<P>>.

  To talk about reachable states in the MO protocol, we will use [RMO],
  which is MO preloaded with all messages.
*)

Definition MO : VLSM Message := free_composite_vlsm M.
Definition RMO : VLSM Message := pre_loaded_with_all_messages_vlsm MO.

(** We set up aliases for some functions operating on free VLSM composition. *)

Definition MO_state : Type := composite_state M.
Definition MO_label : Type := composite_label M.
Definition MO_transition_item : Type := composite_transition_item M.

(** We can lift labels, states and traces from an MO component to the MO protocol. *)

Definition lift_to_MO_label
  (i : index) (li : VLSM.label (M i)) : MO_label :=
    lift_to_composite_label M i li.

Definition lift_to_MO_state
  (us : MO_state) (i : index) (si : VLSM.state (M i)) : MO_state :=
    lift_to_composite_state M us i si.

Definition lift_to_MO_trace
  (us : MO_state) (i : index) (tr : list (transition_item (M i)))
  : list MO_transition_item :=
    pre_VLSM_embedding_finite_trace_project
      _ _ (lift_to_MO_label i) (lift_to_MO_state us i) tr.

#[local] Hint Rewrite @state_update_twice : state_update.

#[local] Hint Unfold lift_to_MO_label : state_update.
#[local] Hint Unfold lift_to_MO_state : state_update.
#[local] Hint Unfold lift_to_MO_trace : state_update.

(**
  We can also lift properties from MO components to the MO protocol, among
  them [valid_state_prop], [valid_message_prop], [input_valid_transition]
  and the various kinds of traces.
*)

Lemma lift_to_MO :
  forall (us : MO_state) (Hus : valid_state_prop MO us) (i : index),
    VLSM_weak_embedding (M i) MO (lift_to_MO_label i) (lift_to_MO_state us i).
Proof. by intros; apply lift_to_free_weak_embedding. Qed.

Lemma lift_to_MO_valid_state_prop :
  forall (i : index) (s : State) (us : MO_state),
    valid_state_prop MO us -> valid_state_prop (M i) s ->
      valid_state_prop MO (lift_to_MO_state us i s).
Proof.
  intros is s us Hvsp.
  by eapply VLSM_weak_embedding_valid_state, lift_to_MO.
Qed.

Lemma lift_to_MO_valid_message_prop :
  forall (i : index) (om : option Message),
    option_valid_message_prop (M i) om ->
      option_valid_message_prop MO om.
Proof.
  intros i [] Hovmp; cycle 1.
  - by exists (``(vs0 MO)); constructor.
  - eapply VLSM_weak_embedding_valid_message.
    + by apply (lift_to_MO (``(vs0 MO))); exists None; constructor.
    + by inversion 1.
    + by apply Hovmp.
Qed.

Lemma lift_to_MO_input_valid_transition :
  forall (i : index) (lbl : Label) (s1 s2 : State) (iom oom : option Message) (us : MO_state),
    valid_state_prop MO us ->
    input_valid_transition (M i) lbl (s1, iom) (s2, oom) ->
      input_valid_transition MO
        (lift_to_MO_label i lbl)
        (lift_to_MO_state us i s1, iom)
        (lift_to_MO_state us i s2, oom).
Proof.
  intros i lbl s1 s2 iom oom us Hivt.
  by apply @VLSM_weak_embedding_input_valid_transition, lift_to_MO.
Qed.

Lemma lift_to_MO_finite_valid_trace_from_to :
  forall (i : index) (s1 s2 : State) (tr : list (transition_item (M i))) (us : MO_state),
    valid_state_prop MO us ->
    finite_valid_trace_from_to (M i) s1 s2 tr ->
      finite_valid_trace_from_to
        MO (lift_to_MO_state us i s1) (lift_to_MO_state us i s2) (lift_to_MO_trace us i tr).
Proof.
  intros i s1 s2 tr us Hvsp Hfvt.
  by eapply (VLSM_weak_embedding_finite_valid_trace_from_to (lift_to_MO _ Hvsp i)).
Qed.

(** We could prove the same lifting lemmas for [RMO], but we won't need them. *)

Lemma lift_to_RMO
  (us : MO_state) (Hus : valid_state_prop RMO us) (i : index) :
  VLSM_weak_embedding (RM i) RMO (lift_to_MO_label i) (lift_to_MO_state us i).
Proof. by apply lift_to_preloaded_free_weak_embedding. Qed.

Lemma lift_to_RMO_valid_state_prop :
  forall (i : index) (s : State) (us : MO_state),
    valid_state_prop RMO us -> valid_state_prop (RM i) s ->
      valid_state_prop RMO (lift_to_MO_state us i s).
Proof.
  intros is s us Hvsp.
  by eapply VLSM_weak_embedding_valid_state, lift_to_RMO.
Qed.

Lemma lift_to_RMO_valid_message_prop :
  forall (i : index) (om : option Message),
    option_valid_message_prop (RM i) om ->
      option_valid_message_prop RMO om.
Proof.
  intros i [] Hovmp; cycle 1.
  - by exists (``(vs0 MO)); constructor.
  - eapply VLSM_weak_embedding_valid_message.
    + by apply (lift_to_RMO (``(vs0 MO))); exists None; constructor.
    + by inversion 1; cbn; [| right].
    + by apply Hovmp.
Qed.

Lemma lift_to_RMO_input_valid_transition :
  forall (i : index) (lbl : Label) (s1 s2 : State) (iom oom : option Message) (us : MO_state),
    valid_state_prop RMO us ->
    input_valid_transition (RM i) lbl (s1, iom) (s2, oom) ->
      input_valid_transition RMO
        (lift_to_MO_label i lbl)
        (lift_to_MO_state us i s1, iom)
        (lift_to_MO_state us i s2, oom).
Proof.
  intros i lbl s1 s2 iom oom us Hivt.
  by apply @VLSM_weak_embedding_input_valid_transition, lift_to_RMO.
Qed.

Lemma lift_to_RMO_finite_valid_trace_from_to :
  forall (i : index) (s1 s2 : State) (tr : list (transition_item (RM i))) (us : MO_state),
    valid_state_prop RMO us ->
    finite_valid_trace_from_to (RM i) s1 s2 tr ->
      finite_valid_trace_from_to
        RMO (lift_to_MO_state us i s1) (lift_to_MO_state us i s2) (lift_to_MO_trace us i tr).
Proof.
  intros i s1 s2 tr us Hvsp Hfvt.
  by apply (VLSM_weak_embedding_finite_valid_trace_from_to (lift_to_RMO _ Hvsp i)).
Qed.

(** *** Lifting lemmas for validating theorem *)

Lemma initial_state_prop_lift_RM_to_MO :
  forall (i : index) (s : State),
    initial_state_prop (RM i) s ->
      initial_state_prop MO (lift_to_MO_state (``(vs0 MO)) i s).
Proof.
  intros i s Hisp j; cbn.
  by destruct (decide (i = j)); subst; state_update_simpl.
Qed.

Lemma finite_valid_trace_lift_RM_to_MO :
  forall (i : index) (s : State),
    initial_state_prop (RM i) s ->
      finite_valid_trace_init_to MO
        (lift_to_MO_state (``(vs0 MO)) i s) (lift_to_MO_state (``(vs0 MO)) i s) [].
Proof.
  constructor; cycle 1.
  - by apply initial_state_prop_lift_RM_to_MO.
  - constructor; exists None; constructor; [| done].
    by apply initial_state_prop_lift_RM_to_MO.
Qed.

Lemma option_valid_message_prop_initial :
  forall i : index,
    option_valid_message_prop MO (Some (MkMessage (MkState [] (idx i)))).
Proof.
  intros i.
  remember (MkMessage (MkState [] (idx i))) as m.
  exists (state_update M (``(vs0 MO)) i (state m <+> MkObservation Send m)).
  by econstructor 2 with
    (s := ``(vs0 MO)) (_om := None) (_s := ``(vs0 MO)) (om := None) (l := existT i Send);
    [by repeat split; constructor.. | rewrite Heqm].
Qed.

Lemma option_valid_message_prop_addObservationToMessage_Send :
  forall m : Message,
    option_valid_message_prop MO (Some m) ->
      option_valid_message_prop MO (Some (m <*> MkObservation Send m)).
Proof.
  intros m [s' IH].
  inversion IH; subst; [by inversion Hom as [j []]; inversion x |].
  destruct l as [k []], om as [m' |];
    inversion Hv; subst; clear Hv;
    inversion Ht; subst; clear Ht.
  unfold addObservationToMessage; cbn; red.
  remember (s k <+> MkObservation Send (MkMessage (s k))) as sk'.
  remember (state_update M s k sk') as ss.
  assert (Heq : ss k = sk') by (subst; state_update_simpl; done).
  rewrite <- Heq in *; clear Heqsk'.
  exists (state_update M ss k (ss k <+> MkObservation Send (MkMessage (ss k)))).
  by econstructor 2 with (s := ss) (_s := ``(vs0 MO)) (om := None) (l := existT k Send);
    [| constructor | repeat split; constructor |].
Qed.

Lemma option_valid_message_prop_addObservationToMessage_Receive :
  forall m mr : Message,
    MO_msg_valid P' mr ->
    option_valid_message_prop MO (Some m) ->
    option_valid_message_prop MO (Some mr) ->
      option_valid_message_prop MO (Some (m <*> MkObservation Receive mr)).
Proof.
  intros m mr Hvalid [sm IH1] [smr IH2].
  inversion IH1; subst; [by inversion Hom as [j []]; inversion x |].
  destruct l as [k []], om as [m' |];
    inversion Hv; subst; clear Hv;
    inversion Ht; subst; clear Ht.
  exists (state_update M s k (s k <+> MkObservation Receive mr <+>
    MkObservation Send (MkMessage (s k <+> MkObservation Receive mr)))).
  econstructor 2 with
    (s := state_update M s k (s k <+> MkObservation Receive mr)) (_om := None)
    (_s := ``(vs0 MO)) (om := None) (l := existT k Send); cycle 1.
  - by constructor.
  - by repeat split; constructor.
  - by cbn; state_update_simpl.
  - by econstructor 2 with (s := s) (om := Some mr) (l := existT k Receive);
      [| | repeat split; constructor |].
Qed.

Lemma option_valid_message_prop_MO_msg_valid :
  forall m : Message,
    MO_msg_valid P' m -> option_valid_message_prop MO (Some m).
Proof.
  induction 1.
  - destruct H1 as (_ & i & Heq).
    replace m with (MkMessage (MkState [] (idx i))) by (apply eq_Message; done).
    by apply option_valid_message_prop_initial.
  - by apply option_valid_message_prop_addObservationToMessage_Send.
  - by apply option_valid_message_prop_addObservationToMessage_Receive.
Qed.

Lemma lift_to_MO_finite_valid_trace_init_to :
  forall (i : index) (s1 s2 : State) (tr : list (transition_item (M i))),
    finite_valid_trace_init_to (RM i) s1 s2 tr ->
      finite_valid_trace_init_to MO (lift_to_MO_state (``(vs0 MO)) i s1)
        (lift_to_MO_state (``(vs0 MO)) i s2) (lift_to_MO_trace (``(vs0 MO)) i tr).
Proof.
  intros i s1 s2 tr [Hfvt Hisp].
  induction Hfvt using finite_valid_trace_from_to_rev_ind; cbn;
    [by apply finite_valid_trace_lift_RM_to_MO |].
  constructor; [| by apply initial_state_prop_lift_RM_to_MO].
  unfold lift_to_MO_trace, pre_VLSM_embedding_finite_trace_project.
  rewrite map_app.
  eapply finite_valid_trace_from_to_app; cbn; [by apply IHHfvt |].
  apply valid_trace_add_last; [| done].
  apply first_transition_valid; cbn.
  destruct Ht as [(Hvsp & _ & Hvalid) Ht], l, iom as [im |]; cbn in *;
    inversion Hvalid; subst; clear Hvalid;
    inversion Ht; subst; cbn in *; clear Ht; cycle 1.
  - repeat split.
    + by eapply finite_valid_trace_from_to_last_pstate, IHHfvt.
    + by apply option_valid_message_None.
    + by constructor.
    + by cbn; state_update_simpl.
  - repeat split.
    + by eapply finite_valid_trace_from_to_last_pstate, IHHfvt.
    + by apply option_valid_message_prop_MO_msg_valid.
    + by constructor.
    + by cbn; state_update_simpl.
Qed.

Lemma lift_RM_to_MO :
  forall i : index,
    VLSM_embedding (RM i) MO (lift_to_MO_label i) (lift_to_MO_state (``(vs0 MO)) i).
Proof.
  constructor; intros.
  by eapply valid_trace_forget_last, lift_to_MO_finite_valid_trace_init_to,
    valid_trace_add_default_last.
Qed.

(**
  Every state in a MO component gives rise to a unique trace leading to this
  state, which we can then lift to the MO protocol.
*)
Definition MO_component_state2trace
  (s : MO_state) (i : index) : list MO_transition_item :=
    lift_to_MO_trace s i (state2trace (s i)).

(**
  Iterating [MO_component_state2trace] shows that every reachable MO state contains a
  trace that leads to this state. However, this trace is not unique, because
  we can concatenate the lifted traces in any order.
*)
Fixpoint MO_state2trace_aux
  (us : MO_state) (is : list index) : list MO_transition_item :=
  match is with
  | [] => []
  | i :: is' =>
    MO_state2trace_aux (state_update _ us i (MkState [] (idx i))) is' ++ MO_component_state2trace us i
  end.

Definition MO_state2trace
  (us : MO_state) : list MO_transition_item :=
    MO_state2trace_aux us (enum index).

Lemma finite_valid_trace_from_to_MO_state2trace_RMO :
  forall us : MO_state,
    valid_state_prop RMO us ->
      finite_valid_trace_init_to RMO (``(vs0 RMO)) us (MO_state2trace us).
Proof.
  intros us Hvsp; split; [| done].
  unfold MO_state2trace.
  assert (Hall : forall i, i ∉ enum index -> us i = MkState [] (idx i))
    by (intros i Hin; contradict Hin; apply elem_of_enum).
  revert us Hall Hvsp.
  generalize (enum index) as is.
  induction is as [| i is']; cbn; intros us Hall Hvsp.
  - replace us with (fun n : index => MkState [] (idx n)).
    + by constructor; apply initial_state_is_valid; compute.
    + extensionality i; rewrite Hall; [done |].
      by apply not_elem_of_nil.
  - eapply finite_valid_trace_from_to_app.
    + apply IHis'.
      * intros j Hj. destruct (decide (i = j)); subst; state_update_simpl; [done |].
        by apply Hall; rewrite elem_of_cons; intros [].
      * by apply pre_composite_free_update_state_with_initial.
    + replace us with (state_update M us i (us i)) at 2 by (state_update_simpl; done).
      apply lift_to_RMO_finite_valid_trace_from_to; [done |].
      apply (composite_constrained_state_project _ us i) in Hvsp as Hvsp'.
      apply valid_state_has_trace in Hvsp' as (s & tr & [Hfvt Hinit]).
      replace s with (MkState [] (idx i)) in *; cycle 1.
      * by inversion Hinit; destruct s; cbn in *; subst.
      * by eapply finite_constrained_trace_init_to_state2trace.
Qed.

(** *** Validators *)

Lemma MO_component_validating :
  forall i : index, component_projection_validator_prop M (free_constraint M) i.
Proof.
  unfold component_projection_validator_prop.
  intros i lj sj omi * Hiv.
  apply input_valid_transition_iff in Hiv as [[s m] Ht].
  destruct (exists_right_finite_trace_from _ _ _ _ _ _ Ht) as (s' & tr & Hfvt & Hlast).
  apply lift_to_MO_finite_valid_trace_init_to in Hfvt as [Hfvt _].
  unfold lift_to_MO_trace, pre_VLSM_embedding_finite_trace_project in Hfvt;
    rewrite map_app in Hfvt.
  apply finite_valid_trace_from_to_app_split in Hfvt as [_ Hfvt].
  remember (finite_trace_last _ _) as ftl.
  change (finite_trace_last _ _)
    with (finite_trace_last
            (lift_to_MO_state (fun j : index => MkState [] (idx j)) i s')
            (lift_to_MO_trace (fun j : index => MkState [] (idx j)) i tr)) in Heqftl.
  apply valid_trace_forget_last, first_transition_valid in Hfvt; cbn in *.
  destruct Hfvt as [[Hvps [Hovmp Hv]] Ht']; cbn in Hv.
  unfold lift_to_MO_trace in Heqftl; cbn in Heqftl.
  rewrite <- pre_VLSM_embedding_finite_trace_last, Hlast in Heqftl.
  exists ftl; split; [by rewrite Heqftl; state_update_simpl |].
  split_and!; [| | done..].
  - eapply VLSM_incl_valid_state; [| by apply Hvps].
    by apply free_composite_vlsm_spec.
  - destruct Hovmp as [ss Hvsmp].
    exists ss.
    apply VLSM_incl_valid_state_message; [| by do 2 red | done].
    by apply free_composite_vlsm_spec.
Qed.

(** *** Equivocation *)

Lemma rec_obs_input_valid_transition :
  forall (i : index) (s1 s2 : State) (m1 m2 : option Message) (lbl : Label),
    input_valid_transition (RM i) lbl (s1, m1) (s2, m2) ->
      forall ob : Observation, rec_obs s1 ob -> rec_obs s2 ob.
Proof.
  intros i s1 s2 m1 m2 lbl Hivt ob Hro.
  destruct Hivt as [(_ & _ & Hvalid) Ht]; cbn in *.
  by inversion Hvalid; subst; inversion Ht; subst; cbn in *; constructor.
Qed.

Record incomparable_state (s1 s2 : State) : Prop :=
{
  incs_not_state_suffix12 : ~ state_suffix s1 s2;
  incs_not_state_suffix21 : ~ state_suffix s2 s1;
  incs_not_equal : s1 <> s2;
}.

Lemma rec_obs_send_inv
  (Q : State -> Observation -> Prop) s ob
  (Hnew : Q s (MkObservation Send (MkMessage s)))
  (Hprev : rec_obs s ob -> Q s ob) :
  rec_obs (s <+> MkObservation Send (MkMessage s)) ob -> Q s ob.
Proof.
  by inversion 1; (replace s with s0 in *; [auto | apply eq_State]).
Qed.

Lemma rec_obs_recv_inv
  (Q : State -> Message -> Observation -> Prop) s m ob
  (Hnew : Q s m (MkObservation Receive m))
  (Hprev : rec_obs s ob -> Q s m ob)
  (Hrecv : rec_obs (state m) ob -> Q s m ob) :
  rec_obs (s <+> MkObservation Receive m) ob -> Q s m ob.
Proof.
  by inversion 1; (replace s with s0 in *; [auto | apply eq_State]).
Qed.

Lemma rec_obs_addObservation_iff (s : State) (ob' ob : Observation) :
  rec_obs (s <+> ob) ob'
    <->
  rec_obs s ob' \/ ob' = ob \/ label ob = Receive /\ rec_obs (state (message ob)) ob'.
Proof.
  split.
  - inversion 1; subst.
    + by right; left.
    + by left; replace s with s0 by (apply eq_State; done).
    + by right; right.
  - destruct 1 as [Hprev | [-> | Hob]].
    + by apply rec_prev.
    + by apply rec_new.
    + destruct ob as [l m]; cbn in Hob.
      destruct Hob as [-> Hm].
      by apply rec_recv.
Qed.

Lemma unfold_rec_obs :
  forall (s : State) (ob : Observation),
    rec_obs s ob
      <->
    ob ∈ obs s \/ exists m, MkObservation Receive m ∈ obs s /\ rec_obs (state m) ob.
Proof using. clear. (* avoid unneccessary dependence on section variables *)
  intros s ob; split.
  - induction 1.
    + by left; constructor.
    + by setoid_rewrite elem_of_addObservation; firstorder.
    + by setoid_rewrite elem_of_addObservation; firstorder.
  - induction s using addObservation_ind.
    + by firstorder using elem_of_nil.
    + setoid_rewrite elem_of_addObservation.
      rewrite rec_obs_addObservation_iff.
      by firstorder; subst; auto.
Qed.

Set Warnings "-cannot-define-projection".
Record local_equivocators (s : State) (i : Address) : Prop :=
{
  lceqv_ob1 : Observation;
  lceqv_ob2 : Observation;
  lceqv_adr1 : adr (state (message lceqv_ob1)) = i;
  lceqv_adr2 : adr (state (message lceqv_ob2)) = i;
  lceqv_rec_obs1 : rec_obs s lceqv_ob1;
  lceqv_rec_obs2 : rec_obs s lceqv_ob2;
  lceqv_incomparable : incomparable (message lceqv_ob1) (message lceqv_ob2);
}.
Set Warnings "cannot-define-projection".

Definition composite_rec_observation
  (s : VLSM.state MO) (ob : Observation) : Prop :=
    exists i : index, rec_obs (s i) ob.

Definition state_after_sending (m : Message) : State :=
  state m <+> MkObservation Send m.

Set Warnings "-cannot-define-projection".
Record global_equivocators
  (sigma : VLSM.state MO) (i : index) : Prop :=
{
  globeqv_ob : Observation;
  globeqv_adr : adr (state (message globeqv_ob)) = idx i;
  globeqv_cro : composite_rec_observation sigma globeqv_ob;
  s := state_after_sending (message globeqv_ob);
  globeqv_nss : ~ state_suffix s (sigma i);
  globeqv_neq : s <> sigma i;
}.
Set Warnings "cannot-define-projection".

Lemma obs_rec_obs :
  forall (s : State) ob,
    ob ∈ obs s -> rec_obs s ob.
Proof.
  intros s ob.
  induction s using addObservation_ind.
  - by inversion 1.
  - intros [<- | Hob]%elem_of_cons.
    + by apply rec_new.
    + by apply rec_prev, IHs, Hob.
Qed.

Lemma messages_rec_obs :
  forall i (s : VLSM.state (RM i)),
    valid_state_prop (RM i) s ->
    forall (m' : Message) (ob : Observation),
      m' ∈ messages s ->
      rec_obs (state m') ob ->
      rec_obs s ob.
Proof.
  intros i s Hs.
  induction Hs using valid_state_prop_ind.
  - destruct s as [ol a].
    assert (ol = []) as -> by apply Hs.
    by inversion 1.
  - intros m' ob Hm' Hob.
    destruct Ht as [(_ & _ & Hvalid) Ht], Hvalid as [s m _ | s];
      cbn in Ht; injection Ht as [= <- <-].
    + change (m' ∈ m :: messages s) in Hm'.
      apply elem_of_cons in Hm' as [-> | Hm'].
      * by apply rec_recv.
      * by eapply rec_prev, IHHs.
    + change (m' ∈ MkMessage s :: messages s) in Hm'.
      apply elem_of_cons in Hm' as [-> | Hm'].
      * by apply rec_prev.
      * by eapply rec_prev, IHHs.
Qed.

Lemma unfold_robs_fwd :
  forall (s : State) ob,
    rec_obs s ob ->
      ob ∈ obs s \/ exists (m' : Message), m' ∈ messages s /\ rec_obs (state m') ob.
Proof.
  intros s ob.
  induction s using addObservation_ind; [by inversion 1 |].
  intro Hob; inversion Hob; subst; clear Hob
  ; replace s0 with s in * by (apply eq_State; done); clear H2 H3.
  - by left; constructor.
  - destruct (IHs H4) as [Hob | (m' & Hm & Hob)].
    + by left; constructor.
    + by right; exists m'; split; [constructor |].
  - by right; exists m; split; [constructor |].
Qed.

Lemma unfold_robs_rev :
  forall [Q : State -> Message -> Prop] [s : State],
    UMO_reachable Q s ->
    forall ob,
      (ob ∈ obs s \/ exists (m' : Message), m' ∈ messages s /\ rec_obs (state m') ob) ->
        rec_obs s ob.
Proof.
  by induction 1; intros ob [Hob | [m' [Hob ?]]];
    apply (@not_elem_of_nil, @elem_of_addObservation, @elem_of_messages_addObservation) in Hob;
    destruct Hob; subst; constructor; eauto.
Qed.

Lemma unfold_robs :
  forall (Q : State -> Message -> Prop) (s : State),
    UMO_reachable Q s ->
    forall ob,
      rec_obs s ob
        <->
      ob ∈ obs s \/ exists (m' : Message), m' ∈ messages s /\ rec_obs (state m') ob.
Proof.
  split.
  - by apply unfold_robs_fwd.
  - by eapply unfold_robs_rev.
Qed.

Lemma rec_obs_size_desc (s : State) (ob : Observation) :
  rec_obs s ob -> sizeState (state (message ob)) < sizeState s.
Proof.
  by induction 1; rewrite addObservation_size, sizeObservation_unfold; cbn; lia.
Qed.

Lemma rec_obs_acyclic (s : State) :
  forall l, ~ rec_obs s (MkObservation l (MkMessage s)).
Proof.
  by intros l Hrobs; apply rec_obs_size_desc, Nat.lt_irrefl in Hrobs.
Qed.

End sec_MOProtocol.

End sec_MO.

Arguments rec_obs_send_inv : clear implicits.
Arguments rec_obs_recv_inv : clear implicits.
