From VLSM.Lib Require Import Itauto.
From Coq Require Import FunctionalExtensionality.
From stdpp Require Import prelude finite.
From VLSM.Lib Require Import Preamble StdppExtras StdppListSet.
From VLSM.Core Require Import VLSM VLSMProjections Composition Equivocation ProjectionTraces.
From VLSM.Core Require Import BaseELMO.

(** * UMO Protocol Definitions and Properties

  This module contains definitions and properties of UMO components and
  the UMO protocol.
*)

Section sec_UMO.

Context
  {Address : Type}
  `{EqDecision Address}
  (State := @State Address)
  (Observation := @Observation Address)
  (Message := @Message Address).

(** ** Component definition *)

Definition UMOComponentState : Type := State.

(** The initial state has no observations and the same address as the component. *)

Definition UMOComponent_initial_state_prop (i : Address) (st : UMOComponentState) : Prop :=
  obs st = [] /\ adr st = i.

Definition UMOComponent_initial_state_type (i : Address) : Type :=
  {st : UMOComponentState | UMOComponent_initial_state_prop i st}.

Program Definition UMOComponent_initial_state
  (i : Address) : UMOComponent_initial_state_type i := MkState [] i.
Next Obligation.
Proof.
  by compute.
Defined.

#[export] Instance Inhabited_UMOComponent_initial_state_type (i : Address) :
  Inhabited (UMOComponent_initial_state_type i) :=
    populate (UMOComponent_initial_state i).

Definition UMOComponent_transition
  (l : Label) (s : State) (om : option Message)
  : State * option Message :=
  match l, om with
  | Send, Some m => (s, om)
  | Send, None   =>
      let ob := MkObservation Send (MkMessage s) in
      let st := s <+> ob in
      let msg := Some (MkMessage s) in
        (st, msg)
  | Receive, None => (s, None)
  | Receive, Some m =>
      let ob := MkObservation Receive m in
      let st := s <+> ob in
      let msg := None in
        (st, msg)
  end.

Inductive UMOComponentValid : Label -> State -> option Message -> Prop :=
| OCV_Send    : forall st : State, UMOComponentValid Send st None
| OCV_Receive : forall (st : State) (msg : Message), UMOComponentValid Receive st (Some msg).

Ltac invert_UMOComponentValid :=
repeat match goal with
| H : UMOComponentValid Receive _ None  |- _ => inversion H; subst; clear H
| H : UMOComponentValid Send _ (Some _) |- _ => inversion H; subst; clear H
end.

Definition UMOComponentMachine (i : Address) : VLSMMachine ELMOComponentType :=
{|
  initial_state_prop := UMOComponent_initial_state_prop i;
  initial_message_prop := const False;
  s0 := Inhabited_UMOComponent_initial_state_type i;
  transition := fun l '(st, om) => UMOComponent_transition l st om;
  valid := fun l '(st, om) => UMOComponentValid l st om;
|}.

Definition UMOComponent (i : Address) : VLSM Message :=
{|
  vtype := ELMOComponentType;
  vmachine := UMOComponentMachine i;
|}.

(** UMO components have a unique initial state. *)
Lemma UMOComponent_initial_state_unique :
  forall {i : Address} {s1 s2 : State},
    UMOComponent_initial_state_prop i s1 ->
    UMOComponent_initial_state_prop i s2 ->
      s1 = s2.
Proof.
  by do 2 inversion 1; destruct s1, s2; cbn in *; subst.
Qed.

Lemma UMOComponent_initial_state_spec :
  forall {i : Address} {s : State},
    UMOComponent_initial_state_prop i s -> s = MkState [] i.
Proof.
  by inversion 1; destruct s; cbn in *; subst.
Qed.

#[export] Instance HasBeenSentCapability_UMOComponent
  (i : Address) : HasBeenSentCapability (UMOComponent i).
Proof.
  apply Build_HasBeenSentCapability with (fun s m => m ∈ sentMessages s)
  ; [by intros s m; typeclasses eauto |].
  split.
  - by intros [] []; cbn in *; subst; cbn; apply not_elem_of_nil.
  - intros l s im s' om [(Hvsp & Hovmp & Hv) Ht] m; cbn in *.
    destruct l, im; cbn in *; invert_UMOComponentValid
    ; inversion Ht; subst; clear Ht; cbn.
    + by rewrite decide_False; cbn; firstorder congruence.
    + rewrite decide_True by done; cbn.
      unfold Message; rewrite elem_of_cons.
      by firstorder congruence.
Defined.

#[export] Instance HasBeenReceivedCapability_UMOComponent
  (i : Address) : HasBeenReceivedCapability (UMOComponent i).
Proof.
  eapply Build_HasBeenReceivedCapability with (fun s m => m ∈ receivedMessages s)
  ; [intros s m; typeclasses eauto | split].
  - by intros [] []; cbn in *; subst; cbn; apply not_elem_of_nil.
  - intros l s im s' om [(Hvsp & Hovmp & Hv) Ht] m; cbn in *.
    destruct l, im; cbn in *; invert_UMOComponentValid
    ; inversion Ht; subst; clear Ht; cbn.
    + rewrite decide_True by done; cbn.
      unfold Message; rewrite elem_of_cons.
      by firstorder congruence.
    + by rewrite decide_False; cbn; firstorder congruence.
Defined.

#[export] Instance HasBeenDirectlyObservedCapability_UMOComponent
  (i : Address) : HasBeenDirectlyObservedCapability (UMOComponent i) :=
    HasBeenDirectlyObservedCapability_from_sent_received (UMOComponent i).

(**
  A reachability predicate specialized for VLSMs refining UMO.
  [UMO_reachable C s] is equivalent to [constrained_state_prop V s] if
  the valid transitions of VLSM <<V>> follow [UMOComponent_transition]
  and the validity predicate is a refinement of [UMOComponent_valid]
  which does not further restrict the [Send] case.
*)
Inductive UMO_reachable (C : State -> Message -> Prop) : State -> Prop :=
| reach_init :
    forall a, UMO_reachable C (MkState [] a)
| reach_send :
    forall s, UMO_reachable C s -> UMO_reachable C (s <+> MkObservation Send (MkMessage s))
| reach_recv :
    forall s msg, C s msg -> UMO_reachable C s ->
      UMO_reachable C (s <+> MkObservation Receive msg).

(**
  An alternative induction principle for [UMO_reachable]
  which has a single case for [addObservation] that covers
  both [Send] and [Receive]. The hypotheses available in that
  case use a [match] on the label to cover the differences between
  the cases. This is useful for proofs where the [Send] and [Receive]
  cases share some reasoning.
*)
Lemma UMO_reachable_ind'
  (C : State -> Message -> Prop) (P : State -> Prop)
  (Hinit : forall a, P (MkState [] a))
  (Hextend : forall s l msg,
      UMO_reachable C s ->
      match l with
      | Send => msg = MkMessage s
      | Receive => C s msg
      end ->
      P s -> P (s <+> MkObservation l msg)) :
  forall s, UMO_reachable C s -> P s.
Proof.
  intros s Hs; induction Hs.
  - by apply Hinit.
  - by apply Hextend.
  - by apply Hextend.
Qed.

(**
  A specialized induction principle for [UMO_reachable]
  when the conclusion begins with [forall m, m ∈ messages s -> ...].
  This handles splitting [m ∈ messages (s <+> ob)] into
  cases for [m ∈ messages s] and for the new observation,
  and uses a new case [HPrev] to handle the [m ∈ messages s]
  parts for both [Send] and [Receive].
  Unfortunately the <<induction _ using _>> variant of the
  [induction] tactic cannot recognize this lemma as an induction
  principle, so it must be used with [refine] or [apply].
*)
Lemma UMO_reachable_elem_of_messages_ind
  (C : State -> Message -> Prop)
  (P : State -> Message -> Prop)
  (HPrev : forall s (Hs : UMO_reachable C s) m ob,
    m ∈ messages s ->
    P s m -> P (s <+> ob) m)
  (HSend : forall s (Hs : UMO_reachable C s),
    (forall m', m' ∈ messages s -> P s m') ->
    P (s <+> MkObservation Send (MkMessage s)) (MkMessage s))
  (HRecv : forall s (Hs : UMO_reachable C s) mr,
    C s mr ->
    (forall m', m' ∈ messages s -> P s m') ->
    P (s <+> MkObservation Receive mr) mr) :
  forall s, UMO_reachable C s ->
    forall m', m' ∈ messages s -> P s m'.
Proof.
  intros s Hs; induction Hs.
  - by inversion 1.
  - by intros m' [-> | Hm']%elem_of_messages_addObservation; eauto.
  - by intros m' [-> | Hm']%elem_of_messages_addObservation; eauto.
Qed.

Lemma UMO_reachable_impl (P Q : State -> Message -> Prop) (HPQ : forall s m, P s m -> Q s m) :
  forall s, UMO_reachable P s -> UMO_reachable Q s.
Proof.
  by induction 1; constructor; auto.
Qed.

(** [Send] transitions in a constrained state are ok. *)
Lemma input_valid_transition_Send :
  forall (i : Address) (m : Message),
    valid_state_prop (pre_loaded_with_all_messages_vlsm (UMOComponent i)) (state m) ->
      input_valid_transition (pre_loaded_with_all_messages_vlsm (UMOComponent i))
        Send (state m, None) (state m <+> MkObservation Send m, Some m).
Proof.
  intros; red; cbn; split_and!.
  - done.
  - by apply option_valid_message_None.
  - by constructor.
  - by do 3 f_equal; apply eq_Message.
Qed.

(** [Receive] transitions in a constrained state are ok. *)
Lemma input_valid_transition_Receive :
  forall (i : Address) (s : State) (m : Message),
    valid_state_prop (pre_loaded_with_all_messages_vlsm (UMOComponent i)) s ->
    input_valid_transition (pre_loaded_with_all_messages_vlsm (UMOComponent i))
      Receive (s, Some m) (s <+> MkObservation Receive m, None).
Proof.
  intros * Hvsp; red; cbn; split_and!; [done | | | done].
  - by apply any_message_is_valid_in_preloaded.
  - by constructor.
Qed.

(**
  This lemma shows that for a VLSM based on UMO
  reachability in the VLSM according to [constrained_state_prop]
  is equivalent to [UMO_reachable] with a predicate
  based on the VLSM's [valid] predicate, plus
  a condition on the address.

  In particular the VLSM must work over the same
  [VLSMType] as UMO, of [Message], [State], and [Label],
  the transition function must be [UMOComponent_transition],
  and the [valid] and [initial_state_prop] must be
  restrictions of UMO's predicates.

  This lemma usually should not be used directly, but
  instead used to prove a  "view" lemma for a
  specific VLSM, such as [ELMO_reachable_view]
  in the [VLSM.ELMO.ELMO] module.
*)
Lemma UMO_based_valid_reachable
  (VM : VLSMMachine (Build_VLSMType Message State Label))
  (V := mk_vlsm VM)
  (Hinit_empty : forall si, initial_state_prop V si -> obs si = [])
  (Hsend_spec : forall s om, constrained_state_prop V s -> valid V Send (s, om) <-> om = None)
  (Htransition : forall l s om, transition V l (s, om) = UMOComponent_transition l s om) :
  forall (s : State),
    constrained_state_prop V s
      <->
    UMO_reachable (fun s m => VM.(valid) Receive (s, Some m)) s
      /\ initial_state_prop V (MkState [] (adr s)).
Proof.
  split.
  - intros Hs; induction Hs using valid_state_prop_ind.
    + destruct s as [ol a].
      cbn in *; replace ol with (@nil Observation) in * by (specialize (Hinit_empty _ Hs); done).
      by split; [apply reach_init |].
    + destruct Ht as [(_ & _ & Hvalid) Ht].
      cbn in Ht; rewrite Htransition in Ht.
      destruct IHHs as [IH Hadr].
      by destruct l, om; inversion Ht; subst; auto using @UMO_reachable.
  - intros [Hs Hadr].
    induction Hs.
    + by apply initial_state_is_valid.
    + apply input_valid_transition_destination
        with (l := Send) (s := s) (om := None) (om' := Some (MkMessage s)).
      repeat split.
      * by apply IHHs.
      * by apply option_valid_message_None.
      * by apply Hsend_spec; [apply IHHs |].
      * by cbn; rewrite Htransition.
    + apply input_valid_transition_destination
        with (l := Receive) (s := s) (om := Some msg) (om' := None).
      repeat split; [| | done |].
      * by apply IHHs.
      * by apply any_message_is_valid_in_preloaded.
      * by cbn; rewrite Htransition.
Qed.

(** ** Every valid state contains a unique valid trace leading to it

  To prove this, we will need some basic properties of UMO components.

  For the rest of this section, we will work with two UMO components,
  one (named [Ui]) for dealing with valid states, and
  another (named [Ri]) for dealing with reachable states.
*)

Section sec_UMOComponent_lemmas.

(**
  [Ui] is a notation for an [UMOComponent] of address [i].

  The "R" in [Ri] stands for "reachability", as it will be used to state and
  prove lemmas and theorems which talk about reachability.
*)

Context
  {i : Address}
  (Ui : VLSM Message := UMOComponent i)
  (Ri : VLSM Message := pre_loaded_with_all_messages_vlsm Ui).

(**
  There is a VLSM inclusion from [Ui] to [Ri]. This is an extremely useful
  fact - we will prove many lemmas just for [Ri] and then use this fact to
  transport them to [Ui].
*)
Lemma VLSM_incl_Ui_Ri :
  VLSM_incl_part Ui Ri.
Proof.
  by apply vlsm_incl_pre_loaded_with_all_messages_vlsm.
Qed.

Lemma UMO_reachable_Ui :
  forall s, valid_state_prop Ui s ->
  UMO_reachable (const (const True)) s /\ adr s = i.
Proof.
  induction 1 using valid_state_prop_ind;
    [by destruct s, Hs as [Hobs Hadr]; cbn in *; subst; split; [constructor 1 |] |].
  by destruct Ht as [(_ & _ & Hv) Ht]; inversion Hv; subst; inversion Ht; subst;
    destruct_and!; (split; [constructor |]).
Qed.

Lemma UMO_reachable_constrained_state_prop :
  forall (s : State),
    constrained_state_prop (UMOComponent i) s
      <->
    UMO_reachable (fun _ _ => True) s /\ adr s = i.
Proof.
  split.
  - induction 1 using valid_state_prop_ind;
      [by destruct s, Hs as [Hobs Hadr]; cbn in *; subst; split; [constructor 1 |] |].
    by destruct Ht as [(_ & _ & Hv) Ht]; inversion Hv; subst; inversion Ht; subst;
      destruct_and!; (split; [constructor |]).
  - intros [Hur Hadr].
    induction Hur; red; cbn in Hadr.
    + by apply initial_state_is_valid; cbv.
    + by eapply input_valid_transition_destination, input_valid_transition_Send, IHHur.
    + by eapply input_valid_transition_destination, input_valid_transition_Receive, IHHur.
Qed.

(** The initial state of [Ri] is unique (that of [Ui] too, but we don't need a separate lemma). *)
Lemma vs0_uniqueness :
  forall is : State,
    UMOComponent_initial_state_prop i is ->
      is = ``(vs0 Ri).
Proof.
  by intros []; inversion 1; cbv in *; by subst.
Qed.

(** Transitions of an UMO component preserve the address of the component. *)
Lemma UMOComponent_transition_adr :
  forall (s1 s2 : State) (iom oom : option Message) (lbl : Label),
    UMOComponent_transition lbl s1 iom = (s2, oom) ->
      adr s2 = adr s1.
Proof.
  by intros s1 s2 [im |] oom []; inversion_clear 1.
Qed.

(** For every trace segment, the initial and final state have the same address. *)

Lemma adr_of_states_within_trace_Ri :
  forall (is s : State) (tr : list transition_item),
    finite_valid_trace_from_to Ri is s tr ->
      adr s = adr is.
Proof.
  induction 1; [done |].
  transitivity (adr s); [done |].
  eapply UMOComponent_transition_adr.
  by destruct Ht as [_ Ht]; cbn in Ht.
Qed.

Lemma adr_of_states_within_trace_Ui :
  forall (is s : State) (tr : list transition_item),
    finite_valid_trace_from_to Ui is s tr ->
      adr s = adr is.
Proof.
  induction 1; [done |].
  transitivity (adr s); [done |].
  eapply UMOComponent_transition_adr.
  by destruct Ht as [_ Ht]; cbn in Ht.
Qed.

(** If a state is reachable, its address is the same as the address of the component. *)

Lemma adr_of_reachable_state_Ri :
  forall (is s : State) (tr : list transition_item),
    finite_valid_trace_init_to Ri is s tr ->
      adr s = i.
Proof.
  intros is s tr [Hfvt Hinit].
  transitivity (adr is).
  - by eapply adr_of_states_within_trace_Ri.
  - by destruct Hinit, is; cbn in *.
Qed.

Lemma adr_of_reachable_state_Ui :
  forall (is s : State) (tr : list transition_item),
    finite_valid_trace_init_to Ui is s tr ->
      adr s = i.
Proof.
  intros is s tr [Hfvt Hinit].
  transitivity (adr is).
  - by eapply adr_of_states_within_trace_Ui.
  - by destruct Hinit, is; cbn in *.
Qed.

(** The address of a valid state is the same as the address of the component. *)
Lemma adr_of_valid_state_Ri :
  forall s : State,
    valid_state_prop Ri s -> adr s = i.
Proof.
  intros s Hvsp.
  apply valid_state_has_trace in Hvsp as (is & tr & Hfvti).
  by eapply adr_of_reachable_state_Ri.
Qed.

Lemma adr_of_valid_state_Ui :
  forall s : State,
    valid_state_prop Ui s -> adr s = i.
Proof.
  intros s Hvsp.
  apply valid_state_has_trace in Hvsp as (is & tr & Hfvti).
  by eapply adr_of_reachable_state_Ui.
Qed.

(** Valid transitions lead to bigger states. *)

Lemma UMOComponent_valid_transition_size :
  forall (s1 s2 : State) (iom oom : option Message) (lbl : Label),
    UMOComponentValid lbl s1 iom ->
    UMOComponent_transition lbl s1 iom = (s2, oom) ->
      sizeState s1 < sizeState s2.
Proof.
  by intros [] s2 [im |] oom []; do 2 inversion_clear 1; cbn; lia.
Qed.

Lemma input_valid_transition_size_Ri :
  forall (s1 s2 : State) (iom oom : option Message) (lbl : Label),
    input_valid_transition Ri lbl (s1, iom) (s2, oom) ->
      sizeState s1 < sizeState s2.
Proof.
  intros s1 s2 iom oom lbl [(_ & _ & Hvalid) Ht]; cbn in *.
  by eapply UMOComponent_valid_transition_size.
Qed.

(**
  A [finite_valid_trace] is either empty or its final state is bigger than
  its initial state.
*)

Lemma finite_valid_trace_from_to_size_Ri :
  forall (s1 s2 : State) (tr : list transition_item),
    finite_valid_trace_from_to Ri s1 s2 tr ->
      s1 = s2 /\ tr = []
        \/
      sizeState s1 < sizeState s2.
Proof.
  induction 1; [by left |].
  assert (sizeState s' < sizeState s)
      by (eapply input_valid_transition_size_Ri; done).
  by destruct IHfinite_valid_trace_from_to; [itauto congruence | itauto lia].
Qed.

(** If a trace leads from a state to itself, then it is empty. *)

Lemma finite_valid_trace_from_to_inv_Ri :
  forall (s : State) (tr : list transition_item),
    finite_valid_trace_from_to Ri s s tr -> tr = [].
Proof.
  by intros s tr Hfvt; apply finite_valid_trace_from_to_size_Ri in Hfvt; itauto lia.
Qed.

(**
  The same lemmas as above, but for the component [Ui]. They follow from the
  above lemmas because there is a VLSM inclusion from [Ri] to [Ui].
*)

Lemma input_valid_transition_size_Ui :
  forall (s1 s2 : State) (iom oom : option Message) (lbl : Label),
    input_valid_transition Ui lbl (s1, iom) (s2, oom) ->
      sizeState s1 < sizeState s2.
Proof.
  intros s1 s2 iom oom lbl Hivt.
  eapply input_valid_transition_size_Ri.
  by apply (@VLSM_incl_input_valid_transition _ Ui Ui Ri)
  ; eauto using VLSM_incl_Ui_Ri.
Qed.

Lemma finite_valid_trace_from_to_size_Ui :
  forall (s1 s2 : State) (tr : list transition_item),
    finite_valid_trace_from_to Ui s1 s2 tr ->
      s1 = s2 /\ tr = []
        \/
      sizeState s1 < sizeState s2.
Proof.
  intros s1 s2 tr Hfvt.
  eapply finite_valid_trace_from_to_size_Ri.
  by apply (@VLSM_incl_finite_valid_trace_from_to _ Ui Ui Ri)
  ; eauto using VLSM_incl_Ui_Ri.
Qed.

Lemma finite_valid_trace_from_to_inv_Ui :
  forall (s : State) (tr : list transition_item),
    finite_valid_trace_from_to Ui s s tr -> tr = [].
Proof.
  intros s tr Hfvt.
  eapply finite_valid_trace_from_to_inv_Ri.
  by apply (@VLSM_incl_finite_valid_trace_from_to _ Ui Ui Ri)
  ; eauto using VLSM_incl_Ui_Ri.
Qed.

(**
  [transition]s in any VLSM are deterministic, i.e., the final state and output
  message are determined by the label, initial state and input message.

  For UMO components, an extremely strong converse property also holds: the
  label, initial state, input message and output message are all determined
  by the final state of a valid transition. Basically, this is true because
  every state contains the whole trace/history.
*)

Lemma input_valid_transition_deterministic_conv_Ri :
  forall (s1 s2 f : State) (iom1 iom2 oom1 oom2 : option Message) (lbl1 lbl2 : Label),
    input_valid_transition Ri lbl1 (s1, iom1) (f, oom1) ->
    input_valid_transition Ri lbl2 (s2, iom2) (f, oom2) ->
      lbl1 = lbl2 /\ s1 = s2 /\ iom1 = iom2 /\ oom1 = oom2.
Proof.
  intros s1 s2 f iom1 iom2 oom1 oom2 lbl1 lbl2 Hivt1 Hivt2
  ; inversion Hivt1 as [(_ & _ & Hvalid1) Ht1]; subst
  ; inversion Hivt2 as [(_ & _ & Hvalid2) Ht2]; subst.
  destruct lbl1, lbl2, iom1, iom2; cbn in *
  ; inversion Ht1; subst; clear Ht1
  ; inversion Ht2; subst; clear Ht2
  ; invert_UMOComponentValid; auto.
  by destruct s1, s2; cbn in *; subst; itauto.
Qed.

Lemma input_valid_transition_deterministic_conv_Ui :
  forall (s1 s2 f : State) (iom1 iom2 oom1 oom2 : option Message) (lbl1 lbl2 : Label),
    input_valid_transition Ui lbl1 (s1, iom1) (f, oom1) ->
    input_valid_transition Ui lbl2 (s2, iom2) (f, oom2) ->
      lbl1 = lbl2 /\ s1 = s2 /\ iom1 = iom2 /\ oom1 = oom2.
Proof.
  intros s1 s2 f iom1 iom2 oom1 oom2 lbl1 lbl2 Hivt1 Hivt2.
  by eapply input_valid_transition_deterministic_conv_Ri
  ; apply (@VLSM_incl_input_valid_transition _ Ui Ui Ri)
  ; eauto using VLSM_incl_Ui_Ri.
Qed.

(** Every trace segment is fully determined by its initial and final state. *)

Lemma finite_valid_trace_from_to_unique_Ri :
  forall (s1 s2 : State) (l1 l2 : list transition_item),
    finite_valid_trace_from_to Ri s1 s2 l1 ->
    finite_valid_trace_from_to Ri s1 s2 l2 ->
      l1 = l2.
Proof.
  intros s1 s2 l1 l2 Hfvt1 Hfvt2; revert l2 Hfvt2.
  induction Hfvt1 using finite_valid_trace_from_to_rev_ind; intros.
  - by apply finite_valid_trace_from_to_size_Ri in Hfvt2; itauto (congruence + lia).
  - destruct Hfvt2 using finite_valid_trace_from_to_rev_ind; [| clear IHHfvt2].
    + apply finite_valid_trace_from_to_size_Ri in Hfvt1.
      apply input_valid_transition_size_Ri in Ht.
      by decompose [and or] Hfvt1; subst; clear Hfvt1; lia.
    + assert (l = l0 /\ s = s0 /\ iom = iom0 /\ oom = oom0)
          by (eapply input_valid_transition_deterministic_conv_Ri; done).
      decompose [and] H; subst; clear H.
      by f_equal; apply IHHfvt1.
Qed.

Lemma finite_valid_trace_from_to_unique_Ui :
  forall (s1 s2 : State) (l1 l2 : list transition_item),
    finite_valid_trace_from_to Ui s1 s2 l1 ->
    finite_valid_trace_from_to Ui s1 s2 l2 ->
      l1 = l2.
Proof.
  by intros s1 s2 l1 l2 Hfvt1 Hfvt2
  ; eapply finite_valid_trace_from_to_unique_Ri
  ; apply VLSM_incl_finite_valid_trace_from_to
  ; eauto using VLSM_incl_Ui_Ri.
Qed.

(** Every trace is determined by its final state. *)

(** Uniqueness *)
Lemma finite_valid_trace_init_to_unique_Ri :
  forall (s f : State) (l1 l2 : list transition_item),
    finite_valid_trace_init_to Ri s f l1 ->
    finite_valid_trace_init_to Ri s f l2 ->
      l1 = l2.
Proof.
  intros s f l1 l2 [Ht1 _] [Ht2 _].
  by eapply finite_valid_trace_from_to_unique_Ri.
Qed.

Lemma finite_valid_trace_init_to_unique_Ui :
  forall (s f : State) (l1 l2 : list transition_item),
    finite_valid_trace_init_to Ui s f l1 ->
    finite_valid_trace_init_to Ui s f l2 ->
      l1 = l2.
Proof.
  by intros s f l1 l2 Hfvit1 Hfvit2
  ; eapply finite_valid_trace_init_to_unique_Ri
  ; apply VLSM_incl_finite_valid_trace_init_to
  ; eauto using VLSM_incl_Ui_Ri.
Qed.

(** If a valid trace leads to state s, the trace extracted from s also leads to s. *)
Lemma finite_valid_trace_init_to_state2trace_Ri :
  forall (is s : State) (tr : list transition_item),
    finite_valid_trace_init_to Ri is s tr ->
      finite_valid_trace_init_to Ri is s (state2trace s).
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

Lemma finite_valid_trace_init_to_state2trace_Ui :
  forall (is s : State) (tr : list transition_item),
    finite_valid_trace_init_to Ui is s tr ->
      finite_valid_trace_init_to Ui is s (state2trace s).
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

Lemma finite_valid_trace_init_to_state2trace_Ri_inv :
  forall (is s : State) (tr : list transition_item),
    finite_valid_trace_init_to Ri is s tr ->
      state2trace s = tr.
Proof.
  intros is s tr Hfvti.
  assert (Hfvti' : finite_valid_trace_init_to Ri is s (state2trace s))
      by (eapply finite_valid_trace_init_to_state2trace_Ri; done).
  by eapply finite_valid_trace_init_to_unique_Ri.
Qed.

Lemma finite_valid_trace_init_to_state2trace_Ui_inv :
  forall (is s : State) (tr : list transition_item),
    finite_valid_trace_init_to Ui is s tr ->
      state2trace s = tr.
Proof.
  by intros is s tr Hfvti
  ; eapply finite_valid_trace_init_to_state2trace_Ri_inv
  ; apply VLSM_incl_finite_valid_trace_init_to
  ; eauto using VLSM_incl_Ui_Ri.
Qed.

(** The trace extracted from a reachable state [s] leads to [s]. *)

(** Existence *)
Lemma finite_valid_trace_init_to_state2trace_Ri' :
  forall (s : State),
    valid_state_prop Ri s ->
      finite_valid_trace_init_to Ri (``(vs0 Ri)) s (state2trace s).
Proof.
  intros s Hs.
  apply valid_state_has_trace in Hs as (is & tr & Htr).
  apply finite_valid_trace_init_to_state2trace_Ri_inv in Htr as Heqtr; subst.
  replace (``(vs0 Ri)) with is; [done |].
  by apply vs0_uniqueness, Htr.
Qed.

Lemma valid_state_contains_unique_valid_trace_Ri :
  forall s : State,
    valid_state_prop Ri s ->
      exists tr : list transition_item,
        finite_valid_trace_init_to Ri (``(vs0 Ri)) s tr
          /\
        forall tr' : list transition_item,
          finite_valid_trace_init_to Ri (``(vs0 Ri)) s tr' -> tr' = tr.
Proof.
  intros s Hvsp.
  exists (state2trace s); split.
  - by eapply finite_valid_trace_init_to_state2trace_Ri'.
  - intros tr' Hfvt. symmetry.
    by eapply finite_valid_trace_init_to_state2trace_Ri_inv.
Qed.

(** Existence *)
Lemma finite_valid_trace_init_to_state2trace_Ui' :
  forall (s : State),
    valid_state_prop Ui s ->
      finite_valid_trace_init_to Ui (``(vs0 Ri)) s (state2trace s).
Proof.
  intros s Hs.
  apply valid_state_has_trace in Hs as (is & tr & Htr).
  apply finite_valid_trace_init_to_state2trace_Ui_inv in Htr as Heqtr; subst.
  replace (``(vs0 Ri)) with is; [done |].
  by apply vs0_uniqueness, Htr.
Qed.

Lemma valid_state_contains_unique_valid_trace_Ui :
  forall s : State,
    valid_state_prop Ui s ->
      exists tr : list transition_item,
        finite_valid_trace_init_to Ui (``(vs0 Ri)) s tr
          /\
        forall tr' : list transition_item,
          finite_valid_trace_init_to Ui (``(vs0 Ri)) s tr' -> tr' = tr.
Proof.
  intros s Hvsp.
  exists (state2trace s); split.
  - by eapply finite_valid_trace_init_to_state2trace_Ui'.
  - intros tr' Hfvt. symmetry.
    by eapply finite_valid_trace_init_to_state2trace_Ui_inv.
Qed.

(** ** The suffix ordering on states is a strict total order

  <<s1>> is a state-suffix of <<s2>> if they have the same address and
  <<s1>>'s observations are a strict suffix of <<s2>>'s observations.
*)

Record state_suffix (s1 s2 : State) : Prop :=
{
  adrs_eq    : adr s1 = adr s2;
  obs_prefix : strict suffix (obs s1) (obs s2);
}.

#[export] Instance state_suffix_dec : RelDecision state_suffix :=
  fun s1 s2 =>
    match decide (adr s1 = adr s2) with
    | left addr_eq =>
        match decide (strict suffix (obs s1) (obs s2)) with
        | left is_suffix => left (Build_state_suffix _ _ addr_eq is_suffix)
        | right Hnot_suffix => right (fun H => Hnot_suffix (obs_prefix _ _ H))
        end
    | right Hnot_addr => right (fun H => Hnot_addr (adrs_eq _ _ H))
    end.

(** We also define a variant of the suffix relation for messages. *)
Definition message_suffix (m1 m2 : Message) : Prop :=
  state_suffix (state m1) (state m2).

(** The state-prefix relation is a strict partial order. *)

#[export] Instance Irreflexive_state_suffix :
  Irreflexive state_suffix.
Proof.
  by intros s (Hadr & Hobs1 & Hobs2).
Qed.

#[export] Instance Transitive_state_suffix :
  Transitive state_suffix.
Proof.
  intros s1 s2 s3 (Hadr12 & Hobs12 & Hobs12') (Hadr23 & Hobs23 & Hobs23').
  split; [by congruence |].
  by transitivity (obs s2).
Qed.

#[export] Instance StrictOrder_state_suffix :
  StrictOrder state_suffix.
Proof.
  by split; typeclasses eauto.
Qed.

Lemma state_suffix_empty_minimal :
  forall (s : State) (a : Address), ~ state_suffix s (MkState [] a).
Proof.
  intros s a [_ [[os Hsuf] Hstrict]]; contradict Hstrict.
  by symmetry in Hsuf; apply app_nil in Hsuf as [-> ->]; exists [].
Qed.

Lemma state_suffix_empty_minimum :
  forall (s : State), s = MkState [] (adr s) \/ state_suffix (MkState [] (adr s)) s.
Proof.
  intros [[| ob obs] a]; cbn; [by left | right].
  split; cbn; [done |].
  split; cbn; [by apply suffix_nil |].
  by intros H; apply suffix_nil_inv in H; subst.
Qed.

(**
  If we add an observation to a state <<s>>, <<s>> is a suffix
  of the resulting state.
*)

Lemma state_suffix_addObservation :
  forall (s : State) (ob : Observation),
    state_suffix s (s <+> ob).
Proof.
  intros s ob.
  constructor; cbn; [done |].
  unfold addObservation; split.
  - by apply suffix_cons_r.
  - by apply suffix_cons_not.
Qed.

Lemma state_suffix_addObservations :
  forall (s : State) (obs' : list Observation),
    obs' <> [] -> state_suffix s (s <++> obs').
Proof.
  intros s obs'.
  constructor; cbn; [done |].
  split.
  - by apply suffix_app_r.
  - by intros Hsuf; apply (suffix_app_inv obs' []), suffix_nil_inv in Hsuf.
Qed.

(** The initial state of a valid transition is a [state_suffix] of the final state. *)
Lemma state_suffix_of_UMOComponent_valid_transition :
  forall (lbl : Label) (s1 s2 : State) (iom oom : option Message),
    UMOComponentValid lbl s1 iom ->
    UMOComponent_transition lbl s1 iom = (s2, oom) ->
      state_suffix s1 s2.
Proof.
  intros [] s1 s2 [im |] oom HValid; cbn
  ; intros H; inversion H; subst; clear H.
  - by apply state_suffix_addObservation.
  - by invert_UMOComponentValid.
  - by invert_UMOComponentValid.
  - by apply state_suffix_addObservation.
Qed.

(** The previous property carries over from transitions to valid transitions. *)
Lemma state_suffix_of_input_valid_transition_Ri :
  forall (lbl : Label) (s1 s2 : State) (iom oom : option Message),
    input_valid_transition Ri lbl (s1, iom) (s2, oom) ->
      state_suffix s1 s2.
Proof.
  intros lbl s1 s2 iom oom [(Hvsp & Hovmp & Hvalid) Ht]; cbn in Ht.
  by eapply state_suffix_of_UMOComponent_valid_transition; cycle 1.
Qed.

(**
  If there is a trace segment from <<s1>> to <<s2>>, then either the states are
  equal (because the trace is empty), or <<s1>> is a state-suffix of <<s2>>.
*)
Lemma state_suffix_of_finite_valid_trace_from_to_Ri :
  forall (s1 s2 : State) (tr : list transition_item),
    finite_valid_trace_from_to Ri s1 s2 tr ->
      s1 = s2 \/ state_suffix s1 s2.
Proof.
  induction 1; [by left |].
  destruct IHfinite_valid_trace_from_to as [-> | IH]; right.
  - by eapply state_suffix_of_input_valid_transition_Ri; eauto.
  - transitivity s; [| done].
    by eapply state_suffix_of_input_valid_transition_Ri; eauto.
Qed.

(**
  [state_suffix_of_finite_valid_trace_from_to_Ri] carries over from
  trace segments to traces.
*)
Lemma state_suffix_of_finite_valid_trace_init_to_Ri :
  forall (s1 s2 : State) (tr : list transition_item),
    finite_valid_trace_init_to Ri s1 s2 tr ->
      s1 = s2 \/ state_suffix s1 s2.
Proof.
  intros s1 s2 tr [Hfvt Hinit].
  by eapply state_suffix_of_finite_valid_trace_from_to_Ri.
Qed.

(**
  Every reachable state is either initial or the target of some transition.
  This transition comes from a source state which is also reachable.
  Additionally, if the label of the transition is [Send], we know that the
  observation contains the source state.
*)
Lemma UMO_reachable_inv P :
  forall s : State,
    UMO_reachable P s ->
      obs s = [] \/
      exists (lbl : Label) (iom oom : option Message) (s' : State) (ob : Observation),
        UMOComponent_transition lbl s' iom = (s, oom) /\
        s = s' <+> ob /\
        UMO_reachable P s' /\
        (lbl = Send -> message ob = MkMessage s').
Proof.
  intros s Hs.
  inversion Hs; [by left | right..].
  - by eexists Send, None, (Some (MkMessage s0)), s0, _.
  - by eexists Receive, (Some msg), None, s0, _.
Qed.

(**
  If a reachable state <<s2>> is a result of adding an observation to a state
  <<s1>>, then <<s1>> is also reachable. Additionally, if the observation's
  label is [Send], then we can characterize the state <<s1>>.
*)

Lemma UMO_reachable_addObservation_inv P :
  forall (s : State) (ob : Observation),
    UMO_reachable P (s <+> ob) -> UMO_reachable P s.
Proof.
  intros s ob Hvsp.
  apply UMO_reachable_inv in Hvsp
     as [[=] | (lbl & iom & oom & s' & ob' & Ht & Hadd & Hvsp & Hss')]; cbn in *.
  by apply addObservation_inj in Hadd as [_ ->].
Qed.

Lemma UMO_reachable_addObservation_inv_Send_state P :
  forall (s : State) (m : Message),
    UMO_reachable P (s <+> MkObservation Send m) ->
      s = state m.
Proof.
  intros s m Hvsp.
  apply UMO_reachable_inv in Hvsp
     as [[=] | (lbl & iom & oom & s' & ob' & Ht & Hadd & Hvsp & Hlbl)]; cbn in *.
  inversion Hadd.
  replace (state m) with (state (message ob')) by (rewrite <- H0; cbn; done).
  rewrite Hlbl; [by apply eq_State |].
  by destruct lbl, iom; cbn in *; inversion Ht; subst; [| | done]
  ; apply (f_equal (fun x => length (obs x))) in Hadd; cbn in Hadd; lia.
Qed.

Lemma UMO_reachable_addObservation_inv_Send P :
  forall (s : State) (m : Message),
    UMO_reachable P (s <+> MkObservation Send m) ->
      UMO_reachable P (state m).
Proof.
  intros s m Hvsp.
  erewrite <- UMO_reachable_addObservation_inv_Send_state; [| done].
  by eapply UMO_reachable_addObservation_inv.
Qed.

Lemma UMO_reachable_addObservation_inv_message P :
  forall (s : State) (ob : Observation),
    UMO_reachable P (s <+> ob) -> label ob = Send ->
      message ob = MkMessage s.
Proof.
  intros s ob Hvsp Heq.
  apply UMO_reachable_inv in Hvsp
     as [[=] | (lbl & iom & oom & s' & ob' & Ht & Hadd & Hvsp & Hss')]; cbn in *.
  apply addObservation_inj in Hadd as [-> ->].
  apply Hss'. destruct lbl, iom; inversion Ht; subst; clear Ht; cbn in *; [done | | done | done].
  by symmetry in H0; apply addObservation_acyclic in H0.
Qed.

(**
  If a reachable state <<s2>> results from adding observations to a state <<s1>>,
  then <<s1>> is also reachable.
*)
Lemma UMO_reachable_addObservations_inv P :
  forall (s : State) (obs' : list Observation),
    UMO_reachable P (s <++> obs') -> UMO_reachable P s.
Proof.
  intros s obs'; revert s.
  induction obs' as [| ob' obs']; cbn; intros s Hvsp.
  - by rewrite <- addObservations_nil.
  - by apply IHobs', UMO_reachable_addObservation_inv with ob'.
Qed.

Lemma UMO_reachable_constrained_state_prop :
  forall (s : State),
    constrained_state_prop (UMOComponent i) s
      <->
    UMO_reachable (fun _ _ => True) s /\ adr s = i.
Proof.
  split; [by apply UMO_reachable_Ri |].
  intros [Hur Hadr].
  induction Hur; red; cbn in Hadr.
  - by apply initial_state_is_valid; cbv.
  - by eapply input_valid_transition_destination, input_valid_transition_Send, IHHur.
  - by eapply input_valid_transition_destination, input_valid_transition_Receive, IHHur.
Qed.

(** If a state is constrained, after sending a message it's still constrained. *)
Lemma constrained_state_prop_Send :
  forall (m : Message),
    constrained_state_prop (UMOComponent i) (state m) ->
    constrained_state_prop (UMOComponent i) (state m <+> MkObservation Send m).
Proof.
  setoid_rewrite UMO_reachable_constrained_state_prop; cbn.
  intros m [Hur Hadr]; split; [| done].
  by destruct m; constructor.
Qed.

(** If a state is constrained, after receiving a message it's still constrained. *)
Lemma constrained_state_prop_Receive :
  forall (s : State) (m : Message),
    constrained_state_prop (UMOComponent i) s ->
    constrained_state_prop (UMOComponent i) (s <+> MkObservation Receive m).
Proof.
  setoid_rewrite UMO_reachable_constrained_state_prop; cbn.
  intros s m [Hur Hadr]; split; [| done].
  by destruct m; constructor.
Qed.

(**
  If a state is constrained after adding an observation, it must have been
  constrained before adding it.
*)
Lemma constrained_state_prop_addObservation_inv :
  forall (s : State) (ob : Observation),
    constrained_state_prop (UMOComponent i) (s <+> ob) ->
    constrained_state_prop (UMOComponent i) s.
Proof.
  setoid_rewrite UMO_reachable_constrained_state_prop; cbn.
  intros s ob [Hur Hadr]; split; [| done].
  by eapply UMO_reachable_addObservation_inv.
Qed.

(**
  If a state is constrained after adding some observations, it must have been
  constrained before adding them.
*)
Lemma constrained_state_prop_addObservations_inv :
  forall (s : State) (obs : list Observation),
    constrained_state_prop (UMOComponent i) (s <++> obs) ->
    constrained_state_prop (UMOComponent i) s.
Proof.
  setoid_rewrite UMO_reachable_constrained_state_prop; cbn.
  intros s ob [Hur Hadr]; split; [| done].
  by eapply UMO_reachable_addObservations_inv.
Qed.

(**
  The lemma just below essentially states that for every reachable state <<s>>,
  messages sent earlier are suffixes of messages sent later and that the
  messages are suffixes of the state <<s>>.

  More technically: if the observations of a reachable state <<s>> contain two
  sent messages <<m1>> and <<m2>> (with potentially some more observations
  in-between), then the state of <<m1>> is a state-suffix of the state of <<m2>>
  and also the state of <<m2>> is a state-suffix of <<s>>.
*)
Lemma state_suffix_totally_orders_sent_messages_Ri P :
  forall (s : State) (m1 m2 : Message) (obs1 obs2 obs3 : list Observation),
    s = MkState [] (adr s) <++>
      obs1 <+> MkObservation Send m1 <++> obs2 <+> MkObservation Send m2 <++> obs3 ->
    UMO_reachable P s ->
      state_suffix (state m1) (state m2) /\ state_suffix (state m2) s.
Proof.
  intros s m1 m2 obs1 obs2 obs3 -> Hvsp.
  apply UMO_reachable_addObservations_inv in Hvsp.
  assert (Hm2 := UMO_reachable_addObservation_inv_message _ _ _ Hvsp).
  apply UMO_reachable_addObservation_inv in Hvsp.
  apply UMO_reachable_addObservations_inv in Hvsp.
  assert (Hm1 := UMO_reachable_addObservation_inv_message _ _ _ Hvsp).
  cbn in *; rewrite Hm1, Hm2 by done;
  cbn in *; rewrite <- Hm1, <- Hm2 by done
  ; clear Hvsp Hm1 Hm2; split.
  - rewrite addObservations_app.
    by apply state_suffix_addObservations, ListExtras.last_not_null.
  - rewrite (addObservations_app _ _ obs3).
    by apply state_suffix_addObservations, ListExtras.last_not_null.
Qed.

(** [state_suffix_totally_orders_sent_messages_Ri] easily carries over to valid states. *)
Lemma state_suffix_totally_orders_sent_messages_Ui :
  forall (s : State) (m1 m2 : Message) (obs1 obs2 obs3 : list Observation),
    s = MkState [] (adr s) <++>
      obs1 <+> MkObservation Send m1 <++> obs2 <+> MkObservation Send m2 <++> obs3 ->
    valid_state_prop Ui s ->
      state_suffix (state m1) (state m2) /\ state_suffix (state m2) s.
Proof.
  intros s m1 m2 obs1 obs2 obs3 Heq Hvsp.
  eapply state_suffix_totally_orders_sent_messages_Ri; [done |].
  by apply UMO_reachable_Ui.
Qed.

(**
  The [message_suffix] relation is trichotomous on the [sentMessages] of any
  reachable state.
*)
Lemma state_suffix_totally_orders_sent_messages_Ri' P :
  forall (s : State) (m1 m2 : Message),
    UMO_reachable P s -> m1 ∈ sentMessages s -> m2 ∈ sentMessages s ->
      message_suffix m1 m2 \/ m1 = m2 \/ message_suffix m2 m1.
Proof.
  intros s m1 m2 Hvalid H1 H2.
  apply elem_of_sentMessages in H1, H2.
  destruct (elem_of_list_split_2 _ _ _ H1 H2) as [Heq | (obs1 & obs2 & obs3 & [H | H])]
  ; [right; left | right; right | left].
  - by congruence.
  - eapply state_suffix_totally_orders_sent_messages_Ri with (s := s); [| done].
    by apply eq_State; cbn; [rewrite app_nil_r |].
  - eapply state_suffix_totally_orders_sent_messages_Ri with (s := s); [| done].
    by apply eq_State; cbn; [rewrite app_nil_r |].
Qed.

(** [state_suffix_totally_orders_sent_messages_Ri'] transfers to [sentMessages] of valid states. *)
Lemma state_suffix_totally_orders_sent_messages_Ui' :
  forall (s : State) (m1 m2 : Message),
    valid_state_prop Ui s -> m1 ∈ sentMessages s -> m2 ∈ sentMessages s ->
      message_suffix m1 m2 \/ m1 = m2 \/ message_suffix m2 m1.
Proof.
  intros s m1 m2 Hvsp Hin1 Hin2.
  by eapply state_suffix_totally_orders_sent_messages_Ri';
    [apply UMO_reachable_Ui | ..].
Qed.

(** ** Observability

  Message [m1] is directly observable in message [m2] if [m1] is an element
  of the list of observation of [m2]'s state.

  It would be possible to use a different definition of [directly_observable],
  which goes by cases on whether the message was sent or received.
*)
Definition directly_observable (m1 m2 : Message) : Prop :=
  m1 ∈ map message (obs (state m2)).

(** Our definition is equivalent to the alternative definition. *)
Lemma directly_observable_spec_other :
  forall m1 m2 : Message,
    m1 ∈ map message (obs (state m2))
      <->
    m1 ∈ sentMessages (state m2) \/ m1 ∈ receivedMessages (state m2).
Proof.
  intros m1 m2.
  unfold sentMessages, sentMessages', receivedMessages, receivedMessages'.
  unfold Message; rewrite !elem_of_list_fmap.
  setoid_rewrite elem_of_list_filter.
  split.
  - intros (ob & Hm & Hin); subst.
    destruct (label ob) eqn: Hlob.
    + by right; exists ob; unfold isReceive; rewrite Hlob.
    + by left; exists ob; unfold isSend; rewrite Hlob.
  - intros [(ob & -> & Hs & Hin) | (ob & -> & Hs & Hin)].
    + by exists ob.
    + by exists ob.
Qed.

(** [observable] is the transitive closure of [directly_observable]. *)
Definition observable : relation Message :=
  tc directly_observable.

(**
  If [m1] is directly observable in a suffix of [m3], then it is also
  directly observable in [m3].
*)
Lemma message_suffix_directly_observable :
  forall m1 m2 m3 : Message,
    message_suffix m2 m3 -> directly_observable m1 m2 -> directly_observable m1 m3.
Proof.
  unfold directly_observable.
  intros [s1] [s2] [s3] (_ & [obs' Hsuf] & _) Hdo; cbn in *.
  by unfold Message; rewrite Hsuf, map_app, elem_of_app; right.
Qed.

(**
  [m] is directly observable in state [s] extended with new observation [ob]
  iff [m] is the message of [ob] or [m] is directly observable in [s].
*)
Lemma directly_observable_addObservation :
  forall (m : Message) (s : State) (ob : Observation),
    directly_observable m (MkMessage (s <+> ob))
      <->
    directly_observable m (MkMessage s) \/ m = message ob.
Proof.
  unfold directly_observable, Message.
  by intros m s ob; cbn; rewrite elem_of_cons; itauto.
Qed.

(**
  [directly_observable_addObservation] easily transfers to a situation in
  which we add multiple observations at once.
*)
Lemma directly_observable_addObservations :
  forall (m : Message) (s : State) (obs' : list Observation),
    directly_observable m (MkMessage (s <++> obs'))
      <->
    directly_observable m (MkMessage s) \/ m ∈ map message obs'.
Proof.
  unfold directly_observable, Message.
  by intros m s obs'; cbn; rewrite map_app, elem_of_app; itauto.
Qed.

(**
  In a reachable state, messages sent earlier are directly observable in
  messages sent later.
*)
Lemma directly_observable_totally_orders_sent_messages_Ri P :
  forall (s : State) (m1 m2 : Message) (obs1 obs2 obs3 : list Observation),
    s = MkState [] (adr s) <++>
      obs1 <+> MkObservation Send m1 <++> obs2 <+> MkObservation Send m2 <++> obs3 ->
    UMO_reachable P s ->
      directly_observable m1 m2.
Proof.
  intros s m1 m2 obs1 obs2 obs3 Heq Hvsp.
  rewrite Heq in Hvsp.
  apply UMO_reachable_addObservations_inv in Hvsp.
  apply UMO_reachable_addObservation_inv_message in Hvsp as Heq'; [| done].
  cbn in Heq'; subst; clear Heq Hvsp.
  repeat (rewrite ?directly_observable_addObservations, ?directly_observable_addObservation); cbn.
  by itauto.
Qed.

(**
  [directly_observable_totally_orders_sent_messages_Ri] can be
  transferred to valid states.
*)
Lemma directly_observable_totally_orders_sent_messages_Ui :
  forall (s : State) (m1 m2 : Message) (obs1 obs2 obs3 : list Observation),
    s = MkState [] (adr s) <++>
      obs1 <+> MkObservation Send m1 <++> obs2 <+> MkObservation Send m2 <++> obs3 ->
    valid_state_prop Ui s ->
      directly_observable m1 m2.
Proof.
  intros s m1 m2 obs1 obs2 obs3 Heq Hvsp.
  by eapply directly_observable_totally_orders_sent_messages_Ri, UMO_reachable_Ui.
Qed.

(**
  If <<ob>> belongs to the observations of a state <<s>>, we can decompose
  <<s>> into some state <<s'>> followed by <<ob>> and then possibly some
  more observations <<obs'>>.

  Moreover, if the observation was a sent message <<m>>, then we know that
  <<s'>> is <<state m>>.
*)

Lemma elem_of_obs_split :
  forall (s : State) (ob : Observation),
    ob ∈ obs s ->
      exists (s' : State) (obs' : list Observation),
        s = s' <+> ob <++> obs'.
Proof.
  intros s m Hin.
  apply elem_of_list_split in Hin as (obs1 & obs2 & Hobs); cbn.
  exists (MkState obs2 (adr s)), obs1.
  by apply eq_State; cbn.
Qed.

Lemma elem_of_valid_obs_Send_split P :
  forall (s : State) (m : Message),
    MkObservation Send m ∈ obs s -> UMO_reachable P s ->
      exists obs' : list Observation,
        s = state m <+> MkObservation Send m <++> obs'.
Proof.
  intros s m Hin Hvsp.
  apply elem_of_obs_split in Hin as (s' & obs' & ->).
  exists obs'; cbn.
  do 2 f_equal.
  by apply UMO_reachable_addObservations_inv, UMO_reachable_addObservation_inv_Send_state in Hvsp.
Qed.

Lemma elem_of_valid_obs_Send_valid P :
  forall (s : State) (m : Message),
    MkObservation Send m ∈ obs s -> UMO_reachable P s ->
      UMO_reachable P (state m).
Proof.
  intros s m Hin Hvsp.
  destruct (elem_of_valid_obs_Send_split _ _ _ Hin Hvsp) as [obs ->].
  by apply UMO_reachable_addObservations_inv, UMO_reachable_addObservation_inv_Send in Hvsp.
Qed.

(**
  [elem_of_obs_split] and [elem_of_valid_obs_Send_split] can be generalized to
  two observations <<ob1>> and <<ob2>> and from there to any numbers of observations.
*)

Lemma elem_of_obs_split_2 :
  forall (s : State) (ob1 ob2 : Observation),
    ob1 ∈ obs s -> ob2 ∈ obs s ->
      ob1 = ob2
        \/
      exists (s' : State) (obs1 obs2 : list Observation),
        s = s' <+> ob1 <++> obs1 <+> ob2 <++> obs2
          \/
        s = s' <+> ob2 <++> obs1 <+> ob1 <++> obs2.
Proof.
  intros s ob1 ob2 Hin1 Hin2.
  destruct (elem_of_list_split_2 _ _ _ Hin1 Hin2)
    as [Heq | (obs1 & obs2 & obs3 & [Heq | Heq])].
  - by left.
  - right; exists (MkState obs3 (adr s)), obs2, obs1.
    by right; apply eq_State; cbn.
  - right; exists (MkState obs3 (adr s)), obs2, obs1.
    by left; apply eq_State; cbn.
Qed.

Lemma elem_of_valid_obs_Send_split_2 P :
  forall (s : State) (m1 m2 : Message),
    MkObservation Send m1 ∈ obs s -> MkObservation Send m2 ∈ obs s ->
    UMO_reachable P s ->
      m1 = m2
        \/
      exists obs1 obs2 : list Observation,
        s = state m1 <+> MkObservation Send m1 <++> obs1 <+> MkObservation Send m2 <++> obs2
          \/
        s = state m2 <+> MkObservation Send m2 <++> obs1 <+> MkObservation Send m1 <++> obs2.
Proof.
  intros s m1 m2 Hin1 Hin2 Hvsp.
  destruct (elem_of_obs_split_2 _ _ _ Hin1 Hin2) as [Heq | (s' & obs1 & obs2 & [Heq | Heq])].
  - by left; congruence.
  - right; exists obs1, obs2; left; subst.
    do 4 f_equal.
    by eapply UMO_reachable_addObservation_inv_Send_state,
      UMO_reachable_addObservations_inv,
      UMO_reachable_addObservation_inv,
      UMO_reachable_addObservations_inv.
  - right; exists obs1, obs2; right; subst.
    do 4 f_equal.
    by eapply UMO_reachable_addObservation_inv_Send_state,
      UMO_reachable_addObservations_inv,
      UMO_reachable_addObservation_inv,
      UMO_reachable_addObservations_inv.
Qed.

(** If <<m>> belongs to [sentMessages] of <<s>>, then its state has the same address as <<s>>. *)
Lemma adr_of_sentMessages P :
  forall (s : State) (m : Message),
    UMO_reachable P s -> m ∈ sentMessages s ->
      adr (state m) = adr s.
Proof.
  intros s m Hvsp Hin.
  apply elem_of_sentMessages, elem_of_obs_split in Hin as (s' & obs' & ->); cbn.
  apply UMO_reachable_addObservations_inv in Hvsp.
  by destruct s'; inversion Hvsp.
Qed.

(**
  A message <<m>> belongs to the [sentMessages] of state <<s>> if and only if
  the state [state m <+> MkObservation Send m] is a (possibly improper)
  state suffix of <<s>>.
*)
Lemma sentMessages_characterization P :
  forall (s : State) (m : Message),
    UMO_reachable P s ->
      m ∈ sentMessages s
        <->
      let s' := state m <+> MkObservation Send m in
        state_suffix s' s \/ s' = s.
Proof.
  intros s m Hvsp; setoid_rewrite elem_of_sentMessages; split.
  - intros Hin; eapply elem_of_valid_obs_Send_split in Hin as (obs' & ->); [| done].
    destruct obs' as [| ob obs'].
    + by right.
    + by left; apply state_suffix_addObservations; inversion 1.
  - cbn; intros [(Hadr & (ob & ->) & Hobs2) | <-].
    + by apply elem_of_app; right; constructor.
    + by constructor.
Qed.

(**
  A message <<m1>> was sent before another message <<m2>> if they have the same
  address and <<m1>> appears in [sentMessages] of the state of <<m2>>.
*)
Definition was_sent_before (m1 m2 : Message) : Prop :=
  adr (state m1) = adr (state m2) /\ m1 ∈ sentMessages (state m2).

(**
  We can characterize [was_sent_before] in terms of [state_suffix] in two
  different ways, provided that the state of <<m2>> is reachable.
*)

Lemma was_sent_before_characterization_1 P :
  forall m1 m2 : Message,
    UMO_reachable P (state m2) ->
      was_sent_before m1 m2
        <->
      let s := state m1 <+> MkObservation Send m1 in
        state_suffix s (state m2) \/ s = state m2.
Proof.
  intros m1 m2 Hvsp; split.
  - intros [Hadr Hsent].
    apply elem_of_sentMessages in Hsent.
    eapply elem_of_valid_obs_Send_split in Hsent as (obs' & ->); [| done].
    destruct obs' as [| ob' obs']; cbn.
    + by right.
    + by left; apply state_suffix_addObservations; inversion 1.
  - intros [(Hadr & Hsuf & Hnsuf) | Heq]; cbn in *.
    + constructor; [done |].
      apply elem_of_sentMessages.
      destruct Hsuf as [obs' ->].
      unfold addObservation'.
      by rewrite elem_of_app, elem_of_cons; right; left.
    + constructor.
      * by apply (f_equal adr) in Heq; cbn in Heq.
      * by rewrite <- Heq; setoid_rewrite elem_of_sentMessages; left.
Qed.

Lemma was_sent_before_characterization_2 P :
  forall m1 m2 : Message,
    UMO_reachable P (state m2) ->
      was_sent_before m1 m2
        <->
      state_suffix (state m1 <+> MkObservation Send m1) (state m2 <+> MkObservation Send m2).
Proof.
  intros m1 m2 Hvsp; split.
  - intros [Hadr Hsent].
    eapply elem_of_sentMessages, elem_of_valid_obs_Send_split in Hsent as (obs' & ->); [| done].
    cbn; rewrite addObservation_cons.
    by apply state_suffix_addObservations; inversion 1.
  - intros (Hadr & Hsuf & Hnsuf).
    constructor; [done |].
    apply elem_of_sentMessages.
    destruct Hsuf as [obs' Heq].
    cbn in Heq; unfold addObservation' in Heq.
    unfold addObservation'.
    destruct obs' as [| ob' obs']; inversion Heq; subst.
    + by contradiction Hnsuf.
    + by rewrite H1, elem_of_app, elem_of_cons; right; left.
Qed.

(**
  The relation [was_sent_before] is trichotomous on the [sentMessages] of any
  reachable state.
*)
Lemma was_sent_before_totally_orders_sentMessages_Ri P :
  forall (s : State) (m1 m2 : Message),
    UMO_reachable P s -> m1 ∈ sentMessages s -> m2 ∈ sentMessages s ->
      was_sent_before m1 m2 \/ m1 = m2 \/ was_sent_before m2 m1.
Proof.
  intros s m1 m2 Hvsp Hin1 Hin2.
  apply elem_of_sentMessages in Hin1, Hin2.
  assert (Hvsp1 : UMO_reachable P (state m1)) by (eapply elem_of_valid_obs_Send_valid; done).
  assert (Hvsp2 : UMO_reachable P (state m2)) by (eapply elem_of_valid_obs_Send_valid; done).
  destruct (elem_of_valid_obs_Send_split_2 P s m1 m2 Hin1 Hin2)
    as [Heq | (obs1 & obs2 & [-> | ->])]; [done | | |]; clear Hin1 Hin2.
  - by right; left.
  - left.
    rewrite was_sent_before_characterization_2; [| done].
    apply UMO_reachable_addObservations_inv,
          UMO_reachable_addObservation_inv_Send_state in Hvsp.
    rewrite <- Hvsp, addObservation_cons.
    by apply state_suffix_addObservations; inversion 1.
  - right; right.
    rewrite was_sent_before_characterization_2; [| done].
    apply UMO_reachable_addObservations_inv,
          UMO_reachable_addObservation_inv_Send_state in Hvsp.
    rewrite <- Hvsp, addObservation_cons.
    by apply state_suffix_addObservations; inversion 1.
Qed.

(**
  Messages <<m1>> and <<m2>> are [sent_comparable] when <<m1 = m2>> or
  [was_sent_before m1 m2] or [was_sent_before m2 m1].
*)
Inductive sent_comparable : Message -> Message -> Prop :=
| sc_refl  : forall m : Message, sent_comparable m m
| sc_wsb_l : forall m1 m2 : Message, was_sent_before m1 m2 -> sent_comparable m1 m2
| sc_wsb_r : forall m1 m2 : Message, was_sent_before m2 m1 -> sent_comparable m1 m2.

(**
  Messages <<m1>> and <<m2>> are [incomparable] if they have the same sender
  and are not [sent_comparable].

  Note that [incomparable] is not simply a negation of [sent_comparable], so
  that there can be messages which are neither [sent_comparable] nor
  [incomparable].
*)
Definition incomparable (m1 m2 : Message) : Prop :=
  adr (state m1) = adr (state m2) /\ ~ sent_comparable m1 m2.

End sec_UMOComponent_lemmas.

#[export] Instance sent_comparable_sym : Symmetric sent_comparable.
Proof. by intros x y []; constructor. Defined.

#[export] Instance sent_comparable_dec : RelDecision sent_comparable.
Proof.
  intros m1 m2.
  destruct (decide (adr (state m1) = adr (state m2)));
    [| by right; destruct 1; apply n; firstorder congruence].
  destruct (decide (obs (state m1) = obs (state m2)));
    [by left; replace m2 with m1 by (apply eq_Message; done); constructor |].
  destruct (decide (m1 ∈ sentMessages (state m2)));
    [by left; constructor; constructor |].
  destruct (decide (m2 ∈ sentMessages (state m1)));
    [by left; constructor; constructor |].
  by right; destruct 1; firstorder.
Defined.

#[export] Instance incomparable_sym : Symmetric incomparable.
Proof. by intros x y []; constructor. Defined.

Section sec_UMOProtocol.

Context
  (index : Type)
  `{finite.Finite index}
  (idx : index -> Address)
  `{!Inj (=) (=) idx}
  (U : index -> VLSM Message := fun i => UMOComponent (idx i))
  (R : index -> VLSM Message := fun i => pre_loaded_with_all_messages_vlsm (U i)).

(** ** Protocol

  The UMO protocol is a free composition of finitely many UMO components.
  To talk about reachable states in the UMO protocol, we will use [RUMO],
  which is UMO preloaded with all messages.
*)

Definition UMO : VLSM Message := free_composite_vlsm U.
Definition RUMO : VLSM Message := pre_loaded_with_all_messages_vlsm UMO.

(** We set up aliases for some functions operating on free VLSM composition. *)

Definition UMO_state : Type := composite_state U.
Definition UMO_label : Type := composite_label U.
Definition UMO_transition_item : Type := composite_transition_item U.

(** We can lift labels, states and traces from an UMO component to the UMO protocol. *)

Definition lift_to_UMO_label
  (i : index) (li : VLSM.label (U i)) : UMO_label :=
    lift_to_composite_label U i li.

Definition lift_to_UMO_state
  (us : UMO_state) (i : index) (si : VLSM.state (U i)) : UMO_state :=
    lift_to_composite_state U us i si.

Definition lift_to_UMO_trace
  (us : UMO_state) (i : index) (tr : list (transition_item (U i)))
  : list UMO_transition_item :=
    pre_VLSM_embedding_finite_trace_project
      _ _ (lift_to_UMO_label i) (lift_to_UMO_state us i) tr.

(**
  We can also lift properties from UMO components to the UMO protocol, among
  them [valid_state_prop], [valid_message_prop], [input_valid_transition]
  and the various kinds of traces.
*)

Lemma lift_to_UMO :
  forall (us : UMO_state) (Hus : valid_state_prop UMO us) (i : index),
    VLSM_weak_embedding (U i) UMO (lift_to_UMO_label i) (lift_to_UMO_state us i).
Proof. by intros; apply lift_to_free_weak_embedding. Qed.

Lemma lift_to_UMO_valid_state_prop :
  forall (i : index) (s : State) (us : UMO_state),
    valid_state_prop UMO us -> valid_state_prop (U i) s ->
      valid_state_prop UMO (lift_to_UMO_state us i s).
Proof.
  intros is s us Hvsp.
  by eapply VLSM_weak_embedding_valid_state, lift_to_UMO.
Qed.

Lemma lift_to_UMO_valid_message_prop :
  forall (i : index) (om : option Message),
    option_valid_message_prop (U i) om ->
      option_valid_message_prop UMO om.
Proof.
  intros i [] Hovmp; cycle 1.
  - exists (fun i => MkState [] (idx i)). by constructor; compute.
  - eapply VLSM_weak_embedding_valid_message.
    + by apply (lift_to_UMO (fun i => MkState [] (idx i))); exists None; constructor.
    + by inversion 1.
    + by apply Hovmp.
Qed.

Lemma lift_to_UMO_input_valid_transition :
  forall (i : index) (lbl : Label) (s1 s2 : State) (iom oom : option Message) (us : UMO_state),
    valid_state_prop UMO us ->
    input_valid_transition (U i) lbl (s1, iom) (s2, oom) ->
      input_valid_transition UMO
        (lift_to_UMO_label i lbl)
        (lift_to_UMO_state us i s1, iom)
        (lift_to_UMO_state us i s2, oom).
Proof.
  intros i lbl s1 s2 iom oom us Hivt.
  by apply @VLSM_weak_embedding_input_valid_transition, lift_to_UMO.
Qed.

Lemma lift_to_UMO_finite_valid_trace_from_to :
  forall (i : index) (s1 s2 : State) (tr : list (transition_item (U i))) (us : UMO_state),
    valid_state_prop UMO us ->
    finite_valid_trace_from_to (U i) s1 s2 tr ->
      finite_valid_trace_from_to
        UMO (lift_to_UMO_state us i s1) (lift_to_UMO_state us i s2) (lift_to_UMO_trace us i tr).
Proof.
  intros i s1 s2 tr us Hvsp Hfvt.
  by eapply (VLSM_weak_embedding_finite_valid_trace_from_to (lift_to_UMO _ Hvsp i)).
Qed.

(** We could prove the same lifting lemmas for [RUMO], but we won't need them. *)

Lemma lift_to_RUMO
  (us : UMO_state) (Hus : valid_state_prop RUMO us) (i : index) :
  VLSM_weak_embedding (R i) RUMO (lift_to_UMO_label i) (lift_to_UMO_state us i).
Proof. by apply lift_to_preloaded_free_weak_embedding. Qed.

Lemma lift_to_RUMO_finite_valid_trace_from_to :
  forall (i : index) (s1 s2 : State) (tr : list (transition_item (R i))) (us : UMO_state),
    valid_state_prop RUMO us ->
    finite_valid_trace_from_to (R i) s1 s2 tr ->
      finite_valid_trace_from_to
        RUMO (lift_to_UMO_state us i s1) (lift_to_UMO_state us i s2) (lift_to_UMO_trace us i tr).
Proof.
  intros i s1 s2 tr us Hvsp Hfvt.
  by apply (VLSM_weak_embedding_finite_valid_trace_from_to (lift_to_RUMO _ Hvsp i)).
Qed.

Lemma lift_to_UMO_constrained_state_prop :
  forall (i : index) (s : State) (us : UMO_state),
    constrained_state_prop UMO us ->
    constrained_state_prop (U i) s ->
    constrained_state_prop UMO (lift_to_UMO_state us i s).
Proof.
  unfold constrained_state_prop.
  intros is s us Hcsp.
  by eapply VLSM_weak_embedding_valid_state, lift_to_RUMO.
Qed.

(**
  Every state in a UMO component gives rise to a unique trace leading to this
  state, which we can then lift to the UMO protocol.
*)
Definition UMOComponent_state2trace
  (s : UMO_state) (i : index) : list UMO_transition_item :=
    lift_to_UMO_trace s i (state2trace (s i)).

(**
  Iterating [UMOComponent_state2trace] shows that every reachable UMO state
  contains a trace that leads to this state. However, this trace is not unique,
  because we can concatenate the lifted traces in any order.
*)
Fixpoint UMO_state2trace_aux
  (us : UMO_state) (is : list index) : list UMO_transition_item :=
  match is with
  | [] => []
  | i :: is' =>
    UMO_state2trace_aux (state_update _ us i (MkState [] (idx i))) is' ++
    UMOComponent_state2trace us i
  end.

Definition UMO_state2trace
  (us : UMO_state) : list UMO_transition_item :=
    UMO_state2trace_aux us (enum index).

Lemma finite_valid_trace_from_to_UMO_state2trace_RUMO :
  forall us : UMO_state,
    valid_state_prop RUMO us ->
      finite_valid_trace_init_to RUMO (``(vs0 RUMO)) us (UMO_state2trace us).
Proof.
  intros us Hvsp; split; [| done].
  unfold UMO_state2trace.
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
        apply Hall. rewrite elem_of_cons. by intros [].
      * by apply pre_composite_free_update_state_with_initial.
    + replace us with (state_update U us i (us i)) at 2 by (state_update_simpl; done).
      apply lift_to_RUMO_finite_valid_trace_from_to; [done |].
      apply (valid_state_project_preloaded_to_preloaded_free _ _ us i) in Hvsp as Hvsp'.
      apply valid_state_has_trace in Hvsp' as (s & tr & [Hfvt Hinit]).
      replace s with (MkState [] (idx i)) in *; cycle 1.
      * by inversion Hinit; destruct s; cbn in *; subst.
      * by eapply finite_valid_trace_init_to_state2trace_Ri.
Qed.

(**
  It turns out that [finite_valid_trace_from_to_UMO_state2trace_RUMO]
  also holds for valid states.
*)
Lemma finite_valid_trace_from_to_UMO_state2trace_UMO :
  forall us : UMO_state,
    valid_state_prop UMO us ->
      finite_valid_trace_init_to UMO (``(vs0 UMO)) us (UMO_state2trace us).
Proof.
  intros us Hvsp.
  apply all_pre_traces_to_valid_state_are_valid_free; [typeclasses eauto | done |].
  apply finite_valid_trace_from_to_UMO_state2trace_RUMO.
  eapply (@VLSM_incl_valid_state _ UMO UMO RUMO); [| done].
  by apply vlsm_incl_pre_loaded_with_all_messages_vlsm.
Qed.

Fixpoint UMO_obs_aux (us : UMO_state) (is : list index) : list Observation :=
  match is with
  | [] => []
  | i :: is' => UMO_obs_aux (state_update _ us i (MkState [] (idx i))) is' ++ obs (us i)
  end.

Definition UMO_obs (us : UMO_state) : list Observation :=
  UMO_obs_aux us (enum index).

Fixpoint UMO_sentMessages_aux (us : UMO_state) (is : list index) : set Message :=
  match is with
  | [] => []
  | i :: is' =>
    UMO_sentMessages_aux (state_update _ us i (MkState [] (idx i))) is' ++ sentMessages (us i)
  end.

Definition UMO_sentMessages (us : UMO_state) : set Message :=
  UMO_sentMessages_aux us (enum index).

Fixpoint UMO_receivedMessages_aux (us : UMO_state) (is : list index) : set Message :=
  match is with
  | [] => []
  | i :: is' =>
    UMO_receivedMessages_aux (state_update _ us i (MkState [] (idx i))) is' ++ receivedMessages (us i)
  end.

Definition UMO_receivedMessages (us : UMO_state) : set Message :=
  UMO_receivedMessages_aux us (enum index).

Fixpoint UMO_messages_aux (us : UMO_state) (is : list index) : set Message :=
  match is with
  | [] => []
  | i :: is' =>
    UMO_messages_aux (state_update _ us i (MkState [] (idx i))) is' ++ messages (us i)
  end.

Definition UMO_messages (us : UMO_state) : set Message :=
  UMO_messages_aux us (enum index).

Lemma valid_state_prop_state_update_init :
  forall (us : UMO_state) (i : index),
    valid_state_prop RUMO us ->
      valid_state_prop RUMO (state_update U us i (MkState [] (idx i))).
Proof.
  intros us i Hvsp.
  by apply pre_composite_free_update_state_with_initial.
Qed.

Lemma elem_of_UMO_sentMessages :
  forall (us : UMO_state) (m : Message) (i : index),
    valid_state_prop RUMO us -> idx i = adr (state m) ->
      m ∈ UMO_sentMessages us <-> m ∈ sentMessages (us i).
Proof.
  intros us m i Hvsp Hidx.
  assert (Hall : forall i, i ∉ enum index -> us i = MkState [] (idx i))
    by (intros j Hin; contradict Hin; apply elem_of_enum).
  revert us m i Hvsp Hidx Hall.
  unfold UMO_sentMessages; generalize (enum index) as is.
  induction is as [| i' is']; intros; [by rewrite Hall; [| apply not_elem_of_nil] |].
  cbn in *; unfold State, Observation, Message in *; rewrite elem_of_app.
  assert (Hvsp' :
    forall j, valid_state_prop (pre_loaded_with_all_messages_vlsm (UMOComponent (idx j))) (us j))
    by (intro j; apply (preloaded_valid_state_projection _ _ _ Hvsp); done).
  split; cycle 1.
  - intros Hin.
    destruct (decide (i = i')); subst; [by right |].
    left. unfold Message, State, Observation in *; cbn.
    rewrite (IHis' (state_update U us i' (MkState [] (idx i'))) m i).
    + by state_update_simpl.
    + by apply valid_state_prop_state_update_init.
    + erewrite adr_of_sentMessages, adr_of_valid_state_Ri; [done | .. | done].
      * by rewrite <- Hidx; apply Hvsp'.
      * by eapply UMO_reachable_Ri, Hvsp'.
    + intros j Hnin. destruct (decide (i' = j)); subst.
      * by state_update_simpl.
      * by state_update_simpl; apply Hall; inversion 1.
  - intros [Hin | Hin]; cycle 1.
    + eapply adr_of_sentMessages in Hin as Hin';
        [| by eapply UMO_reachable_Ri, Hvsp'].
      erewrite Hin', adr_of_valid_state_Ri in Hidx by apply Hvsp'.
      by apply Inj0 in Hidx; subst.
    + rewrite (IHis' _ _ i) in Hin; [| | done |].
      * by destruct (decide (i = i')); subst; state_update_simpl; [inversion Hin |].
      * by apply valid_state_prop_state_update_init.
      * intros j Hnin. destruct (decide (i' = j)); subst; state_update_simpl; [done |].
        by apply Hall; inversion 1.
Qed.

Lemma UMO_sentMessages_characterization :
  forall (us : UMO_state) (m : Message) (i : index),
    valid_state_prop RUMO us -> idx i = adr (state m) ->
      m ∈ UMO_sentMessages us
        <->
      let s' := state m <+> MkObservation Send m in
        state_suffix s' (us i) \/ s' = us i.
Proof.
  intros us m i Hvsp Hidx.
  rewrite elem_of_UMO_sentMessages by done.
  rewrite <- sentMessages_characterization; [done |].
  by apply @UMO_reachable_Ri with (idx i),
    (preloaded_valid_state_projection _ _ _ Hvsp).
Qed.

End sec_UMOProtocol.

End sec_UMO.

Arguments UMO_reachable_ind' [Address]%type_scope (C P Hinit Hextend)%function_scope s Hs.
