From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude finite.
From Coq Require Import Recdef.
From Coq Require Import Reals.
From VLSM.Lib Require Import Preamble Measurable ListExtras StdppExtras StdppListSet.
From VLSM.Core Require Import VLSM VLSMProjections ProjectionTraces.
From VLSM.Core Require Import Composition Equivocation.

(** * Legacy Definitions and Lemmas for the ELMO protocol *)

Inductive Label :=
 | Receive
 | Send.

Inductive Prestate : Type := St {
  observations : list Observation;
}

with Observation : Type := Ob {
  label   : Label;
  premessage : Premessage;
  witness : nat; (* TODO: remove *)
}

with Premessage : Type := Msg {
  prestate : Prestate;
  author : nat;
}.

(** [Prestate]s, [Observation]s and [Premessage]s are printed like ordinary inductives,
    using their constructor names, instead of as records with the {| ... |} notation. *)
#[local] Unset Printing Records.

(* For now, the induction principle seems to be unused. *)
Section induction_principle.

Context
  (Pps : Prestate -> Prop)
  (Plo : list Observation -> Prop)
  (Pob : Observation -> Prop)
  (Ppm : Premessage -> Prop)
  (Hps : forall ps : Prestate, Plo (observations ps) -> Pps ps)
  (Hlonil : Plo nil)
  (Hlocons : forall (a : Observation) (l : list Observation),
      Pob a ->
      Plo l ->
      Plo (a::l)
  )
  (Hob : forall ob : Observation,
      Ppm (premessage ob) ->
      Pob ob)
  (Hpm : forall pm : Premessage,
      Pps (prestate pm) ->
      Ppm pm)
  .

Fixpoint Prestate_mut_ind (p : Prestate) : Pps p :=

  let ListObservation_mut_ind :=
    fix ListObservation_mut_ind (lo : list Observation) : Plo lo :=
      match lo with
      | [] => Hlonil
      | y :: lo0 => Hlocons y lo0 (Observation_mut_ind y) (ListObservation_mut_ind lo0)
      end
  in

  Hps p (ListObservation_mut_ind (observations p))

with Observation_mut_ind (ob : Observation) : Pob ob :=
  Hob ob (Premessage_mut_ind (premessage ob))

with Premessage_mut_ind (pm : Premessage) : Ppm pm :=
  Hpm pm (Prestate_mut_ind (prestate pm))
.

End induction_principle.

#[export] Instance Label_eqdec : EqDecision Label.
Proof.
  unfold EqDecision, Decision.
  decide equality.
Qed.

#[local] Lemma Prestate_eq_dec' :
  forall (s1 s2 : Prestate), {s1 = s2} + {s1 <> s2}

with  Observation_eq_dec' :
  forall (o1 o2 : Observation), {o1 = o2} + {o1 <> o2}

with  Premessage_eq_dec' :
  forall (m1 m2 : Premessage), {m1 = m2} + {m1 <> m2}.
Proof.
  all: repeat decide equality.
Qed.

#[export] Instance Prestate_eq_dec : EqDecision Prestate := Prestate_eq_dec'.
#[export] Instance Observation_eq_dec : EqDecision Observation := Observation_eq_dec'.
#[export] Instance Premessage_eq_dec : EqDecision Premessage := Premessage_eq_dec'.

Definition dummy_prestate := St [].
Definition dummy_premessage := Msg dummy_prestate 0.
Definition dummy_observation := Ob Receive dummy_premessage 0.

#[export] Instance Prestate_inhabited : Inhabited Prestate := populate dummy_prestate.
#[export] Instance Premessage_inhabited : Inhabited Premessage := populate dummy_premessage.
#[export] Instance Observation_inhabited : Inhabited Observation := populate dummy_observation.

Definition isWitnessedBy (component : nat) (ob : Observation) : Prop :=
  witness ob = component.

#[export] Instance isWitnessedBy_dec (component : nat) (ob : Observation) : Decision (isWitnessedBy component ob).
Proof.
  unfold isWitnessedBy.
  typeclasses eauto.
Defined.

Definition isReceive (ob : Observation) : Prop :=
  match label ob with
  | Receive => True
  | _ => False
  end.

#[export] Instance isReceive_dec (ob : Observation) : Decision (isReceive ob).
Proof.
  by destruct ob as [[] p n]; compute; [left|right].
Defined.

Definition isSend (ob : Observation) : Prop :=
  match label ob with
  | Send => True
  | _ => False
  end.

#[export] Instance isSend_dec (ob : Observation) : Decision (isSend ob).
Proof.
  by destruct ob as [[] p n]; compute; [right|left].
Defined.

#[export] Instance elmo_type : VLSMType Premessage :=
  {| state := Prestate;
     VLSM.label := Label;
  |}.

Definition elmo_state : Type := @state Premessage elmo_type.

Definition elmo_initial_state_prop (ps : elmo_state) : Prop :=
  observations ps = [].

Definition elmo_initial_state : Type :=
  {s : elmo_state | elmo_initial_state_prop s}.

Definition elmo_s0 : elmo_initial_state :=
  exist _ (St []) eq_refl.

#[export] Instance elmo_initial_state_inh : Inhabited elmo_initial_state := {| inhabitant := elmo_s0 |}.

Definition haveCorrespondingObservation
  (prefix : list Observation) (component : nat) (ob : Observation)
    : Prop :=
  if decide (author (premessage ob) = component)
  then
    Ob Send (premessage ob) component ∈ prefix
  else
    Ob Receive (premessage ob) component ∈ prefix.

#[export] Instance haveCorrespondingObservation_dec prefix component ob :
  Decision (haveCorrespondingObservation prefix component ob).
Proof.
  unfold haveCorrespondingObservation.
  destruct (decide (author (premessage ob) = component)); typeclasses eauto.
Defined.

(** Check that every message received or sent in <<m>> has been received in the
    prefix by the component.
*)
Definition fullNode (m : Premessage) (prefix : list Observation) (component : nat) : Prop :=
  Forall (haveCorrespondingObservation prefix component) (observations (prestate m)).

#[export] Instance fullNode_dec m prefix component : Decision (fullNode m prefix component).
Proof.
  typeclasses eauto.
Defined.

#[local] Instance Rlt_dec' (r1 r2 : R) : Decision (r1 < r2)%R.
Proof.
  red. apply Rlt_dec.
Defined.

Definition nth_update {A : Type} (l : list A) (idx : nat) (v : A) : list A :=
  firstn idx l ++ v :: skipn (S idx) l.

(* FIXME: consistently use Prop and decidability instead of bool *)
Definition update
  (m : Premessage)
  (weights : list pos_R)
  (othreshold : option R)
  (curState : list Prestate)
  (curEq : set nat)
  : bool * list Prestate * set nat
  :=
  let p := prestate m in
  let a := author m in
  let lp := length (observations p) in
  let ca := nth a curState dummy_prestate in
  let la := length (observations ca) in
  if
    decide (la <=? lp /\ firstn la (observations p) = observations ca)
  then
    (true, nth_update curState a (St (observations p ++ [Ob Send m a])), curEq)
  else if
    decide
      (S lp <=? la /\
      firstn lp (observations ca) = observations p /\
      nth lp (observations ca) dummy_observation = Ob Send m a)
  then
    (true, curState, curEq)
  else
    match othreshold with
    | Some threshold =>
      let newEq := set_add a curEq in
      if
        decide
          ((@sum_weights _ {| weight idx := nth idx weights (exist _ 1%R Rlt_0_1) |} newEq)
            <
          threshold)%R
      then
        (false, curState, curEq)
      else
        (true, curState, newEq)
    | None => (true, curState, curEq)
    end.

Functional Scheme update_ind := Induction for update Sort Prop.

Record Args : Type := Arg {
  result : bool;
  idx : nat;
  curState : list Prestate;
  curEq : set nat;
}.

(* FIXME: consistently use Prop and decidability instead of bool *)
Definition isProtocol_step
  (component : nat)
  (weights : list pos_R)
  (othreshold : option R)
  (obs : list Observation)
  (args : Args)
  (ob : Observation)
  : Args
  :=
    let '(Arg result i  curState curEq) := args in
    match result with
    | false => args
    | true =>
      let l := label ob in
      let m := premessage ob in
      let p := prestate m in
      let a := author m in
      let w := witness ob in
      let prefix := firstn i obs in
      let i := S i in
      (* w <> component *)
      if decide (w <> component) then
        Arg false i curState curEq
      else (* w = component *)
        if decide (a = component) then
          match l with
          | Send =>
            let result := bool_decide (observations p = prefix) in
              Arg result i curState curEq
          | Receive =>
            let result := bool_decide (Ob Send m component ∈ prefix) in
              Arg result i curState curEq
          end
        else
          (* a <> component *)
          match l with
          | Send =>
              Arg false i curState curEq
          | Receive =>
            if decide (fullNode m prefix component) then
              let '(result, newState, newEq) := update m weights othreshold curState curEq in
                Arg result i newState newEq
            else
              Arg false i curState curEq
          end
    end.

Functional Scheme isProtocol_step_ind := Induction for isProtocol_step Sort Prop.

(* FIXME: consistently use Prop and decidability instead of bool *)
Fixpoint isProtocol_aux
  (component : nat)
  (weights : list pos_R)
  (othreshold: option R)
  (obs1 obs2 : list Observation)
  (args : Args)
  : Args :=
  match obs2 with
  | [] => args
  | ob :: obs =>
      isProtocol_aux
        component weights othreshold
        obs1 obs
        (isProtocol_step component weights othreshold obs1 args ob)
  end.

Functional Scheme isProtocol_aux_ind := Induction for isProtocol_aux Sort Prop.

(* FIXME: consistently use Prop and decidability instead of bool *)
Definition isProtocol
  (prestate : Prestate)
  (component : nat)
  (weights : list pos_R)
  (othreshold: option R)
  : bool :=
    (isProtocol_aux
      component weights othreshold
      (observations prestate)
      (observations prestate)
      (Arg true 0 (map (fun x => St []) weights) [])).(result).

Section isProtocolLemmas.

Context
  {component : nat}
  {weights : list pos_R}
  {othreshold : option R}.

Lemma isProtocol_step_false {l args ob} :
  args.(result) = false ->
    isProtocol_step component weights othreshold l args ob = args.
Proof.
  by destruct args; cbn; intros ->.
Qed.

Lemma isProtocol_step_true_idx {l args ob res} :
  isProtocol_step component weights othreshold l args ob = res ->
    args.(result) = true ->
      res.(idx) = S args.(idx).
Proof.
  by functional induction isProtocol_step component weights othreshold l args ob;
  cbn; intros; subst; simpl.
Qed.

Lemma isProtocol_step_inv {l args ob} :
  let res := isProtocol_step component weights othreshold l args ob in
    res.(result) = true ->
      args.(result) = true /\
      res.(idx) = S args.(idx).
Proof.
  by functional induction isProtocol_step component weights othreshold l args ob; simpl.
Qed.

Lemma isProtocol_step_inv_result {l args ob} :
  let res := isProtocol_step component weights othreshold l args ob in
    res.(result) = true ->
      args.(result) = true.
Proof.
  by intros res [H _]%isProtocol_step_inv.
Qed.

Lemma isProtocol_step_inv_idx {l args ob} :
  let res := isProtocol_step component weights othreshold l args ob in
    res.(result) = true ->
      res.(idx) = S args.(idx).
Proof.
  by intros res [_ H]%isProtocol_step_inv.
Qed.

Lemma isProtocol_aux_false {l1 l2 args} :
  args.(result) = false ->
    isProtocol_aux component weights othreshold l1 l2 args = args.
Proof.
  functional induction isProtocol_aux component weights othreshold l1 l2 args; [done |].
  by destruct args as [b i s e]; cbn [result]; intros ->; apply IHa.
Qed.

Lemma isProtocol_aux_inv_result {l1 l2 args} :
  (isProtocol_aux component weights othreshold l1 l2 args).(result) = true ->
    args.(result) = true.
Proof.
  intro H.
  destruct args as [[] i s e]; [done |].
  by rewrite isProtocol_aux_false in H.
Qed.

Lemma isProtocol_aux_inv_idx {l1 l2 args} :
  let res := isProtocol_aux component weights othreshold l1 l2 args in
    res.(result) = true -> res.(idx) = args.(idx) + length l2.
Proof.
  functional induction isProtocol_aux component weights othreshold l1 l2 args.
  - cbn. lia.
  - functional induction isProtocol_step component weights othreshold l1 args ob.
    1-6: cbn in *; rewrite <- plus_n_Sm; auto.
    rewrite ?isProtocol_aux_false in *; done.
Qed.

Lemma isProtocol_step_app {l1 l2 args ob} :
  args.(idx) <= length l1 ->
    isProtocol_step component weights othreshold (l1 ++ l2) args ob
      =
    isProtocol_step component weights othreshold l1 args ob.
Proof.
  intros Hidx.
  destruct args as [b i s e]; cbn in * |-.
  assert (Hidx': i - length l1 = 0) by lia.
  unfold isProtocol_step.
  by rewrite !firstn_app, !Hidx', !app_nil_r.
Qed.

Lemma isProtocol_aux_app_l {l1 l2 l3 args} :
  length l3 + args.(idx) <= length l1 ->
    isProtocol_aux component weights othreshold (l1 ++ l2) l3 args
      =
    isProtocol_aux component weights othreshold l1 l3 args.
Proof.
  functional induction isProtocol_aux component weights othreshold l1 l3 args;
  cbn; intro Hlen; [done |].
  destruct (args.(result)) eqn: Hresult; cycle 1.
  - rewrite !isProtocol_step_false in * by done.
    apply IHa. lia.
  - rewrite isProtocol_step_app by itauto lia.
    apply (isProtocol_step_true_idx (l := l1) (ob := ob) eq_refl) in Hresult.
    apply IHa. lia.
Qed.

Lemma isProtocol_aux_app_r {l1 l2 l3 args} :
  isProtocol_aux component weights othreshold l1 (l2 ++ l3) args
    =
  isProtocol_aux component weights othreshold l1 l3
    (isProtocol_aux component weights othreshold l1 l2 args).
Proof.
  by functional induction isProtocol_aux component weights othreshold l1 l2 args; cbn.
Qed.

Lemma isProtocol_aux_last {l ob} :
  isProtocol (St (l ++ [ob])) component weights othreshold = true ->
    isProtocol (St l) component weights othreshold = true.
Proof.
  unfold isProtocol; cbn.
  rewrite isProtocol_aux_app_r; cbn.
  intros H%isProtocol_step_inv_result.
  by rewrite isProtocol_aux_app_l in H by (cbn; lia).
Qed.

Lemma isProtocol_extend l ob :
  othreshold = None ->
  witness ob = component ->
  (label ob = Receive -> author (premessage ob) ≠ component ->
    fullNode (premessage ob) l component ) ->
  (label ob = Receive -> author (premessage ob) = component ->
    Ob Send (premessage ob) component ∈ l) ->
  (label ob = Send ->
    observations (prestate (premessage ob)) = l /\
    author (premessage ob) = component) ->
  isProtocol (St l) component weights othreshold = true ->
    isProtocol (St (l ++ [ob])) component weights othreshold = true.
Proof.
  intros Hothreshold Hwo Hfn Hrecv Hsend H.
  unfold isProtocol; simpl.
  rewrite isProtocol_aux_app_r; simpl.
  unfold isProtocol in H; simpl in H.
  rewrite isProtocol_aux_app_l by (cbn; lia).
  remember (isProtocol_aux component weights othreshold l l
                      (Arg true 0 (map (λ _ : pos_R, St []) weights) [])) as FL.
  destruct FL as [b' n' curState' curEq'].
  simpl in H. inversion H. subst b'.
  pose proof (Hidx := @isProtocol_aux_inv_idx l l (Arg true 0 (map (λ _ : pos_R, St []) weights) [])).
  rewrite <- HeqFL in Hidx. specialize (Hidx eq_refl).
  simpl in Hidx; subst n'. simpl.
  destruct (decide (witness ob <> component)) eqn:Hwo'; [done | simpl].
  rewrite take_app.
  destruct (decide (author (premessage ob) = component)) eqn: Hao',
           (label ob) eqn: Hlbl; simpl.
  - apply bool_decide_eq_true. firstorder.
  - apply bool_decide_eq_true. firstorder.
  - destruct (decide (fullNode (premessage ob) l component)); simpl in *; [| auto].
    destruct (update (premessage ob) weights othreshold curState' curEq')
          as [[b'' curState''] curEq''] eqn: HeqU.
    unfold update in HeqU. subst othreshold. simpl in HeqU.
    repeat match goal with
    | H : context [if ?x then _ else _] |- _ => destruct x
    | H : (true, _, _) = (b'', _, _) |- _ => by inversion H
    end.
  - firstorder.
Qed.

Lemma isProtocol_last_sendInPrefix {l p n0} :
  isProtocol (St (l ++ [Ob Receive (Msg p component) n0])) component weights othreshold = true ->
    Ob Send (Msg p component) component ∈ l.
Proof.
  intros Hproto.
  unfold isProtocol in Hproto; simpl in Hproto.
  rewrite isProtocol_aux_app_r in Hproto; simpl in Hproto.
  remember (isProtocol_aux component weights othreshold
              (l ++ [Ob Receive (Msg p component) n0]) l
              (Arg true 0 (map (fun _ => St []) weights) [])) as FL.
  unfold isProtocol_step in Hproto at 1.
  destruct FL as [[] i curState curEq]; simpl in Hproto; [| congruence].
  destruct (decide (n0 <> component)); simpl in Hproto; [congruence |].
  rewrite decide_True in Hproto; [| done].
  apply bool_decide_eq_true in Hproto.
  pose proof (Hidx := @isProtocol_aux_inv_idx
                        (l ++ [Ob Receive (Msg p component) n0])
                        l (Arg true 0 (map (fun _ => St []) weights) [])).
  rewrite <- HeqFL in Hidx. specialize (Hidx (eq_refl _)).
  simpl in Hidx; subst i.
  by rewrite firstn_app, Nat.sub_diag, take_0, app_nil_r, firstn_all in Hproto.
Qed.

End isProtocolLemmas.

Definition elmo_valid
  (addresses : list nat)
  (component : nat)
  (weights : list pos_R)
  (othreshold : option R)
  (label : Label)
  (bsom : Prestate * option Premessage)
    : Prop :=
  let '(state, message) := bsom in
  match label, message with
  | Send   , None   => True
  | Send   , Some _ => False
  | Receive, None   => False
  | Receive, Some m =>
    author m ∈ addresses /\
    fullNode m (observations state) component /\
    (author m = component -> Ob Send m component ∈ observations state) /\
    isProtocol (prestate m) (author m) weights othreshold
  end.

Definition elmo_transition
  (component : nat)
  (label : VLSM.label)
  (bsom : Prestate * option Premessage)
  : Prestate * option Premessage
  :=
  let '(state, message) := bsom in
  match label, message with
  | Send, Some _ => (state, None)
  | Send, None   =>
    let m := Msg state component in
    let ob := Ob Send m component in
    let s := St (observations state ++ [ob]) in
      (s, Some m)
  | Receive, None => (state, None)
  | Receive, Some msg =>
    let ob := Ob Receive msg component in
    let s := St (observations state ++ [ob]) in
      (s, None)
  end.

Functional Scheme elmo_transition_ind := Induction for elmo_transition Sort Prop.

Definition elmo_vlsm_machine
  (addresses : list nat)
  (component : nat)
  (weights : list pos_R)
  (othreshold : option R)
  : VLSMMachine elmo_type
  :=
  {| initial_state_prop := elmo_initial_state_prop;
     initial_message_prop := fun _ => False;
     valid := elmo_valid addresses component weights othreshold;
     transition := elmo_transition component
  |}.

Section capabilities.

Context
  (addresses : list nat)
  (component : nat)
  (weights : list pos_R)
  (othreshold : option R)
  (vlsm := mk_vlsm (elmo_vlsm_machine addresses component weights othreshold))
  .

Definition elmo_has_been_received_oracle (s : Prestate) (m : Premessage) : Prop :=
  m ∈ map premessage (filter isReceive (filter (isWitnessedBy component) (observations s))).

Definition elmo_has_been_sent_oracle (s : Prestate) (m : Premessage) : Prop :=
  m ∈ map premessage (filter isSend (filter (isWitnessedBy component) (observations s))).

Instance elmo_has_been_received_oracle_dec : RelDecision elmo_has_been_received_oracle.
Proof.
  unfold RelDecision, elmo_has_been_received_oracle.
  typeclasses eauto.
Defined.

Instance elmo_has_been_sent_oracle_dec : RelDecision elmo_has_been_sent_oracle.
Proof.
  unfold RelDecision, elmo_has_been_sent_oracle.
  typeclasses eauto.
Defined.

Lemma elmo_has_been_received_oracle_no_inits :
  forall (s : vstate vlsm),
    vinitial_state_prop vlsm s ->
    forall m, ~ elmo_has_been_received_oracle s m.
Proof.
  simpl.
  unfold elmo_initial_state_prop, elmo_has_been_received_oracle.
  intros s -> m.
  simpl. apply not_elem_of_nil.
Qed.

Lemma elmo_has_been_received_oracle_step_update :
  forall l s im s' om,
    input_valid_transition (pre_loaded_with_all_messages_vlsm vlsm) l (s,im) (s',om) ->
      forall msg,
        elmo_has_been_received_oracle s' msg
          <->
        field_selector input msg {| l := l; input := im; destination := s'; output := om |}
          \/
        elmo_has_been_received_oracle s msg.
Proof.
  intros l s im s' om [Hvalid Htransition] msg; simpl in *.
  unfold elmo_has_been_received_oracle.
  destruct l, im; inversion Htransition; subst; clear Htransition; simpl.
  - rewrite ?filter_app, map_app, elem_of_app.
    unfold isWitnessedBy, filter; cbn.
    rewrite decide_True by done; simpl.
    rewrite elem_of_list_singleton.
    itauto congruence.
  - itauto congruence.
  - cbn in Hvalid; itauto.
  - rewrite ?filter_app, map_app, elem_of_app.
    unfold isWitnessedBy, filter; simpl.
    rewrite decide_True by done; simpl.
    rewrite elem_of_nil.
    itauto congruence.
Qed.

Definition elmo_has_been_received_oracle_stepwise_props
  : @oracle_stepwise_props _ vlsm (field_selector input) elmo_has_been_received_oracle
  := {| oracle_no_inits := elmo_has_been_received_oracle_no_inits;
        oracle_step_update := elmo_has_been_received_oracle_step_update;
     |}.

Lemma elmo_has_been_sent_oracle_no_inits :
  forall (s : vstate vlsm),
    vinitial_state_prop vlsm s ->
    forall m, ~ elmo_has_been_sent_oracle s m.
Proof.
  simpl.
  unfold elmo_initial_state_prop, elmo_has_been_sent_oracle.
  intros s -> m.
  simpl. apply not_elem_of_nil.
Qed.

Lemma elmo_has_been_sent_oracle_step_update:
  forall l s im s' om,
    input_valid_transition (pre_loaded_with_all_messages_vlsm vlsm) l (s,im) (s',om) ->
      forall msg,
        elmo_has_been_sent_oracle s' msg
          <->
        (field_selector output msg {|l:=l; input:=im; destination:=s'; output:=om|}
          \/
        elmo_has_been_sent_oracle s msg).
Proof.
  intros l s im s' om [Hvalid Htransition] msg; simpl in *.
  unfold elmo_has_been_sent_oracle.
  destruct l, im; inversion Htransition; subst; clear Htransition; simpl.
  - rewrite ?filter_app, map_app, elem_of_app.
    unfold isWitnessedBy, filter; simpl.
    rewrite decide_True by done; simpl.
    rewrite elem_of_nil.
    itauto congruence.
  - itauto congruence.
  - itauto congruence.
  - rewrite ?filter_app, map_app, elem_of_app.
    unfold isWitnessedBy, filter; simpl.
    rewrite decide_True by done; simpl.
    rewrite elem_of_list_singleton.
    split; intros []; itauto congruence.
Qed.

Definition elmo_has_been_sent_oracle_stepwise_props
  : @oracle_stepwise_props _ vlsm (field_selector output) elmo_has_been_sent_oracle
  := {| oracle_no_inits := elmo_has_been_sent_oracle_no_inits;
        oracle_step_update := elmo_has_been_sent_oracle_step_update;
     |}.

Instance elmo_HasBeenSentCapability : HasBeenSentCapability vlsm.
Proof.
  eapply HasBeenSentCapability_from_stepwise; cycle 1.
  - apply elmo_has_been_sent_oracle_stepwise_props.
  - typeclasses eauto.
Defined.

Instance elmo_HasBeenReceivedCapability : HasBeenReceivedCapability vlsm.
Proof.
  eapply HasBeenReceivedCapability_from_stepwise; cycle 1.
  - apply elmo_has_been_received_oracle_stepwise_props.
  - typeclasses eauto.
Defined.

End capabilities.

Section weight.

Fixpoint Prestate_weight (p : Prestate) : nat :=
  let ListObservation_weight :=
    fix ListObservation_weight (obs : list Observation) : nat :=
      match obs with
      | [] => 0
      | ob :: obs' => S (Observation_weight ob + ListObservation_weight obs')
      end
  in
  S (ListObservation_weight (observations p))

with Observation_weight (o : Observation) : nat :=
  S (Premessage_weight (premessage o))

with Premessage_weight (p : Premessage) : nat :=
  S (Prestate_weight (prestate p))
.

Fixpoint ListObservation_weight (obs : list Observation) : nat :=
  match obs with
  | [] => 0
  | ob :: obs' => S (Observation_weight ob + ListObservation_weight obs')
  end.

Lemma Observation_in_list_weight ob l :
  ob ∈ l -> Observation_weight ob < ListObservation_weight l.
Proof.
  induction l; intro H; cbn.
  - by apply elem_of_nil in H.
  - apply elem_of_cons in H as []; subst; itauto lia.
Qed.

Lemma Observation_nested_weight ob1 ob2 :
  ob1 ∈ observations (prestate (premessage ob2)) ->
    Observation_weight ob1 < Observation_weight ob2.
Proof.
  destruct ob2 as [lbl [[lo] n]];
  simpl; fold (ListObservation_weight lo).
  intros H%Observation_in_list_weight.
  lia.
Qed.

Lemma Observation_nested_neq ob1 ob2 :
  ob1 ∈ observations (prestate (premessage ob2)) ->
    ob1 <> ob2.
Proof.
  intros H ->.
  apply Observation_nested_weight in H.
  lia.
Qed.

Lemma Observation_list_weight_last l ob :
  Observation_weight ob < ListObservation_weight (l ++ [ob]).
Proof.
  apply Observation_in_list_weight.
  apply elem_of_app. right. constructor.
Qed.

End weight.

Section ob_sent_contains_previous_prop_lemmas.

(** Observations of sent messages contain all previous messages. *)
Inductive ob_sent_contains_previous_prop : list Observation -> Prop :=
 | oscpp_nil  :
    ob_sent_contains_previous_prop []
 | oscpp_cons_receive :
    forall
      (ob : Observation) (obs : list Observation),
      label ob = Receive -> ob_sent_contains_previous_prop obs ->
      ob_sent_contains_previous_prop (obs ++ [ob])
 | oscpp_cons_send :
    forall (ob : Observation) (obs : list Observation),
      label ob = Send -> Forall (fun ob' => ob' ∈ observations (prestate (premessage ob))) obs ->
      ob_sent_contains_previous_prop obs -> ob_sent_contains_previous_prop (obs ++ [ob]).

Lemma ob_sent_contains_previous_prop_inv
  (P : list Observation -> Observation -> Prop)
  (obs : list Observation)
  (ob : Observation) :
    (label ob = Receive -> ob_sent_contains_previous_prop obs -> P obs ob) ->
    (label ob = Send
       -> Forall (λ ob' : Observation, ob' ∈ observations (prestate (premessage ob))) obs
       -> ob_sent_contains_previous_prop obs -> P obs ob) ->
    ob_sent_contains_previous_prop (obs ++ [ob]) ->
      P obs ob.
Proof.
  inversion 3; subst.
  - by apply app_cons_not_nil in H3.
  - apply app_inj_tail in H2 as []; subst. firstorder.
  - apply app_inj_tail in H2 as []; subst. firstorder.
Qed.

Lemma ob_sent_contains_previous_prop_app l1 l2 :
  ob_sent_contains_previous_prop (l1 ++ l2) ->
  ob_sent_contains_previous_prop l1 /\ ob_sent_contains_previous_prop l2.
Proof.
  revert l1.
  induction l2 as [| ob obs] using rev_ind; cbn; intros.
  - rewrite app_nil_r in H. firstorder constructor.
  - rewrite app_assoc in H.
    inversion H using ob_sent_contains_previous_prop_inv;
    intros; clear H; firstorder.
    + constructor 2; [done |]. firstorder.
    + constructor 3; [done | | firstorder].
      apply Forall_app in H1. firstorder.
Qed.

Lemma ob_sent_contains_previous_prop_tail x xs :
  ob_sent_contains_previous_prop (x :: xs) ->
    ob_sent_contains_previous_prop xs.
Proof.
  rewrite <- app_cons.
  by intros [_ H]%ob_sent_contains_previous_prop_app.
Qed.

Lemma ob_sent_contains_previous_prop_middle l1 a l2 :
  ob_sent_contains_previous_prop (l1 ++ a :: l2) ->
  ob_sent_contains_previous_prop (l1 ++ l2).
Proof.
  revert a l1.
  induction l2 as [| ob obs'] using rev_ind; cbn; intros.
  - rewrite app_nil_r.
    inversion H using ob_sent_contains_previous_prop_inv; auto.
  - rewrite app_comm_cons, app_assoc in *.
    inversion H using ob_sent_contains_previous_prop_inv; intros.
    + constructor 2; [done |]. firstorder.
    + constructor 3; [done | | firstorder].
      rewrite Forall_app, Forall_cons in H1. apply Forall_app. firstorder.
Qed.

(** We now prove that all the states of a single component satisfy
    [ob_sent_contains_previous_prop]. We start with an initial state.
*)
Lemma ob_sent_contains_previous_prop_initial : ob_sent_contains_previous_prop [].
Proof.
  constructor.
Qed.

(** We prove that the transition function preserves this property. *)
Lemma ob_sent_contains_previous_prop_step
  (addresses : list nat)
  (component : nat)
  (weights : list pos_R)
  (othreshold : option R)
  (label : Label)
  (bsom : Prestate * option Premessage) :
    ob_sent_contains_previous_prop (observations (fst bsom)) ->
    elmo_valid addresses component weights othreshold label bsom ->
    ob_sent_contains_previous_prop (observations (fst (elmo_transition component label bsom))).
Proof.
  destruct bsom as [bs om].
  intros Hinit Hvalid.
  simpl in Hinit |- *.
  destruct label.
  - destruct om; simpl; [| done]. constructor 2; cbn; auto.
  - destruct om; simpl; [done |].
    constructor 3; cbn; auto.
    remember (observations bs) as obs; clear -obs Hinit.
    by rewrite Forall_forall.
Qed.

(** If we have an observation of a received message, the message is not sent later
    (assuming [ob_sent_contains_previous_prop]).
*)
Lemma ob_sent_contains_previous_prop_impl_received_is_not_sent_later component m l2 :
  ob_sent_contains_previous_prop (Ob Receive m component :: l2) ->
    Ob Send m component ∉ l2.
Proof.
  induction l2 as [| ob obs] using rev_ind; cbn; intros H Hcontra.
  - contradict Hcontra. apply not_elem_of_nil.
  - rewrite elem_of_app, elem_of_list_singleton in Hcontra.
    rewrite app_comm_cons in H;
    inversion H using ob_sent_contains_previous_prop_inv;
    firstorder; subst; simpl in *.
    + congruence.
    + apply Forall_cons in H1 as [].
      eapply Observation_nested_neq with (ob2 := Ob Receive m component); eauto.
Qed.

End ob_sent_contains_previous_prop_lemmas.

(** Now we can prove the lemma saying that [isProtocol_step] ignores the rest
   of the list after [x]. Specifically, if [isProtocol_step] is given the index [i],
   it uses only the observations with lower or equal index.
*)
Lemma isProtocol_step_in {component weights othreshold l1 l2 args ob} :
  ob_sent_contains_previous_prop (l1 ++ ob :: l2) ->
  args.(idx) = length l1 ->
    isProtocol_step component weights othreshold (l1 ++ ob :: l2) args ob
      =
    isProtocol_step component weights othreshold (l1 ++ [ob]) args ob.
Proof.
  by functional induction isProtocol_step component weights othreshold l1 args ob;
  cbn; intros Hi Hprev; subst;
  repeat match goal with
  | H : ?x = _ |- context [if ?x then _ else _] => rewrite H
  end;
  rewrite ?firstn_app, ?Nat.sub_diag, <- ?app_nil_end.
Qed.

(** But how do we know that the assumption [ob_sent_contains_previous_prop]
    of [isProtocol_step_in] holds? Yes, it holds on all local states, because we
    proved it is an invariant; however, [isProtocol_step] is called with a list of observations
    from a state contained in a received message. About the received message we know only that
    it satisfies [isProtocol]; therefore, we need to prove that [isProtocol] implies
    [ob_sent_contains_previous_prop], which is what
    the lemma [isProtocol_implies_ob_sent_contains_previous_prop] is about.
    Before that we prove some helper results.
*)

Lemma isProtocol_implies_ob_sent_contains_previous_prop {component weights othreshold l} :
  isProtocol (St l) component weights othreshold = true ->
    ob_sent_contains_previous_prop l.
Proof.
  intros H.
  induction l using rev_ind.
  - constructor.
  - specialize (IHl (isProtocol_aux_last H)).
    unfold isProtocol in H; simpl in H;
    rewrite isProtocol_aux_app_r in H; simpl in H.
    apply isProtocol_step_inv_result in H as Hresult.
    apply isProtocol_aux_inv_idx in Hresult as Hidx.
    unfold isProtocol_step in H;
    destruct (isProtocol_aux component weights othreshold _ _ _)
          as [tt i' curState' curEq'];
    destruct (label x) eqn: Hlabel;
    simpl in Hresult, Hidx |-; subst i' tt.
    * by constructor 2.
    * constructor 3; [done | | done].
      destruct (decide (witness x <> component)); simpl in H; [congruence |];
      destruct (decide (author (premessage x) = component)); simpl in H; [| congruence];
      apply bool_decide_eq_true in H.
      by rewrite H, firstn_app, Nat.sub_diag, app_nil_r, firstn_all, Forall_forall.
Qed.

Section fullNodeLemmas.

Lemma fullNode_appone (l obs : list Observation) (ob : Observation) (n component : nat) :
  fullNode (Msg (St (l ++ [ob])) n) obs component ->
  fullNode (Msg (St l) n) obs component.
Proof.
  intros H.
  induction l using rev_ind;
  unfold fullNode in *; simpl in *.
  - constructor.
  - rewrite Forall_app in H. firstorder.
Qed.

Lemma fullNode_dropMiddle (l1 l2 obs : list Observation) (ob : Observation) (n component : nat) :
  fullNode (Msg (St (l1 ++ (ob :: l2))) n) obs component ->
  fullNode (Msg (St (l1 ++ l2)) n) obs component.
Proof.
  unfold fullNode; cbn.
  rewrite !Forall_app, Forall_cons.
  itauto.
Qed.

Lemma fullNode_last_receive_self (l obs : list Observation) (p : Prestate) (n n0 component : nat) :
  fullNode (Msg (St (l ++ [Ob Receive (Msg p component) n0])) n) obs component ->
    Ob Send (Msg p component) component ∈ obs.
Proof.
  unfold fullNode; cbn.
  unfold haveCorrespondingObservation; cbn.
  rewrite Forall_app, Forall_singleton, decide_True; itauto.
Qed.

Lemma fullNode_last_receive_not_self
  (l obs : list Observation) (p : Prestate)
  (n component1 component2 component3 : nat) :
    component1 <> component2 ->
    fullNode (Msg (St (l ++ [Ob Receive (Msg p component2) component3])) n) obs component1 ->
  Ob Receive (Msg p component2) component1 ∈ obs.
Proof.
  unfold fullNode; cbn; intro Hneq.
  unfold haveCorrespondingObservation; cbn.
  rewrite Forall_app, Forall_singleton, decide_False; itauto.
Qed.

End fullNodeLemmas.

Definition all_received_satisfy_isprotocol_prop {weights} {threshold} (obs : list Observation) : Prop :=
  Forall
    (fun ob : Observation =>
      if decide (isReceive ob)
      then
        isProtocol (prestate (premessage ob)) (author (premessage ob)) weights threshold
      else
        true
    )
    obs.

(** [m1] is a prefix of [m2] *)
Definition is_prefix_of (m1 m2 : Premessage) : Prop :=
  let s1 := prestate m1 in
  let s2 := prestate m2 in
  observations s1 = firstn (length (observations s1)) (observations s2).

#[export] Instance is_prefix_of_dec : RelDecision is_prefix_of.
Proof.
  unfold RelDecision, is_prefix_of.
  typeclasses eauto.
Defined.

Definition equivocation_evidence (m1 m2 : Premessage) : Prop :=
  author m1 = author m2
    /\
  ~ is_prefix_of m1 m2
    /\
  ~ is_prefix_of m2 m1.

#[export] Instance equivocation_evidence_dec : RelDecision equivocation_evidence.
Proof.
  unfold RelDecision, equivocation_evidence.
  typeclasses eauto.
Qed.

Definition is_equivocator (component : nat) (s : Prestate) : Prop :=
  let obs := observations s in
  Exists
    (fun ob1 =>
        Exists
          (fun ob2 =>
            label ob1 = Receive
            /\ label ob2 = Receive
            /\ author (premessage ob1) = component
            /\ author (premessage ob2) = component
            /\ equivocation_evidence (premessage ob1) (premessage ob2)
          )
          obs
    )
    obs.

#[export] Instance is_equivocator_dec component s : Decision (is_equivocator component s).
Proof.
  unfold is_equivocator.
  typeclasses eauto.
Defined.

Section composition.

Context
  (weights : list pos_R)
  (othreshold : option R)
  `{finite_index : finite.Finite index}
  (indices := enum index)
  (indices_weights_eqlenght : length indices = length weights)
  `{i0 : Inhabited index}
  .
(* TODO(traiansf): the Inhabited requirement above is only needed to have
a default value for nth in component_to_index. *)

Definition addresses : list nat := seq 0 (length indices).

Definition index_to_component (idx : index) : nat :=
  match list_find (idx =.) indices with
  | Some (i, _) => i
  | _ => length indices
  end.

Definition component_to_index (component : nat) : index :=
  nth component indices inhabitant.

Lemma index_to_component_to_index (idx : index) :
  component_to_index (index_to_component idx) = idx.
Proof.
  unfold component_to_index, index_to_component.
  destruct (list_find (eq idx) indices) as [[i v] |] eqn: Heqresult.
  + rewrite nth_lookup.
    by apply list_find_Some in Heqresult as (-> & -> & _).
  + apply list_find_None in Heqresult.
    rewrite Forall_forall in Heqresult.
    exfalso; eapply Heqresult; [apply elem_of_enum | done].
Qed.

Definition address_valid (a : nat) : Prop :=
  a < length indices.

Instance address_valid_dec (a : nat) : Decision (address_valid a).
Proof.
  unfold address_valid.
  typeclasses eauto.
Qed.

Lemma component_to_index_to_component (a : nat) :
  address_valid a ->
  index_to_component (component_to_index a) = a.
Proof.
  unfold address_valid, index_to_component, component_to_index.
  intros Hvalid.
  rewrite nth_lookup.
  assert (is_Some (list_find (eq (default inhabitant (indices !! a))) indices)).
  {
    eapply list_find_elem_of.
    - by apply elem_of_list_lookup_total_2.
    - by rewrite list_lookup_lookup_total_lt.
  }
  inversion_clear H as [[n i] Hni]; rewrite Hni.
  rewrite list_find_Some in Hni;
  destruct Hni as (Hi & Ha & _).
  eapply NoDup_lookup; [| done |].
  - apply NoDup_enum.
  - apply lookup_lt_is_Some_2 in Hvalid.
    inversion_clear Hvalid as [i' Hi'].
    rewrite Hi' in Ha; cbn in Ha; congruence.
Qed.

Definition IM' (i : index) :=
  elmo_vlsm_machine addresses (index_to_component i) weights othreshold.
Definition IM (i : index) := mk_vlsm (IM' i).

(** <<component>> is equivocating and we have an evidence in some state
   of the list <<states>>.
*)
Definition is_equivocator_states (states : list Prestate) (component : nat) : Prop :=
  fold_right or False (map (is_equivocator component) states).

Instance is_equivocator_states_dec (states : list Prestate) (component : nat)
  : Decision (is_equivocator_states states component).
Proof.
  unfold is_equivocator_states.
  induction states as [| state states']; simpl; typeclasses eauto.
Defined.

Definition equivocators (states : list Prestate) : list nat :=
  filter (is_equivocator_states states) (seq 0 (length indices)).

Definition composition_constraint
  (cl : composite_label IM)
  (sm : composite_state IM * option Premessage)
  : Prop :=
    match sm with
    | (_, None) => True
    | (cs, Some m) =>
      let states := map cs indices in
      let transitions := map (fun i => @transition _ _ (IM' i)) indices in
      let new_states := zip_with (fun s t => fst (t Receive (s, Some m))) states transitions in
      let eqs := equivocators new_states in
      match othreshold with
        | Some threshold =>
          ((@sum_weights _ (Build_Measurable _ (fun idx => nth idx weights (exist _ 1%R Rlt_0_1))) eqs)
              <
            threshold)%R
        | None => True
      end
    end.

Definition composite_elmo := @composite_vlsm Premessage index _ IM composition_constraint.
Definition free_composite_elmo := @free_composite_vlsm Premessage index _ IM.

Lemma all_receive_observation_have_component_as_witness st m witness idx :
  valid_state_prop free_composite_elmo st ->
  Ob Receive m witness ∈ observations (st idx) ->
  witness = index_to_component idx.
Proof.
  induction 1 using valid_state_prop_ind; intro Hin.
  - contradict Hin. rewrite Hs. apply not_elem_of_nil.
  - destruct Ht as [Hvalid Ht], l as [i li];
    unfold transition in Ht; simpl in Ht.
    destruct (vtransition (IM i) li (s i, om)) as [si'' om''] eqn: HeqVT;
    inversion Ht; subst; clear Ht.
    unfold vtransition in HeqVT; cbn in HeqVT.
    destruct (decide (i = idx)); cycle 1.
    + rewrite state_update_neq in Hin by congruence. itauto.
    + destruct li, om;
      inversion HeqVT; subst; clear HeqVT;
      rewrite state_update_eq in Hin; cbn in Hin;
      rewrite ?elem_of_app, ?elem_of_list_singleton in Hin;
      itauto congruence.
Qed.

Instance free_composite_elmo_HasBeenReceivedCapability :
  HasBeenReceivedCapability free_composite_elmo.
Proof.
  eapply composite_HasBeenReceivedCapability.
  intros i. apply elmo_HasBeenReceivedCapability.
Defined.

Lemma has_receive_observation_implies_is_protocol st idx m :
  valid_state_prop free_composite_elmo st ->
  Ob Receive m (index_to_component idx) ∈ observations (st idx) ->
  valid_message_prop free_composite_elmo m.
Proof.
  intros Hpsp Hin.
  apply valid_state_has_trace in Hpsp as Hpsp';
  destruct Hpsp' as (si & tr & Htrace & Hlast).
  eapply valid_trace_input_is_valid.
  - by eapply finite_valid_trace_from_to_forget_last.
  - eapply proper_received; cycle 2.
    + split; [| done].
      by apply preloaded_weaken_finite_valid_trace_from_to.
    + by apply pre_loaded_with_all_messages_valid_state_prop.
    + do 5 red; clear -Hin. exists idx.
      unfold has_been_received, elmo_HasBeenReceivedCapability;
      cbn; unfold elmo_has_been_received_oracle.
      change m with (premessage (Ob Receive m (index_to_component idx))).
      apply elem_of_list_fmap_1.
      rewrite !elem_of_list_filter.
      unfold isWitnessedBy; cbn.
      itauto.
Qed.

Lemma has_send_observation_implies_is_protocol st idx m author :
  valid_state_prop free_composite_elmo st ->
  Ob Send m author ∈ observations (st idx) ->
  valid_message_prop free_composite_elmo m.
Proof.
  intro Hpsp; induction Hpsp using valid_state_prop_ind; intro Hin.
  - contradict Hin. rewrite Hs. apply not_elem_of_nil.
  - destruct Ht as [Hvalid Ht], l as [i li];
    unfold transition in Ht; simpl in Ht.
    destruct (vtransition (IM i) li (s i, om)) as [si'' om''] eqn: HeqVT;
    unfold vtransition in HeqVT; cbn in HeqVT.
    destruct (decide (i = idx)); cycle 1.
    + apply IHHpsp.
      inversion Ht; subst; clear Ht.
      rewrite state_update_neq in Hin; congruence.
    + destruct li, om;
      inversion HeqVT; subst; clear HeqVT;
      inversion Ht; subst; clear Ht;
      rewrite state_update_eq in Hin; cbn in Hin;
      rewrite ?elem_of_app, ?elem_of_list_singleton in Hin;
      destruct Hin; rewrite ?elem_of_cons in IHHpsp; try itauto congruence.
      unfold valid_message_prop, input_valid in *.
      destruct Hvalid as [[m0 Hs] [_ Hvalid]].
      eexists. eapply (valid_generated_state_message _ s m0 Hs (fun _ => St []) None).
      * by apply valid_initial_state_message.
      * done.
      * cbn. by inversion H.
Qed.

Lemma valid_state_satisfies_all_received_satisfy_isprotocol_prop st idx :
  valid_state_prop free_composite_elmo st ->
  @all_received_satisfy_isprotocol_prop weights othreshold (observations (st idx)).
Proof.
  intros Hpsp; induction Hpsp using valid_state_prop_ind.
  - rewrite Hs; unfold all_received_satisfy_isprotocol_prop.
    by rewrite Forall_nil.
  - destruct Ht as [Hvalid Ht], l as [i li];
    unfold input_valid_transition in Ht; simpl in Ht.
    destruct (vtransition (IM i) li (s i, om)) as [si'' om''] eqn: HeqVT;
    destruct (decide (i = idx)); cycle 1.
    + replace (s' idx) with (s idx); [done |].
      inversion Ht; subst.
      rewrite state_update_neq; congruence.
    + inversion Ht; subst; clear Ht.
      rewrite state_update_eq.
      cbn in HeqVT; destruct li, om; inversion HeqVT; clear HeqVT; subst
      ; [| done | done |].
      * unfold all_received_satisfy_isprotocol_prop; cbn.
        rewrite Forall_app, Forall_cons, decide_True; cbn; [| done].
        split_and!; [itauto | | itauto].
        destruct Hvalid as (_ & _ & [Hvalid _]); cbn in Hvalid.
        itauto.
      * unfold all_received_satisfy_isprotocol_prop; cbn.
        rewrite Forall_app, Forall_cons, Forall_nil; cbn.
        rewrite decide_False; itauto.
Qed.

Lemma valid_state_contains_receive_implies_isProtocol st idx msg n0 :
  valid_state_prop free_composite_elmo st ->
  Ob Receive msg n0 ∈ observations (st idx) ->
  isProtocol (prestate msg) (author msg) weights othreshold.
Proof.
  intros Hpsp Hin.
  apply valid_state_satisfies_all_received_satisfy_isprotocol_prop
   with st idx in Hpsp;
  unfold all_received_satisfy_isprotocol_prop in Hpsp.
  rewrite Forall_forall in Hpsp.
  by apply (Hpsp _ Hin).
Qed.

(* TODO [s1] is reachable from [s0] *)
Lemma valid_message_was_sent_from_valid_state s1 st author :
  valid_state_message_prop free_composite_elmo s1 (Some (Msg st author)) ->
  (
  exists s0,
    valid_state_prop free_composite_elmo s0
    /\ (s0 (component_to_index author)) = st
  ) /\ (Ob Send (Msg st author) author ∈ observations (s1 (component_to_index author))).
Proof.
  inversion_clear 1.
  - compute in Hom.
    by destruct Hom as (_ & [_ Hom] & _).
  - destruct l as [i li].
    simpl in Ht; destruct (vtransition _ _ _) as [st' om'] eqn: Hti;
    inversion Ht; subst; clear Ht.
    unfold vtransition in Hti;
    cbn in Hti; destruct li, om.
    1-3: congruence.
    inversion Hti; subst; clear Hti.
    rewrite index_to_component_to_index.
    split.
    + unfold valid_state_prop. eauto.
    + rewrite state_update_eq; cbn;
      rewrite elem_of_app, elem_of_list_singleton; itauto.
Qed.

Lemma isProtocol_last_fullNode l p n1 n0 component :
  n1 <> component ->
  isProtocol (St (l ++ [Ob Receive (Msg p n1) n0]))
             component weights othreshold = true ->
  fullNode (Msg p n1) l component.
Proof.
  intros Hneq Hproto.
  unfold isProtocol in Hproto; cbn in Hproto;
  rewrite isProtocol_aux_app_r in Hproto; cbn in Hproto.
  (* Short names for things, necessary for funind. *)
  remember (l ++ [Ob Receive (Msg p n1) n0]) as l';
  remember (Ob Receive (Msg p n1) n0) as ob;
  remember (Arg true 0 (map (fun _ => St []) weights) []) as args;
  remember (isProtocol_aux component weights othreshold l' l args) as isP;
  symmetry in HeqisP.
  (* funind on isProtocol_step, discharge contradictory cases. *)
  functional induction isProtocol_step component weights othreshold l' isP ob;
  cbn in *;  subst; try congruence;
  rename _x1 into HfN; clear -HfN HeqisP.
  (* i = length l *)
  assert (Hidx := isProtocol_aux_inv_idx (f_equal result HeqisP)).
  rewrite HeqisP in Hidx; cbn in Hidx; subst; clear -HfN.
  (* List reasoning. *)
  by rewrite firstn_app, firstn_all, Nat.sub_diag, take_0, app_nil_r in HfN.
Qed.

Lemma sent_is_protocol st m component :
  address_valid component ->
  valid_state_prop free_composite_elmo st ->
  Ob Send m component ∈ observations (st (component_to_index component)) ->
  valid_message_prop free_composite_elmo m.
Proof.
  intros Haddr Hpsp Hin.
  induction Hpsp using valid_state_prop_ind.
  - contradict Hin. rewrite Hs. apply not_elem_of_nil.
  - destruct Ht as [Hvalid Ht], l as [i li].
    unfold transition in Ht; simpl in Ht;
    destruct (vtransition (IM i) li (s i, om)) as [si'' om''] eqn: HeqVT.
    inversion Ht; subst; clear Ht.
    destruct (decide (component_to_index component = i)); cycle 1.
    + apply IHHpsp. rewrite state_update_neq in Hin; congruence.
    + rewrite e in *; clear e.
      rewrite state_update_eq in Hin.
      cbn in Hvalid; destruct Hvalid as (Hpsp & Hopmp & Hvalid).
      unfold vtransition in HeqVT; cbn in HeqVT
      ; destruct li, om; inversion HeqVT; subst; clear HeqVT
      ; [| auto | auto |]; cbn in Hin
      ; rewrite elem_of_app, elem_of_list_singleton in Hin.
      * itauto congruence.
      * destruct Hin; [itauto |].
        inversion_clear H.
        destruct Hpsp as [_om Hpsp].
        assert (Hpi : valid_state_message_prop free_composite_elmo (fun _ => St []) None)
            by (apply valid_initial_state_message; compute; itauto).
        eexists.
        eapply (valid_generated_state_message free_composite_elmo
                  _ _om Hpsp _ _ Hpi _ Hvalid _ _ eq_refl).
Qed.

Lemma fullNode_appObservation m component l ob :
  fullNode m l component ->
  fullNode m (l ++ [ob]) component.
Proof.
  unfold fullNode, haveCorrespondingObservation; intro H.
  eapply Forall_impl; [done |].
  cbn; intro; case_decide; rewrite elem_of_app; itauto.
Qed.

(** All observations in a state have the same witness, which is the address of the node. *)
Lemma observationsHaveSameWitness st component ob :
  address_valid component ->
  valid_state_prop free_composite_elmo st ->
  ob ∈ observations (st (component_to_index component)) ->
  witness ob = component.
Proof.
  intros Haddr Hpsp Hin.
  induction Hpsp using valid_state_prop_ind.
  - contradict Hin. rewrite Hs. apply not_elem_of_nil.
  - unfold input_valid_transition in Ht;
    destruct Ht as [Hvalid Ht], l as [i li];
    unfold transition in Ht; simpl in Ht.
    destruct (vtransition (IM i) li (s i, om)) as [si'' om''] eqn: HeqVT.
    inversion Ht; subst om'' s'; clear Ht.
    destruct (decide (component_to_index component = i)); cycle 1.
    + rewrite state_update_neq in Hin; auto.
    + subst i; rewrite state_update_eq in Hin.
      unfold vtransition in HeqVT; cbn in HeqVT
      ; destruct li, om; inversion HeqVT; clear HeqVT; subst
      ; [| auto | auto |]; cbn in Hin
      ; rewrite elem_of_app, elem_of_list_singleton in Hin;
      destruct Hin; try itauto; subst; cbn;
      by apply component_to_index_to_component.
Qed.

(** All observations with sender other than the component are <<Receive>> observations. *)
Lemma observationsWithAddressNotComponentAreReceive st component ob :
  address_valid component ->
  valid_state_prop free_composite_elmo st ->
  ob ∈ observations (st (component_to_index component)) ->
  author (premessage ob) <> component ->
  label ob = Receive.
Proof.
  intros Haddr Hpsp Hin Hauthor.
  induction Hpsp using valid_state_prop_ind.
  - contradict Hin. rewrite Hs. apply not_elem_of_nil.
  - unfold input_valid_transition in Ht;
    destruct Ht as [Hvalid Ht], l as [i li];
    unfold transition in Ht; simpl in Ht;
    destruct (vtransition (IM i) li (s i, om)) as [si'' om''] eqn: HeqVT;
    inversion Ht; subst om'' s'; clear Ht.
    destruct (decide (component_to_index component = i)); cycle 1.
    + rewrite state_update_neq in Hin; auto.
    + subst i; rewrite state_update_eq in Hin.
      unfold vtransition in HeqVT; cbn in HeqVT.
      destruct li, om; inversion HeqVT; clear HeqVT; subst; auto;
      cbn in Hin; rewrite elem_of_app, elem_of_list_singleton in Hin;
      destruct Hin; subst; cbn.
      1-3: itauto.
      contradict Hauthor. by apply component_to_index_to_component.
Qed.

Lemma trace_from_to_impl_observations_prefix s1 s2 (tr : list transition_item) component :
  finite_valid_trace_from_to
    (pre_loaded_with_all_messages_vlsm (IM (component_to_index component))) s1 s2 tr ->
  exists (n : nat),
    length (observations s2) >= n /\
    firstn n (observations s2) = observations s1.
Proof.
  generalize (component_to_index component); revert s1 s2.
  induction tr; intros s1 s2 i Htr;
  inversion Htr as [| s' s2' tr' Htl s1' iom oom lbl Ht H1 H2]; subst; clear Htr.
  - exists (length (observations s2)).
    rewrite firstn_all; itauto.
  - specialize (IHtr _ _ i Htl) as (n & Hl & Hn).
    unfold input_valid_transition in Ht; simpl in Ht
    ; destruct Ht as [[[opmp Hopmp] [Hiom Hvalid]] Htrans]
    ; destruct (vtransition (IM i) lbl (s1, iom)) as [s1' oom'] eqn: HeqVT
    ; inversion Htrans; subst; clear Htrans
    ; unfold vtransition in HeqVT; cbn in HeqVT.
    destruct lbl, iom; inversion HeqVT; subst; clear HeqVT; [| eauto | eauto |].
    + apply take_app_inv in Hn as Hn'; destruct Hn' as [n' ->].
      erewrite -> take_S_r in Hn
      ; [| by apply list_lookup_lookup_total_lt].
      apply app_inj_tail in Hn as [Hn Hlast].
      exists n'. split; [lia | done].
    + apply take_app_inv in Hn as Hn'; destruct Hn' as [n' ->].
      erewrite -> take_S_r in Hn
      ; [| by apply list_lookup_lookup_total_lt].
      apply app_inj_tail in Hn as [Hn Hlast].
      exists n'. split; [lia | done].
Qed.

(** If there is a [Ob Receive m component], then there is also
                  [Ob Send    m component].
*)
Lemma received_from_self_implies_sent st s component :
  address_valid component ->
  valid_state_prop free_composite_elmo st ->
  let obs := observations (st (component_to_index component)) in
  Ob Receive (Msg s component) component ∈ obs ->
  Ob Send (Msg s component) component ∈ obs.
Proof.
  cbn; intros Haddr Hpsp Hrecv.
  assert (Hhbr : @has_been_received _
                  (IM (component_to_index component))
                  (elmo_HasBeenReceivedCapability _ _ _ _)
                  (st (component_to_index component))
                  (Msg s component)).
  {
    cbn; unfold elmo_has_been_received_oracle.
    change (Msg s component)
      with (premessage (Ob Receive (Msg s component) component)).
    apply elem_of_list_fmap_1.
    rewrite component_to_index_to_component, !elem_of_list_filter; done.
  }
  (* Maybe if we had the check that the message was already sent... *)
  remember (component_to_index component) as i.
  assert (Hpspi : valid_state_prop (pre_loaded_with_all_messages_vlsm (IM i)) (st i)).
  {
    apply (VLSM_projection_valid_state (preloaded_component_projection IM i)).
    by apply pre_loaded_with_all_messages_valid_state_prop.
  }
  destruct (has_been_received_in_state_preloaded _ _ _ Hpspi Hhbr)
        as (s0 & item & tr & Hin & Hfpt);
  inversion Hfpt; subst tl f s' item; cbn in Hin; subst iom.
  unfold input_valid_transition in Ht;
  destruct Ht as [(Hs0 & Hmsg & Hvalid) Hs1]; cbn in *.
  destruct l; [| done]; destruct_and!; subst.
  destruct (trace_from_to_impl_observations_prefix _ _ _ _ Hfpt) as (n & _ & Hprefix).
  eapply elem_of_take; rewrite Hprefix.
  rewrite component_to_index_to_component in H0; itauto.
Qed.

Lemma valid_message_has_valid_sender p address :
  valid_message_prop free_composite_elmo (Msg p address) ->
  address_valid address.
Proof.
  intros [[im Him] | ([i v] & som & s' & Htrans)]%valid_message_prop_iff.
  - by destruct im as [m (n & [m' H] & Hmi)]; cbn in *.
  - unfold input_valid_transition in Htrans
    ; destruct Htrans as [_ Htrans]
    ; unfold transition in Htrans; cbn in Htrans
    ; unfold composite_transition in Htrans; destruct som as [s o]
    ; destruct (vtransition (IM i) v (s i, o)) as [s0 o0] eqn: HeqVT
    ; inversion Htrans; subst; clear Htrans
    ; unfold vtransition, transition in HeqVT; cbn in HeqVT.
    destruct v, o; inversion HeqVT; clear HeqVT; subst.
    unfold address_valid, index_to_component.
    assert (Hfound : is_Some (list_find (eq i) indices)).
    {
      apply list_find_elem_of with i; [| done].
      apply elem_of_enum.
    }
    inversion Hfound as [[n i'] H]; rewrite H.
    rewrite -> list_find_Some in H.
    destruct H as [Hn _].
    rewrite <- lookup_lt_is_Some, Hn.
    unfold is_Some. eauto.
Qed.

Lemma sent_is_fullNode st m component component' :
  address_valid component ->
  valid_state_prop free_composite_elmo st ->
  author m = component ->
  let st' := st (component_to_index component) in
  Ob Send m component' ∈ observations st' ->
  fullNode m (observations st') component.
Proof.
  intros Haddr Hpsp Hauthor st' Hin.
  induction Hpsp using valid_state_prop_ind.
  - contradict Hin. unfold st'; rewrite Hs. apply not_elem_of_nil.
  - unfold input_valid_transition in Ht
    ; destruct Ht as [Hvalid Ht], l as [i li]
    ; unfold transition in Ht; simpl in Ht
    ; destruct (vtransition (IM i) li (s i, om)) as [si'' om''] eqn: HeqVT
    ; inversion Ht; subst om'' s'; clear Ht.
    destruct (decide (component_to_index component = i)); cycle 1.
    + unfold st' in *.
      rewrite state_update_neq in * by done.
      by apply IHHpsp.
    + subst i.
      unfold st' in Hin; rewrite state_update_eq in Hin
      ; unfold input_valid in Hvalid
      ; destruct Hvalid as (Hpsp & Hopmp & Hvalid)
      ; unfold vtransition in HeqVT; simpl in HeqVT.
      destruct li, om; inversion HeqVT; subst; clear HeqVT;
      unfold st'; rewrite state_update_eq; auto; simpl in *;
      rewrite ?component_to_index_to_component in * by done.
      * apply fullNode_appObservation, IHHpsp.
        rewrite ?elem_of_app, ?elem_of_list_singleton in Hin by done.
        itauto congruence.
      * rewrite ?elem_of_app, ?elem_of_list_singleton in Hin by exact Haddr.
        destruct Hin as [Hin | Hin]
        ; [apply fullNode_appObservation; itauto |].
        inversion_clear Hin; destruct m as [p n]; cbn in *.
        apply fullNode_appObservation.
        unfold fullNode; cbn; apply Forall_forall.
        intros [l [p' n1] n0] Hx.
        (* Some facts:
          1. All observations in a state have the same witness - which is the address
            of the node (lemma [observationsHaveSameWitness]).
          2. If there is a [Ob Receive m component], then there is also
             [Ob Send m component].
          3. All observations with sender other than the component are Receive observations.
          Then the following cases might happen:
          * n1 = n -> Either l = Send, and we can use Hx,
                      or l = Receive, and by (2), there is some Send in obs.
          * n1 <> n -> The message was sent by some other node
                       and by (3) we have l = Receive and we can use Hx.
          *)
        assert (n0 = n).
        {
          by pose proof (observationsHaveSameWitness s n _ Haddr Hpsp Hx).
        }
        subst n0; unfold haveCorrespondingObservation; cbn.
        destruct (decide (n1 = n)).
        -- subst n1. destruct l; [| done].
           by apply received_from_self_implies_sent.
        -- erewrite <- (observationsWithAddressNotComponentAreReceive); do 2 eauto.
Qed.

Lemma elmo_initial_state_is_empty s :
  elmo_initial_state_prop s -> s = St [].
Proof.
  destruct s.
  inversion 1. simpl in H0.
  congruence.
Qed.

Lemma initial_state_is_collection_of_empty_states s :
  vinitial_state_prop free_composite_elmo s ->
    forall n : index, (s n) = St [].
Proof.
  intros Hinitial n.
  apply elmo_initial_state_is_empty, Hinitial.
Qed.

Lemma next_to_last_from_message ps n ist s tr :
  finite_valid_trace_init_to free_composite_elmo ist s tr ->
  option_map output (list.last tr) = Some (Some (Msg ps n)) ->
  exists st,
    (finite_trace_nth ist tr (length tr - 1) = Some st)
    /\ st (component_to_index n) = ps.
Proof.
  intros Hfpti Hlast.
  destruct (has_last_or_null tr) as [(tr' & a & ->) |]
  ; [| subst; simpl in *; congruence].
  rewrite app_length; cbn
  ; rewrite Nat.add_sub, finite_trace_nth_app1,
            finite_trace_nth_last by lia.
  eexists; split; [done |].
  unfold finite_valid_trace_init_to in Hfpti
  ; destruct Hfpti as [Hfpt Hist]
  ; apply finite_valid_trace_from_to_app_split in Hfpt as [Hfpt1 Hfpt2]
  ; inversion Hfpt2; subst; clear Hfpt2.
  rewrite last_snoc in Hlast; cbn in Hlast
  ; inversion Hlast; clear Hlast
  ; inversion Htl; subst; clear Htl.
  unfold input_valid_transition in Ht
  ; destruct Ht as [Hvalid Htransition]
  ; simpl in Htransition; destruct l.
  destruct (vtransition (IM x) v (finite_trace_last ist tr' x, iom))
        as [s0 o] eqn: HeqVT
  ; setoid_rewrite HeqVT in Htransition
  ; inversion Htransition; subst s o; clear Htransition
  ; unfold vtransition in HeqVT; simpl in HeqVT.
  destruct v, iom; inversion HeqVT; subst; clear HeqVT.
  by rewrite index_to_component_to_index.
Qed.

Lemma component_didnt_move v suffix st i l x tr :
  list.last (v :: suffix) = Some st ->
  suffix = map destination (tail tr) ->
  finite_valid_trace_from_to free_composite_elmo v st (tail tr) ->
  st i = St (l ++ [x]) ->
  (forall x0, x0 ∈ suffix -> length (l ++ [x]) <= length (observations (x0 i)) ) ->
  length (l ++ [x]) <= length (observations (v i)) ->
  v i = St (l ++ [x]).
Proof.
  remember (tail tr) as ttr
  ; intros Hlast Hsuf Htr Hst Hstates Hv
  ; revert suffix Hsuf Hstates v Hlast tr Heqttr Htr Hv
  ; induction ttr; intros suffix Hsuf Hstates v Hlast tr Heqttr Htr Hv
  ; inversion Htr; subst.
  - done.
  - assert (Hsi : s i = St (l ++ [x])).
    {
      eapply IHttr with (tr := {| l := l0; input := iom; destination := s; output := oom |} :: ttr)
      ; cbn in *; setoid_rewrite elem_of_cons in Hstates; itauto.
    }
    rename Ht into Hstep; unfold input_valid_transition in Hstep
    ; destruct Hstep as [_ Hstep], l0 as [j lj]
    ; unfold transition in Hstep; simpl in Hstep
    ; destruct (vtransition (IM j) lj (v j, iom)) as [si' om'] eqn: HeqVT
    ; inversion Hstep; subst; clear Hstep.
    destruct (decide (j = i)); cycle 1.
    + rewrite state_update_neq in Hsi; congruence.
    + subst j; unfold vtransition in HeqVT; simpl in HeqVT.
      destruct lj, iom; inversion HeqVT; subst; clear HeqVT;
      rewrite state_update_eq in Hsi; [| done | done |]
      ; inversion Hsi as [Hsi']; clear Hsi
      ; rewrite <- Hsi', app_length in Hv; cbn in *; lia.
Qed.

Lemma protocol_message_from_protocol_state n l :
  address_valid n ->
  (
    exists (st1 : state),
      valid_state_prop free_composite_elmo st1
      /\ st1 (component_to_index n) = St l
  ) ->
  valid_message_prop free_composite_elmo (Msg (St l) n).
Proof.
  intros Haddr (st1 & [_om Hpspst1] & Hst1i)
  ; unfold valid_message_prop.
  exists (state_update IM st1 (component_to_index n)
                       (St (l ++ [Ob Send (Msg (St l) n) n]))).
  assert (Hnone : option_valid_message_prop free_composite_elmo None)
      by apply option_valid_message_None
  ; destruct Hnone as [_s Hnone].
  apply valid_generated_state_message
   with st1 _om _s None (existT (component_to_index n) Send)
  ; [done | done | cbv; itauto |].
  cbn; rewrite Hst1i, component_to_index_to_component; auto.
Qed.

Lemma middle_of_protocol_trace_is_protocol ist s a tr' prefix lst v suffix :
  ist :: map destination tr' = prefix ++ lst :: v :: suffix ->
  finite_valid_trace_from_to free_composite_elmo ist s (tr' ++ [a]) ->
  vinitial_state_prop free_composite_elmo ist ->
  valid_state_prop free_composite_elmo lst.
Proof.
  intros Heq Htr' Hist.
  assert (Hltr' : length tr' = length (prefix ++ lst :: v :: suffix) - 1)
      by (rewrite <- Heq, cons_length, map_length; lia).
  assert (H1 : lst = finite_trace_last ist (firstn (length prefix) tr')).
  {
    destruct prefix.
    - cbn; rewrite firstn_O; cbn in *; congruence.
    - unfold finite_trace_last; simpl in Heq |- *.
      inversion Heq as [[Hist' Hmap]]; subst.
      by rewrite map_firstn, Hmap, <- app_cons, app_assoc, take_app_alt, last_is_last
           by (rewrite app_length; cbn; lia).
  }
  subst. apply finite_valid_trace_last_pstate.
  rewrite <- (firstn_skipn (length prefix)) in Htr'.
  apply finite_valid_trace_from_to_app_split in Htr'.
  destruct Htr' as [Htr' _].
  rewrite take_app_le in Htr' by (rewrite Hltr', app_length; cbn; lia).
  by apply finite_valid_trace_from_to_forget_last in Htr'.
Qed.

Lemma transition_from_stripped iom oom lbl i v lst l x :
  v i ≠ lst i ->
  (v, oom) = vtransition free_composite_elmo lbl (lst, iom) ->
  v i = St (l ++ [x]) ->
  lst i = St l.
Proof.
  intros Hvi_ne_lasti Hsteplastv Hcdm.
  unfold vtransition in Hsteplastv; simpl in Hsteplastv
  ; destruct lbl as [j lj]
  ; destruct (vtransition (IM j) lj (lst j, iom)) as [s o] eqn: HeqVT
  ; inversion Hsteplastv; subst; clear Hsteplastv.
  destruct (decide (i = j)); cycle 1.
  - contradict Hvi_ne_lasti. by apply state_update_neq.
  - subst; rewrite ?state_update_eq in Hcdm, Hvi_ne_lasti; subst
    ; unfold vtransition in HeqVT; cbn in HeqVT.
    by destruct lj, iom; inversion HeqVT; subst; clear HeqVT
    ; [| congruence | congruence |]
    ; apply app_inj_tail in H0 as [H0 _]; subst
    ; destruct (lst j); cbn.
Qed.

(* The proof of the following lemma needs refactoring, but specifically,
   we need to extract the proof of the following:

  Hs01 : valid_state_prop free_composite_elmo s0
  i : index
  Heqi : i = component_to_index n
  Hs02 : s0 i = St (l ++ [x])
  ============================
  ∃ sm1 : state,
    valid_state_prop free_composite_elmo sm1
    ∧ sm1 i = St l ∧ vvalid free_composite_elmo (existT i Receive) (sm1, Some (premessage x))

    (something like that should be present).

Maybe a result like this would help?

  Hs01 : valid_state_prop free_composite_elmo s0
  i : index
  Heqi : i = component_to_index n
  Hs02 : s0 i = St (l ++ [x])
  ==================================
  valid_state_prop (pre_loaded_with_all_messages_vlsm (IM i)) (St l)
  valid (IM i)  Receive (St l,  Some (premessage x))
  isProtocol (premessage m)

Proof sketch:

  Hs01 : valid_state_prop free_composite_elmo s0
  i : index
  -------
  valid_state_prop (pre_loaded_with_all_messages_vlsm (IM i)) (s0 i)

  Heqi : i = component_to_index n
  Hs02 : s0 i = St (l ++ [x])
  ---
  valid_state_prop (pre_loaded_with_all_messages_vlsm (IM i)) (St l)
  input_valid_transition (pre_loaded_with_all_messages_vlsm (IM i)) Receive (St l,  Some (premessage x)) (s0 i, None)
  __
  valid (IM i)  Receive (St l,  Some (premessage x))
  isProtocol (premessage m)

*)

#[local] Arguments state : simpl never.
#[local] Arguments type : simpl never.
#[local] Arguments free_composite_elmo : simpl never.

Lemma protocol_strip_last l x n :
  address_valid n ->
  valid_message_prop free_composite_elmo (Msg (St (l ++ [x])) n) ->
  valid_message_prop free_composite_elmo (Msg (St l) n).
Proof.
  intros Haddr [s Hproto].
  (* [Msg (St (l ++ [x]))] must have been sent from some protocol state
     [s] such that [s n = St (l ++ [x])].
     Now if there were no transition to [s n] from some protocol state [s'] satisfying
     [s' n = St l], then the [n]th projection of any state on any trace leading to [s]
     would be [St (l ++ [x])] - even the initial state. But initial state is empty!
     That is a contradiction, and therefore there must be some such [s'].

     Consider a trace [is, tr] leading to [s]. There must be some position [i] such that
     [map label (nth_error tr i) = Some (n, Receive)]
     and [finite_trace_nth is tr i = Some l].
     Well, it depends who's observation is [x].
     At the very least, there must be some position [i] such that
     and [finite_trace_nth is tr i = Some l] - because the state can only grow
     and starts in empty state.

     We can then extend the i-prefix of tr with label [(n, Send)] and get
     the protocol message (Msg (St l) n).
   *)

  (* [s] is not an initial state. TODO: extract a lemma. *)
  apply valid_state_message_has_trace in Hproto
     as [[Hinit (n0 & [m []] & _)] | (ist & tr & Htr & Hlast)].
  destruct (next_to_last_from_message (St (l ++ [x])) n _ _ _ Htr)
        as (st & Htrst & Hst); [| clear Hlast].
  {
    rewrite <- last_last_error; unfold option_map.
    destruct tr.
    - simpl in Hlast; inversion Hlast.
    - unfold finite_trace_last_output in Hlast.
      by simpl; rewrite <- Hlast, last_map.
  }
  (* Now I need to be looking for a position in the trace where the [n]th component
     takes a step. First I need to prove that it takes a step at all. *)
  destruct (has_last_or_null tr) as [(tr' & a & ->) | ->].
  2: {
    unfold finite_trace_nth in Htrst; simpl in Htrst
    ; inversion Htrst; subst; clear Htrst
    ; destruct Htr as [Htr Hist].
    rewrite initial_state_is_collection_of_empty_states in Hst
    ; [| done]; inversion Hst as [H].
    contradict H; apply app_cons_not_nil.
  }
  rewrite app_length in Htrst; cbn in Htrst
  ; rewrite Nat.add_sub, finite_trace_nth_app1 in Htrst by done
  ; unfold finite_trace_nth in Htrst.
  (* There exists a state on the trace such that its [n]th projection
     is smaller than [l ++ [x]]. We are looking for last such state, because that is
     where [n] takes a step.
   *)
  assert (Hsome :
    existsb
      (fun (st : forall (n : index), vstate (IM n)) =>
        length (observations (st (component_to_index n))) <? length (l ++ [x]))
      (ist :: map destination tr')
      =
    true).
  {
    rewrite -> existsb_exists.
    exists ist; split.
    - by cbn; left.
    - destruct Htr as [Htr Hinit].
      rewrite initial_state_is_collection_of_empty_states; [| done].
      apply Nat.ltb_lt; cbn.
      rewrite app_length; cbn; lia.
  }
  destruct (existsb_last _ _ Hsome) as (prefix & suffix & last & Hlast' & Heq & Hsuffix)
  ; clear Hsome; cbn in Heq.
  (* suffix is nonempty. *)
  destruct suffix as [| v suffix].
  {
    apply Nat.ltb_lt in Hlast'; contradict Hlast'.
    erewrite (nth_error_last _ _ _ last), Heq, last_is_last in Htrst
    ; inversion Htrst; subst last; clear Htrst.
    rewrite Hst; cbn; lia.
    Unshelve. by cbn; rewrite map_length.
  }
  (* now [last] and [v] have different sizes on the component [n],
     so [n] must have taken a step between the two *)
  simpl in Hsuffix
  ; apply Bool.orb_false_elim in Hsuffix as [Hlenv Hsuffix]
  ; rewrite existsb_forall in Hsuffix
  ; setoid_rewrite <- elem_of_list_In in Hsuffix
  ; setoid_rewrite Nat.ltb_ge in Hsuffix.
  assert (v (component_to_index n) <> last (component_to_index n))
      by congruence
  ; apply Nat.ltb_ge in Hlenv.
  unfold finite_valid_trace_init_to in Htr
  ; destruct Htr as [Htr Hist].
  assert (exists iom oom lbl, (v, oom) = vtransition free_composite_elmo lbl (last, iom))
      as (iom & oom & lbl & Hsteplastv).
  {
    destruct prefix; inversion Heq; subst.
    - inversion Htr; subst
      ; [contradict H4; apply app_cons_not_nil |].
      exists iom, oom, l0.
      apply (f_equal (map destination)) in H4
      ; rewrite map_app, H2 in H4; cbn in H4
      ; inversion H4; subst; clear H4.
      destruct Ht as [Hvalid Htrans]; auto.
    - change (last :: v :: suffix) with ([last] ++ ([v] ++ suffix)) in H2
      ; destruct (map_eq_app _ _ _ _ H2) as (l1' & l2' & -> & <- & Hmdl2').
      apply map_eq_app in Hmdl2' as (l1'' & l2'' & -> & Hprefix'' & Hmdl2'').
      rewrite <- app_assoc in Htr
      ; apply finite_valid_trace_from_to_app_split in Htr as [Htr1 Htr2]
      ; rewrite <- app_assoc in Htr2
      ; apply finite_valid_trace_from_to_app_split in Htr2 as [Htr2 Htr3]
      ; inversion Htr3; subst; clear Htr3
      ; [contradict H4; apply app_cons_not_nil |].
      apply (f_equal (map destination)) in H4
      ; rewrite map_app in H4; setoid_rewrite Hmdl2'' in H4; cbn in H4
      ; inversion H4; subst; clear H4.
      exists iom, oom, l0.
      by destruct Ht as [Hvalid Htrans]
      ; setoid_rewrite <- Htrans
      ; unfold finite_trace_last; do 2 f_equal
      ; rewrite <- last_app; setoid_rewrite Hprefix''
      ; rewrite last_is_last.
  }
  (* So now we have a transition from [last] to [v].
     Since the component [component_to_index n] changed its state, it must
     have taken step; i.e., lbl = component_to_index n.
     Because of Hsuffix, all the i-th projections of states in [suffix]
     have length >= length (l ++ [x]).
   *)
  assert (Htrst' : list.last (v :: suffix) = Some st)
  ; [| clear Htrst; rename Htrst' into Htrst].
  {
    clear -Heq Htrst.
    replace (length tr')
       with (length (prefix ++ last :: v :: suffix) - 1)
         in Htrst by (rewrite <- Heq, cons_length, map_length; lia).
    rewrite Heq, nth_error_app2, app_length
         in Htrst by (rewrite app_length; cbn; lia).
    replace (length prefix + length (last :: v :: suffix) - 1 - length prefix)
       with  (length (last :: v :: suffix) - 1)
         in Htrst by lia.
    simpl in Htrst.
    replace (length suffix) with ((length (v :: suffix)) - 1) in Htrst by (simpl; lia).
    by rewrite nth_error_stdpp_last in Htrst.
  }
  apply protocol_message_from_protocol_state; [done |].
  eexists; split.
  - eapply middle_of_protocol_trace_is_protocol; eauto.
  - eapply transition_from_stripped; eauto.
    eapply (component_didnt_move v suffix st).
    1, 4-6: eauto.
    + assert (Hvs : v :: suffix = drop (length prefix) (map destination tr')).
      {
        apply (f_equal tail) in Heq; cbn in Heq.
        by rewrite Heq, skipn_tail_comm, drop_app; cbn.
      }
      by rewrite map_tail, map_skipn, <- Hvs; cbn.
    + rewrite <- skipn_tail_comm, <- skipn_S_tail, <- Nat.add_1_r.
      apply finite_valid_trace_from_to_app_split in Htr as [Htr _].
      rewrite <- (take_drop (length prefix + 1)) in Htr.
      apply finite_valid_trace_from_to_app_split in Htr as [_ Htr].
      replace (finite_trace_last ist tr')
         with st in Htr; cycle 1.
      {
        symmetry; unfold finite_trace_last.
        by rewrite <- unroll_last with (random := ist), Heq, last_app, unroll_last
        ; apply last_error_some; rewrite last_last_error.
      }
      replace (finite_trace_last ist (take (length prefix + 1) tr'))
         with v in Htr; [done |].
      unfold finite_trace_last.
      destruct prefix; simpl; simpl in Heq
      ; inversion Heq; subst; rewrite map_firstn, H2; simpl; [done |].
      rewrite <- (app_cons last), <- (app_cons v), !app_assoc.
      replace (S (length prefix + 1))
        with (length ((prefix ++ [last]) ++ [v]))
        by (repeat rewrite app_length; simpl; lia).
      by rewrite take_app, last_is_last.
Qed.

Lemma author_last_sent_from_component component st l x :
  address_valid component ->
  valid_state_prop free_composite_elmo st ->
  observations (st (component_to_index component)) = l ++ [x] ->
  isSend x ->
  author (premessage x) = component.
Proof.
  intros Haddr Hpsp Hobs Hsent.
  induction Hpsp using valid_state_prop_ind.
  - contradict Hobs.
    rewrite (elmo_initial_state_is_empty
               (s (component_to_index component))).
    + cbn; apply app_cons_not_nil.
    + apply Hs.
  - destruct Ht as [Hvalid Htrans], l0 as [x0 v]; simpl in Htrans
    ; destruct (vtransition (IM x0) v (s x0, om)) as [s0 o] eqn: HeqVT
    ; inversion Htrans; subst; clear Htrans.
    destruct (decide (x0 = component_to_index component)); cycle 1.
    + rewrite state_update_neq in Hobs; auto.
    + subst x0; rewrite state_update_eq in Hobs
      ; unfold vtransition in HeqVT; cbn in HeqVT.
      destruct v, om; inversion HeqVT; subst; clear HeqVT
      ; [| auto | auto |]; apply app_inj_tail in Hobs as [_ Hobs].
      * contradict Hsent; subst; cbn in *; auto.
      * subst; cbn in *. rewrite component_to_index_to_component; auto.
Qed.

End composition.
