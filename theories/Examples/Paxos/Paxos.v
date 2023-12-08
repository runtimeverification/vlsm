From VLSM.Lib Require Import Itauto.
From stdpp Require Import prelude finite fin_sets fin_maps nmap.
From Coq Require Import Streams FunctionalExtensionality Eqdep_dec.
From VLSM.Lib Require Import Preamble ListExtras FinSetExtras.
From VLSM.Core Require Import VLSM Plans VLSMProjections Composition Equivocation.
From VLSM.Core.Equivocation Require Import NoEquivocation.
From VLSM.Examples Require Import Voting.

Create HintDb list_simpl discriminated.
#[export] Hint Rewrite or_False @elem_of_cons @elem_of_nil @elem_of_app : list_simpl.

Ltac simpl_elem_of_list := rewrite_strat any (topdown (hints list_simpl)).
Ltac simpl_elem_of_list_in H := rewrite_strat any (topdown (hints list_simpl)) in H.

(** * Paxos: A Basic Paxos Protocol

  This protocol maintains safety in the presence of message loss,
  but may not be safe for Byzantine failures.

  As in the voting specification, consensus is established
  by votes from a quorum of acceptor nodes.
  In addition to acceptor nodes this protocol also has
  a leader process for each ballot.

  In an implementation leader nodes are often selected from
  among the same computers hosting acceptors, but such colocation
  is not visible at the protocol level so we just let the
  leaders be indexed by ballot number.
*)

(**
  Represent a set that contains either all values in a type,
  or just a finite subset.

  This is sufficient for representing the set of values that are
  still possible candidates for the consensus choice.
*)
Variant AllOrFin VSet : Type :=
| any_value
| some_values (vs : VSet).

Arguments any_value   {VSet}.
Arguments some_values [VSet] vs.

#[export] Instance elem_of_all_or_fin `{ElemOf V VSet} : ElemOf V (AllOrFin VSet) :=
  fun v fv =>
  match fv with
  | any_value => True
  | some_values vs => v ∈ vs
  end.

#[export] Instance AllOrFin_eq_dec `{EqDecision VSet} : EqDecision (AllOrFin VSet).
Proof.
  intros [| xs] [| ys]; [by unfold Decision; auto.. |].
  by destruct (decide_rel eq xs ys); [left | right]; congruence.
Defined.

Section sec_paxos_spec.

Context
  `{FinSet Value VSet}
  `{EqDecision VSet}
  {VSDec : RelDecision (∈@{VSet})}
  `{FinMap Acceptor AMap}
  `{!finite.Finite Acceptor}
  .

Notation ASet := (mapset.mapset AMap).

#[export] Instance ASet_Dom {A:Type} : Dom (AMap A) ASet := mapset.mapset_dom.
#[export] Instance AMap_FinMapDom : fin_map_dom.FinMapDom Acceptor AMap ASet :=
  mapset.mapset_dom_spec.

Context
  (Quorum : ASet -> Prop)
  (QDec : forall Q, Decision (Quorum Q))
  (QClosed : Proper (subseteq ==> impl) Quorum)
  (QA : forall (Q1 Q2 : sig Quorum), exists a, a ∈ `Q1 ∩ `Q2)
  .

Inductive paxos_message_body : Type :=
| m_1a
| m_1b (a : Acceptor) (last_vote : option (Ballot * Value))
| m_1c (safe_v : AllOrFin VSet)
| m_2a (v : Value)
| m_2b (a : Acceptor) (v : Value).

Definition paxos_message : Type := Ballot * paxos_message_body.

#[export] Instance paxos_message_eq_dec : EqDecision paxos_message.
Proof.
  assert (EqDecision (option (Ballot * Value))) by typeclasses eauto.
  assert (EqDecision (AllOrFin VSet)) by typeclasses eauto.
  intros m1 m2.
  refine (prod_eq_dec _ _).
  unfold EqDecision, Decision in *.
  decide equality.
Qed.

(**
  A 1a message for a ballot <<b>> is sent by the leader of b to announce the ballot.
  An acceptor receiving a 1a message for a ballot greater than <<maxBal>>
  increases <<maxBal>> to <<b>> and replies with a 1b message with their identitity and
  the ballot number, carrying their current <<maxVBal>> and <<maxVVal>>.
  When the leader has received 1b messages for their ballot from a quorum
  it determines a set of values safe at b and sends a 1c message
  (None means all values are safe at b).
  The leader then also sends a 2a message for some value which it approved
  in the 1c message (this finishes the participation of the leader)
  An acceptor receiving a 2a message for a ballot >= their current <<maxBal>>
  sets <<maxBal>> and <<maxVBal>> to <<b>>, <<maxVVal>> to the given value, and sends a 2b
  message for their identitity and the given ballot and value.
*)

Section sec_paxos_acceptor_vlsm.

Context
  (self : Acceptor)
  .

Record paxos_acceptor_state :=
{
  paxos_maxBal : Ballot';
  lastVote : option (Ballot * Value);
  sent_messages : list paxos_message;
}.

Definition maxVBal (sa : paxos_acceptor_state) : Ballot' := fst <$> lastVote sa.
Definition maxVVal (sa : paxos_acceptor_state) : option Value := snd <$> lastVote sa.

Definition paxos_acceptor_initial : paxos_acceptor_state :=
{|
  paxos_maxBal := None;
  lastVote := None;
  sent_messages := [];
|}.

Inductive paxos_acceptor_label : Type :=
| A_send_1b
| A_send_2b.

Definition paxos_acceptor_type : VLSMType paxos_message :=
{|
  state := paxos_acceptor_state;
  label := paxos_acceptor_label;
|}.

Definition paxos_acceptor_valid :
 paxos_acceptor_label -> paxos_acceptor_state * option paxos_message -> Prop :=
  fun l som =>
    match l, som with
    | A_send_1b, (s, Some (b, m_1a)) => (paxos_maxBal s < b)%Z
    | A_send_2b, (s, Some (b, m_2a v)) => (paxos_maxBal s <= b)%Z
    | _, _ => False
    end.

Definition paxos_acceptor_transition
 (l : paxos_acceptor_label) (som : paxos_acceptor_state * option paxos_message)
  : paxos_acceptor_state * option paxos_message :=
  match l, som with
  | A_send_1b, (s, Some (b, m_1a)) =>
      let reply := (b, m_1b self (lastVote s)) in
      ({| paxos_maxBal := Some b; lastVote := lastVote s;
          sent_messages := reply :: sent_messages s; |},
        Some reply)
  | A_send_2b, (s, Some (b, m_2a v)) =>
      let reply := (b, m_2b self v) in
      ({| paxos_maxBal := Some b; lastVote := Some (b, v);
          sent_messages := reply::sent_messages s|},
        Some reply)
  | _, _ => (som.1, None) (* illegal inputs *)
  end.

Definition paxos_acceptor_machine : VLSMMachine paxos_acceptor_type :=
{|
  initial_state_prop := (.= paxos_acceptor_initial);
  s0 := populate (exist _ paxos_acceptor_initial eq_refl);
  initial_message_prop := (fun _ => False);
  valid := paxos_acceptor_valid;
  transition := paxos_acceptor_transition;
|}.

Definition paxos_acceptor_vlsm : VLSM paxos_message := mk_vlsm paxos_acceptor_machine.

Definition paxos_acceptor_has_been_sent
 (s : state paxos_acceptor_vlsm) (m : paxos_message) : Prop :=
  m ∈ sent_messages s.

#[export] Instance paxos_acceptor_has_been_sent_dec :
 RelDecision paxos_acceptor_has_been_sent :=
  fun s m => elem_of_list_dec m (sent_messages s).

Lemma paxos_acceptor_has_been_sent_stepwise_props :
 has_been_sent_stepwise_prop paxos_acceptor_has_been_sent.
Proof.
  constructor.
  - intros s Hs m.
    unfold paxos_acceptor_has_been_sent.
    simpl in Hs; subst s.
    by apply not_elem_of_nil.
  - intros l s im s' om Htrans msg.
    simpl.
    enough (H_hist : sent_messages s' =
      match om with Some m' => m' :: sent_messages s | None => sent_messages s end).
    {
      unfold paxos_acceptor_has_been_sent.
      destruct om; rewrite H_hist, ?elem_of_cons; itauto congruence.
    }
    destruct Htrans as [(_ & _ & Hvalid) Htran].
    change transition with paxos_acceptor_transition in Htran.
    by destruct l, im as [[? []] |]; simpl in Htran; inversion Htran.
Qed.

#[export] Instance paxos_acceptor_has_been_sent_inst :
 HasBeenSentCapability paxos_acceptor_vlsm :=
{|
  has_been_sent := paxos_acceptor_has_been_sent;
  has_been_sent_dec := paxos_acceptor_has_been_sent_dec;
  has_been_sent_stepwise_props := paxos_acceptor_has_been_sent_stepwise_props;
|}.

End sec_paxos_acceptor_vlsm.

Section sec_paxos_acceptor_vlsm_lem.

Lemma examine_paxos_acceptor_output :
  forall [a l s oim s' ob om],
    paxos_acceptor_transition a l (s, oim) = (s', Some (ob, om)) ->
    match om with
    | m_1b a' _ => l = A_send_1b /\ a' = a
    | m_2b a' _ => l = A_send_2b /\ a' = a
    | _ => False
    end.
Proof.
  by intros a [] s [[? []] |] * Ht; inversion Ht.
Qed.

Lemma paxos_maxBal_mono :
  forall a l s im s' om,
    input_valid_transition (pre_loaded_with_all_messages_vlsm (paxos_acceptor_vlsm a)) l (s, im) (s', om) ->
    (paxos_maxBal s <= paxos_maxBal s')%Z.
Proof.
  intros * [(_ & _ & Hvalid) Htrans].
  cbn in Hvalid, Htrans;
    unfold paxos_acceptor_valid, paxos_acceptor_transition in Hvalid, Htrans.
  by repeat case_match; injection Htrans as [= <- <-]; cbn -[Ballot'_to_Z];
    change (Ballot'_to_Z (Some ?b)) with (Ballot_to_Z b); lia.
Qed.

Lemma last_vote_was_sent :
  forall a s,
    valid_state_prop (pre_loaded_with_all_messages_vlsm (paxos_acceptor_vlsm a)) s ->
    forall lv,
      lastVote s = Some lv -> has_been_sent (paxos_acceptor_vlsm a) s (lv.1, m_2b a lv.2).
Proof.
  intros a s Hs.
  induction Hs using valid_state_prop_ind; intros lv Hlv;
    [by rewrite Hs in Hlv |].
  rewrite has_been_sent_step_update with (1 := Ht).
  cut (om' = Some (lv.1, m_2b a lv.2) \/ lastVote s = lastVote s').
  {
    intros []; [by left |].
    by right; apply IHHs; congruence.
  }
  destruct Ht as [_ Ht].
  change transition with (paxos_acceptor_transition a) in Ht.
  destruct l; cbn in Ht, IHHs |- *.
  - right.
    apply (f_equal fst) in Ht; simpl in Ht; subst s'.
    by destruct om as [[? []] |]; simpl.
  - destruct lv as [b_lv v_lv], om as [[? []]|]; simpl in *;
      injection Ht as [= <- <-]; try (by right); [].
    left; simpl in Hlv.
    by congruence.
Qed.

Lemma paxos_acceptor_sent_bounds_maxBal :
  forall a s,
    valid_state_prop (pre_loaded_with_all_messages_vlsm (paxos_acceptor_vlsm a)) s ->
  forall b mb,
    has_been_sent (paxos_acceptor_vlsm a) s (b, mb) ->
    (b <= paxos_maxBal s)%Z.
Proof.
  intros a s Hs b mb.
  apply (from_send_to_from_sent_argument
    (paxos_acceptor_vlsm a) (fun s => b <= paxos_maxBal s)%Z); [.. | done].
  - by intros * Ht; apply paxos_maxBal_mono in Ht; lia.
  - intros * [_ Htrans].
    cbn in Htrans; unfold paxos_acceptor_transition in Htrans.
    by repeat case_match; inversion Htrans.
Qed.

Lemma maxVBal_le_paxos_maxBal :
  forall a s,
    valid_state_prop (pre_loaded_with_all_messages_vlsm (paxos_acceptor_vlsm a)) s ->
      (maxVBal s <= paxos_maxBal s)%Z.
Proof.
  intros a s Hs.
  unfold maxVBal.
  destruct (lastVote s) as [[b_lv v_lv] |] eqn: Heq; simpl.
  - eapply paxos_acceptor_sent_bounds_maxBal; [done |].
    by apply (last_vote_was_sent a s Hs _ Heq).
  - by destruct (paxos_maxBal s); simpl; lia.
Qed.

Lemma maxVBal_mono :
  forall a l s im s' om,
    input_valid_transition 
      (pre_loaded_with_all_messages_vlsm
         (paxos_acceptor_vlsm a)) l (s, im) (s', om) ->
    (maxVBal s <= maxVBal s')%Z.
Proof.
  intros * Ht.
  destruct Ht as [(Hs & _ & Hvalid) Htrans].
  cbn in Hvalid, Htrans; unfold paxos_acceptor_valid, paxos_acceptor_transition in Hvalid, Htrans.
  repeat case_match; inversion Htrans; cbn; try done.
  by transitivity (paxos_maxBal s); [apply maxVBal_le_paxos_maxBal |].
Qed.

Lemma sent_vote_le_maxVBal :
  forall a s,
    valid_state_prop (pre_loaded_with_all_messages_vlsm (paxos_acceptor_vlsm a)) s ->
  forall b v,
    has_been_sent (paxos_acceptor_vlsm a) s (b, m_2b a v) ->
    (b <= maxVBal s)%Z.
Proof.
  intros a s Hs b v; revert s Hs.
  apply (from_send_to_from_sent_argument (paxos_acceptor_vlsm a) (fun s => b <= maxVBal s)%Z);
    intros * Ht; [by apply maxVBal_mono in Ht; lia |].
  destruct Ht as [_ Htrans].
  destruct (examine_paxos_acceptor_output Htrans) as [-> _].
  by cbn in Htrans; repeat case_match; inversion Htrans.
Qed.

Lemma sending_1b_updates_maxBal :
  forall [a l s im s' b lv],
    input_valid_transition (pre_loaded_with_all_messages_vlsm
      (paxos_acceptor_vlsm a)) l (s, im) (s', Some (b, m_1b a lv)) ->
    (paxos_maxBal s < b)%Z /\ (paxos_maxBal s' = Some b).
Proof.
  intros * [(_ & _ & Hvalid) Hstep]; cbn in Hstep.
  apply examine_paxos_acceptor_output in Hstep as Hla; destruct Hla as [-> _].
  by destruct im as [[? []] |]; cbn in s, s', Hvalid; inversion Hstep; subst.
Qed.

End sec_paxos_acceptor_vlsm_lem.

Section sec_leaders_vlsm.

(**
   We directly define a VLSM that represents all leaders
   instead of using [composite_vlsm], because [composite_vlsm]
   requires a finite index set.

   A finite map has entries for ballots whose leader is not
   in the initial state.
 *)

Record ballot_state :=
{
  sent_1a : bool;
  gathered_1b : AMap (option (Ballot * Value));
  sent_1c : list (AllOrFin VSet); (* Some if we have sent any 1c - combine with multiple steps *)
  sent_2a : option Value; (* Some v if we have sent a 2a for v *)
}.

Definition initial_ballot_state : ballot_state :=
{|
  sent_1a := false;
  gathered_1b := ∅;
  sent_1c := [];
  sent_2a := None;
|}.

#[export] Instance ballot_state_empty : Empty ballot_state := initial_ballot_state.

Definition set_sent_1a (sb : ballot_state) : ballot_state :=
{|
  sent_1a := true;
  gathered_1b := gathered_1b sb;
  sent_1c := sent_1c sb;
  sent_2a := sent_2a sb;
|}.

Definition insert_gathered_1b
  (a : Acceptor) (last_vote : option (Ballot * Value)) (sb : ballot_state) : ballot_state :=
{|
  sent_1a := sent_1a sb;
  gathered_1b := <[ a := last_vote ]> (gathered_1b sb);
  sent_1c := sent_1c sb;
  sent_2a := sent_2a sb;
|}.

Definition set_sent_1c (safe_v : AllOrFin VSet) (sb : ballot_state) : ballot_state :=
{|
  sent_1a := sent_1a sb;
  gathered_1b := gathered_1b sb;
  sent_1c := safe_v :: sent_1c sb;
  sent_2a := sent_2a sb;
|}.

Definition set_sent_2a (v : Value) (sb : ballot_state) : ballot_state :=
{|
  sent_1a := sent_1a sb;
  gathered_1b := gathered_1b sb;
  sent_1c := sent_1c sb;
  sent_2a := Some v;
|}.

Definition leaders_state := Bmap ballot_state.

Inductive leader_label : Type :=
| L_send_1a
| L_recv_1b
| L_send_1c (safe_v : AllOrFin VSet)
| L_send_2a (v : Value).

Definition leaders_label : Type := Ballot * leader_label.

Definition leaders_type : VLSMType paxos_message :=
{|
  state := leaders_state;
  label := leaders_label;
|}.

Definition calculate_safe_values
  (b : Ballot) (participants : AMap (option (Ballot * Value))) : AllOrFin VSet :=
  let FreeVoters := dom (filter (fun '(_, lv) => lv = None) participants) in
    if decide (Quorum FreeVoters)
    then any_value
    else
      let VotersFor (v : Value) : ASet :=
        dom (filter (fun '(a,lv) => ((fst <$> lv : Ballot') < b)%Z /\
        snd <$> lv = Some v) participants) in
      let VotedValues : VSet := map_to_set (fun _ v => v) (omap (fmap snd) participants) in
        some_values (filter (fun v => Quorum (VotersFor v ∪ FreeVoters)) VotedValues).

Lemma calculate_safe_values_any_ok  (b : Ballot) (participants : AMap (option (Ballot * Value))) :
  calculate_safe_values b participants = any_value ->
    exists Q : sig Quorum, forall a : Acceptor, a ∈ `Q -> participants !! a = Some None.
Proof.
  unfold calculate_safe_values.
  case_match eqn: Hcheck; [| done].
  intros _; exists (exist _ _ q).
  cbn; intros a Ha.
  apply fin_map_dom.elem_of_dom in Ha as [lv Ha].
  by apply map_lookup_filter_Some in Ha as [Ha ->].
Qed.

Lemma calculate_safe_values_some_ok
  (b : Ballot) (participants : AMap (option (Ballot * Value))) (safe_v : VSet) :
  calculate_safe_values b participants = some_values safe_v ->
  forall v : Value, v ∈ safe_v ->
    exists Q : sig Quorum,
    (forall a : Acceptor, a ∈ `Q ->
      (exists (vbal : Ballot), participants !! a = Some (Some (vbal, v)) /\ (vbal < b)%Z)
      \/ participants !! a = Some None)
    /\ exists (a_hist : Acceptor) (lv : option (Ballot * Value)),
         a_hist ∈ `Q /\ participants !! a_hist = Some lv /\ lv <> None.
Proof.
  cbv beta delta[calculate_safe_values].
  set (FreeVoters:= dom _).
  set (VotersFor := fun v => dom _).
  simpl.
  destruct (decide (Quorum FreeVoters)) as [| Hno_free_quorum]; [done|].
  intros [= <-] v Hv.
  apply elem_of_filter in Hv as [HQ Hv].
  exists (exist _ _ HQ); simpl.
  split.
  - intros a Ha.
    apply elem_of_union in Ha as [Ha | Ha];
      apply fin_map_dom.elem_of_dom in Ha as [lv Ha];
      apply map_lookup_filter_Some in Ha;
      [| itauto congruence].
    destruct Ha as (Ha & Hbal & Hlv).
    destruct lv as [[vbal vval] |]; cbn in Hbal, Hlv; [| by contradict Hlv].
    left; exists vbal.
    by inversion Hlv; subst v.
  - cut (exists a : Acceptor, a ∈ VotersFor v).
    {
      intros [a Ha]; exists a.
      apply fin_map_dom.elem_of_dom in Ha as Ha'; destruct Ha' as [lv Ha_lv].
      exists lv.
      split; [by set_solver |].
      apply map_lookup_filter_Some in Ha_lv as (Hlookup & _ & Hnot_None).
      split; [by apply Hlookup |].
      by destruct lv; cbn.
    }
    apply set_choose.
    intros Hequiv.
    eapply Hno_free_quorum, QClosed; [| by apply HQ].
    by rewrite Hequiv, (union_empty_l FreeVoters).
Qed.

Section sec_one_leader.

Context
  (self : Ballot)
  .

Definition leader_valid : leader_label -> (option ballot_state * option paxos_message) -> Prop :=
  fun l '(osb, m) =>
    let sb := default ∅ osb in
    match l, m with
    | L_send_1a, None => True (* no side conditions *)
    | L_recv_1b, Some (b, m_1b a _) => b = self (* no conditions *)
    | L_send_1c safe_vs, None => safe_vs = calculate_safe_values self sb.(gathered_1b)
    | L_send_2a v, None =>
        None = sent_2a sb (* Have not previously sent a 2a *)
        /\ exists safe_vs, v ∈ safe_vs /\ safe_vs ∈ sent_1c sb
    (* Did previously sent 1c that approves v *)
    | _, _ => False
    end.

Definition leader_transition (l : leader_label)
  : ballot_state * option paxos_message -> option (ballot_state * option paxos_message_body) :=
  fun '(sb, im) =>
    match l, im with
    | L_send_1a, None => Some (set_sent_1a sb, Some m_1a)
    | L_recv_1b, Some (b, m_1b a lv) =>
        Some (insert_gathered_1b a lv sb, None)
    | L_send_1c safe_v, None =>
        Some (set_sent_1c safe_v sb, Some (m_1c safe_v))
    | L_send_2a v, None =>
        if sent_2a sb then None else Some (set_sent_2a v sb, Some (m_2a v))
    | _, _ => None
    end.

(**
  A quick sanity check that [initial_ballot_state] cannot be produced in
  the output of [leader_transition].
  So the reachable values of [leader_state] have a
  unique representation in the sense that
  <<forall i, m !!! i = n !!! i>> implies <<m ≡ n>>.
*)
Lemma leader_result_not_initial :
  forall l b im r om,
    leader_transition l (b, im) = Some (r, om) ->
    r <> initial_ballot_state.
Proof.
  intros *.
  unfold leader_transition.
  repeat case_match; subst; intros [= <- <-]; try discriminate.
  intros Heq.
  apply (f_equal gathered_1b) in Heq; cbn in Heq.
  by apply insert_non_empty in Heq.
Qed.

Definition leader_messages (sb : ballot_state) : list paxos_message_body :=
  (if sent_1a sb then [m_1a] else [])
    ++ (m_1c <$> sent_1c sb)
    ++ (m_2a <$> option_list (sent_2a sb)).

Lemma leader_messages_correct :
  forall (l : leader_label) (sb : ballot_state) im sb' oom,
    leader_transition l (sb, im) = Some (sb', oom) ->
    forall m, m ∈ leader_messages sb' <-> oom = Some m \/ m ∈ leader_messages sb.
Proof.
  intros l sb im sb' oom Ht m.
  rewrite (eq_comm oom).
  unfold leader_transition in Ht.
  pose proof (nosend_lem := fun P => or_r _ P (Some_ne_None m)).
  by repeat case_match; (try discriminate Ht); subst; injection Ht as [= <- <-]; subst;
    (rewrite ?(inj_iff Some), ?nosend_lem; clear nosend_lem;
     unfold leader_messages; destruct sb as [sent_1a ? ? sent_2a]; simpl in *; subst; simpl);
    [destruct sent_1a | ..]; simpl_elem_of_list; itauto.
Qed.

Lemma leader_gathered_1b_step :
  forall (l : leader_label) (sb : ballot_state) im sb' oom,
    leader_transition l (sb, im) = Some (sb', oom) ->
    forall a lv, gathered_1b sb' !! a = Some lv ->
      (l = L_recv_1b /\ exists b, im = Some (b, m_1b a lv)) \/ gathered_1b sb !! a = Some lv.
Proof.
  intros l [? sb_gathered_1b ? ?] * Ht a lv; cbn.
  unfold leader_transition in Ht.
  repeat case_match; inversion Ht; cbn; only 1, 3-4: by right.
  destruct (decide (a0 = a)) as [-> | Hneq].
  - rewrite lookup_insert; intros [=->].
    by (left; eauto).
  - rewrite lookup_insert_ne by done.
    by right.
Qed.

End sec_one_leader.

Definition leaders_valid : leaders_label -> (leaders_state * option paxos_message) -> Prop :=
  fun '(b, l) '(s, om) => leader_valid b l (s !! b, om).

Definition leaders_transition
  : leaders_label -> leaders_state * option paxos_message -> leaders_state * option paxos_message :=
  fun '(b, l) '(s, im) =>
    match leader_transition l (s !!! b, im) with
    | Some (sb', om) => (<[b := sb']> s, pair b <$> om)
    | None => (s, None)
    end.

Definition leaders_machine : VLSMMachine leaders_type :=
{|
  initial_state_prop := (.= ∅);
  s0 := populate (exist _ ∅ eq_refl);
  initial_message_prop := fun _ => False;
  valid := leaders_valid;
  transition := leaders_transition;
|}.

Definition leaders_vlsm : VLSM paxos_message := mk_vlsm leaders_machine.

Definition leaders_messages (s : leaders_state) : list paxos_message :=
  elements (dom s) ≫= fun b : Ballot => pair b <$> leader_messages (s !!! b).

Lemma elem_of_leaders_messages b mb s :
  (b, mb) ∈ leaders_messages s <-> mb ∈ leader_messages (s !!! b).
Proof.
  unfold leaders_messages.
  rewrite elem_of_list_bind.
  split.
  - intros (y & Hmsgs & _).
    by apply elem_of_list_fmap in Hmsgs as [y0 [[= <- <-] Hmsgs]].
  - intros Hmsgs.
    exists b.
    split; [by apply elem_of_list_fmap_1 |].
    rewrite elem_of_elements, (fin_map_dom.elem_of_dom s b).
    rewrite (lookup_total_alt s) in Hmsgs.
    by destruct (_ !! b); [| apply elem_of_nil in Hmsgs].
Qed.

Lemma leaders_messages_correct :
  forall l s im s' om,
    leaders_transition l (s, im) = (s', om) ->
    forall m, m ∈ leaders_messages s' <-> (om = Some m \/ m ∈ leaders_messages s).
Proof.
  intros [b l] s im s' om.
  unfold leaders_transition.
  destruct (leader_transition _ _) as [[sb' omb] |] eqn: H_local;
    intros [= <- <-] [b_m m]; [| by itauto congruence].
  apply leader_messages_correct with (m := m) in H_local.
  rewrite 2 elem_of_leaders_messages.
  destruct (decide (b_m = b)) as [-> | Hneq].
  - rewrite (lookup_total_insert s), H_local.
    destruct omb; simpl.
    + by rewrite !(inj_iff Some), (inj_iff (pair b)).
    + by rewrite !or_r.
  - rewrite (lookup_total_insert_ne s) by done.
    rewrite or_r; [done |].
    by destruct omb; simpl; congruence.
Qed.

(** Send history can be checked without enumerating all the past messages. *)
Definition leader_has_been_sent (s : ballot_state) (m : paxos_message_body) : Prop :=
  match m with
  | m_1a => sent_1a s = true
  | m_1c vs => vs ∈ sent_1c s
  | m_2a v => sent_2a s = Some v
  | _ => False
  end.

Definition leaders_has_been_sent (s : leaders_state) (m : paxos_message) : Prop :=
  let (b, mb) := m in leader_has_been_sent (s !!! b) mb.

Lemma leaders_messages_iff (s : leaders_state) (m : paxos_message) :
  leaders_has_been_sent s m <-> m ∈ leaders_messages s.
Proof.
  destruct m as [b m]; cbn.
  rewrite elem_of_leaders_messages.
  generalize (s !!! b); intros sb.
  unfold leader_messages; simpl_elem_of_list.
  split.
  - unfold leader_has_been_sent.
    destruct sb; cbn; intros Hm.
    by destruct m; subst; simpl; simpl_elem_of_list; auto using elem_of_list_fmap_1.
  - intros [Hm | [Hm | Hm]].
    + destruct (sent_1a sb) eqn: H_1a.
      * by apply elem_of_list_singleton in Hm as ->.
      * by apply elem_of_nil in Hm.
    + by apply elem_of_list_fmap in Hm as (? & -> & ?).
    + destruct (sent_2a sb) eqn: H_2a.
      * by apply elem_of_list_singleton in Hm as ->.
      * by apply elem_of_nil in Hm.
Qed.

#[export] Instance leaders_has_been_sent_dec : RelDecision leaders_has_been_sent.
Proof.
  by intros s [b []]; simpl; typeclasses eauto.
Defined.

Lemma leaders_has_been_sent_props :
  has_been_sent_stepwise_prop (vlsm := leaders_vlsm) leaders_has_been_sent.
Proof.
  split.
  - intros s -> [b m]; simpl.
    unfold leaders_state; rewrite lookup_total_empty.
    by destruct m; simpl; auto using not_elem_of_nil.
  - intros * [(_ & _ & Hvalid) Ht] m; simpl.
    rewrite 2 leaders_messages_iff.
    by eapply leaders_messages_correct.
Qed.

#[export] Instance leaders_has_been_sent_cap : HasBeenSentCapability leaders_vlsm :=
{|
  has_been_sent_stepwise_props := leaders_has_been_sent_props;
|}.

Lemma examine_leaders_output :
  forall l s im s' om,
    leaders_transition l (s, im) = (s', Some om) ->
    match om with
    | (b, m_1a) => l = (b, L_send_1a)
    | (b, m_1c vs) => l = (b, L_send_1c vs)
    | (b, m_2a v) => l = (b, L_send_2a v)
    | _ => False
    end.
Proof.
  unfold leaders_transition, leader_transition.
  intros [lb []] s [[ib im] |] s' [ob om] Ht; try done.
  - by inversion Ht.
  - by destruct im.
  - by inversion Ht.
  - by destruct (sent_2a _); inversion Ht.
Qed.

End sec_leaders_vlsm.

Section sec_paxos_vlsm.

Inductive paxos_index : Type :=
| leaders_ix
| acceptor_ix (a : Acceptor).

#[export] Instance pi_cancel :
  Cancel eq (from_option acceptor_ix leaders_ix)
    (paxos_index_rect (λ _ : paxos_index, option Acceptor) None Some).
Proof.
  by intros [].
Defined.

#[export] Instance paxos_index_eq_dec : EqDecision paxos_index.
Proof.
  by generalize cancel_inj; apply inj_eq_dec.
Defined.

#[export] Instance cancel_pi :
  Cancel eq (paxos_index_rect (λ _ : paxos_index, option Acceptor) None Some)
   (from_option acceptor_ix leaders_ix).
Proof.
  by intros [].
Defined.

#[export] Instance acceptor_inj : Inj eq eq (from_option acceptor_ix leaders_ix).
Proof. by apply cancel_inj. Defined.

#[export] Instance acceptor_surj : Surj eq (from_option acceptor_ix leaders_ix).
Proof. by apply cancel_surj. Defined.

#[export] Instance paxos_index_finite : finite.Finite paxos_index :=
 bijective_finite (from_option acceptor_ix leaders_ix).

Definition IM (ix : paxos_index) : VLSM paxos_message :=
  match ix with
  | leaders_ix => leaders_vlsm
  | acceptor_ix a => paxos_acceptor_vlsm a
  end.

#[export] Instance IM_HasBeenSentCapability (ix : paxos_index) : HasBeenSentCapability (IM ix).
Proof.
  by destruct ix; typeclasses eauto.
Defined.

Definition paxos_vlsm := composite_vlsm IM (no_equivocations (free_composite_vlsm IM)).

Definition preloaded_paxos_vlsm := pre_loaded_with_all_messages_vlsm paxos_vlsm.

End sec_paxos_vlsm.

Definition message_sender (m : paxos_message_body) : paxos_index :=
  match m with
  | m_1a => leaders_ix
  | m_1b a _ => acceptor_ix a
  | m_1c _ => leaders_ix
  | m_2a _ => leaders_ix
  | m_2b a _ => acceptor_ix a
  end.

Lemma localize_send :
  forall l s im s' om,
    transition preloaded_paxos_vlsm l (s, im) = (s', Some om) ->
    projT1 l = message_sender (snd om).
Proof.
  intros * Ht; destruct om as [ob omb]; cbn in Ht |- *.
  destruct l as [[| a_l] l], (transition _ _ _) as [si' om'] eqn: H_step in Ht;
    injection Ht as [= <- ->].
  - by apply examine_leaders_output in H_step; destruct omb.
  - cbn in H_step; apply examine_paxos_acceptor_output in H_step.
    by destruct omb; cbn; itauto congruence.
Qed.

Lemma localize_sent_messages
  (s : state paxos_vlsm)
  (Hs : valid_state_prop preloaded_paxos_vlsm s) (* or preloaded *)
  : forall m : paxos_message,
    has_been_sent paxos_vlsm s m
    <-> has_been_sent (IM (message_sender (snd m))) (s (message_sender (snd m))) m.
Proof.
  induction Hs using valid_state_prop_ind;
    [by intros m; split; intros []%has_been_sent_no_inits |].
  intros [b mb].
  erewrite has_been_sent_step_update; [| by apply Ht].
  rewrite IHHs.
  destruct l as [i l].
  destruct (decide (i = message_sender mb)) as [-> | Hneq].
  - apply input_valid_transition_preloaded_project_active in Ht; cbn in Ht.
    by rewrite <- has_been_sent_step_update.
  - apply input_valid_transition_preloaded_project_any with (i := message_sender mb) in Ht as Ht'.
    cbn; destruct Ht' as [-> | [li [[= Heq] _]]]; [| done].
    rewrite or_r; [done |].
    by intros ->; destruct Ht as [_ Hstep]; apply localize_send in Hstep.
Qed.

Notation Pred_Stable_In VLSM P :=
  (forall l s im s' om, input_valid_transition VLSM l (s, im) (s', om) -> P s -> P s').

Lemma lift_component_stable_prop ix (P : state (IM ix) -> Prop) :
  Pred_Stable_In (pre_loaded_with_all_messages_vlsm (IM ix)) P ->
  Pred_Stable_In preloaded_paxos_vlsm (fun s => P (s ix)).
Proof.
  intros H_stable_in_ix * Ht.
  destruct l as [i_l l].
  apply input_valid_transition_preloaded_project_any with (i := ix)
    in Ht as [<- | (li & _ & Ht)]; [done|].
  by eapply H_stable_in_ix.
Qed.

Lemma lift_acceptor_stable_prop (P : paxos_acceptor_state -> Prop) a :
  Pred_Stable_In (pre_loaded_with_all_messages_vlsm (paxos_acceptor_vlsm a)) P ->
  (forall l s im s' om,
    input_valid_transition (pre_loaded_with_all_messages_vlsm paxos_vlsm) l (s, im) (s', om) ->
      P (s (acceptor_ix a)) -> P (s' (acceptor_ix a))).
Proof.
  by exact (lift_component_stable_prop (acceptor_ix a) P).
Qed.

Lemma lift_leaders_stable_prop (P : leaders_state -> Prop) :
  Pred_Stable_In (pre_loaded_with_all_messages_vlsm leaders_vlsm) P ->
  (forall l s im s' om,
    input_valid_transition (pre_loaded_with_all_messages_vlsm paxos_vlsm) l (s, im) (s', om) ->
      P (s leaders_ix) -> P (s' leaders_ix)).
Proof.
  by exact (lift_component_stable_prop leaders_ix P).
Qed.

Lemma send_implies_sent_argument
  (a b : paxos_message) :
  (forall l s oim s',
    input_valid_transition preloaded_paxos_vlsm l (s, oim) (s', Some b) ->
    has_been_sent paxos_vlsm s a) ->
  (forall s,
    valid_state_prop preloaded_paxos_vlsm s ->
    has_been_sent paxos_vlsm s b ->
    has_been_sent paxos_vlsm s a).
Proof.
  intros * H_at_sent s Hs.
  induction Hs using valid_state_prop_ind.
  - by intros Hsent; apply has_been_sent_no_inits in Hsent.
  - rewrite 2 (has_been_sent_step_update Ht).
    intros [-> | Hsent_b]; right.
    + by apply H_at_sent in Ht.
    + by apply IHHs.
Qed.

Lemma sends_unique_argument
  A (f : A -> paxos_message) (P : state paxos_vlsm -> Prop)
  (f_inj : Inj eq eq f)
  (HP_stable : forall l s oim s' oom,
    input_valid_transition preloaded_paxos_vlsm l (s, oim) (s', oom) ->
    P s -> P s')
  (HP_step : forall l s oim s' x,
      input_valid_transition preloaded_paxos_vlsm l (s, oim) (s', Some (f x)) ->
      ~ P s /\ P s') :
  forall s,
    valid_state_prop preloaded_paxos_vlsm s ->
  forall a b,
    has_been_sent paxos_vlsm s (f a) ->
    has_been_sent paxos_vlsm s (f b) ->
      a = b.
Proof.
  intros s Hs.
  induction Hs using valid_state_prop_ind;
    [by intros a b []%has_been_sent_no_inits |].
  assert (Hs : valid_state_prop preloaded_paxos_vlsm s) by apply Ht.
  assert (HP_sent : forall s : state paxos_vlsm,
    valid_state_prop preloaded_paxos_vlsm s ->
    forall a : A, has_been_sent paxos_vlsm s (f a) -> P s).
  {
    clear -HP_step HP_stable.
    intros s Hs.
    induction Hs using valid_state_prop_ind; intros a Hsent;
      [by apply has_been_sent_no_inits in Hsent |].
    apply has_been_sent_step_update with (1 := Ht) in Hsent as [-> | Hsent].
    - by apply HP_step in Ht; apply Ht.
    - by eapply HP_stable, IHHs.
  }
  intros a b Ha Hb; specialize (IHHs a b).
  rewrite has_been_sent_step_update with (1 := Ht) in Ha, Hb.
  destruct Ha as [Ha | Ha], Hb as [Hb | Hb]; [subst om'.. |].
  - by injection Hb; apply inj.
  - apply (HP_sent _ Hs) in Hb; contradict Hb.
    by apply HP_step in Ht; apply Ht.
  - apply (HP_sent _ Hs) in Ha; contradict Ha.
    by apply HP_step in Ht; apply Ht.
  - by apply IHHs.
Qed.

Lemma sent_1b_once :
  forall (s : state paxos_vlsm),
    valid_state_prop preloaded_paxos_vlsm s ->
  forall (b : Ballot) (a : Acceptor) lv1 lv2,
    has_been_sent paxos_vlsm s (b, m_1b a lv1) ->
    has_been_sent paxos_vlsm s (b, m_1b a lv2) ->
    lv1 = lv2.
Proof.
  intros s Hs b a; revert s Hs.
  apply (sends_unique_argument _ (fun x => (b, m_1b a x))
    (fun s => (b <= paxos_maxBal (s (acceptor_ix a)))%Z)).
  - by intros x y; congruence.
  - (* P_stable *)
    apply (lift_acceptor_stable_prop (fun sb => b <= paxos_maxBal sb)%Z a).
    intros * Ht Hle.
    transitivity (paxos_maxBal s); [done |].
    by eapply paxos_maxBal_mono.
  - intros * Ht.
    apply input_valid_transition_preloaded_project_active in Ht as Ht'.
    destruct Ht as [(_ & _ & Hvalid) Ht].
    apply localize_send in Ht as Hix.
    destruct l as [ix_l l].
    simpl in Hix; subst ix_l; simpl in Ht'.
    apply sending_1b_updates_maxBal in Ht'.
    destruct Ht' as [Hlt ->].
    simpl; fold (Ballot_to_Z b).
    by lia.
Qed.

Lemma last_vote_was_sent_paxos :
  forall s,
    valid_state_prop preloaded_paxos_vlsm s ->
  forall a lv,
    lastVote (s (acceptor_ix a)) = Some lv ->
    has_been_sent paxos_vlsm s (lv.1, m_2b a lv.2).
Proof.
  intros s Hs a lv Hlv.
  apply localize_sent_messages; [done |].
  apply last_vote_was_sent; [| done].
  by apply valid_state_project_preloaded_to_preloaded with (i := acceptor_ix a) in Hs.
Qed.

Lemma sent_1b_impl_sent_lastvote_as_2b :
  forall s, valid_state_prop preloaded_paxos_vlsm s ->
  forall (b : Ballot) (a : Acceptor) (b_lv : Ballot) (v_lv : Value),
    has_been_sent paxos_vlsm s (b, m_1b a (Some (b_lv, v_lv))) ->
    has_been_sent paxos_vlsm s (b_lv, m_2b a v_lv).
Proof.
  intros s Hs b a b_lv v_lv; revert s Hs.
  apply send_implies_sent_argument.
  intros [i_l l] s im s' Ht.
  assert (i_l = acceptor_ix a) as ->
    by (destruct Ht as [_ Ht]; apply localize_send in Ht; done).
  apply localize_sent_messages; cbn; [by apply Ht |].
  apply input_valid_transition_preloaded_project_active
    in Ht as [(Hs & _ & Hvalid) Ht]; cbn in Hvalid, Ht.
  apply examine_paxos_acceptor_output in Ht as Hl; destruct Hl as [-> _].
  simpl in Hvalid.
  destruct im as [[ib []] |]; [| done..].
  injection Ht as [= Heq_s' -> Hlv].
  by revert Hlv; apply last_vote_was_sent.
Qed.

Lemma sent_2b_after_2a :
  forall s, valid_state_prop preloaded_paxos_vlsm s ->
  forall (b : Ballot) (a : Acceptor) v,
    has_been_sent paxos_vlsm s (b, m_2b a v) ->
    has_been_sent paxos_vlsm s (b, m_2a v).
Proof.
  intros s Hs b a v; revert s Hs.
  apply send_implies_sent_argument.
  intros [i_l l] s im s' Ht.
  cut (im = Some (b, m_2a v)).
  {
     by intros ->; destruct Ht as [[_ [_ [_ []]]] _].
  }
  destruct (Ht) as [_ Hstep].
  apply localize_send in Hstep as Hi_l; simpl in Hi_l; subst i_l; clear Hstep.
  apply input_valid_transition_preloaded_project_active in Ht; simpl in Ht.
  destruct Ht as [(_ & _ & Hvalid) Hstep_a]; cbn in Hstep_a.
  apply examine_paxos_acceptor_output in Hstep_a as Hl; destruct Hl as [-> _].
  by cbn in Hvalid; destruct im as [[? []] |]; inversion Hstep_a.
Qed.

Lemma sent_2a_unique :
  forall s : state paxos_vlsm,
    valid_state_prop preloaded_paxos_vlsm s ->
  forall (b : Ballot) (v w : Value),
    has_been_sent paxos_vlsm s (b, m_2a v) ->
    has_been_sent paxos_vlsm s (b, m_2a w) ->
    v = w.
Proof.
  intros s Hs b; revert s Hs.
  apply (sends_unique_argument Value (fun v => (b, m_2a v))
    (fun s => is_Some (sent_2a ((s leaders_ix : leaders_state) !!! b)))).
  - by intros x y; congruence.
  - apply (lift_leaders_stable_prop (fun sl => is_Some (sent_2a (sl !!! b)))).
    intros [b_l l] * [_ Hstep].
    change transition with leaders_transition in Hstep.
    unfold leaders_transition in Hstep.
    destruct (leader_transition l _) as [[sb' omb] |] eqn: H_step_l;
      injection Hstep as [= <- <-]; [| done].
    destruct (decide (b = b_l)) as [<- | Hneq];
      [| by rewrite (lookup_total_insert_ne s)].
    rewrite (lookup_total_insert s b sb').
    by cbn in H_step_l; repeat case_match; inversion H_step_l.
  - intros [ix l] * Ht.
    destruct (Ht) as [_ Hix].
    apply localize_send in Hix; simpl in Hix; subst ix.
    apply input_valid_transition_preloaded_project_active in Ht; simpl in Ht.
    revert Ht; generalize (s leaders_ix) as sl, (s' leaders_ix) as sl'; clear s s'; intros.
    destruct Ht as [(_ & _ & Hvalid) Hstep].
    change valid with leaders_valid in Hvalid.
    change transition with leaders_transition in Hstep.
    apply examine_leaders_output in Hstep as Hl; subst l.
    destruct oim; [done |].
    destruct Hvalid as [H_field_2a _].
    cbn in Hstep; replace (sent_2a _) with (@None Value) in Hstep |- *.
    injection Hstep as [= <-].
    rewrite (lookup_total_insert sl).
    unfold is_Some; cbn.
    by split; [intros [] | eexists].
Qed.

Lemma sent_2b_unique :
  forall s,
    valid_state_prop preloaded_paxos_vlsm s ->
  forall (b : Ballot) (a : Acceptor) v w,
    has_been_sent paxos_vlsm s (b, m_2b a v) ->
    has_been_sent paxos_vlsm s (b, m_2b a w) ->
    v = w.
Proof.
  intros s Hs b a v w Hv Hw.
  apply sent_2b_after_2a in Hv, Hw; [| done..].
  by eapply sent_2a_unique.
Qed.

Lemma sent_2a_after_1c :
  forall s,
    valid_state_prop preloaded_paxos_vlsm s ->
  forall (b : Ballot) (v : Value),
    has_been_sent paxos_vlsm s (b, m_2a v) ->
    exists (safe_v : AllOrFin VSet),
      v ∈ safe_v /\ has_been_sent paxos_vlsm s (b, m_1c safe_v).
Proof.
  intros s Hs b v.
  induction Hs using valid_state_prop_ind;
    [by intros Hsent%has_been_sent_no_inits |].
  rewrite (has_been_sent_step_update Ht).
  intros [Hnew | Hsent]; cycle 1.
  - destruct (IHHs Hsent) as (safe_v & Hv & Hsent_1c).
    exists safe_v; split; [done |].
    rewrite (has_been_sent_step_update Ht).
    by right.
  - clear IHHs.
    subst om'.
    assert (Hs' : valid_state_prop preloaded_paxos_vlsm s')
      by (apply input_valid_transition_destination in Ht; done).
    destruct l as [ix l].
    destruct (Ht) as [_ Hstep].
    apply localize_send in Hstep; simpl in Hstep; subst ix.
    apply input_valid_transition_preloaded_project_active in Ht; simpl in Ht.
    destruct (Ht) as [_ Hstep].
    apply examine_leaders_output in Hstep; subst l.
    destruct Ht as [(_ & _ & Hvalid) Hstep]; cbn in Hvalid.
    change transition with leaders_transition in Hstep.
    destruct om; [done |].
    destruct Hvalid as (H_no_sent_2a & safe_v & H_vs & H_sent_1c).
    exists safe_v; split; [done |].
    apply localize_sent_messages; cbn in Hstep |- *; [done |].
    replace (sent_2a _) with (@None Value) in Hstep.
    injection Hstep as [= <-].
    rewrite (lookup_total_insert (s leaders_ix)).
    change (safe_v ∈ sent_1c ((s leaders_ix : leaders_state) !!! b)) in H_sent_1c.
    revert H_sent_1c.
    clear -s; generalize ((s leaders_ix : leaders_state) !!! b) as sb; clear s.
    by intros []; simpl.
Qed.

Lemma sender_id_m_2b :
  forall s,
    valid_state_prop preloaded_paxos_vlsm s ->
  forall a b v a',
    (b, m_2b a v) ∈ sent_messages (s (acceptor_ix a')) ->
    a' = a.
Proof.
  intros s Hs a b v a'.
  induction Hs using valid_state_prop_ind;
    [by rewrite (Hs (acceptor_ix a')), elem_of_nil |].
  destruct (decide (a' = a)); [done |].
  intros Hs'; apply IHHs; clear IHHs.
  apply input_valid_transition_preloaded_project_any with (i := acceptor_ix a') in Ht.
  destruct Ht as [-> | (li & -> & _ & Hstep)]; [done |]; cbn in Hstep.
  revert Hstep Hs'.
  generalize (s (acceptor_ix a')); intros sa.
  generalize (s' (acceptor_ix a')); intros sa'.
  unfold paxos_acceptor_transition.
  by repeat case_match; intros [= <- <-]; cbn; try done;
    rewrite elem_of_cons; intros [[=] |].
Qed.

(**
  Define various functions and lemmas that only need to work
  over a single state, without referring to transitions.

  This includes the claims of invariants.
*)

Section sec_paxos_refinement_map.

Context
  (s : state paxos_vlsm)
  (Hs : valid_state_prop preloaded_paxos_vlsm s)
  .

Definition was_voted (a : Acceptor) (b : Ballot) (v : Value) : Prop :=
  has_been_sent paxos_vlsm s (b, m_2b a v).

Definition is_chosen (v : Value) : Prop :=
  exists (Q : sig Quorum) (b : Ballot), forall a, a ∈ `Q -> was_voted a b v.

(**
  These predicates are decidable.
  The sets [Ballot] and [Value] may be infinite, but it
  is only necessary to consider ballots or values that have ever
  been used in a phase 2B vote message, and the set of
  sent messages is finite.
*)

Definition vote_messages : list (Ballot * Acceptor * Value) :=
  enum Acceptor ≫= fun a =>
    omap
      (fun '(b, m) =>
         match m with
         | m_2b a' v => if decide (a' = a) then Some (b, a, v) else None
         | _ => None
         end)
      (sent_messages (s (acceptor_ix a))).

Lemma vote_messages_complete :
  forall a b v,
    was_voted a b v -> (b, a, v) ∈ vote_messages.
Proof.
  intros a b v [[| ia] Hsent]; [done |].
  change (has_been_sent _) with (paxos_acceptor_has_been_sent a) in Hsent.
  unfold paxos_acceptor_has_been_sent in Hsent.
  unfold vote_messages.
  rewrite elem_of_list_bind.
  exists a.
  rewrite elem_of_list_omap.
  split; [| by apply elem_of_enum].
  exists (b, m_2b a v).
  split.
  - by apply sender_id_m_2b in Hsent as Heq; subst.
  - by rewrite decide_True.
Qed.

Lemma vote_messages_sound :
  forall a b v,
    (b, a, v) ∈ vote_messages -> was_voted a b v.
Proof.
  intros a b v.
  unfold vote_messages.
  rewrite elem_of_list_bind.
  intros [a' Helem].
  rewrite elem_of_list_omap in Helem.
  destruct Helem as [[[b' mb] [Helem Hmsg]] _].
  exists (acceptor_ix a).
  destruct mb; [by inversion Hmsg.. |].
  destruct (decide (a0 = a')) as [<- |]; [| done].
  by inversion Hmsg; subst.
Qed.

Definition combine_votesets : Bmap (AMap VSet) -> Bmap (AMap VSet) -> Bmap (AMap VSet) :=
  union_with (fun av1 av2 => Some (union_with (fun vs1 vs2 => Some (union vs1 vs2)) av1 av2)).

Definition vote_in_voteset : Ballot -> Acceptor -> Value -> Bmap (AMap VSet) -> Prop :=
  fun b a v S => v ∈ ((S !!! b) !!! a).

Definition singleton_voteset : Ballot -> Acceptor -> Value -> Bmap (AMap VSet) :=
  fun b a v => {[b := {[a := {[ v ]} ]} ]}.

Lemma entry_of_singleton_voteset :
  forall b a v b' a' v',
    vote_in_voteset b a v (singleton_voteset b' a' v') <-> (b, a, v) = (b', a', v').
Proof.
  intros b a v b' a' v'.
  unfold vote_in_voteset, singleton_voteset.
  split; [| by intros [= <- <- <-]; rewrite 2 lookup_total_singleton, elem_of_singleton].
  intros H_elem.
  replace b' with b in *; cycle 1.
  {
    destruct (decide (b' = b)); [done |].
    rewrite lookup_total_singleton_ne in H_elem by done; cbn in H_elem.
    rewrite lookup_total_empty in H_elem; cbn in H_elem.
    by rewrite elem_of_empty in H_elem.
  }
  rewrite lookup_total_singleton in H_elem.
  replace a' with a in *; cycle 1.
  {
    destruct (decide (a' = a)); [done|].
    rewrite lookup_total_singleton_ne in H_elem by done; cbn in H_elem.
    by rewrite elem_of_empty in H_elem.
  }
  rewrite lookup_total_singleton, elem_of_singleton in H_elem.
  by subst.
Qed.

Lemma entry_of_combine_votesets :
  forall b a v S1 S2,
    vote_in_voteset b a v (combine_votesets S1 S2)
    <-> vote_in_voteset b a v S1 \/ vote_in_voteset b a v S2.
Proof.
  intros b a v S1 S2.
  unfold vote_in_voteset, combine_votesets, lookup_total, map_lookup_total; cbn.
  rewrite lookup_union_with.
  generalize (S1 !! b); intro S1b.
  generalize (S2 !! b); intro S2b.
  destruct S1b as [av1 |], S2b as [av2 |]; simpl;
    [| by rewrite lookup_empty; simpl; rewrite elem_of_empty; itauto..].
  rewrite lookup_union_with.
  generalize (av1 !! a); intro av1a.
  generalize (av2 !! a); intro av2a.
  by destruct av1a as [vs1 |], av2a as [vs2 |]; simpl; set_solver.
Qed.

Definition paxos_votes : Bmap (AMap VSet) :=
  foldr (fun '(b, a, v) => combine_votesets (singleton_voteset b a v)) ∅ vote_messages.

Lemma elem_of_paxos_votes :
  forall b a v,
    (b, a, v) ∈ vote_messages <-> vote_in_voteset b a v paxos_votes.
Proof.
  intros b a v.
  unfold paxos_votes.
  induction vote_messages; simpl.
  - rewrite elem_of_nil.
    unfold vote_in_voteset.
    by do 2 (rewrite lookup_total_empty; simpl); rewrite elem_of_empty.
  - destruct a0 as [[b' a'] v']; simpl.
    rewrite elem_of_cons, entry_of_combine_votesets, entry_of_singleton_voteset.
    by itauto.
Qed.

Lemma paxos_votes_good :
  forall a b v,
    was_voted a b v <-> vote_in_voteset b a v paxos_votes.
Proof.
  intros a b v.
  rewrite <- elem_of_paxos_votes.
  split.
  - by apply vote_messages_complete.
  - by apply vote_messages_sound.
Qed.

Definition votes_from_paxos_acceptor (acc : paxos_acceptor_state) : Bmap VSet :=
  let m_2a_msgs_a :=
    omap (fun m => match m with (b, m_2b _ v) => Some (b, v) | _ => None end) (sent_messages acc)
  in
    foldr (fun '(b, v) votes => mmap_insert b v votes) ∅ m_2a_msgs_a.

Lemma votes_from_paxos_acceptor_to_sent (a : Acceptor) :
  forall b v,
    v ∈ votes_from_paxos_acceptor (s (acceptor_ix a)) !!! b ->
      (b, m_2b a v) ∈ sent_messages (s (acceptor_ix a)).
Proof.
  intros b v Hv.
  pose proof (Hsender := fun a' => sender_id_m_2b s Hs a' b v a).
  unfold votes_from_paxos_acceptor in Hv; revert Hv.
  set (msgs := sent_messages (s (acceptor_ix a))) in *; clearbody msgs; clear s Hs.
  induction msgs; cbn; [by rewrite lookup_total_empty; simpl; set_solver |].
  case_match.
  - destruct p as [b0 v0]; simpl.
    intros Hv.
    apply elem_of_mmap_insert in Hv as [[-> ->] |].
    + destruct a0 as [b0 []]; try done.
      assert ((b, m_2b a0 v) ∈ (b0, m_2b a0 v0) :: msgs)
        by (rewrite elem_of_cons; left; congruence).
      by erewrite Hsender.
    + right; apply IHmsgs; [| done].
      by intros a' Ha'; apply Hsender; constructor.
  - intros Hv; constructor.
    apply IHmsgs; [| done].
    by intros a' Ha'; apply Hsender; constructor.
Qed.

Lemma votes_from_paxos_acceptor_from_sent (a : Acceptor) :
  forall b v,
    (b, m_2b a v) ∈ sent_messages (s (acceptor_ix a)) ->
    v ∈ votes_from_paxos_acceptor (s (acceptor_ix a)) !!! b.
Proof.
  intros b v.
  unfold votes_from_paxos_acceptor.
  generalize (sent_messages (s (acceptor_ix a))) as msgs.
  induction msgs; intros H_elem; [by apply elem_of_nil in H_elem |].
  destruct a0 as [b0 m0].
  apply elem_of_cons in H_elem as [<- | H_elem].
  - by simpl; apply elem_of_mmap_insert; left.
  - destruct m0; simpl; try apply (IHmsgs H_elem); [].
    by apply elem_of_mmap_insert; right; apply IHmsgs.
Qed.

Lemma votes_from_paxos_acceptor_iff :
  forall a b v,
    (b, m_2b a v) ∈ sent_messages (s (acceptor_ix a))
    <-> v ∈ votes_from_paxos_acceptor (s (acceptor_ix a)) !!! b.
Proof.
  split.
  - by apply votes_from_paxos_acceptor_from_sent.
  - by apply votes_from_paxos_acceptor_to_sent.
Qed.

(**
  The projection from Paxos to Voting maps each acceptor to a voter,
  using the [paxos_maxBal] of the acceptor and the set [votes_from_paxos_acceptor]
  as the [maxBal] and [votes] of the voter.
*)
Definition to_voting_state : state (voting_vlsm Value VSet Acceptor ASet Quorum) :=
  fun a =>
    {|
      maxBal := paxos_maxBal (s (acceptor_ix a));
      votes := votes_from_paxos_acceptor (s (acceptor_ix a));
    |}.

(**
  The source development from Lamport provides some
  predicates which are conjectured to be invariants of
  the Paxos transition system, and conjectured to
  be sufficient to finish the refinement proof,
  but does not provide proofs.

  Some of the conjectured invariants are defined using
  predicates from the Voting module applied to the projection of the
  state.
*)
Definition V_DidNotVoteIn : Acceptor -> Ballot -> Prop :=
  fun a b => Voting.did_not_vote_in _ VSet (to_voting_state a) b.

Definition V_VotedFor : Acceptor -> Ballot -> Value -> Prop :=
  fun a b v => Voting.voted_for _ VSet (to_voting_state a) b v.

Definition V_SafeAt : Ballot -> Value -> Prop :=
  fun b v => Voting.SafeAt _ VSet _ ASet Quorum to_voting_state v b.

(**
  Conjectured invariants.
  The definitions named "_prop" are the statements of
  the conjectured invariants.
*)

Definition Inv_past_vote_info_prop : Prop :=
  forall (a : Acceptor),
    (maxVBal (s (acceptor_ix a)) <= paxos_maxBal (s (acceptor_ix a)))%Z
    /\ (forall (b : Ballot),
         (maxVBal (s (acceptor_ix a)) < b)%Z -> (b < paxos_maxBal (s (acceptor_ix a)))%Z ->
            V_DidNotVoteIn a b)
    /\ match lastVote (s (acceptor_ix a)) with
       | None => True
       | Some (b_lv, v_lv) => V_VotedFor a b_lv v_lv
       end.

Definition P1bInv_prop : Prop :=
  forall (b_m : Ballot) (a_m : Acceptor) (lv_m : option (Ballot * Value)),
    let mbal_m := fst <$> lv_m : Ballot' in
      has_been_sent paxos_vlsm s (b_m, m_1b a_m lv_m) ->
      (b_m <= paxos_maxBal (s (acceptor_ix a_m)))%Z
      /\ (mbal_m < b_m)%Z
      /\ (forall (b : Ballot), (b < b_m)%Z -> (mbal_m < b)%Z -> V_DidNotVoteIn a_m b).

Definition P1cInv_prop : Prop :=
  forall b_m (vs_m : AllOrFin VSet),
    has_been_sent paxos_vlsm s (b_m, m_1c vs_m) ->
  forall (v : Value), v ∈ vs_m -> V_SafeAt b_m v.

Definition P2aInv_prop : Prop :=
  forall b_m v_m,
    has_been_sent paxos_vlsm s (b_m, m_2a v_m) ->
      exists vs_c, v_m ∈ vs_c /\ has_been_sent paxos_vlsm s (b_m, m_1c vs_c).

(**
  This holds for a Quorum [Q] and [b] if all acceptors in [Q] have sent a 1b message for ballot [b],
  and either all those messages recorded that the acceptor has no previous vote,
  or there is some ballot b_c which is not earlier than any previous vote from the 1b messages,
  such that there is a 1c message for ballot [b_c] asserting that v is safe,
  and also any acceptors from [Q] whose last_vote was exactly at ballot [b_c] voted for [v]
  (recall the [last_vote] records what the acceptor sent in its last 2b message,
  so a 2b message from round b_c comes after this 1c message).
*)
Definition NoPrevVotes (s : state paxos_vlsm) (As : ASet) (b : Ballot) : Prop :=
  forall a, a ∈ As -> forall lv, has_been_sent _ s (b, m_1b a lv) -> lv = None.

(* A curiosity - could we allow a prev vote that actually votes for v to come after the 1c? *)

Definition ShowsSafeAt (s : state paxos_vlsm) (Q : sig Quorum) (b : Ballot) (v : Value) : Prop :=
  (forall a, a ∈ `Q -> exists last_vote, has_been_sent _ s (b, m_1b a last_vote))
  /\ (NoPrevVotes s (`Q) b
     \/ (exists b_1c vsafe, v ∈ vsafe /\ has_been_sent _ s (b_1c, m_1c vsafe)
        (*
          This clause added for convenience in induction.
          A 1c message will imply a ShowsSafeAt at it's time,
          and we would like one with (b_1c < b) so we can use it for induction.
          It should be equivalent (on preloaded-valid states) by
          arguing that w.l.o.g we can chose b_1c to be the newest time
          recorded in a last_vote in the 1b messages from the first clause.
         *)
         /\ (exists a, a ∈ `Q /\ exists v_lv_a, has_been_sent _ s (b, m_1b a (Some (b_1c, v_lv_a))))
         /\ (forall a, a ∈ `Q -> forall b_lv v_lv,
              has_been_sent _ s (b, m_1b a (Some (b_lv, v_lv))) ->
                (b_lv <= b_1c)%Z /\ (b_lv = b_1c -> v_lv = v)))).

Lemma gathered_1b_ok :
  forall (b : Ballot) (a : Acceptor) lv,
    gathered_1b ((s leaders_ix : leaders_state) !!! b) !! a = Some lv ->
    has_been_sent paxos_vlsm s (b, m_1b a lv).
Proof.
  induction Hs using valid_state_prop_ind.
  - intros a b lv Hlookup.
    rewrite (Hs0 leaders_ix) in Hlookup.
    rewrite (lookup_total_empty (A := ballot_state) (M := Bmap)) in Hlookup; cbn in Hlookup.
    by rewrite lookup_empty in Hlookup.
  - rename Hs into Hs'.
    assert (Hs : valid_state_prop preloaded_paxos_vlsm s) by apply Ht.
    intros b a lv Hlookup.
    destruct l as [[| a_l] li]; cycle 1.
    + (* On an acceptor state, the gathered_1b field of the leaders state can't change *)
      rewrite has_been_sent_step_update by (apply Ht; done).
      right; apply IHv; [done |].
      cut (s' leaders_ix = s leaders_ix); [by intros <- |].
      apply input_valid_transition_preloaded_project_any with (i := leaders_ix) in Ht.
      by destruct Ht as [<- | [? [[=]]]].
    + (* On a leader update, has_been_sent of acceptor messages can't change *)
      destruct (Ht) as [_ Hstep]; cbn in Hstep.
      destruct (leaders_transition _ _) as [si' om'0] eqn: H_leaders_step in Hstep.
      injection Hstep as [= <- ->].
      rewrite state_update_eq in Hlookup.
      apply localize_sent_messages; [done |].
      simpl; rewrite state_update_neq by discriminate.
      rewrite <- (localize_sent_messages s Hs (b, m_1b a lv)).
      unfold leaders_transition in H_leaders_step.
      destruct li as [b_l l].
      assert (H_unchanged : s leaders_ix = si' -> has_been_sent paxos_vlsm s (b, m_1b a lv))
        by (intros <-; auto).
      destruct (leader_transition _ _) as [[slb' lom] |] eqn: H_leader_step in H_leaders_step;
        [| by apply H_unchanged; congruence].
      injection H_leaders_step as [= <- <-].
      destruct (decide (b = b_l)) as [<- |].
      * clear H_unchanged.
        rewrite (lookup_total_insert (s leaders_ix)) in Hlookup by done.
        apply leader_gathered_1b_step with (1 := H_leader_step)
          in Hlookup as [[-> [b' ->]] |]; [| by auto].
        destruct Ht as [(_ & _ & Hvalid) _].
        destruct Hvalid as [H_leader_valid H_no_equivocation].
        cbn in H_leader_valid; subst b'.
        by destruct H_no_equivocation.
      * rewrite (lookup_total_insert_ne (s leaders_ix)) in Hlookup by done.
        by apply IHv.
Qed.

Lemma check_safe_at_okay :
  forall b v,
    v ∈ calculate_safe_values b ((s leaders_ix : leaders_state) !!! b).(gathered_1b) ->
      exists Q : sig Quorum, ShowsSafeAt s Q b v.
Proof.
  intros b v.
  destruct (calculate_safe_values _ _) as [| safe_vs] eqn: H_safe_vs; simpl; intros Hv.
  - apply calculate_safe_values_any_ok in H_safe_vs as [Q HQ].
    exists Q.
    unfold ShowsSafeAt.
    split; [| left]; (intros a Ha; specialize (HQ a Ha); apply gathered_1b_ok in HQ).
    + by exists None.
    + by intros; eapply sent_1b_once.
  - apply calculate_safe_values_some_ok with (v := v)
      in H_safe_vs as (Q & HQ & H_some_Q_voted); [| done].
    exists Q.
    unfold ShowsSafeAt.
    split.
    + intros a Ha.
      destruct (HQ a Ha) as [(vbal & HQ' & Hbal_lt) | HQ']; apply gathered_1b_ok in HQ'.
      * by exists (Some (vbal, v)).
      * by exists None.
    + right.
      change (v ∈ safe_vs) in Hv.
      set (messages_from_Q :=
        filter (fun '(a, _) => a ∈ `Q) (gathered_1b ((s leaders_ix : leaders_state) !!! b))).
      set (prev_votes := map_to_set (fun _ b => b) (omap (fmap fst) messages_from_Q) : Bset).
      assert (H16 : prev_votes ≢ ∅).
      {
        destruct H_some_Q_voted as (a_hist & lv_hist & Ha_hist & Hlookup & H_lv_not_none).
        destruct lv_hist as [[lv_bal lv_val] |]; [clear H_lv_not_none | done].
        destruct (HQ a_hist Ha_hist) as [(a_hist_bal & Ha_bal & Hbal_lt) |]; [| by congruence].
        apply (non_empty_inhabited a_hist_bal), elem_of_map_to_set.
        exists a_hist, a_hist_bal.
        split; [| done].
        apply lookup_omap_Some.
        exists (Some (a_hist_bal, v)); split; [done |].
        unfold messages_from_Q.
        by apply map_lookup_filter_Some.
      }
      assert (H17 : exists newest_vote : N,
        newest_vote ∈ prev_votes /\ minimal (flip N.le) newest_vote prev_votes).
      {
        by apply minimal_exists; try typeclasses eauto.
      }
      destruct H17 as (newest_lv & H_newest_lv_voted & H_newest_lv_maximal).
      change Ballot in newest_lv.
      exists newest_lv.
      assert (H_prev_votes : forall b_vote : Ballot, b_vote ∈ prev_votes <->
        exists a, a ∈ `Q /\
        gathered_1b ((s leaders_ix : leaders_state) !!! b) !! a = Some (Some (b_vote, v))).
      {
        intros b_vote.
        split.
        - intro H_voted.
          apply elem_of_map_to_set in H_voted as (a_bv & x & H_a_bv & ->).
          exists a_bv.
          apply lookup_omap_Some in H_a_bv as (x & H_x_fst & H_a_bv).
          destruct x as [[xbal xv] |]; [| by contradict H_x_fst].
          injection H_x_fst as [=->].
          apply map_lookup_filter_Some in H_a_bv as [H_abv_lookup H_abv_Q].
          split; [done |].
          by destruct (HQ _ H_abv_Q) as [(vbal' & H_abv_lookup' & _) |]; congruence.
        - intros (a & Ha & Hlookup).
          apply elem_of_map_to_set.
          exists a, b_vote.
          split; [| done].
          apply lookup_omap_Some.
          exists (Some (b_vote, v)).
          split; [done |].
          by apply map_lookup_filter_Some.
      }
      apply H_prev_votes in H_newest_lv_voted as Hsent; destruct Hsent as (a' & _ & Hsent).
      apply pre_loaded_with_all_messages_valid_state_prop in Hs as Hs_pre.
      apply gathered_1b_ok, sent_1b_impl_sent_lastvote_as_2b, sent_2b_after_2a, sent_2a_after_1c
        in Hsent as (vsafe_vs & H_v_safe_vs & H_safe_vs_sent); [| done..].
      exists vsafe_vs; split; [done |]; split; [done |].
      split.
      * rename H_newest_lv_voted into Hnew.
        unfold prev_votes in Hnew.
        apply elem_of_map_to_set in Hnew as (a & ? & Hnew & ->).
        exists a.
        apply lookup_omap_Some in Hnew as (lv_new & Hlv_new & Hnew).
        destruct lv_new as [[b_new v_new] |]; cbn in Hlv_new; [| done].
        injection Hlv_new as [= ->].
        apply map_lookup_filter_Some in Hnew as [Hnew Ha].
        split; [done |].
        exists v_new.
        by apply gathered_1b_ok in Hnew.
      * intros a Ha b_a v_a Hsent.
        assert (H_sent_unique : forall lv,
          gathered_1b ((s leaders_ix : leaders_state) !!! b) !! a = Some lv ->
            lv = (Some (b_a, v_a))).
        {
          intros lv' Hlv.
          apply gathered_1b_ok in Hlv.
          by eapply sent_1b_once.
        }
        assert (b_a ∈ prev_votes).
        {
          apply H_prev_votes.
          exists a; split; [done |].
          by destruct (HQ a Ha) as [(vbal' & Hsent2 & _) | Hsent2];
            rewrite Hsent2; apply H_sent_unique in Hsent2; congruence.
        }
        split.
        -- apply N2Z.inj_le.
           generalize (H_newest_lv_maximal b_a H17); simpl.
           by lia.
        -- by destruct (HQ a Ha) as [(vbal' & Hsent2 & _) | Hsent2];
            apply H_sent_unique in Hsent2; congruence.
Qed.

(** Now we relate these claimed inductive properties, Paxos's ShowsSafeAt, and Voting's SafeAt *)
Lemma PT1 :
  P1bInv_prop -> P1cInv_prop ->
  forall (Q : sig Quorum) (b : Ballot) (v : Value),
    ShowsSafeAt s Q b v -> V_SafeAt b v.
Proof.
  unfold P1bInv_prop, P1cInv_prop, ShowsSafeAt.
  intros Inv1 Inv2 Q bv v [H_Q_voted_bv Hprev_votes].
  assert (H_non_voter :
    forall a : Acceptor, a ∈ `Q ->
      has_been_sent paxos_vlsm s (bv, m_1b a None) ->
      forall (d : Ballot), (d < bv)%Z -> V_DidNotVoteIn a d).
  {
    intros a Ha Hsent d Hd.
    apply Inv1 in Hsent as (_ & _ & Hsent).
    apply (Hsent _ Hd).
    by unfold Ballot_to_Z; cbn; lia.
  }
  assert (Hwlog : NoPrevVotes s (`Q) bv -> SafeAt _ VSet _ ASet Quorum to_voting_state v bv).
  {
    (* There were no votes from Q before bv, so Q preserves safety of v all the way back *)
    intros H_no_prev_votes d Hd.
    exists Q.
    unfold consensus_blocking_quorum.
    split; intros a Ha.
    - unfold vote_committed.
      destruct (H_Q_voted_bv a Ha) as [a_lv H_a_sent_bv].
      destruct (Inv1 _ _ _ H_a_sent_bv) as [H_a_maxbal _].
      by simpl; lia.
    - unfold voted_none_but.
      destruct (H_Q_voted_bv a Ha) as [a_lv H_a_sent_bv].
      assert (a_lv = None) as -> by (apply (H_no_prev_votes a Ha); done).
      intros w Hvote.
      by apply H_non_voter in Hvote.
  }
  destruct Hprev_votes as [| H_had_1c]; [by apply Hwlog |].
  destruct H_had_1c as (b_1c & vsafe & H_v_vsafe & H_sent_1c & _ & H_last_votes_bounded).
  assert (H_safe_at_1c : SafeAt _ VSet _ ASet Quorum to_voting_state v b_1c)
    by (eapply Inv2; done).
  intros d Hd.
  assert (Hwlog2 : (d < b_1c)%Z -> exists Q0,
    consensus_blocking_quorum _ VSet _ ASet Quorum to_voting_state d v Q0).
  {
    by intros Hlt; apply H_safe_at_1c; lia.
  }
  destruct (Z.le_gt_cases b_1c d) as [Hle |]; [| by itauto].
  clear H_safe_at_1c Hwlog Hwlog2.
  exists Q.
  split; intros a Ha; destruct (H_Q_voted_bv a Ha) as [a_lv Hsent].
  - unfold vote_committed.
    apply Inv1 in Hsent as [Hbound _].
    by simpl; lia.
  - destruct a_lv as [[b_lv v_lv] |];
      [| by intros w Hvote; contradict Hvote; eapply H_non_voter].
    destruct (Inv1 _ _ _ Hsent) as (_ & H_blv & H_dnv).
    change (b_lv < bv)%Z in H_blv.
    specialize (H_dnv d Hd).
    change (Z.lt _ _) with (b_lv < d)%Z in H_dnv.
    destruct (H_last_votes_bounded a Ha _ _ Hsent) as [H_blv_b1c H_vlv].
    intros w Hw.
    assert (Htmp : (b_lv < d)%Z \/ (b_lv =@{Z} b_1c /\ d =@{Z} b_1c)) by lia.
    destruct Htmp as [| [H_blv_eq H_d_eq]]; [by apply H_dnv in Hw |].
    apply N2Z.inj in H_blv_eq; specialize (H_vlv H_blv_eq); subst b_lv v_lv.
    apply N2Z.inj in H_d_eq; subst d.
    assert (has_been_sent paxos_vlsm s (b_1c, m_2b a w)) as H_sent_w.
    {
      apply (localize_sent_messages s); [done |].
      cbn; unfold paxos_acceptor_has_been_sent.
      unfold voted_for, to_voting_state in Hw; simpl in Hw.
      by apply votes_from_paxos_acceptor_iff in Hw.
    }
    clear Hw.
    apply sent_1b_impl_sent_lastvote_as_2b in Hsent; [| done].
    by eapply sent_2b_unique.
Qed.

Definition PInv : Prop := Inv_past_vote_info_prop /\ P1bInv_prop /\ P1cInv_prop /\ P2aInv_prop.

(**
  <<ShowsSafeAt s Q b v>> holds if <<Q>> is a set of acceptors which are consistent with
  value <<v>> at ballot <<b>>.

  1. Every acceptor in <<Q>> sent a 1b message for ballot <<b>>.
  2. Either none of those 1b messages record a past vote,
     or a 1c message supporting <<b>>
     was sent at a ballot <<m1c_bal>> which is at least
     as large as the [maxVBal] of any acceptor in <<Q>>,
     and if the [maxVVal] of any acceptor was from the
     same round as <<m1c_bal>> then also their [maxVVal] is <<v>> (from that round).

   We can have <<m1c_bal>> strictly less than <<b>>, if the acceptors in <<Q>>
   all have a last vote at least that early.
*)

End sec_paxos_refinement_map.

Lemma V_VotedFor_iff :
  forall s,
    valid_state_prop preloaded_paxos_vlsm s ->
  forall a b v,
    V_VotedFor s a b v <->
    has_been_sent paxos_vlsm s (b, m_2b a v).
Proof.
  intros s Hs.
  unfold V_VotedFor, voted_for, to_voting_state; simpl.
  split.
  - intros H_vote_msg.
    apply localize_sent_messages; [done |].
    by apply votes_from_paxos_acceptor_iff.
  - intros H_sent.
    apply votes_from_paxos_acceptor_iff; [done |].
    by apply localize_sent_messages in H_sent.
Qed.

Lemma V_DidNotVoteIn_iff :
  forall s,
    valid_state_prop preloaded_paxos_vlsm s ->
  forall a b,
    V_DidNotVoteIn s a b <->
      forall v, ~ has_been_sent paxos_vlsm s (b, m_2b a v).
Proof.
  by split; intros H_vote v; specialize (H_vote v); contradict H_vote; apply V_VotedFor_iff.
Qed.

Lemma past_vote_info_is_invariant:
  forall s,
    valid_state_prop preloaded_paxos_vlsm s ->
      Inv_past_vote_info_prop s.
Proof.
  intros s Hs a.
  split; [| split].
  - apply valid_state_project_preloaded_to_preloaded with (i := acceptor_ix a) in Hs as Hsa.
    by eapply maxVBal_le_paxos_maxBal.
  - (* No voting in the middle *)
    intros b H_VBal H_Bal v Hvote.
    clear H_Bal (* don't *).
    apply valid_state_project_preloaded_to_preloaded with (i := acceptor_ix a) in Hs as Hsa.
    apply V_VotedFor_iff, localize_sent_messages, sent_vote_le_maxVBal in Hvote; [| done..].
    by simpl in Hvote; lia.
  - destruct (lastVote _) as [[b v] |] eqn: Hlv; [| done].
    apply V_VotedFor_iff; [done |].
    by apply last_vote_was_sent_paxos in Hlv.
Qed.

Lemma P1bInv_is_invariant:
  forall s,
    valid_state_prop preloaded_paxos_vlsm s ->
    P1bInv_prop s.
Proof.
  cbv beta delta [P1bInv_prop].
  intros s Hs b a lv mbal_m Hsent.
  split; [| split].
  - apply valid_state_project_preloaded_to_preloaded with (i:=acceptor_ix a) in Hs as Hsa.
    by apply localize_sent_messages, paxos_acceptor_sent_bounds_maxBal in Hsent.
  - subst mbal_m.
    apply localize_sent_messages in Hsent; [| done].
    simpl message_sender in Hsent.
    change (IM _) with (paxos_acceptor_vlsm a) in Hsent.
    pattern (s (acceptor_ix a)).
    revert Hsent; apply (from_send_to_from_sent_argument (paxos_acceptor_vlsm a));
      [done | ..]; cycle 1.
    + by apply valid_state_project_preloaded_to_preloaded with (i:=acceptor_ix a) in Hs.
    + clear s Hs; intros s * Ht.
      apply input_valid_transition_origin in Ht as Hs.
      destruct (Ht) as [_ Htrans].
      apply sending_1b_updates_maxBal in Ht as [Hb _].
      assert (maxVBal s <= paxos_maxBal s)%Z by (apply maxVBal_le_paxos_maxBal; done).
      cbn in Htrans.
      apply examine_paxos_acceptor_output in Htrans as Hl.
      destruct Hl as [-> _].
      simpl in Htrans.
      destruct oim as [[? []] |]; try discriminate; [].
      injection Htrans as [= <- -> <-].
      change (maxVBal s < b)%Z.
      by lia.
  - intros b_mid; revert b_mid. (* rename the bound variable *)
    revert Hsent.
    setoid_rewrite V_DidNotVoteIn_iff; [| done].
    setoid_rewrite localize_sent_messages; [| done..].
    simpl (message_sender _).
    change (IM (acceptor_ix a)) with (paxos_acceptor_vlsm a).
    subst mbal_m.
    assert (Hsa : valid_state_prop (pre_loaded_with_all_messages_vlsm (paxos_acceptor_vlsm a))
      (s (acceptor_ix a))).
    {
      by apply valid_state_project_preloaded_to_preloaded with (i := acceptor_ix a) in Hs.
    }
    induction Hsa using valid_state_prop_ind;
      [by intros _ b_mid _ _ v; apply has_been_sent_no_inits |].
    intros H_sent_s'.
    apply input_valid_transition_origin in Ht as Hs0.
    destruct (proj1 (has_been_sent_step_update Ht _) H_sent_s') as [-> | H_sent_s].
    + clear IHHsa.
      intros b_mid Hmid1 Hmid2 v H_sent_old_s'.
      apply (has_been_sent_step_update Ht) in H_sent_old_s'.
      destruct H_sent_old_s' as [| H_sent_old_s]; [done |].
      apply sent_vote_le_maxVBal in H_sent_old_s; [| done].
      destruct Ht as [(_ & _ & Hvalid) Htrans].
      destruct (examine_paxos_acceptor_output Htrans) as [-> _].
      change transition with (paxos_acceptor_transition a) in Htrans; cbn in Htrans.
      destruct om as [[? []] |]; try discriminate; [].
      injection Htrans as [= <- -> <-].
      change valid with paxos_acceptor_valid in Hvalid; cbn in Hvalid.
      change (maxVBal s0 < b_mid)%Z in Hmid2.
      by lia.
    + intros b_mid Hmid1 Hmid2 v H_sent_old_s'.
      apply (has_been_sent_step_update Ht) in H_sent_old_s' as [-> | H_bad_send_s0];
        [| by eapply IHHsa].
      assert (b <= paxos_maxBal s0)%Z by (apply paxos_acceptor_sent_bounds_maxBal in H_sent_s; done).
      cut (paxos_maxBal s0 <= b_mid)%Z; [by lia |].
      destruct Ht as [(_ & _ & Hvalid) Htrans].
      destruct (examine_paxos_acceptor_output Htrans) as [-> _].
      change transition with (paxos_acceptor_transition a) in Htrans; cbn in Htrans.
      destruct om as [[? []] |]; try discriminate; [].
      change valid with paxos_acceptor_valid in Hvalid; cbn in Hvalid.
      by injection Htrans as [= <- ->].
Qed.

Lemma V_SafeAt_stable :
  forall [l s oim s' oom],
    input_valid_transition preloaded_paxos_vlsm l (s, oim) (s', oom) ->
  forall b v,
    V_SafeAt s b v -> V_SafeAt s' b v.
Proof.
  unfold V_SafeAt, SafeAt, consensus_blocking_quorum.
  intros * Ht b v H_prev d Hd.
  destruct (H_prev d Hd) as (Q & HQ1 & HQ2).
  exists Q.
  split; intros a Ha; specialize (HQ1 a Ha).
  - revert HQ1; cbn.
    unfold vote_committed, to_voting_state; simpl.
    apply input_valid_transition_preloaded_project_any with (i := acceptor_ix a)
      in Ht as [-> | (li & -> & Ht)]; [done |].
    apply paxos_maxBal_mono in Ht.
    by lia.
  - specialize (HQ2 a Ha); revert HQ2; cbn.
    apply input_valid_transition_origin in Ht as Hs0.
    apply input_valid_transition_destination in Ht as Hs'.
    unfold voted_none_but.
    setoid_rewrite V_VotedFor_iff; [| done..].
    clear H_prev; intros H_prev w Hsent_s'.
    apply H_prev; clear H_prev.
    apply (has_been_sent_step_update Ht) in Hsent_s' as [-> |]; [| done].
    exfalso.
    unfold vote_committed in HQ1; simpl in HQ1.
    cut (paxos_maxBal (s (acceptor_ix a)) <= d)%Z; [by lia |].
    destruct l as [li l].
    assert (li = acceptor_ix a) as ->
      by (destruct Ht as [_ Htrans]; apply localize_send in Htrans; done).
    apply input_valid_transition_preloaded_project_active in Ht; simpl in Ht.
    destruct Ht as [(_ & _ & Hvalid) Htrans]; cbn in Htrans, Hvalid.
    apply examine_paxos_acceptor_output in Htrans as Hl; destruct Hl as [-> _].
    simpl in Hvalid.
    destruct oim as [[? []] |]; try done; [].
    by inversion Htrans; subst.
Qed.

Lemma P2aInv_is_invariant :
  forall (s : state preloaded_paxos_vlsm),
    valid_state_prop preloaded_paxos_vlsm s ->
    P2aInv_prop s.
Proof.
  unfold P2aInv_prop.
  intros s Hs b v Hsent.
  pattern s; revert s Hs Hsent; apply from_send_to_from_sent_argument.
  - (* the propery is just an existential around has_been_sent, so stability is easy *)
    intros * Ht (vs & Hv & Hsent).
    exists vs.
    split; [done |].
    apply (has_been_sent_step_update Ht).
    by right.
  - intros * Ht.
    apply input_valid_transition_origin in Ht as Hs.
    destruct l as [ix l].
    destruct (Ht) as [_ Htrans].
    apply localize_send in Htrans; simpl in Htrans; subst ix.
    apply input_valid_transition_preloaded_project_active in Ht as Ht_l; simpl in Ht_l.
    destruct Ht_l as [(_ & _ & Hvalid) Htrans].
    change valid with leaders_valid in Hvalid.
    change transition with leaders_transition in Htrans.
    apply examine_leaders_output in Htrans as Hl; subst l.
    simpl in Hvalid.
    destruct oim; [done |].
    destruct Hvalid as (_ & vs & Hv & Hvs).
    exists vs.
    split; [done |].
    rewrite (has_been_sent_step_update Ht); right.
    by apply localize_sent_messages.
Qed.

Lemma ShowsSafeAt_stable :
  forall [l s oim s' oom],
    input_valid_transition preloaded_paxos_vlsm l (s, oim) (s', oom) ->
  forall (Q : sig Quorum) b v,
    ShowsSafeAt s Q b v -> ShowsSafeAt s' Q b v.
Proof.
  intros * Ht Q b v [H_participated_b H_safe_v].
  apply input_valid_transition_destination in Ht as Hs'.
  split.
  - intros a Ha.
    destruct (H_participated_b a Ha) as [lv Hlv].
    exists lv.
    by apply (has_been_sent_step_update Ht); right.
  - destruct H_safe_v as [H_no_votes | H_safe_votes].
    + left.
      intros a Ha.
      destruct (H_participated_b a Ha) as [lv Hlv].
      specialize (H_no_votes a Ha lv Hlv); subst lv.
      assert (H_sent_None : has_been_sent paxos_vlsm s' (b, m_1b a None))
        by (apply (has_been_sent_step_update Ht); right; done).
      intros lv Hlv'; revert Hlv' H_sent_None.
      by apply sent_1b_once.
    + right.
      destruct H_safe_votes as (b_1c & vsafe & Hvs & Hsent_1c & H1c_from_votes & Hvoted_by_1c).
      exists b_1c, vsafe.
      split; [done |].
      split; [by apply (has_been_sent_step_update Ht); right |].
      split.
      * destruct H1c_from_votes as (a & Ha & v_lv_a & H_a_voted_at_1c).
        exists a; split; [done |].
        exists v_lv_a.
        by apply (has_been_sent_step_update Ht); right.
      * intros a Ha b_lv v_lv H_sent_s'.
        apply (Hvoted_by_1c a Ha b_lv v_lv).
        destruct (H_participated_b a Ha) as [lv H_sent_1b].
        cut (lv = Some (b_lv, v_lv)); [by intros -> |].
        revert H_sent_s'; apply sent_1b_once; [done |].
        by apply (has_been_sent_step_update Ht); right.
Qed.

Lemma sent_1c_implies_ShowsSafeAt :
  forall (s : state preloaded_paxos_vlsm),
    valid_state_prop preloaded_paxos_vlsm s ->
  forall b vs,
    has_been_sent paxos_vlsm s (b, m_1c vs) ->
  forall v, v ∈ vs -> exists (Q : sig Quorum), ShowsSafeAt s Q b v.
Proof.
  intros s Hs b vs Hsent v Hv; revert s Hs Hsent.
  apply from_send_to_from_sent_argument;
    [by intros * ? [Q ?]; exists Q; eapply ShowsSafeAt_stable |].
  intros * Ht.
  assert (Hs : valid_state_prop preloaded_paxos_vlsm s) by apply Ht.
  cut (exists Q, ShowsSafeAt s Q b v);
    [by intros [Q ?]; exists Q; eapply ShowsSafeAt_stable |].
  apply (check_safe_at_okay s Hs).
  destruct (Ht) as [_ Hix].
  destruct l as [ix l]; apply localize_send in Hix; simpl in Hix; subst ix.
  apply input_valid_transition_preloaded_project_active in Ht; simpl in Ht.
  destruct (Ht) as [(_ & _ & Hvalid) Hlabel].
  apply examine_leaders_output in Hlabel; subst l.
  change valid with leaders_valid in Hvalid; cbn in Hvalid.
  destruct oim; [done |].
  by rewrite Hvalid in Hv.
Qed.

Lemma ShowsSafeAt_impl_V_SafeAt :
   forall (s : state preloaded_paxos_vlsm),
    valid_state_prop preloaded_paxos_vlsm s ->
  forall b v,
    (exists (Q : sig Quorum), ShowsSafeAt s Q b v) ->
      V_SafeAt s b v.
Proof.
  intros s Hs b v.
  assert (Inv1 : P1bInv_prop s) by (apply P1bInv_is_invariant; done).
  assert (Inv2 : P2aInv_prop s) by (apply P2aInv_is_invariant; done).
  unfold P1bInv_prop in Inv1.
  unfold P2aInv_prop in Inv2.
  (*
    We might need to unfold the ShowsSafeAt and drop the part about voting at b to
    get the correct induction goal.
  *)
  induction (N.lt_wf_0 b) as [b _ IHb].
  setoid_rewrite N2Z.inj_lt in IHb.
  change Z.of_N with Ballot_to_Z in *.
  change N with Ballot in *.
  intros [Q [H_Q_participating [H_Q_never_voted | H_Q_protects_to_past_1c]]].
  - intros b' Hb'.
    exists Q.
    unfold consensus_blocking_quorum.
    split; intros a Ha;
      apply valid_state_project_preloaded_to_preloaded with (i := acceptor_ix a) in Hs as Hsa;
      destruct (H_Q_participating a Ha) as [lv Hsent_1b].
    + unfold vote_committed; simpl.
      cut (b <= paxos_maxBal (s (acceptor_ix a)))%Z; [by lia |].
      by apply localize_sent_messages, paxos_acceptor_sent_bounds_maxBal in Hsent_1b.
    + intros w Hvoted.
      apply V_VotedFor_iff in Hvoted; [| done].
      contradict Hvoted.
      specialize (H_Q_never_voted a Ha _ Hsent_1b); subst lv.
      apply Inv1 in Hsent_1b as (_ & _ & H_dnv); cbn in H_dnv.
      setoid_rewrite V_DidNotVoteIn_iff in H_dnv; [| done].
      apply (H_dnv _ Hb').
      by unfold Ballot_to_Z; lia.
  - (*
      Here Q is only known to protect as far back as
      some ballot b_1c, where a previous 1c message for v
      had been sent.
    *)
    destruct H_Q_protects_to_past_1c as
      (b_1c & vs & Hv & H_sent_1c & H1c_from_votes & H_Q_voted_before_1c).
    assert (b_1c < b)%Z.
    {
      destruct H1c_from_votes as (a & Ha & v_lv_a & H_a_voted_at_1c).
      by destruct (Inv1 _ _ _ H_a_voted_at_1c) as (_ & Hb_1c_lt_b & _).
    }
    assert (H_safe_at_1c' : V_SafeAt s b_1c v)
      by (intro; eapply IHb, sent_1c_implies_ShowsSafeAt; done).
    intros d Hd.
    destruct (Z.lt_ge_cases d b_1c) as [H_d_lt_1c | H_d_ge_1c];
      [by apply (H_safe_at_1c' d H_d_lt_1c) |].
    exists Q.
    (*
      No acceptor in Q voted between b_1c and b,
      any vote from Q at b_1c was for v, so
      Q is consensus_blocking strictly between by having no votes,
      and at b_1c less trivially.
    *)
    unfold consensus_blocking_quorum.
    split; intros a Ha;
      destruct (H_Q_participating a Ha) as [lv Hsent_1b].
    + unfold vote_committed; simpl.
      cut (b <= paxos_maxBal (s (acceptor_ix a)))%Z; [by lia |].
      apply localize_sent_messages in Hsent_1b; [| done].
      apply valid_state_project_preloaded_to_preloaded with (i:=acceptor_ix a) in Hs as Hsa.
      by apply paxos_acceptor_sent_bounds_maxBal in Hsent_1b.
    + intros w Hvote_w.
      destruct (Inv1 _ _ _ Hsent_1b) as (H_b_s & H_b_lv & Hdnv).
      specialize (H_Q_voted_before_1c a Ha).
      specialize (Hdnv _ Hd).
      destruct lv as [[b_lv v_lv] |];
        [| by contradict Hvote_w; apply Hdnv; simpl; unfold Ballot_to_Z; lia].
      destruct (H_Q_voted_before_1c _ _ Hsent_1b) as [H_lv_le H_lv_eq_only_v].
      change (b_lv < b)%Z in H_b_lv.
      change (Z.lt _ _) with (b_lv < d)%Z in Hdnv.
      assert (Htmp : (b_lv < d \/ b_lv =@{Z} d)%Z) by lia.
      destruct Htmp as [H_lv_lt | H_lv_eq];
        [by apply Hdnv in Hvote_w |].
      apply N2Z.inj in H_lv_eq; subst b_lv.
      clear Hdnv.
      assert (H_d_eq : d =@{Z} b_1c) by lia.
      apply N2Z.inj in H_d_eq; subst d.
      specialize (H_lv_eq_only_v (eq_refl _)); subst v_lv.
      apply V_VotedFor_iff in Hvote_w; [| done].
      apply sent_1b_impl_sent_lastvote_as_2b in Hsent_1b; [| done].
      by eapply sent_2b_unique.
Qed.

Lemma P1cInv_is_invariant :
  forall s,
    valid_state_prop preloaded_paxos_vlsm s ->
    P1cInv_prop s.
Proof.
  unfold P1cInv_prop.
  intros s Hs b vs Hsent v Hv.
  pattern s.
  revert Hsent; apply from_send_to_from_sent_argument; [.. | done].
  - (* V_SafeAt is persistant *)
    by intros * Ht; apply (V_SafeAt_stable Ht).
  - (* V_SafeAt holds when the 1c is sent *)
    clear s Hs.
    intros * Ht.
    apply input_valid_transition_origin in Ht as Hs.
    destruct (Ht) as [_ Hsender].
    apply localize_send in Hsender.
    destruct l as [li l]; simpl in Hsender; subst li.
    apply input_valid_transition_preloaded_project_active in Ht as Ht_l; simpl in Ht_l.
    destruct Ht_l as [(_ & _ & Hvalid) Htrans].
    apply examine_leaders_output in Htrans as ->.
    cbn in Hvalid; destruct oim; [done |].
    subst vs.
    apply check_safe_at_okay in Hv; [| done].
    apply (V_SafeAt_stable Ht); clear Ht.
    by eapply ShowsSafeAt_impl_V_SafeAt.
Qed.

Lemma paxos_invariants (s : state paxos_vlsm) :
  valid_state_prop preloaded_paxos_vlsm s -> PInv s.
Proof.
  intros Hs.
  unfold PInv.
  repeat split_and.
  - by apply past_vote_info_is_invariant.
  - by apply P1bInv_is_invariant.
  - by apply P1cInv_is_invariant.
  - by apply P2aInv_is_invariant.
Qed.

End sec_paxos_spec.
