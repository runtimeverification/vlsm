From VLSM.Lib Require Import Itauto.
From stdpp Require Import prelude finite.
From VLSM.Core Require Import VLSM VLSMProjections Composition.
From VLSM.Lib Require Import Preamble EquationsExtras ListExtras.
From VLSM.Core Require Import ConstrainedVLSM.

(** * Tutorial: Round-Based Asynchronous Muddy Children Puzzle

  This module formalizes the Muddy Children (MC) puzzle
  as a constrained composition of VLSMs that communicate
  asynchronously in rounds. The module provides an advanced
  self-contained example of modeling and reasoning with VLSMs.

  Consider a
  #<a href="https://plato.stanford.edu/entries/dynamic-epistemic/appendix-B-solutions.html">
  standard statement of the MC puzzle</a>#:

  "Three children are playing in the mud. Father calls the children to the house,
  arranging them in a semicircle so that each child can clearly see every other
  child. _At least one of you has mud on your forehead_, says Father.
  The children look around, each examining every other child's forehead.
  Of course, no child can examine his or her own. Father continues,
  _If you know whether your forehead is dirty, then step forward now_.
  No child steps forward. Father repeats himself a second time,
  _If you know whether your forehead is dirty, then step forward now_.
  Some but not all of the children step forward. Father repeats himself a third
  time, _If you know whether your forehead is dirty, then step forward now_.
  All of the remaining children step forward. How many children have muddy foreheads?"

  We alter the puzzle in two ways:
  - we allow an arbitrary but fixed number of children, and
  - we allow the children to communicate asynchronously.

  To allow asynchronous communication, we let each child maintain the "round"
  they perceive themselves to be in and to communicate their round number to their peers.

  We define some VLSM-specific notions in the
  context of the MC puzzle (such as labels, states, initial states,
  messages, transitions, valid transitions, and composition constraints),
  but there are also some MC-specific notions (final state,
  consistent state, observation equivalence, and invariant).

  The consistency property of states guarantees that a state adheres
  to the assumptions in the puzzle's statement:
  - there is at least one muddy child, and
  - any child sees all the muddy children except themselves.

  Final states are those states in which each child has decided on a status,
  i.e., as muddy or clean.

  The main result in the module is the theorem [MC_safety], which establishes
  that final states are reachable from any non-initial valid state.
  The proof is based on the lemmas [MC_composite_invariant_preservation],
  [MC_progress] and [MC_round_bound].
*)

(** ** Basic definitions *)

Inductive Label : Type :=
| init
| emit
| receive.

Inductive ChildStatus : Type :=
| undecided
| muddy
| clean.

Record RoundStatus : Type := mkRS
{
  rs_round : nat;
  rs_status : ChildStatus;
}.

Section sec_muddy.

Context
  (index : Type)
  `{finite.Finite index}
  `{Inhabited index}
  `{FinSet index indexSet}
  .

(**
  Children maintain the set of (indices of) other children they perceive
  as being muddy and (except for their initial state) the current round they
  perceive themselves to be at and their [ChildStatus].
*)
Record State : Type := mkSt
{
  st_obs : indexSet;
  st_rs : option RoundStatus;
}.

(**
  A message carries the identity of its sender, and shares the round number
  and their [ChildStatus].
*)
Record Message : Type := mkMsg
{
  msg_index : index;
  msg_round : nat;
  msg_status : ChildStatus;
}.

Definition MCType : VLSMType Message :=
{|
  state := State;
  label := Label;
|}.

Definition MC_initial_state_prop (s : State) : Prop :=
  st_rs s = None.

Equations MC_transition (i : index) (l : Label)
 (s : State) (om : option Message) : State * option Message :=
MC_transition i init (mkSt o None) None with size o :=
 { | 0 => (mkSt o (Some (mkRS 0 muddy)), None)
   | S _ => (mkSt o (Some (mkRS 0 undecided)), None)
 };
MC_transition i emit (mkSt o (Some (mkRS r status))) None :=
 ((mkSt o (Some (mkRS r status))), Some (mkMsg i r status));
MC_transition i receive (mkSt o (Some (mkRS r undecided))) (Some (mkMsg j r' clean))
 with decide (j ∈ o) :=
 { | right Hin =>
     if decide (r' = size o) then
       (mkSt o (Some (mkRS r' clean)), None)
     else if decide (r' = size o + 1) then
       (mkSt o (Some (mkRS (r' - 1) muddy)), None)
     else (mkSt o (Some (mkRS r undecided)), None)
   | left Hin => (mkSt o (Some (mkRS r undecided)), None)
 };
MC_transition i receive (mkSt o (Some (mkRS r undecided))) (Some (mkMsg j r' muddy))
 with decide (j ∈ o) :=
  { | left Hin =>
      if decide (r' = size o) then
       (mkSt o (Some (mkRS r' muddy)), None)
      else if decide (r' = size o - 1) then
       (mkSt o (Some (mkRS (r' + 1) clean)), None)
      else (mkSt o (Some (mkRS r undecided)), None)
   | right Hin => (mkSt o (Some (mkRS r undecided)), None)
  };
(**
  One of the most interesting cases of the transition function is the one when
  a child [i] who doesn't know their status receives a message from a child [j]
  who also doesn't know their own status. However, being at round [r'], [j] knows
  there are more than [r'] muddy children.
*)
MC_transition i receive (mkSt o (Some (mkRS r undecided))) (Some (mkMsg j r' undecided))
  (**
    If child [i] sees [j] as muddy, they can infer that there are actually more than
    [r' + 1] muddy children.
  *)
  with decide (j ∈ o) :=
  { | left Hin =>
      (**
        If [r' + 1] is less than or equal to the current round number of [i], then
        the round doesn't change and the status remains undecided.
      *)
      if decide (r' < r) then
        (mkSt o (Some (mkRS r undecided)), None)
      (**
        Else, we update the round number to [r' + 1], and have to compare it to
        the number of muddy children seen by child [i].
        If its less than that, the information gained is not useful enough to
        infer anything, so the status remains undecided.
      *)
      else if decide (r <= r' < size o - 1) then
        (mkSt o (Some (mkRS (r' + 1) undecided)), None)
      (**
        Else, if the updated round ever becomes equal to the number of muddy children
        seen by [i], they can conclude they are muddy.
      *)
      else if decide (r' = size o - 1) then
        (mkSt o (Some (mkRS (r' + 1) muddy)), None)
      else (mkSt o (Some (mkRS r undecided)), None)
    | right Hin =>
      if decide (r' <= r) then
        (mkSt o (Some (mkRS r undecided)), None)
      else if decide (r < r' < size o) then
        (mkSt o (Some (mkRS r' undecided)), None)
      else if decide (r' = size o) then
        (mkSt o (Some (mkRS r' muddy)), None)
      else (mkSt o (Some (mkRS r undecided)), None)
  };
MC_transition _ _ s _ := (s, None).

Definition state_status (s : option RoundStatus) : ChildStatus :=
  from_option rs_status undecided s.

Definition state_round (s : option RoundStatus) : nat :=
  from_option rs_round 0 s.

Definition state_round_inc (s : State) : nat :=
  match st_rs s with
  | Some rs => S (rs_round rs)
  | _ => 0
  end.

Definition message_status (om : option Message) : ChildStatus :=
  from_option msg_status undecided om.

Definition message_round (om : option Message) : nat :=
  from_option msg_round 0 om.

Definition message_index (om : option Message) (i : index) : index :=
  from_option msg_index i om.

Inductive MC_valid : Label -> State -> option Message -> Prop :=
| MC_valid_init : forall o : indexSet,
    MC_valid init (mkSt o None) None
| MC_valid_emit : forall (o : indexSet) (rs : RoundStatus),
    MC_valid emit (mkSt o (Some rs)) None
| MC_valid_receive : forall (o : indexSet) (rs : RoundStatus) (m : Message),
    MC_valid receive (mkSt o (Some rs)) (Some m).

#[export] Instance ChildStatus_eq_dec : EqDecision ChildStatus.
Proof. by intros x y; unfold Decision; decide equality. Qed.

Definition MC_initial_state_type : Type :=
  {st : State | MC_initial_state_prop st}.

Program Definition MC_initial_state : MC_initial_state_type :=
  exist _ (mkSt ∅ None) _.
Next Obligation.
Proof. done. Qed.

#[export] Instance Decision_MC_initial_state_prop :
  forall s, Decision (MC_initial_state_prop s).
Proof. by typeclasses eauto. Qed.

#[export] Instance Inhabited_MC_initial_state_type : Inhabited (MC_initial_state_type) :=
  populate (MC_initial_state).

Definition MCMachine (i : index) : VLSMMachine MCType :=
{|
  initial_state_prop := MC_initial_state_prop;
  initial_message_prop := const False;
  transition := fun l '(st, om) => MC_transition i l st om;
  valid := fun l '(st, om) => MC_valid l st om;
|}.

Definition MCVLSM (i : index) : VLSM Message :=
{|
  vtype := MCType;
  vmachine := MCMachine i;
|}.

#[export] Instance MC_composite_initial_state_dec :
  forall s, Decision (composite_initial_state_prop MCVLSM s).
Proof.
  intros s; eapply @Decision_iff with
    (P := Forall (fun n : index => initial_state_prop (MCVLSM n) (s n)) (enum index)).
  - rewrite Forall_forall; apply forall_proper.
    split; [| done].
    by intros Hx; apply Hx, elem_of_enum.
  - by typeclasses eauto.
Qed.

Definition MuddyUnion (s : composite_state MCVLSM) : indexSet :=
  ⋃ (map (fun i => st_obs (s i)) (enum index)).

Lemma MuddyUnion_elem (s : composite_state MCVLSM) (i j : index) :
  i ∈ st_obs (s j) -> i ∈ MuddyUnion s.
Proof.
  intros Hobs.
  apply elem_of_union_list.
  exists (st_obs (s j)); split; [| done].
  apply elem_of_list_fmap.
  exists j; split; [done |].
  by apply elem_of_enum.
Qed.

Definition consistent (s : composite_state MCVLSM) : Prop :=
  MuddyUnion s ≢  ∅ /\ forall n : index, st_obs (s n) ≡ MuddyUnion s ∖ {[n]}.

Definition MC_no_equivocation (s : composite_state MCVLSM) (m : Message) : Prop :=
  match m with
  | mkMsg n r' status' =>
    match s n with
    | mkSt _ (Some (mkRS r status)) =>
      (status' = status /\ r' = r) \/ (status' = undecided /\ r' < r)
    | _ => False
    end
  end.

Inductive MC_no_equivocation_inductive : composite_state MCVLSM -> Message -> Prop :=
| MC_no_equivocation_inductive_msg_eq : forall s n o r status,
    s n = mkSt o (Some (mkRS r status)) ->
    MC_no_equivocation_inductive s (mkMsg n r status)
| MC_no_equivocation_inductive_undecided : forall s n o r r' status,
    s n = mkSt o (Some (mkRS r status)) ->
    r' < r ->
    MC_no_equivocation_inductive s (mkMsg n r' undecided).

Lemma MC_no_equivocation_inductive_equiv :
  forall s m, MC_no_equivocation s m <-> MC_no_equivocation_inductive s m.
Proof.
  split; destruct m; cbn.
  - repeat case_match; [| done].
    intros [[] | []]; subst.
    + by eapply MC_no_equivocation_inductive_msg_eq; eauto.
    + by eapply MC_no_equivocation_inductive_undecided; eauto.
  - by repeat case_match; inversion 1; itauto congruence.
Qed.

Definition MC_constraint
  (l : composite_label MCVLSM) (sm : composite_state MCVLSM * option Message) : Prop :=
  match l, sm with
  | existT _ init, (s, _) => consistent s
  | existT _ receive, (s, Some m) => MC_no_equivocation s m
  | _, _ => True
  end.

Definition MC_composite_vlsm : VLSM Message :=
  composite_vlsm MCVLSM MC_constraint.

Definition MC_final_state (s : composite_state MCVLSM) : Prop :=
  forall n : index, state_status (st_rs (s n)) <> undecided.

Definition MC_initial_consistent_state (s : composite_state MCVLSM) : Prop :=
  composite_initial_state_prop MCVLSM s /\ consistent s.

Definition MC_non_initial_valid_state (s : composite_state MCVLSM) : Prop :=
  valid_state_prop MC_composite_vlsm s /\ ~ (composite_initial_state_prop MCVLSM s).

Definition MC_obs_equivalence (s1 s2 : composite_state MCVLSM) : Prop :=
  forall n : index, st_obs (s1 n) ≡ st_obs (s2 n).

#[export] Instance MC_obs_equiv_refl : Reflexive MC_obs_equivalence.
Proof. done. Qed.

#[export] Instance MC_obs_equiv_symm : Symmetric MC_obs_equivalence.
Proof. by unfold MC_obs_equivalence; intros x y Hxy. Qed.

#[export] Instance MC_obs_equiv_trans : Transitive MC_obs_equivalence.
Proof.
  by unfold MC_obs_equivalence; intros s1 s2 s3 H12 H23;
    etransitivity; [apply H12 | apply H23].
Qed.

#[export] Instance MC_obs_equiv_equiv : Equivalence MC_obs_equivalence.
Proof. by split; typeclasses eauto. Qed.

Lemma MC_state_update_preserves_obs_equiv
  (s : composite_state MCVLSM) (i : index) (si : State) :
  st_obs (s i) ≡ st_obs si -> MC_obs_equivalence s (state_update MCVLSM s i si).
Proof.
  by intros Hobs n; destruct (decide (n = i)); subst; state_update_simpl.
Qed.

Lemma MC_obs_equiv_preserves_muddy (s1 s2 : composite_state MCVLSM) :
  MC_obs_equivalence s1 s2 -> MuddyUnion s1 ≡ MuddyUnion s2.
Proof.
  intros Hobs; unfold MuddyUnion.
  intros i; rewrite !elem_of_union_list.
  split; intros (X & HX & Hi); apply elem_of_list_fmap in HX as (y & -> & Hy).
  - exists (st_obs (s2 y)); split.
    + by apply elem_of_list_fmap; exists y.
    + by apply Hobs.
  - exists (st_obs (s1 y)); split.
    + by apply elem_of_list_fmap; exists y.
    + by apply Hobs.
Qed.

Lemma MC_obs_equiv_preserves_consistency (s1 s2 : composite_state MCVLSM) :
  MC_obs_equivalence s1 s2 -> consistent s1 -> consistent s2.
Proof.
  intros Hobs [Hnempty Hcons]; split.
  - unfold MuddyUnion in Hnempty |- *.
    rewrite empty_union_list, Forall_forall in Hnempty |- *.
    contradict Hnempty.
    intros x Hx.
    apply elem_of_list_fmap in Hx as (j & -> & _).
    unfold MC_obs_equivalence in Hobs; rewrite Hobs.
    apply Hnempty, elem_of_list_fmap.
    exists j; split; [done |].
    by apply elem_of_enum.
  - intros j x.
    rewrite <- MC_obs_equiv_preserves_muddy by done.
    unfold MC_obs_equivalence in Hobs; rewrite <- Hobs.
    by apply Hcons.
Qed.

Lemma MC_trans_preserves_obs_equiv (s : composite_state MCVLSM) :
  forall (l : composite_label MCVLSM) (s' : composite_state MCVLSM) (m m' : option Message),
    composite_transition (MCVLSM) l (s, m) = (s', m') -> MC_obs_equivalence s s'.
Proof.
  intros; unfold composite_transition in H9.
  destruct l as [i li], (transition li (s i, m)) eqn: Ht;
    cbn in Ht; inversion H9; subst; clear H9.
  apply MC_state_update_preserves_obs_equiv.
  destruct s0, (s i).
  revert Ht.
  by apply FunctionalElimination_MC_transition; intros; inversion Ht;
    subst; try done; repeat case_decide; inversion H10.
Qed.

Lemma MC_in_futures_preserves_obs_equiv
  (s s' : composite_state MCVLSM)
  (Hfutures : in_futures MC_composite_vlsm s s') :
  MC_obs_equivalence s s'.
Proof.
  apply (in_futures_preserving MC_composite_vlsm); [.. | done].
  - by split; typeclasses eauto.
  - intros s1 s2 l om1 om2 [].
    by apply MC_trans_preserves_obs_equiv with l om1 om2.
Qed.

Lemma MC_in_futures_preserves_muddy
  (s s' : composite_state MCVLSM) (Hfutures : in_futures MC_composite_vlsm s s') :
    MuddyUnion s ≡ MuddyUnion s'.
Proof.
  by intros; apply MC_obs_equiv_preserves_muddy, MC_in_futures_preserves_obs_equiv.
Qed.

Lemma MC_in_futures_preserves_consistency
  (s s' : composite_state MCVLSM) (Hfutures : in_futures MC_composite_vlsm s s') :
    consistent s <-> consistent s'.
Proof.
  unfold consistent.
  apply MC_in_futures_preserves_obs_equiv in Hfutures as Hfutures'.
  unfold MC_obs_equivalence in Hfutures'.
  setoid_rewrite Hfutures'.
  apply MC_in_futures_preserves_muddy in Hfutures.
  by setoid_rewrite Hfutures.
Qed.

Lemma MC_non_initial_valid_consistent :
  forall (s : composite_state MCVLSM), MC_non_initial_valid_state s -> consistent s.
Proof.
  intros s [Hvalid Hnon_initial].
  induction Hvalid using valid_state_prop_ind; [done |].
  destruct Ht as [(_ & _ & Hv & Hc) Ht].
  destruct (decide (composite_initial_state_prop MCVLSM s)).
  - destruct l as [i []]; cbn in Hv.
    + eapply MC_obs_equiv_preserves_consistency; [| done].
      by eapply MC_trans_preserves_obs_equiv
        with (s := s) (l := existT i init) (m := om) (m' := om').
    + by inversion Hv; specialize (c i); rewrite <- H9 in c.
    + by inversion Hv; specialize (c i); rewrite <- H9 in c.
  - eapply MC_obs_equiv_preserves_consistency; [| by apply IHHvalid].
    by apply MC_trans_preserves_obs_equiv
      with (s := s) (l := l) (m := om) (m' := om').
Qed.

Lemma MC_muddy_number_of_muddy_seen (s : composite_state MCVLSM) (j : index) :
  consistent s ->
  j ∈ MuddyUnion s ->
  size (st_obs (s j)) = size (MuddyUnion s) - 1.
Proof.
  intros [Hnempty Hn] n.
  rewrite Hn, size_difference.
  - by rewrite size_singleton.
  - by rewrite singleton_subseteq_l.
Qed.

Lemma MC_muddy_number_of_muddy_seen_iff (s : composite_state MCVLSM) (j : index) :
  consistent s ->
  j ∈ MuddyUnion s <-> size (st_obs (s j)) = size (MuddyUnion s) - 1.
Proof.
  intros [Hnempty Hn].
  split; [by apply MC_muddy_number_of_muddy_seen |].
  intros Hsize.
  rewrite Hn, size_difference_alt in Hsize.
  destruct (decide (size (MuddyUnion s) = 0));
    [by apply size_non_empty_iff in Hnempty |].
  cut (size (MuddyUnion s ∩ {[j]}) ≠ 0).
  {
    intros Hsizennull.
    apply size_non_empty_iff in Hsizennull.
    by set_solver.
  }
  by lia.
Qed.

Lemma MC_clean_number_of_muddy_seen (s : composite_state MCVLSM) (j : index) :
  consistent s ->
  j ∉ MuddyUnion s ->
  size (st_obs (s j)) = size (MuddyUnion s).
Proof.
  intros [Hnempty Hn] n.
  rewrite Hn, size_difference_alt.
  replace (size (MuddyUnion s ∩ {[j]})) with 0; [by lia |].
  by symmetry; apply size_empty_iff; set_solver.
Qed.

Lemma MC_clean_number_of_muddy_seen_iff (s : composite_state MCVLSM) (j : index) :
  consistent s ->
  j ∉ MuddyUnion s <-> size (st_obs (s j)) = size (MuddyUnion s).
Proof.
  intros [Hnempty Hn].
  split; [by apply MC_clean_number_of_muddy_seen |].
  intros Hsize.
  rewrite Hn, size_difference_alt in Hsize.
  destruct (decide (size (MuddyUnion s) = 0));
    [by apply size_non_empty_iff in Hnempty |].
  cut (size (MuddyUnion s ∩ {[j]}) = 0).
  {
    intros Hsize0.
    apply size_empty_iff in Hsize0.
    by set_solver.
  }
  by lia.
Qed.

Lemma MC_number_of_muddy_seen (s : composite_state MCVLSM) :
  consistent s ->
  forall n, size (st_obs (s n)) <= size (MuddyUnion s) <= size (st_obs (s n)) + 1.
Proof.
  intros Hcons n.
  destruct (decide (n ∈ MuddyUnion s)) as [Hdec | Hdec].
  - by apply MC_muddy_number_of_muddy_seen in Hdec as ->; [lia |].
  - by apply MC_clean_number_of_muddy_seen in Hdec as ->; [lia |].
Qed.

Lemma MC_transition_undecided_receive_clean_round_obs :
  forall (i : index) (s : State) (m : Message),
    state_status (st_rs s) = undecided ->
    msg_status m = clean ->
    msg_index m ∉ st_obs s ->
    msg_round m = size (st_obs s) ->
    MC_transition i receive
      (mkSt (st_obs s) (Some (mkRS (state_round (st_rs s)) (state_status (st_rs s)))))
      (Some (mkMsg (msg_index m) (msg_round m) (msg_status m)))
      =
    (mkSt (st_obs s) (Some (mkRS (msg_round m) clean)), None).
Proof.
  by intros; rewrite H9, H10, MC_transition_equation_9;
    unfold MC_transition_clause_3; repeat case_decide.
Qed.

Lemma MC_transition_undecided_receive_clean_round_obs_plus_one :
  forall (i : index) (s : State) (m : Message),
    state_status (st_rs s) = undecided ->
    msg_status m = clean ->
    msg_index m ∉ st_obs s ->
    msg_round m = size (st_obs s) + 1 ->
    MC_transition i receive
      (mkSt (st_obs s) (Some (mkRS (state_round (st_rs s)) (state_status (st_rs s)))))
      (Some (mkMsg (msg_index m) (msg_round m) (msg_status m)))
      =
    (mkSt (st_obs s) (Some (mkRS (msg_round m - 1) muddy)), None).
Proof.
  by intros; rewrite H9, H10, MC_transition_equation_9;
    unfold MC_transition_clause_3; repeat case_decide; try done; lia.
Qed.

Lemma MC_transition_undecided_receive_muddy_round_obs :
  forall (i : index) (s : State) (m : Message),
    state_status (st_rs s) = undecided ->
    msg_status m = muddy ->
    msg_index m ∈ st_obs s ->
    msg_round m = size (st_obs s) ->
    MC_transition i receive
      (mkSt (st_obs s) (Some (mkRS (state_round (st_rs s)) (state_status (st_rs s)))))
      (Some (mkMsg (msg_index m) (msg_round m) (msg_status m)))
      =
    (mkSt (st_obs s) (Some (mkRS (msg_round m) muddy)), None).
Proof.
  by intros; rewrite H9, H10, MC_transition_equation_8;
    unfold MC_transition_clause_4; repeat case_decide.
Qed.

Lemma MC_transition_undecided_receive_muddy_round_obs_minus_one :
  forall (i : index) (s : State) (m : Message),
    state_status (st_rs s) = undecided ->
    msg_status m = muddy ->
    msg_index m ∈ st_obs s ->
    msg_round m = size (st_obs s) - 1 ->
    MC_transition i receive
      (mkSt (st_obs s) (Some (mkRS (state_round (st_rs s)) (state_status (st_rs s)))))
      (Some (mkMsg (msg_index m) (msg_round m) (msg_status m)))
      =
    (mkSt (st_obs s) (Some (mkRS (msg_round m + 1) clean)), None).
Proof.
  intros; rewrite H9, H10, MC_transition_equation_8;
    unfold MC_transition_clause_4; repeat case_decide; [| done..].
  destruct (decide (size (st_obs s) = 0)); [| by lia].
  by apply non_empty_inhabited, size_non_empty_iff in H11.
Qed.

Lemma MC_transition_undecided_receive_undecided_round_obs_minus_one :
  forall (i : index) (s : State) (m : Message),
    state_status (st_rs s) = undecided ->
    msg_status m = undecided ->
    msg_index m ∈ st_obs s ->
    msg_round m = size (st_obs s) - 1 ->
    state_round (st_rs s) < size (st_obs s) ->
    MC_transition i receive
      (mkSt (st_obs s) (Some (mkRS (state_round (st_rs s)) (state_status (st_rs s)))))
      (Some (mkMsg (msg_index m) (msg_round m) (msg_status m)))
      =
    (mkSt (st_obs s) (Some (mkRS (msg_round m + 1) muddy)), None).
Proof.
  by intros; rewrite H9, H10, MC_transition_equation_7;
    unfold MC_transition_clause_5; repeat case_decide; try done; lia.
Qed.

Lemma MC_transition_undecided_receive_undecided_round_obs :
  forall (i : index) (s : State) (m : Message),
    state_status (st_rs s) = undecided ->
    msg_status m = undecided ->
    msg_index m ∉ st_obs s ->
    msg_round m = size (st_obs s) ->
    state_round (st_rs s) < size (st_obs s) ->
    MC_transition i receive
      (mkSt (st_obs s) (Some (mkRS (state_round (st_rs s)) (state_status (st_rs s)))))
      (Some (mkMsg (msg_index m) (msg_round m) (msg_status m)))
      =
    (mkSt (st_obs s) (Some (mkRS (msg_round m) muddy)), None).
Proof.
  by intros; rewrite H9, H10, MC_transition_equation_7;
    unfold MC_transition_clause_5; repeat case_decide; try done; lia.
Qed.

Lemma MC_transition_undecided_receive_undecided_round_lt_obs_minus_one :
  forall (i : index) (s : State) (m : Message),
    state_status (st_rs s) = undecided ->
    msg_status m = undecided ->
    msg_index m ∈ st_obs s ->
    state_round (st_rs s) <= msg_round m < size (st_obs s) - 1 ->
    state_round (st_rs s) < size (st_obs s) ->
    MC_transition i receive
      (mkSt (st_obs s) (Some (mkRS (state_round (st_rs s)) (state_status (st_rs s)))))
      (Some (mkMsg (msg_index m) (msg_round m) (msg_status m)))
      =
    (mkSt (st_obs s) (Some (mkRS (msg_round m + 1) (state_status (st_rs s)))), None).
Proof.
  by intros; rewrite H9, H10, MC_transition_equation_7;
    unfold MC_transition_clause_5; repeat case_decide; try done; lia.
Qed.

(** ** Invariant preservation *)

Definition MC_component_invariant_helper (s : State) (union : indexSet) : Prop :=
  match state_status (st_rs s) with
  | undecided => state_round (st_rs s) < size (st_obs s)
  | clean => state_round (st_rs s) = size (st_obs s) /\ size union = size (st_obs s)
  | muddy => state_round (st_rs s) = size (st_obs s) /\ size union - 1 = size (st_obs s)
  end.

Definition MC_component_invariant (s : composite_state MCVLSM) (i : index) : Prop :=
  MC_component_invariant_helper (s i) (MuddyUnion s).

Inductive MC_component_invariant_inductive : composite_state MCVLSM -> index -> Prop :=
| component_invariant_undecided : forall s i,
    state_status (st_rs (s i)) = undecided ->
    state_round (st_rs (s i)) < size (st_obs (s i)) ->
    MC_component_invariant_inductive s i
| component_invariant_clean : forall s i,
    state_status (st_rs (s i)) = clean ->
    state_round (st_rs (s i)) = size (st_obs (s i)) ->
    size (MuddyUnion s) = size (st_obs (s i)) ->
    MC_component_invariant_inductive s i
| component_invariant_muddy : forall s i,
   state_status (st_rs (s i)) = muddy ->
   state_round (st_rs (s i)) = size (st_obs (s i)) ->
   size (MuddyUnion s) - 1 = size (st_obs (s i)) ->
   MC_component_invariant_inductive s i.

Lemma MC_component_invariant_equiv_MC_component_invariant_inductive :
  forall (s : composite_state MCVLSM) (i : index),
    MC_component_invariant s i <-> MC_component_invariant_inductive s i.
Proof.
  intros s i.
  unfold MC_component_invariant, MC_component_invariant_helper.
  case_match; split; intros.
  - by apply component_invariant_undecided.
  - by inversion H10; [| congruence..].
  - by apply component_invariant_muddy; destruct H10.
  - by inversion H10; split; congruence.
  - by apply component_invariant_clean; destruct H10.
  - by inversion H10; split; congruence.
Qed.

Definition MC_composite_invariant (s : composite_state MCVLSM) : Prop :=
  forall (i : index),
    initial_state_prop (MCVLSM i) (s i) \/ MC_component_invariant s i.

Definition MC_composite_invariant_inductive (s : composite_state MCVLSM) : Prop :=
  forall (i : index),
    initial_state_prop (MCVLSM i) (s i) \/ MC_component_invariant_inductive s i.

Lemma MC_composite_invariant_preservation_muddy_from_undecided
  (s sm : composite_state MCVLSM) (i j : index) (o : indexSet) :
  o ≡ st_obs (s i) ->
  j ∈ o -> consistent s ->
  (forall k, st_obs (sm k) ≡ st_obs (s k)) ->
  size o - 1 < size (st_obs (sm j)) ->
  size (MuddyUnion s) - 1 = size o.
Proof.
  intros Heqo Hin Hconsistent Hobs_equiv Hinvs.
  destruct (Hconsistent) as [_ Hcons].
  rewrite Heqo in *; clear o Heqo.
  remember (size (st_obs (s i))) as o.
  rewrite Hobs_equiv, Hcons, size_difference in Hinvs.
  - rewrite size_singleton in Hinvs.
    apply MC_number_of_muddy_seen with (n := i) in Hconsistent.
    by destruct Hconsistent; lia.
  - apply singleton_subseteq_l.
    unfold MuddyUnion; rewrite elem_of_union_list.
    exists (st_obs (s i)); split; [| done].
    apply elem_of_list_fmap.
    by exists i; split; [| apply elem_of_enum].
Qed.

Lemma MC_composite_invariant_preservation_muddy_from_clean (s sm : composite_state MCVLSM)
  (i j : index) (o : indexSet) :
  o ≡ st_obs (s i) -> j ∉ o -> consistent s ->
  (forall k, st_obs (sm k) ≡ st_obs (s k)) ->
  size o < size (st_obs (sm j)) ->
  size (MuddyUnion s) - 1 = size o.
Proof.
  intros Heqo Hin Hconsistent Hobs_equiv Hinvs.
  destruct (Hconsistent) as [_ Hcons].
  rewrite Heqo in *; clear o Heqo.
  rewrite Hobs_equiv in Hinvs.
  destruct (decide (i = j)); [by subst; lia |].
  remember (size (st_obs (s i))) as o.
  rewrite Hcons, size_difference_alt in Hinvs.
  replace (size (MuddyUnion s ∩ {[j]})) with 0 in Hinvs.
  - by apply MC_number_of_muddy_seen with (n := i) in Hconsistent; lia.
  - symmetry; apply size_empty_iff.
    by rewrite Hcons in Hin; set_solver.
Qed.

Lemma non_initial_state_has_init_tr (is s : composite_state MCVLSM)
  (tr : list (composite_transition_item MCVLSM)) :
  finite_valid_trace_init_to MC_composite_vlsm is s tr -> forall (i : index),
  ~ MC_initial_state_prop (s i) ->
  exists (item : composite_transition_item MCVLSM), item ∈ tr /\ projT2 (l item) = init.
Proof.
  intros Htr i Hnoninit.
  induction Htr using finite_valid_trace_init_to_rev_ind;
    [by contradiction Hnoninit; apply Hsi |].
  destruct (decide (MC_initial_state_prop (s i))); cycle 1.
  - destruct (IHHtr n) as (item & Hitem & Hinit).
    by exists item; rewrite elem_of_app; itauto.
  - eexists.
    rewrite elem_of_app, elem_of_list_singleton.
    split; [by right |]; cbn.
    destruct Ht as [(_ & _ & Hv & _) Ht], l as (j & lj); cbn in Ht, Hv |- *.
    destruct (MC_transition j lj (s j) iom) as [si' om'].
    inversion Ht; subst; clear Ht.
    destruct (decide (i = j)); subst; state_update_simpl; [| done].
    unfold MC_initial_state_prop in m.
    destruct (s j); cbn in *; subst.
    by inversion Hv; subst.
Qed.

Lemma size_MuddyUnion_input_valid_transition :
  forall (l : label MC_composite_vlsm) (s s' : composite_state MCVLSM) (iom oom : option Message),
    input_valid_transition MC_composite_vlsm l (s, iom) (s', oom) ->
      size (MuddyUnion s) = size (MuddyUnion s').
Proof.
  intros * Hivt.
  apply set_size_proper, MC_obs_equiv_preserves_muddy.
  apply MC_trans_preserves_obs_equiv with l iom oom.
  by apply Hivt.
Qed.

Lemma consistent_finite_valid_trace_from_to :
  forall (s1 s2 : composite_state MCVLSM) (tr : list transition_item) (i : index),
    finite_valid_trace_from_to MC_composite_vlsm s1 s2 tr ->
    st_rs (s2 i) <> None ->
      consistent s2.
Proof.
  intros * Hfvt Hneq.
  destruct (decide (composite_initial_state_prop MCVLSM s2)).
  - by specialize (c i).
  - apply MC_non_initial_valid_consistent.
    split; [| done].
    by apply valid_trace_last_pstate in Hfvt.
Qed.

Lemma consistent_valid_state_prop :
  forall (s : composite_state MCVLSM) (i : index),
    valid_state_prop MC_composite_vlsm s -> st_rs (s i) <> None ->
      consistent s.
Proof.
  intros * Hv Hneq.
  eapply consistent_finite_valid_trace_from_to; [| done].
  by constructor.
Qed.

Lemma MC_component_invariant_helper_from_constraint :
  forall (s : composite_state MCVLSM) (i : index) (r : nat) (status : ChildStatus),
    MC_composite_invariant s ->
    MC_constraint (existT i receive)
      (s, Some {| msg_index := i; msg_round := r; msg_status := status |}) ->
    MC_component_invariant_helper
    {|
      st_obs := st_obs (s i); st_rs := Some {| rs_round := r; rs_status := status |}
    |} (MuddyUnion s).
Proof.
  cbn; intros * Hinvs Hc.
  destruct (s i) as [oj [[rj statusj] |]] eqn: Hsj; [| done].
  destruct (Hinvs i) as [Hjinit | Hinvsj]; [by rewrite Hsj in Hjinit |].
  unfold MC_component_invariant, MC_component_invariant_helper in Hinvsj.
  rewrite Hsj in Hinvsj; cbn in Hinvsj |- *.
  destruct Hc as [[] | []]; subst; [done |].
  by destruct statusj; cbn; lia.
Qed.

(**
  The proof of the following lemma proceeds by induction on the length of the trace
  to the state [s] (such a trace exists because of the assumption that the state [s]
  is valid). The induction step analyzes each case of the transition function
  and proves the corresponding relations depending on the particular
  conditions of the transition.
*)
Lemma MC_composite_invariant_preservation (s : composite_state MCVLSM) :
  valid_state_prop MC_composite_vlsm s -> MC_composite_invariant s.
Proof.
  intros Hvsp.
  apply valid_state_has_trace in Hvsp as (is & tr & Htr).
  remember (length tr) as len_tr.
  revert s tr Heqlen_tr Htr.
  induction len_tr as [len_tr Hind] using (well_founded_induction Wf_nat.lt_wf).
  intros; subst len_tr.
  destruct_list_last tr tr' lst Htr_lst;
    destruct Htr as [Htr Hinit]; [by inversion Htr; subst; left |].
  intros i.
  apply finite_valid_trace_from_to_app_split in Htr as [Htr' Hlst].
  remember (finite_trace_last is tr') as s'.
  apply valid_trace_get_last in Hlst as Heqs.
  apply valid_trace_forget_last, first_transition_valid in Hlst.
  cbn in Heqs, Hlst; rewrite Heqs in Hlst.
  destruct lst; cbn in *.
  unfold MC_component_invariant, MC_component_invariant_helper.
  erewrite <- size_MuddyUnion_input_valid_transition by done.
  destruct l as [j lj], Hlst as [(_ & _ & Hv & Hc) Ht]; cbn in Ht.
  destruct MC_transition eqn: Htj.
  inversion Ht as [Hdest]; subst s o.
  assert (Hinvs : MC_composite_invariant s').
  {
    eapply Hind; [| done..].
    by rewrite app_length; cbn; lia.
  }
  destruct (decide (j = i)); [subst j |]; state_update_simpl; [| by apply (Hinvs i)].
  clear - Htr' Hinit Hdest Hv Hc Htj Hinvs Hind.
  right.
  pose proof (Hinvs' := Hinvs).
  specialize (Hinvs i).
  funelim (MC_transition i lj (s' i) input);
    inversion Hv; try congruence;
    rewrite <- H10 in H0; inversion H0; subst; clear H0; rewrite Htj in Heqcall.
  - (* emit *)
    inversion Heqcall; subst; cbn in *; clear Heqcall Htj.
    unfold MC_component_invariant in Hinvs; rewrite <- H10 in Hinvs; cbn in Hinvs.
    by destruct Hinvs.
  - (* receive *)
    inversion Heqcall; subst; cbn in *; clear Heqcall Htj.
    unfold MC_component_invariant in Hinvs; rewrite <- H10 in Hinvs; cbn in Hinvs.
    by destruct Hinvs.
  - (* receive *)
    inversion Heqcall; subst; cbn in *; clear Heqcall Htj.
    unfold MC_component_invariant in Hinvs; rewrite <- H10 in Hinvs; cbn in Hinvs.
    by destruct Hinvs.
  - (* init *)
    inversion Heqcall; subst; cbn in *; clear Heqcall Htj Hinvs.
    split; [done |].
    destruct Hc as [Hunion Hc].
    specialize (Hc i); rewrite <- H10 in Hc.
    cbn in Hc; rewrite Hc, size_difference, size_singleton; [done |].
    apply singleton_subseteq_l.
    by apply size_empty_iff in Heq; rewrite Heq in Hc; set_solver.
  - (* init *)
    by inversion Heqcall; subst; cbn in *; lia.
  - (* receive *)
    unfold MC_component_invariant in Hinvs; rewrite <- H10 in Hinvs; cbn in Hinvs.
    destruct Hinvs; [done |].
    eapply consistent_finite_valid_trace_from_to in Htr'
      as [HMuddy_s' Hconsistent]; [| by rewrite <- H10; cbn].
    specialize (Hconsistent i) as Hconsi.
    rewrite <- H10 in Hconsi; cbn in Hconsi.
    assert (Hinvs : MC_component_invariant_helper (mkSt (st_obs (s' j))
      (Some (mkRS r' undecided))) (MuddyUnion s'))
      by (eapply MC_component_invariant_helper_from_constraint; done).
    assert (o0 ≡ st_obs (s' i)) by (rewrite <- H10; done).
    repeat case_decide; inversion Heqcall; subst; cbn in *; clear Heqcall;
      repeat split; try lia; [| done].
    by eapply MC_composite_invariant_preservation_muddy_from_undecided.
  - (* receive *)
    unfold MC_component_invariant in Hinvs; rewrite <- H10 in Hinvs; cbn in Hinvs.
    destruct Hinvs; [done |].
    eapply consistent_finite_valid_trace_from_to in Htr'
      as [HMuddy_s' Hconsistent]; [| by rewrite <- H10; cbn].
    specialize (Hconsistent i) as Hconsi.
    rewrite <- H10 in Hconsi; cbn in Hconsi.
    assert (Hinvs : MC_component_invariant_helper (mkSt (st_obs (s' j))
      (Some (mkRS r' undecided))) (MuddyUnion s'))
      by (eapply MC_component_invariant_helper_from_constraint; done).
    assert (o0 ≡ st_obs (s' i)) by (rewrite <- H10; done).
    repeat case_decide; inversion Heqcall; subst; cbn in *; clear Heqcall;
      repeat split; try lia; [done |].
    by eapply MC_composite_invariant_preservation_muddy_from_clean.
  - (* receive *)
    unfold MC_component_invariant in Hinvs; rewrite <- H10 in Hinvs; cbn in Hinvs.
    destruct Hinvs; [done |].
    eapply consistent_finite_valid_trace_from_to in Htr'
      as [HMuddy_s' Hconsistent]; [| by rewrite <- H10; cbn].
    specialize (Hconsistent i) as Hconsi.
    rewrite <- H10 in Hconsi; cbn in Hconsi.
    assert (Hinvs : MC_component_invariant_helper (mkSt (st_obs (s' j))
      (Some (mkRS r' muddy))) (MuddyUnion s'))
      by (eapply MC_component_invariant_helper_from_constraint; done).
    assert (o0 ≡ st_obs (s' i)) by (rewrite <- H10; done).
    repeat case_decide; inversion Heqcall; subst; cbn in *; clear Heqcall;
      repeat split; try lia; [| done].
    destruct Hinvs as [Hstobs Hmuddy].
    rewrite <- Hmuddy in Hstobs.
    destruct (decide (size (MuddyUnion s') = 0)); [| by lia].
    by apply size_non_empty_iff in HMuddy_s'.
  - (* receive *)
    inversion Heqcall; subst; cbn in *; clear Heqcall Htj.
    unfold MC_component_invariant in Hinvs; rewrite <- H10 in Hinvs; cbn in Hinvs.
    by destruct Hinvs.
  - (* receive *)
    inversion Heqcall; cbn in *; subst; clear Heqcall Htj.
    unfold MC_component_invariant in Hinvs; rewrite <- H10 in Hinvs; cbn in Hinvs.
    by destruct Hinvs.
  - (* receive *)
    unfold MC_component_invariant in Hinvs; rewrite <- H10 in Hinvs; cbn in Hinvs.
    destruct Hinvs; [done |].
    eapply consistent_finite_valid_trace_from_to in Htr'
      as [HMuddy_s' Hconsistent]; [| by rewrite <- H10; cbn].
    specialize (Hconsistent i) as Hconsi.
    rewrite <- H10 in Hconsi; cbn in Hconsi.
    assert (Hinvs : MC_component_invariant_helper (mkSt (st_obs (s' j))
      (Some (mkRS r' clean))) (MuddyUnion s'))
      by (eapply MC_component_invariant_helper_from_constraint; done).
    assert (o0 ≡ st_obs (s' i)) by (rewrite <- H10; done).
    by repeat case_decide; inversion Heqcall; subst; cbn in *; clear Heqcall; lia.
Qed.

Lemma MC_composite_invariant_preservation_inductive (s : composite_state MCVLSM) :
  valid_state_prop MC_composite_vlsm s -> MC_composite_invariant_inductive s.
Proof.
  intros Hv i.
  destruct (MC_composite_invariant_preservation _ Hv i); [by left|].
  by right; apply MC_component_invariant_equiv_MC_component_invariant_inductive.
Qed.

(** ** Auxiliary progress results *)

Lemma MC_valid_noequiv_muddy (s : composite_state MCVLSM) (m : Message) :
  valid_state_prop MC_composite_vlsm s ->
  msg_status m = muddy ->
  MC_no_equivocation s m ->
  msg_round m = size (MuddyUnion s) - 1 /\ msg_index m ∈ MuddyUnion s.
Proof.
  intros Hs Hmuddy Hnoequiv.
  pose proof (Hs' := Hs).
  apply MC_composite_invariant_preservation in Hs.
  destruct (Hs (msg_index m)) as [Hinit | Hinvariant].
  - assert (Hsminit : MC_initial_state_prop (s (msg_index m))) by apply Hinit.
    unfold MC_initial_state_prop in Hsminit.
    unfold MC_no_equivocation in Hnoequiv.
    repeat case_match; cbn in *; [| done].
    by rewrite H10 in Hsminit.
  - unfold MC_component_invariant, MC_component_invariant_helper in Hinvariant.
    unfold MC_no_equivocation in Hnoequiv.
    repeat case_match; cbn in *; subst; try done;
      destruct Hnoequiv as [[Hnoequivst Hnoequivr] | [Hnoequivst Hnoequivr]];
      subst; rewrite H11 in H9; cbn in *; try done.
    rewrite H11 in Hinvariant; cbn in Hinvariant.
    destruct Hinvariant as [Hn Hstobs].
    split; [by rewrite <- Hstobs in Hn |].
    eapply consistent_valid_state_prop in Hs' as [Hnempty Hcons];
      [| by rewrite H11; cbn].
    replace st_obs0 with (st_obs (s msg_index0)) in Hstobs; [| by rewrite H11].
    rewrite Hcons, size_difference_alt in Hstobs.
    apply size_non_empty_iff in Hnempty.
    assert (Hintersectgeq1 : size (MuddyUnion s ∩ {[msg_index0]}) >= 1) by lia.
    assert (Hintersectleq1 : MuddyUnion s ∩ {[msg_index0]} ⊆ {[msg_index0]}) by set_solver.
    apply subseteq_size in Hintersectleq1.
    rewrite size_singleton in Hintersectleq1.
    assert (Hintersecteq1 : size (MuddyUnion s ∩ {[msg_index0]}) = 1) by lia.
    apply size_1_elem_of in Hintersecteq1.
    by set_solver.
Qed.

Lemma MC_valid_noninitial_state_undecided_round_less_obs
  (s : composite_state MCVLSM) (i : index) :
  valid_state_prop MC_composite_vlsm s ->
  ~ MC_initial_state_prop (s i) ->
  state_status (st_rs (s i)) = undecided ->
  state_round (st_rs (s i)) < size (st_obs (s i)).
Proof.
  intros Hvalid Hundecided.
  apply MC_composite_invariant_preservation_inductive in Hvalid.
  destruct (Hvalid i); [done |].
  by inversion H9; [| congruence ..].
Qed.

(**
  The definitions [MC_build_muddy_muddy_trace] and [MC_build_clean_muddy_trace] are
  useful in the proof of the lemma [MC_build_valid_message], where, having a valid
  state, we aim to obtain a valid message with status [undecided], emitted earlier
  on a trace leading to that state.

  To achieve this, we take two indexes [i] and [j], with child [j] being seen as muddy
  by [i], and want to build a valid trace which corresponds to an exchange of messages
  between these two children.

  We then use these two function definitions in order to build these traces between
  two specific children.
*)
Fixpoint MC_build_muddy_muddy_trace (is : composite_state MCVLSM)
  (target helper : index) (round : nat) : list (composite_transition_item MCVLSM) :=
match round with
| 0 =>
  let s := state_update MCVLSM is helper
    (mkSt (st_obs (is helper)) (Some (mkRS 0 undecided)))
  in
  let item0 := Build_transition_item (T := composite_type MCVLSM)
    (existT helper init) None s None
  in
  let item1 := Build_transition_item (T := composite_type MCVLSM)
    (existT target init) None (state_update MCVLSM s target (mkSt (st_obs (s target))
    (Some (mkRS 0 undecided)))) None
  in [item0; item1]
| S n =>
  let tr := MC_build_muddy_muddy_trace is helper target n in
  let s := finite_trace_last is tr in
  let item := Build_transition_item (T := composite_type MCVLSM)
    (existT target receive) (Some (mkMsg helper n undecided))
    (state_update MCVLSM s target (mkSt (st_obs (s target))
      (Some (mkRS (S n) undecided)))) None
  in tr ++ [item]
end.

Lemma MC_build_muddy_muddy_trace_last_target
  (is : composite_state MCVLSM)
  (target helper : index) (round : nat) :
  exists (obs : indexSet),
    finite_trace_last is (MC_build_muddy_muddy_trace is target helper round) target
      =
    mkSt obs (Some (mkRS round undecided)).
Proof.
  destruct round; cbn.
  - by state_update_simpl; eexists.
  - rewrite map_app; cbn; rewrite last_last.
    by state_update_simpl; eexists.
Qed.

Lemma MC_build_muddy_muddy_trace_last_helper
  (is : composite_state MCVLSM)
  (target helper : index) (round : nat) :
  helper <> target ->
  exists (obs : indexSet),
    finite_trace_last is (MC_build_muddy_muddy_trace is target helper round) helper
      =
    mkSt obs (Some (mkRS (round - 1) undecided)).
Proof.
  intros Hneq.
  destruct round; cbn; [by state_update_simpl; eexists |].
  rewrite map_app; cbn; rewrite last_last.
  state_update_simpl.
  destruct (MC_build_muddy_muddy_trace_last_target is helper target round)
    as (obs & Hlast).
  rewrite Hlast; cbn.
  replace (round - 0) with round by lia.
  by eexists.
Qed.

Lemma MC_valid_message_from_valid_state (s : composite_state MCVLSM) :
  valid_state_prop MC_composite_vlsm s ->
  forall (i : index) (obs : indexSet) (round : nat) (status : ChildStatus),
  s i = mkSt obs (Some (mkRS round status)) ->
  valid_message_prop MC_composite_vlsm (mkMsg i round status).
Proof.
  intros Hvalid * Hsi.
  apply input_valid_transition_out
    with (l := existT i emit) (s := s) (s' := s) (om := None).
  repeat split; subst; cbn in *; [done | ..].
  - by apply option_valid_message_None.
  - by rewrite Hsi; constructor.
  - by rewrite !Hsi, MC_transition_equation_5, state_update_id.
Qed.

Lemma MC_build_muddy_muddy_trace_valid
  (is : composite_state MCVLSM)
  (target helper : index) (round : nat) :
  composite_initial_state_prop MCVLSM is ->
  consistent is ->
  target ∈ MuddyUnion is ->
  helper ∈ MuddyUnion is ->
  target <> helper ->
  round < size (MuddyUnion is) - 1 ->
  finite_valid_trace MC_composite_vlsm is
    (MC_build_muddy_muddy_trace is target helper round).
Proof.
  intros Hinit Hcons Htarget Hhelper Hdiff Hround.
  revert target helper Htarget Hhelper Hdiff Hround.
  induction round as [| round IHround]; intros.
  - specialize (Hinit helper) as Hinithelper.
    cbn in Hinithelper; unfold MC_initial_state_prop in Hinithelper.
    specialize (Hinit target) as Hinittarget.
    cbn in Hinittarget; unfold MC_initial_state_prop in Hinittarget.
    destruct Hcons as [Hmuddyunion Hconsobs].
    specialize (Hconsobs helper) as Hconshelper.
    specialize (Hconsobs target) as Hconstarget.
    assert (size (MuddyUnion is) >= 2) by lia.
    eapply valid_trace_forget_last, finite_valid_trace_init_to_alt_equiv.
    constructor; [| done].
    repeat (apply mvt_extend); cbn.
    + by apply option_valid_message_None.
    + destruct (is helper) as [o_helper []] eqn: Hishelper; [done |].
      rewrite MC_transition_equation_3; unfold MC_transition_clause_1.
      case_match eqn: Hso.
      replace o_helper with (st_obs (is helper)) in * by (rewrite Hishelper; done).
      rewrite Hconsobs, size_difference, size_singleton in Hso.
      * by case_match; inversion Hso; subst; [lia |].
      * by rewrite <- elem_of_subseteq_singleton.
    + split; [| done].
      destruct (is helper); cbn in *; subst.
      by constructor.
    + by apply option_valid_message_None.
    + state_update_simpl.
      destruct (is target) as [o_target []] eqn: Histarget; [done |].
      rewrite MC_transition_equation_3; unfold MC_transition_clause_1.
      case_match eqn: Hso.
      replace o_target with (st_obs (is target)) in * by (rewrite Histarget; done).
      rewrite Hconsobs, size_difference, size_singleton in Hso.
      * by case_match; inversion Hso; subst; [lia |].
      * by rewrite <- elem_of_subseteq_singleton.
    + state_update_simpl.
      split.
      * destruct (is target); cbn in *; subst.
        by constructor.
      * apply (MC_obs_equiv_preserves_consistency is); [| done].
        by apply MC_state_update_preserves_obs_equiv.
    + by apply mvt_empty.
  - cbn.
    specialize (IHround helper target Hhelper Htarget).
    spec IHround; [done |].
    spec IHround; [by lia |].
    apply valid_trace_add_default_last in IHround as [IH IHinit].
    eapply valid_trace_forget_last.
    split; [| done].
    eapply finite_valid_trace_from_to_app; [done |].
    apply valid_trace_add_default_last, finite_valid_trace_singleton.
    destruct (MC_build_muddy_muddy_trace_last_helper is helper target round)
      as (obs & Hlasthelper); [done |].
    destruct (MC_build_muddy_muddy_trace_last_target is helper target round)
      as (obs' & Hlast).
    repeat split; cbn in *.
    + by apply valid_trace_last_pstate in IH.
    + apply valid_trace_last_pstate in IH as Hfinal.
      remember (finite_trace_last _ _) as final.
      by apply MC_valid_message_from_valid_state with (s := final) (obs := obs').
    + rewrite Hlasthelper.
      by constructor.
    + rewrite Hlast.
      by left.
    + rewrite Hlasthelper, MC_transition_equation_7; cbn.
      unfold MC_transition_clause_5.
      assert (Hobsequiv : st_obs (is target) ≡ obs).
      {
        replace obs with (st_obs (finite_trace_last is
          (MC_build_muddy_muddy_trace is helper target round) target));
          [| by rewrite Hlasthelper].
        apply MC_in_futures_preserves_obs_equiv.
        by eexists.
      }
      rewrite decide_True, decide_False, decide_True.
      * by replace (round + 1) with (S round) by lia.
      * split; [by lia |].
        rewrite MC_in_futures_preserves_muddy in Hround; [| by eexists].
        rewrite <- MC_in_futures_preserves_muddy in Hround; [| by eexists].
        pose proof (Hnrmuddy := MC_muddy_number_of_muddy_seen is target Hcons Htarget).
        by rewrite <- Hobsequiv; lia.
      * by lia.
      * rewrite <- Hobsequiv.
        destruct Hcons as [Hnempty ->].
        by set_solver.
Qed.

Fixpoint MC_build_clean_muddy_trace (is : composite_state MCVLSM)
  (target helper : index) (round : nat) : list (composite_transition_item MCVLSM) :=
match round with
| 0 =>
  let s := state_update MCVLSM is helper
    (mkSt (st_obs (is helper)) (Some (mkRS 0 undecided)))
  in
  let item0 := Build_transition_item (T := composite_type MCVLSM)
    (existT helper init) None s None
  in
  let item1 := Build_transition_item (T := composite_type MCVLSM)
    (existT target init) None
    (state_update MCVLSM s target
      (mkSt (st_obs (s target)) (Some (mkRS 0 undecided)))) None
  in [item0; item1]
| S n =>
  let tr := MC_build_clean_muddy_trace is target helper n in
  let s := finite_trace_last is tr in
  let item0 := Build_transition_item (T := composite_type MCVLSM)
    (existT helper receive) (Some (mkMsg target n undecided))
    (state_update MCVLSM s helper
      (mkSt (st_obs (s helper)) (Some (mkRS n undecided)))) None
  in
  let item1 := Build_transition_item (T := composite_type MCVLSM)
    (existT target receive) (Some (mkMsg helper n undecided))
    (state_update MCVLSM (destination item0) target
      (mkSt (st_obs (s target)) (Some (mkRS (S n) undecided)))) None
  in tr ++ [item0; item1]
end.

Lemma MC_build_clean_muddy_trace_last_target
  (is : composite_state MCVLSM)
  (target helper : index) (round : nat) :
    exists (obs : indexSet),
      finite_trace_last is (MC_build_clean_muddy_trace is target helper round) target
        =
      mkSt obs (Some (mkRS round undecided)).
Proof.
  destruct round; cbn.
  - by state_update_simpl; eexists.
  - rewrite map_app; cbn; rewrite last_app; cbn.
    by state_update_simpl; eexists.
Qed.

Lemma MC_build_clean_muddy_trace_last_helper
  (is : composite_state MCVLSM)
  (target helper : index) (round : nat) :
    helper <> target ->
    exists (obs : indexSet),
      finite_trace_last is (MC_build_clean_muddy_trace is target helper round) helper
        =
      mkSt obs (Some (mkRS (round - 1) undecided)).
Proof.
  intros Hneq.
  destruct round; cbn.
  - by state_update_simpl; eexists.
  - rewrite map_app; cbn; rewrite last_app; cbn.
    replace (round - 0) with round by lia.
    by state_update_simpl; eexists.
Qed.

Lemma MC_build_clean_muddy_trace_valid
  (is : composite_state MCVLSM)
  (target helper : index) (round : nat) :
  composite_initial_state_prop MCVLSM is ->
  consistent is ->
  target ∉ MuddyUnion is ->
  helper ∈ MuddyUnion is ->
  round < size (st_obs (is target)) ->
  size (MuddyUnion is) >= 2 ->
  finite_valid_trace MC_composite_vlsm is
    (MC_build_clean_muddy_trace is target helper round).
Proof.
  intros Hinit Hcons Htarget Hhelper Hround Hsizemuddy.
  assert (Hdiff : target <> helper) by (intros ->; done).
  revert Hround.
  induction round as [| round IHround]; intros.
  - specialize (Hinit helper) as Hinithelper.
    cbn in Hinithelper; unfold MC_initial_state_prop in Hinithelper.
    specialize (Hinit target) as Hinittarget.
    cbn in Hinittarget; unfold MC_initial_state_prop in Hinittarget.
    destruct Hcons as [Hmuddyunion Hconsobs].
    specialize (Hconsobs helper) as Hconshelper.
    specialize (Hconsobs target) as Hconstarget.
    eapply valid_trace_forget_last, finite_valid_trace_init_to_alt_equiv.
    constructor; [| done].
    repeat (apply mvt_extend); cbn.
    + by apply option_valid_message_None.
    + destruct (is helper) as [o_helper []] eqn: Hishelper; [done |].
      rewrite MC_transition_equation_3; unfold MC_transition_clause_1.
      case_match eqn: Hso.
      replace o_helper with (st_obs (is helper)) in * by (rewrite Hishelper; done).
      rewrite Hconsobs, size_difference, size_singleton in Hso.
      * by case_match; inversion Hso; subst; [lia |].
      * by rewrite <- elem_of_subseteq_singleton.
    + split; [| done].
      destruct (is helper); cbn in *; subst.
      by constructor.
    + by apply option_valid_message_None.
    + state_update_simpl.
      destruct (is target) as [o_target [|]] eqn: Histarget; [done |].
      rewrite MC_transition_equation_3; unfold MC_transition_clause_1.
      destruct (decide (size o_target = 0)); cycle 1.
      * by cbn; repeat case_match; [lia | inversion H9].
      * replace o_target with (st_obs (is target)) in e by (rewrite Histarget; done).
        rewrite Hconsobs, size_difference, size_singleton in e; [by lia |].
        exfalso.
        rewrite size_difference_alt in e.
        assert (Hsizeintersect : size (MuddyUnion is ∩ {[target]}) >= 2) by lia.
        assert (Hintersectleq1 : MuddyUnion is ∩ {[target]} ⊆ {[target]}) by set_solver.
        apply subseteq_size in Hintersectleq1.
        rewrite size_singleton in Hintersectleq1.
        by lia.
    + state_update_simpl.
      split.
      * destruct (is target); cbn in *; subst.
        by constructor.
      * apply (MC_obs_equiv_preserves_consistency is); [| done].
        by apply MC_state_update_preserves_obs_equiv.
    + by apply mvt_empty.
  - spec IHround; [lia |].
    apply valid_trace_add_default_last in IHround as [IH IHinit].
    eapply valid_trace_forget_last.
    split; [| done].
    cbn; eapply finite_valid_trace_from_to_app; [done |].
    destruct (MC_build_clean_muddy_trace_last_helper is target helper round)
      as (obs & Hlasthelper); [done |].
    destruct (MC_build_clean_muddy_trace_last_target is target helper round)
      as (obs' & Hlast).
    assert (Hvalidtr1 : input_valid_transition MC_composite_vlsm
      (existT helper receive)
      (finite_trace_last is
        (MC_build_clean_muddy_trace is target helper round),
        Some {| msg_index := target; msg_round := round; msg_status := undecided |})
      (state_update MCVLSM
        (finite_trace_last is
          (MC_build_clean_muddy_trace is target helper round)) helper
          {| st_obs := st_obs (finite_trace_last is
               (MC_build_clean_muddy_trace is target helper round) helper);
             st_rs := Some (mkRS round undecided)
          |}, None)).
    {
      repeat split; cbn in *.
      - by apply valid_trace_last_pstate in IH.
      - apply valid_trace_last_pstate in IH as Hfinal.
        remember (finite_trace_last _ _) as final.
        by apply MC_valid_message_from_valid_state with (s := final) (obs := obs').
      - by rewrite Hlasthelper; constructor.
      - by subst; rewrite Hlast; cbn; left.
      - rewrite Hlasthelper, MC_transition_equation_7; cbn.
        assert (Hobsequiv : st_obs (is helper) ≡ obs).
        {
          replace obs with (st_obs (finite_trace_last is
            (MC_build_clean_muddy_trace is target helper round) helper));
            [| by rewrite Hlasthelper].
          apply MC_in_futures_preserves_obs_equiv.
          by eexists.
        }
        destruct Hcons as [Hnempty Hcons].
        assert (Htargetobs : target ∉ obs).
        {
          rewrite <- Hobsequiv, Hcons.
          by set_solver.
        }
        unfold MC_transition_clause_5.
        rewrite decide_False by done.
        destruct round; [by rewrite decide_True by lia; cbn; state_update_simpl |].
        rewrite decide_False, decide_True; [done | | by lia].
        split; [by lia |].
        rewrite Hcons, size_difference_alt in Hround.
        rewrite <- Hobsequiv, Hcons, size_difference, size_singleton by set_solver.
        by lia.
    }
    constructor; [| done].
    apply finite_valid_trace_from_to_singleton.
    repeat split; cbn in *.
    + by eapply input_valid_transition_destination.
    + apply valid_trace_last_pstate in IH as Hfinal.
      remember (state_update _ _ _ _) as final.
      apply input_valid_transition_out
        with (l := existT helper emit) (s := final) (s' := final) (om := None).
      repeat split; subst; cbn.
      * by eapply input_valid_transition_destination.
      * by apply option_valid_message_None.
      * by state_update_simpl; constructor.
      * state_update_simpl.
        by rewrite MC_transition_equation_5, state_update_twice.
    + rewrite Hlasthelper; cbn.
      state_update_simpl.
      rewrite Hlast.
      by constructor.
    + by state_update_simpl; left.
    + state_update_simpl.
      rewrite Hlast, MC_transition_equation_7.
      unfold MC_transition_clause_5.
      assert (Hobsequiv : st_obs (is target) ≡ obs').
      {
        replace obs' with (st_obs (finite_trace_last is
          (MC_build_clean_muddy_trace is target helper round) target));
          [| by rewrite Hlast].
        apply MC_in_futures_preserves_obs_equiv.
        by eexists.
      }
      destruct Hcons as [Hnempty Hcons].
      assert (Htargetobs : helper ∈ obs').
      {
        rewrite <- Hobsequiv, Hcons.
        by set_solver.
      }
      rewrite decide_True by done.
      rewrite decide_False by lia.
      rewrite decide_True.
      * by replace (round + 1) with (S round) by lia.
      * split; [by lia |].
        rewrite <- Hobsequiv, Hcons.
        rewrite Hcons in Hround.
        by lia.
Qed.

Lemma MC_build_valid_message (s : composite_state MCVLSM) (round : nat) :
  MC_non_initial_valid_state s ->
  length (enum index) > 1 ->
  forall (i : index), round < size (st_obs (s i)) ->
  valid_message_prop MC_composite_vlsm (mkMsg i round undecided).
Proof.
  intros Hvalid Hlength i Hround.
  apply MC_non_initial_valid_consistent in Hvalid as Hcons.
  destruct Hvalid as [Hvalid Hnoninit].
  apply valid_state_has_trace in Hvalid as (is & tr & Hfromto & Hinit).
  destruct (Hcons) as [Hnemptys Hconss].
  rewrite <- MC_in_futures_preserves_consistency in Hcons; [| by eexists].
  destruct (Hcons) as [Hnempty Hcons'].
  assert (Hmuddyis : MuddyUnion is ≡ MuddyUnion s).
  {
    by apply MC_in_futures_preserves_muddy; exists tr.
  }
  rewrite Hconss, <- Hmuddyis in Hround.
  assert (exists (j : index), j ∈ st_obs (is i)) as (j & Hj).
  {
    setoid_rewrite Hcons'.
    apply set_choose, size_non_empty_iff.
    by lia.
  }
  apply MuddyUnion_elem in Hj as Hhelper.
  rewrite Hcons' in Hj.
  assert (Hdiff : i <> j) by set_solver.
  destruct (decide (i ∈ MuddyUnion is)).
  - destruct (MC_build_muddy_muddy_trace_last_target is i j round) as (obsf & Hlasti).
    eapply MC_valid_message_from_valid_state; [| done].
    destruct (MC_build_muddy_muddy_trace_valid is i j round Hinit Hcons e Hhelper Hdiff).
    + by rewrite size_difference, size_singleton in Hround; [| set_solver].
    + by apply finite_valid_trace_last_pstate.
  - destruct (decide (size (MuddyUnion is) <= 1)); cycle 1.
    + destruct (MC_build_clean_muddy_trace_last_target is i j round) as (obsf & Hlasti).
      eapply MC_valid_message_from_valid_state; [| done].
      destruct (MC_build_clean_muddy_trace_valid is i j round Hinit Hcons n Hhelper); [| by lia |].
      * by rewrite <- Hcons' in Hround.
      * by apply finite_valid_trace_last_pstate.
    + replace round with 0 by (rewrite size_difference_alt in Hround; lia).
      apply MC_valid_message_from_valid_state with
        (s := state_update MCVLSM is i (mkSt (st_obs (is i)) (Some (mkRS 0 undecided))))
        (obs := st_obs (is i)); [| by state_update_simpl].
      apply input_valid_transition_destination
        with (l := existT i init) (s := is) (om := None) (om' := None).
      repeat split; subst; [by apply initial_state_is_valid | ..].
      * by apply option_valid_message_None.
      * specialize (Hinit i).
        cbn in *.
        unfold MC_initial_state_prop in Hinit.
        destruct (is i); cbn in *; subst.
        by constructor.
      * done.
      * by cbn in *; apply Hcons'.
      * by apply Hcons'.
      * cbn.
        specialize (Hinit i).
        destruct (is i) eqn: Hisi.
        cbn in *; unfold MC_initial_state_prop in Hinit; cbn in Hinit; subst.
        rewrite MC_transition_equation_3.
        unfold MC_transition_clause_1.
        replace st_obs0 with (st_obs (is i)); [| by rewrite Hisi].
        replace (size (st_obs (is i))) with 1; [done |].
        rewrite Hcons', size_difference_alt.
        assert (MuddyUnion is ∩ {[i]} ≡ ∅) as -> by set_solver.
        destruct (size (MuddyUnion is)) eqn: Heq.
        -- by apply size_empty_inv in Heq.
        -- by rewrite size_empty; lia.
Qed.

Lemma MC_valid_noequiv_valid (s : composite_state MCVLSM) (m : Message) :
  valid_state_prop MC_composite_vlsm s ->
  MC_no_equivocation s m ->
  length (enum index) > 1 ->
  valid_message_prop MC_composite_vlsm m.
Proof.
  intros Hs Hnoequiv Hlength.
  unfold MC_no_equivocation in Hnoequiv.
  destruct m as [j rm statusm].
  destruct (s j) as [oj [[rj statusj] |]] eqn: Hsjf; [| done].
  destruct Hnoequiv as [[-> ->] | [-> Hrm]];
    [by eapply MC_valid_message_from_valid_state |].
  assert (Hnivs : MC_non_initial_valid_state s).
  {
    clear - Hs j Hsjf.
    split; [done |].
    intros Hforall.
    apply Forall_finite in Hforall.
    contradict Hforall.
    apply Exists_not_Forall, Exists_exists.
    exists j; split; cbn; [by apply elem_of_enum |].
    by rewrite Hsjf.
  }
  assert (Hcons : consistent s) by (apply MC_non_initial_valid_consistent; done).
  destruct Hcons as [Hnempty Hcons'].
  apply MC_composite_invariant_preservation in Hs as Hinvariants.
  destruct (Hinvariants j) as [| Hinvariant]; [by rewrite Hsjf in H9 |].
  unfold MC_component_invariant, MC_component_invariant_helper in Hinvariant.
  rewrite Hsjf in Hinvariant; cbn in Hinvariant.
  apply (MC_build_valid_message s); [done.. |].
  replace oj with (st_obs (s j)) in *; [| by rewrite Hsjf].
  by case_match; lia.
Qed.

(** ** Progress *)

Lemma MC_undecided_muddy_to_muddy_increase_round
  (s : composite_state MCVLSM)
  (item : composite_transition_item MCVLSM) (i := projT1 (l item)) :
  projT2 (l item) = receive ->
  state_status (st_rs (s i)) = undecided ->
  message_status (input item) = muddy ->
  message_index (input item) i ∈ st_obs (s i) ->
  message_round (input item) = size (st_obs (s i)) ->
  input_valid_transition_item (MC_composite_vlsm) s item ->
  state_round (st_rs (destination item i)) > state_round (st_rs (s i)).
Proof.
  intros Hl Hsundecided Hmmuddy Hmindex Hmround Hvalid.
  apply MC_transition_undecided_receive_muddy_round_obs with
    i (s i) (mkMsg (message_index (input item) i) (message_round (input item))
    (message_status (input item)))
    in Hsundecided as Htr; [| done..].
  destruct item, l, Hvalid as [(Hs & _ & Hv & Hc) Ht].
  cbn in *; subst.
  assert (Hrounds : state_round (st_rs (s x)) < size (st_obs (s x))).
  {
    by apply MC_valid_noninitial_state_undecided_round_less_obs; [| inversion Hv |].
  }
  inversion Hv; subst; cbn in Hsundecided.
  rewrite <- H9 in *; clear H9; destruct rs, m; cbn in *.
  by rewrite Htr in Ht; inversion Ht; subst; state_update_simpl; cbn; lia.
Qed.

Lemma MC_undecided_muddy_to_clean_increase_round
  (s : composite_state MCVLSM)
  (item : composite_transition_item MCVLSM) (i := projT1 (l item)) :
  projT2 (l item) = receive ->
  input_valid_transition_item (MC_composite_vlsm) s item ->
  state_status (st_rs (s i)) = undecided ->
  message_status (input item) = muddy ->
  message_index (input item) i ∈ st_obs (s i) ->
  message_round (input item) = size (st_obs (s i)) - 1 ->
  state_round (st_rs (destination item i)) > state_round (st_rs (s i)).
Proof.
  intros Hl Hvalid Hsundecided Hmmuddy Hmindex Hmround.
  apply MC_transition_undecided_receive_muddy_round_obs_minus_one with
    i (s i) (mkMsg (message_index (input item) i) (message_round (input item))
    (message_status (input item)))
    in Hsundecided as Htr; [| done..].
  destruct item, l, Hvalid as [(Hs & _ & Hv & Hc) Ht].
  cbn in *; subst i l.
  assert (Hrounds : state_round (st_rs (s x)) < size (st_obs (s x))).
  {
    by apply MC_valid_noninitial_state_undecided_round_less_obs; [| inversion Hv |].
  }
  inversion Hv; subst; cbn in Hsundecided.
  rewrite <- H9 in *; clear H9; destruct rs, m; cbn in *.
  by rewrite Htr in Ht; inversion Ht; subst; state_update_simpl; cbn; lia.
Qed.

Lemma MC_undecided_muddy_increase_round
  (s : composite_state MCVLSM)
  (item : composite_transition_item MCVLSM) (i := projT1 (l item)) :
  projT2 (l item) = receive ->
  input_valid_transition_item (MC_composite_vlsm) s item ->
  state_status (st_rs (s i)) = undecided ->
  message_status (input item) = muddy ->
  message_index (input item) i ∈ st_obs (s i) ->
  message_round (input item) = size (st_obs (s i)) - 1 \/
    message_round (input item) = size (st_obs (s i)) ->
  state_round (st_rs (destination item i)) > state_round (st_rs (s i)).
Proof.
  intros Hl Hvalid Hsundecided Hmmuddy Hmindex [].
  - by apply MC_undecided_muddy_to_clean_increase_round.
  - by apply MC_undecided_muddy_to_muddy_increase_round.
Qed.

Lemma MC_undecided_undecided_increase_round
  (s : composite_state MCVLSM)
  (item : composite_transition_item MCVLSM) (i := projT1 (l item)) :
  projT2 (l item) = receive ->
  input_valid_transition_item (MC_composite_vlsm) s item ->
  state_status (st_rs (s i)) = undecided ->
  message_status (input item) = undecided ->
  message_index (input item) i ∈ st_obs (s i) ->
  state_round (st_rs (s i)) <= message_round (input item) < size (st_obs (s i)) - 1 ->
  state_round (st_rs (destination item i)) > state_round (st_rs (s i)).
Proof.
  intros Hl Hvalid Hsundecided Hmmuddy Hmindex Hmround.
  destruct item, l, Hvalid as [(Hs & _ & Hv & Hc) Ht].
  assert (Hrounds : state_round (st_rs (s x)) < size (st_obs (s x))).
  {
    by apply MC_valid_noninitial_state_undecided_round_less_obs;
      cbn in *; subst; [| inversion Hv |].
  }
  apply MC_transition_undecided_receive_undecided_round_lt_obs_minus_one with
    i (s i) (mkMsg (message_index input i) (message_round input)
    (message_status input))
    in Hsundecided as Htr; cbn in *; subst; [| done..].
  inversion Hv; subst; cbn in Hsundecided |- *.
  rewrite <- H9 in *; clear H9; destruct rs, m; cbn in *.
  by rewrite Htr in Ht; inversion Ht; subst; state_update_simpl; cbn; lia.
Qed.

Lemma MC_undecided_undecided_to_muddy_increase_round
  (s : composite_state MCVLSM)
  (item : composite_transition_item MCVLSM) (i := projT1 (l item)) :
  projT2 (l item) = receive ->
  input_valid_transition_item (MC_composite_vlsm) s item ->
  state_status (st_rs (s i)) = undecided ->
  message_status (input item) = undecided ->
  message_index (input item) i ∈ st_obs (s i) ->
  message_round (input item) = size (st_obs (s i)) - 1 ->
  state_round (st_rs (destination item i)) > state_round (st_rs (s i)).
Proof.
  intros Hl Hvalid Hsundecided Hmmuddy Hmindex Hmround.
  destruct item, l, Hvalid as [(Hs & _ & Hv & Hc) Ht].
  assert (Hrounds : state_round (st_rs (s x)) < size (st_obs (s x))).
  {
    by apply MC_valid_noninitial_state_undecided_round_less_obs;
      cbn in *; subst; [| inversion Hv |].
  } 
  apply MC_transition_undecided_receive_undecided_round_obs_minus_one with
    i (s i) (mkMsg (message_index input i) (message_round input)
    (message_status input)) in Hsundecided
    as Htr; cbn in *; subst; [| done..].
  inversion Hv; subst; cbn in Hsundecided.
  rewrite <- H9 in *; clear H9; destruct rs, m; cbn in *.
  by rewrite Htr in Ht; inversion Ht; subst; state_update_simpl; cbn; lia.
Qed.

Definition MC_transition_item_update s j i st rs : transition_item :=
{|
  l := existT i receive : composite_label MCVLSM;
  input := Some
    {| msg_index := j; msg_status := st; msg_round := state_round (st_rs (s j)) |};
  destination := state_update MCVLSM s i
    {| st_obs := st_obs (s i); st_rs := Some rs |};
  output := None
|}.

(**
  The progress lemma [MC_progress] ensures that from any valid non-initial
  composite state, there is a valid transition to a new composite state, in
  which at least one component has greater round than before the transition.

  This result will be further used in the proof of the correctness theorem.
  To prove the progress lemma, we proceed by case analysis. We distinguish
  two main cases:
  - at least one component is in an initial state, so we can use an init
    transition to prove our goal;
  - else, we have to obtain two convenient components and build a transition
    between them, that results in an increased round number.
*)
Lemma MC_progress (s : composite_state MCVLSM) :
  MC_non_initial_valid_state s ->
  ~ MC_final_state s ->
  length (enum index) > 1 ->
  exists (item : composite_transition_item MCVLSM) (i := projT1 (l item)),
  input_valid_transition_item (MC_composite_vlsm) s item /\
  state_round_inc (destination item i) > state_round_inc (s i).
Proof.
  unfold MC_final_state.
  rewrite <- Forall_finite.
  intros Hs Hall.
  destruct (decide (exists i, MC_initial_state_prop (s i))) as [(i & He) |].
  - destruct (size (st_obs (s i))) eqn: Hobssi.
    + exists (Build_transition_item (T := composite_type MCVLSM) (existT i init) None
        (state_update MCVLSM s i (mkSt (st_obs (s i)) (Some (mkRS 0 muddy)))) None); cbn.
      state_update_simpl; cbn.
      unfold state_round_inc.
      unfold MC_initial_state_prop in He; rewrite He.
      split; [| by lia].
      repeat split; cbn; [by apply Hs | ..].
      * by apply option_valid_message_None.
      * destruct (s i); cbn in *; subst.
        by constructor.
      * by apply MC_non_initial_valid_consistent in Hs as [].
      * by apply MC_non_initial_valid_consistent in Hs as []; set_solver.
      * by apply MC_non_initial_valid_consistent in Hs as []; set_solver.
      * destruct (s i); cbn in *; subst.
        funelim (MC_transition i init
          {| st_obs := st_obs0; st_rs := None |} None); try done.
        -- by rewrite <- Heqcall; inversion H11.
        -- by inversion H10; congruence.
    + exists (Build_transition_item (T := composite_type MCVLSM) (existT i init) None
        (state_update MCVLSM s i (mkSt (st_obs (s i)) (Some (mkRS 0 undecided)))) None); cbn.
      state_update_simpl; cbn.
      unfold state_round_inc.
      unfold MC_initial_state_prop in He; rewrite He.
      split; [| by lia].
      repeat split; cbn; [by apply Hs | ..].
      * by apply option_valid_message_None.
      * destruct (s i); cbn in *; subst.
        by constructor.
      * by apply MC_non_initial_valid_consistent in Hs as [].
      * apply MC_non_initial_valid_consistent in Hs as []; set_solver.
      * apply MC_non_initial_valid_consistent in Hs as []; set_solver.
      * destruct (s i); cbn in *; subst.
        funelim (MC_transition i init
          {| st_obs := st_obs0; st_rs := None |} None); try done.
        -- by inversion H10; congruence.
        -- by rewrite <- Heqcall; inversion H11.
  - apply not_Forall_Exists in Hall; [| by typeclasses eauto].
    apply Exists_exists in Hall as (i & _ & Hi); cbn in Hi.
    assert (Hundecided : state_status (st_rs (s i)) = undecided).
    {
      by destruct (decide (state_status (st_rs (s i)) = undecided)).
    }
    assert (Hcons : consistent s) by (apply MC_non_initial_valid_consistent; done).
    destruct (decide (exists (j : index), state_status (st_rs (s j)) = muddy))
      as [(j & He) |].
    + destruct (decide (i ∈ st_obs (s j))).
      * exists (Build_transition_item (T := composite_type MCVLSM) (existT i receive)
          (Some (mkMsg j (state_round (st_rs (s j))) muddy))
          (state_update MCVLSM s i (mkSt (st_obs (s i))
          (Some (mkRS (state_round (st_rs (s j))) muddy)))) None).
        cbn; state_update_simpl; cbn.
        unfold MC_non_initial_valid_state in Hs.
        destruct Hs as [Hvalid Hnoninitial].
        cut (input_valid_transition_item MC_composite_vlsm s
          (MC_transition_item_update s j i muddy (mkRS (state_round (st_rs (s j))) muddy))).
        {
          intros Ht.
          destruct (Ht) as [(_ & Hm & Hv & Hc) _].
          unfold MC_constraint, l, input in Hc.
          apply MC_valid_noequiv_muddy in Hc; cbn in *; [| done ..].
          destruct Hc as [Hroundj Hj].
          destruct Hcons as [Hmuddy Hobs].
          split; [done |].
          apply MC_undecided_muddy_to_muddy_increase_round in Ht; cbn in Ht |- *; try done.
          - state_update_simpl.
            unfold state_round_inc.
            by case_match; cbn in Ht; lia.
          - destruct (decide (i = j)); [by subst |].
            rewrite Hobs in *.
            by clear - Hj n e; set_solver.
          - rewrite Hroundj, MC_muddy_number_of_muddy_seen; [done.. |].
            rewrite (Hobs j) in e.
            by clear - e; set_solver.
        }
        assert (Hnoequiv : MC_no_equivocation s {|
          msg_index := j;
          msg_round := state_round (st_rs (s j));
          msg_status := muddy;
        |}).
        {
          unfold MC_no_equivocation.
          by repeat case_match; [rewrite <- H10; left; rewrite H10, <- He |].
        }
        destruct (s i) eqn: Hsi.
        destruct st_rs0; [| by contradict n; eexists; rewrite Hsi].
        destruct r as [ri sti].
        cbn in Hundecided; subst.
        repeat split; cbn; [done | | | done |].
        -- by eapply MC_valid_noequiv_valid.
        -- by rewrite Hsi; constructor.
        -- rewrite Hsi, MC_transition_equation_8.
           unfold MC_transition_clause_4.
           apply MC_composite_invariant_preservation in Hvalid.
           destruct (Hvalid j) as [| Hinvariant]; [by contradict n; eexists |].
           unfold MC_component_invariant, MC_component_invariant_helper in Hinvariant.
           rewrite He in Hinvariant.
           destruct Hinvariant as [Hroundj Hobsj].
           symmetry in Hobsj.
           apply MC_muddy_number_of_muddy_seen_iff in Hobsj as Hjmuddy; [| done].
           rewrite Hroundj, Hobsj in *.
           replace st_obs0 with (st_obs (s i)) by (rewrite Hsi; done).
           rewrite decide_True.
           ++ rewrite decide_True; [done |].
              by symmetry; apply MC_muddy_number_of_muddy_seen_iff;
                [| by apply MuddyUnion_elem in e].
           ++ destruct Hcons as [Hinit ->].
              by destruct (decide (i = j)); [subst; rewrite Hsi in He | set_solver].
      * exists (Build_transition_item (T := composite_type MCVLSM) (existT i receive)
          (Some (mkMsg j (state_round (st_rs (s j))) muddy))
          (state_update MCVLSM s i (mkSt (st_obs (s i))
          (Some (mkRS (state_round (st_rs (s j)) + 1) clean)))) None).
        cbn; state_update_simpl; cbn.
        unfold MC_non_initial_valid_state in Hs.
        destruct Hs as [Hvalid Hnoninitial].
        destruct (Hcons) as [Hmuddy Hobs].
        cut (input_valid_transition_item MC_composite_vlsm s
          (MC_transition_item_update s j i muddy (mkRS (state_round (st_rs (s j)) + 1) clean))).
        {
          intros Ht.
          destruct (Ht) as [(_ & Hm & Hv & Hc) _].
          unfold MC_constraint, l, input in Hc.
          apply MC_valid_noequiv_muddy in Hc; cbn in Hc; [| done ..].
          destruct Hc as [Hroundj Hj].
          split; [done |].
          apply MC_undecided_muddy_to_clean_increase_round in Ht; cbn; [| done.. | |].
          - cbn in Ht; state_update_simpl; cbn in Ht; unfold state_round_inc.
            by case_match; cbn in Ht; lia.
          - destruct (decide (i = j)); [by subst; rewrite He in Hundecided |].
            rewrite Hobs in *.
            by clear - Hj n n1; set_solver.
          - rewrite Hroundj, MC_clean_number_of_muddy_seen; [done .. |].
            rewrite (Hobs j) in n0.
            destruct (decide (i = j)); [by subst; congruence |].
            by clear - n0 n1; set_solver.
        }
        assert (Hnoequiv :  MC_no_equivocation s {|
          msg_index := j;
          msg_round := state_round (st_rs (s j));
          msg_status := muddy
        |}).
        {
          unfold MC_no_equivocation.
          by repeat case_match; [rewrite <- H10; left; rewrite H10, <- He |].
        }
        destruct (s i) eqn: Hsi.
        destruct st_rs0; [| by contradict n; eexists; rewrite Hsi].
        destruct r as [ri sti].
        cbn in Hundecided; subst.
        repeat split; cbn; [done | | | done |].
        -- by eapply MC_valid_noequiv_valid.
        -- by rewrite Hsi; constructor.
        -- rewrite Hsi, MC_transition_equation_8.
           unfold MC_transition_clause_4.
           apply MC_composite_invariant_preservation in Hvalid.
           destruct (Hvalid j) as [| Hinvariant]; [by contradict n; eexists |].
           unfold MC_component_invariant, MC_component_invariant_helper in Hinvariant.
           rewrite He in Hinvariant.
           destruct Hinvariant as [Hroundj Hobsj].
           symmetry in Hobsj.
           apply MC_muddy_number_of_muddy_seen_iff in Hobsj as Hjmuddy; [| done].
           rewrite Hroundj, Hobsj in *.
           replace st_obs0 with (st_obs (s i)) by (rewrite Hsi; done).
           rewrite decide_True; [rewrite decide_False; [rewrite decide_True |] |]; [done | ..].
           ++ destruct (decide (i = j)) as [-> |].
              ** by rewrite Hsi in He.
              ** rewrite Hobs in n0.
                 assert (HinotinMuddy : i ∉ MuddyUnion s) by set_solver.
                 by apply MC_clean_number_of_muddy_seen in HinotinMuddy; [rewrite HinotinMuddy |].
           ++ destruct (decide (i = j)) as [-> |].
              ** by rewrite Hsi in He.
              ** rewrite Hobs in n0.
                 assert (HinotinMuddy : i ∉ MuddyUnion s) by set_solver.
                 apply MC_clean_number_of_muddy_seen in HinotinMuddy; [| done].
                 by destruct (decide (size (MuddyUnion s) = 0)); [apply size_empty_iff in e | lia].
           ++ rewrite Hobs.
              destruct (decide (i = j)) as [-> |].
              ** by rewrite Hsi in He.
              ** by set_solver.
    + destruct Hcons as [Hmuddy Hobs].
      assert (exists (j : index), j ∈ MuddyUnion s) as (j & Hjmuddyunion)
        by (apply set_choose in Hmuddy; done).
      unfold MC_non_initial_valid_state in Hs.
      destruct Hs as [Hvalid Hnoninit].
      pose proof Hvalid as Hvalid'.
      apply MC_composite_invariant_preservation_inductive in Hvalid'.
      assert (exists (k : index), k ∈ st_obs (s j)) as (k & Hkobs).
      {
        apply set_choose, size_non_empty_iff.
        destruct (Hvalid' j) as [| Hinvariant]; [by contradiction n; eexists |].
        inversion Hinvariant; [by lia | | by contradict n0; eexists].
        apply MC_muddy_number_of_muddy_seen in Hjmuddyunion; [| done].
        by apply size_non_empty_iff in Hmuddy; lia.
      }
      assert (Hkundecided : state_status (st_rs (s k)) = undecided).
      {
        destruct (Hvalid' k) as [| Hinvariantk]; [by contradict n; eexists |].
        unfold MC_component_invariant in Hinvariantk.
        inversion Hinvariantk; [done | | by contradict n0; eexists].
        apply MuddyUnion_elem, MC_muddy_number_of_muddy_seen in Hkobs; [| done].
        rewrite Hkobs in H11.
        by apply size_non_empty_iff in Hmuddy; lia.
      }
      assert (Hkinvariant : state_round (st_rs (s k)) < size (st_obs (s k))).
      {
        destruct (Hvalid' k) as [| Hkinvariant]; [by contradict n; eexists |].
        inversion Hkinvariant; [done | | by contradict n0; eexists].
        apply MuddyUnion_elem, MC_muddy_number_of_muddy_seen in Hkobs; [| done].
        by rewrite Hkobs in H11; apply size_non_empty_iff in Hmuddy; lia.
      }
      assert (Hjundecided : state_status (st_rs (s j)) = undecided).
      {
        destruct (Hvalid' j) as [| Hinvariantj]; [by contradict n; eexists |].
        unfold MC_component_invariant in Hinvariantj.
        inversion Hinvariantj; [done | | by contradict n0; eexists].
        apply MC_muddy_number_of_muddy_seen in Hjmuddyunion; [| done].
        rewrite Hjmuddyunion in H11.
        by apply size_non_empty_iff in Hmuddy; lia.
      }
      assert (Hjinvariant : state_round (st_rs (s j)) < size (st_obs (s j))).
      {
        destruct (Hvalid' j) as [| Hjinvariant]; [by contradict n; eexists |].
        inversion Hjinvariant; [done | | by contradict n0; eexists].
        apply MC_muddy_number_of_muddy_seen in Hjmuddyunion; [| done].
        by rewrite Hjmuddyunion in H11; apply size_non_empty_iff in Hmuddy; lia.
      }
      assert (Hjk_eq_size_muddy : size (st_obs (s j)) = size (st_obs (s k))).
      {
        apply MC_muddy_number_of_muddy_seen in Hjmuddyunion; [| done].
        apply MuddyUnion_elem, MC_muddy_number_of_muddy_seen in Hkobs; [| done].
        by rewrite <- Hjmuddyunion in Hkobs.
      }
      assert (Hjobs : j ∈ st_obs (s k)).
      {
        rewrite Hobs.
        destruct (decide (j = k)) as [-> |]; [| set_solver].
        by rewrite Hobs in Hkobs; set_solver.
      }
      destruct (decide (state_round (st_rs (s j)) < state_round (st_rs (s k)))).
      * destruct (decide (state_round (st_rs (s k)) = size (st_obs (s j)) - 1))
          as [Heqobsminus1 | Hneqobsminus1].
        -- exists (Build_transition_item (T := composite_type MCVLSM) (existT j receive)
             (Some (mkMsg k (state_round (st_rs (s k))) undecided))
             (state_update MCVLSM s j (mkSt (st_obs (s j))
             (Some (mkRS (state_round (st_rs (s k)) + 1) muddy)))) None).
           cbn; state_update_simpl; cbn.
           cut (input_valid_transition_item MC_composite_vlsm s
             (MC_transition_item_update s k j undecided
             (mkRS (state_round (st_rs (s k)) + 1) muddy))).
           {
             intro Ht; destruct (id Ht) as [(_ & Hm & Hv & Hc) _].
             unfold MC_constraint, input in Hc.
             apply MC_valid_noequiv_valid in Hc; [| done..].
             cbn in Hc; destruct Hc as [Hroundk Hk].
             split; [done |].
             apply MC_undecided_undecided_to_muddy_increase_round in Ht; try done.
             cbn in Ht; state_update_simpl; cbn in Ht; unfold state_round_inc.
             case_match; [| by lia].
             remember (state_round (st_rs (s k))) as roundk; unfold state_round in Ht.
             by cbn in Ht; lia.
           }
           assert (Hnoequiv :  MC_no_equivocation s
            (mkMsg k (state_round (st_rs (s k))) undecided)).
           {
             by unfold MC_no_equivocation; repeat case_match;
               cbn in *; [left; split | lia].
           }
           pose proof Hjundecided as Hjundecided'.
           destruct (s j) eqn: Hsj in Hjundecided'.
           destruct st_rs0; [| by contradict n; eexists; rewrite Hsj].
           destruct r as [rj stj].
           repeat split; only 1,4: done; cbn;
             [by eapply MC_valid_noequiv_valid | by rewrite Hsj; constructor |].
           pose proof Hjundecided as Hjundecided''.
           rewrite Hsj; rewrite Hsj in Hjundecided; cbn in Hjundecided; rewrite Hjundecided.
           rewrite MC_transition_equation_7. unfold MC_transition_clause_5.
           replace st_obs0 with (st_obs (s j)); [| by rewrite Hsj];
             replace rj with (state_round (st_rs (s j))); [| by rewrite Hsj].
           by rewrite decide_True, decide_False, decide_False, decide_True; [| lia .. |].
        -- exists (Build_transition_item (T := composite_type MCVLSM) (existT j receive)
             (Some (mkMsg k (state_round (st_rs (s k))) undecided))
             (state_update MCVLSM s j (mkSt (st_obs (s j))
             (Some (mkRS (state_round (st_rs (s k)) + 1) undecided)))) None).
           cbn; state_update_simpl; cbn.
           cut (input_valid_transition_item MC_composite_vlsm s
             (MC_transition_item_update s k j undecided
             (mkRS (state_round (st_rs (s k)) + 1) undecided))).
           {
             intro Ht; destruct (id Ht) as [(_ & Hm & Hv & Hc) _].
             unfold MC_constraint, input in Hc.
             apply MC_valid_noequiv_valid in Hc; [| done..].
             cbn in Hc; destruct Hc as [Hroundk Hk].
             split; [done |].
             apply MC_undecided_undecided_increase_round in Ht; try done.
             - cbn in Ht; state_update_simpl; cbn in Ht;
                 unfold state_round_inc; case_match; [| by lia].
               remember (state_round (st_rs (s k))) as roundk.
               unfold state_round in Ht.
               by cbn in Ht; lia.
             - cbn in *. split; [lia |].
               apply MC_composite_invariant_preservation in Hvalid.
               by rewrite Hjk_eq_size_muddy; lia.
           }
           assert (Hnoequiv :  MC_no_equivocation s
             (mkMsg k (state_round (st_rs (s k))) undecided)).
           {
             by unfold MC_no_equivocation; repeat case_match; [left | cbn in *; lia].
           }
           pose proof Hjundecided as Hjundecided'.
           destruct (s j) eqn: Hsj in Hjundecided'.
           destruct st_rs0; [| by contradict n; eexists; rewrite Hsj].
           destruct r as [rj stj].
           repeat split; only 1,4: done; cbn;
             [by eapply MC_valid_noequiv_valid | rewrite Hsj; constructor |].
           pose proof Hjundecided as Hjundecided''.
           rewrite Hsj; rewrite Hsj in Hjundecided; cbn in Hjundecided; rewrite Hjundecided.
           rewrite MC_transition_equation_7. unfold MC_transition_clause_5.
           replace st_obs0 with (st_obs (s j)); [| by rewrite Hsj];
             replace rj with (state_round (st_rs (s j))); [| by rewrite Hsj].
           by rewrite decide_True, decide_False, decide_True; [| lia.. |].
      * destruct (decide (state_round (st_rs (s j)) = size (st_obs (s k)) - 1)).
        -- exists (Build_transition_item (T := composite_type MCVLSM) (existT k receive)
             (Some (mkMsg j (state_round (st_rs (s j))) undecided))
             (state_update MCVLSM s k (mkSt (st_obs (s k))
             (Some (mkRS (state_round (st_rs (s j)) + 1) muddy)))) None).
           cbn; state_update_simpl; cbn.
           cut (input_valid_transition_item MC_composite_vlsm s
             (MC_transition_item_update s j k undecided
             (mkRS (state_round (st_rs (s j)) + 1) muddy))).
           {
             intros Ht.
             destruct (Ht) as [(_ & Hm & Hv & Hc) _].
             unfold MC_constraint, input in Hc.
             apply MC_valid_noequiv_valid in Hc; cbn in Hc; [| done..].
             destruct Hc as [Hroundj Hj].
             split; [done |].
             apply MC_undecided_undecided_to_muddy_increase_round in Ht; [| done..].
             cbn in Ht; state_update_simpl; cbn in Ht.
             unfold state_round_inc.
             by case_match; cbn in Ht; lia.
           }
           assert (Hnoequiv :  MC_no_equivocation s
             (mkMsg j (state_round (st_rs (s j))) undecided)).
           {
             by unfold MC_no_equivocation; repeat case_match; cbn in *;
               [left | contradict n; eexists; rewrite H10].
           }
           pose proof (Hkundecided' := Hkundecided).
           destruct (s k) eqn: Hsk in Hkundecided'.
           destruct st_rs0; [| by contradict n; eexists; rewrite Hsk].
           destruct r as [rk stk].
           repeat split; cbn; [done | | | done |].
           ++ by eapply MC_valid_noequiv_valid.
           ++ by rewrite Hsk; constructor.
           ++ pose proof (Hkundecided'' := Hkundecided').
              rewrite Hsk in Hkundecided |- *; cbn in Hkundecided; rewrite Hkundecided.
              rewrite MC_transition_equation_7.
              unfold MC_transition_clause_5.
              replace st_obs0 with (st_obs (s k)); [| by rewrite Hsk].
              replace rk with (state_round (st_rs (s k))); [| by rewrite Hsk].
              by rewrite decide_True, decide_False, decide_False, decide_True; [| | lia.. |].
        -- exists (Build_transition_item (T := composite_type MCVLSM) (existT k receive)
             (Some (mkMsg j (state_round (st_rs (s j))) undecided))
             (state_update MCVLSM s k (mkSt (st_obs (s k))
             (Some (mkRS (state_round (st_rs (s j)) + 1) undecided)))) None).
           cbn; state_update_simpl; cbn.
           cut (input_valid_transition_item MC_composite_vlsm s
             (MC_transition_item_update s j k undecided
             (mkRS (state_round (st_rs (s j)) + 1) undecided))).
           {
             intros Ht.
             destruct (Ht) as [(_ & Hm & Hv & Hc) _].
             unfold MC_constraint, input in Hc.
             apply MC_valid_noequiv_valid in Hc; cbn in Hc; [| done..].
             destruct Hc as [Hroundj Hj].
             split; [done |].
             apply MC_undecided_undecided_increase_round in Ht;
               [| done.. | by cbn in *; lia].
             unfold state_round_inc.
             cbn in Ht; state_update_simpl; cbn in Ht.
             by case_match; cbn in Ht; lia.
           }
           assert (Hnoequiv :  MC_no_equivocation s
             (mkMsg j (state_round (st_rs (s j))) undecided)).
           {
             unfold MC_no_equivocation; repeat case_match; cbn in n1.
             - by rewrite <- H10; left; rewrite H10.
             - by contradict n; eexists; rewrite H10.
           }
           pose proof (Hkundecided' := Hkundecided).
           destruct (s k) eqn: Hsk in Hkundecided'.
           destruct st_rs0; [| by contradict n; eexists; rewrite Hsk].
           destruct r as [rk stk].
           repeat split; cbn; [done | | | done |].
           ++ by eapply MC_valid_noequiv_valid.
           ++ by rewrite Hsk; constructor.
           ++ pose proof (Hjundecided' := Hjundecided).
              rewrite Hsk in Hkundecided |- *; cbn in Hkundecided; rewrite Hkundecided.
              rewrite MC_transition_equation_7.
              unfold MC_transition_clause_5.
              replace st_obs0 with (st_obs (s k)); [| by rewrite Hsk].
              replace rk with (state_round (st_rs (s k))); [| by rewrite Hsk].
              by rewrite decide_True, decide_False, decide_True; [| lia.. |].
Qed.

(** ** Safety *)

Lemma MC_round_bound (s : composite_state MCVLSM) :
  valid_state_prop MC_composite_vlsm s ->
  forall (i : index), state_round_inc (s i) <= size (st_obs (s i)) + 1.
Proof.
  intros Hvalid i.
  apply MC_composite_invariant_preservation in Hvalid.
  unfold MC_composite_invariant in Hvalid.
  unfold state_round_inc.
  destruct (Hvalid i) as [Hinit | Hinv].
  - cbn in Hinit; unfold MC_initial_state_prop in Hinit.
    rewrite Hinit.
    by lia.
  - unfold MC_component_invariant, MC_component_invariant_helper in Hinv.
    destruct (st_rs (s i)) as [[round status] |]; cbn in *; [| by lia].
    by destruct status; lia.
Qed.

Definition steps_until_final_component (s : State) : nat :=
  size (st_obs s) + 1 - state_round_inc s.

Definition steps_until_final_composite (s : composite_state MCVLSM) : nat :=
  sum_list_with (fun i => steps_until_final_component (s i)) (enum index).

(**
  The main result states that, from any non-initial valid state,
  there is a trace to a final state.
*)
Theorem MC_safety (Hindex : length (enum index) > 1) (s : composite_state MCVLSM) :
  MC_non_initial_valid_state s ->
  exists (tr : list (composite_transition_item MCVLSM)) (sf : composite_state MCVLSM),
  finite_valid_trace_from_to MC_composite_vlsm s sf tr /\ MC_final_state sf.
Proof.
  remember (steps_until_final_composite s) as nr_steps.
  revert s Heqnr_steps.
  induction nr_steps as [nr_steps Hind] using (well_founded_induction Wf_nat.lt_wf).
  intros ? ? Hnoninitvalid.
  destruct (decide (MC_final_state s));
    [by exists [], s; constructor; [constructor; apply Hnoninitvalid |] |].
  pose proof (Hrounds := MC_round_bound s (proj1 Hnoninitvalid)).
  apply MC_progress in Hnoninitvalid as Hprogress; [| done..].
  destruct Hprogress as (item & Hitem & Hround).
  apply input_valid_transition_destination in Hitem as Hdest.
  pose proof (Hrounddest := MC_round_bound (destination item) Hdest).
  assert (Hdestvalid : MC_non_initial_valid_state (destination item)).
  {
    destruct item, l; cbn in *.
    split; [done |].
    intros Hinit.
    specialize (Hinit x).
    cbn in Hinit; unfold MC_initial_state_prop in Hinit.
    destruct (destination x); cbn in *.
    unfold state_round_inc in Hround; cbn in Hround; subst.
    by lia.
  }
  eapply Hind in Hdestvalid; [.. | done].
  {
    destruct Hdestvalid as (tr & sf & Htr & Hsf).
    by exists (item :: tr), sf; split; [destruct item; constructor |].
  }
  destruct item, l; cbn in *.
  destruct Hitem as [Hv Ht].
  unfold transition in Ht.
  apply MC_trans_preserves_obs_equiv in Ht as Hobs; cbn in *.
  destruct (MC_transition x l (s x)) eqn: Htx.
  inversion Ht; subst.
  state_update_simpl.
  clear - Hround Hobs Hrounds Hrounddest.
  unfold steps_until_final_composite.
  assert (Hxelem : x ∈ enum index) by apply elem_of_enum.
  pose proof (Hnodup := NoDup_enum index).
  revert Hxelem Hnodup.
  generalize (enum index) as is.
  induction is; [by inversion 1 |].
  rewrite elem_of_cons, NoDup_cons; cbn.
  intros [-> | Hx] [Ha Hnodup]; cycle 1.
  - rewrite state_update_neq; [| by set_solver].
    specialize (IHis Hx Hnodup).
    by lia.
  - specialize (Hobs a).
    specialize (Hrounds a).
    specialize (Hrounddest a).
    state_update_simpl.
    cut (sum_list_with (fun i => steps_until_final_component (state_update MCVLSM s a s0 i)) is =
      sum_list_with (fun i => steps_until_final_component (s i)) is).
    {
      intros ->.
      unfold steps_until_final_component in *.
      by destruct s0 as (obs0 & [[round0 status0] |]),
        (s a) as (obsa & [[rounda statusa] |]);
        cbn in *; rewrite Hobs; lia.
    }
    clear IHis Hnodup.
    revert Ha.
    induction is; cbn; [done |].
    rewrite not_elem_of_cons.
    intros [Hdiff Hnotelem].
    by rewrite IHis; [state_update_simpl |].
Qed.

(**
  This corollary states that final states are reachable from initial consistent states.
  This is weaker then the [MC_safety] result, and is proved using it.
*)
Corollary MC_safety_initial
  (Hindex : length (enum index) > 1) (s : composite_state MCVLSM) (i : index):
  composite_initial_state_prop MCVLSM s ->
  consistent s ->
  exists (tr : list (composite_transition_item MCVLSM))
    (sf : composite_state MCVLSM),
  finite_valid_trace_init_to MC_composite_vlsm s sf tr /\ MC_final_state sf.
Proof.
  intros Hinit [Hnempty Hcons].
  unfold composite_initial_state_prop in Hinit; cbn in Hinit.
  assert (Hsi : s i = mkSt (st_obs (s i)) None).
  {
    destruct (s i) eqn: Hsi.
    unfold MC_initial_state_prop in Hinit; cbn.
    replace st_rs0 with (st_rs (s i)); [| by rewrite Hsi].
    by rewrite Hinit.
  }
  destruct (decide (size (st_obs (s i)) = 0)).
  - remember (Build_transition_item (T := composite_type MCVLSM)
      (existT i init) None (state_update MCVLSM s i (mkSt (st_obs (s i))
      (Some (mkRS 0 muddy)))) None) as item.
    assert (Hvalidtr : input_valid_transition MC_composite_vlsm (existT i init) (s, None)
      (state_update MCVLSM s i {| st_obs := st_obs (s i); st_rs := Some (mkRS 0 muddy) |},
      None)).
    {
      repeat split; cbn; [| | | done | by rewrite Hcons.. |].
      - by apply initial_state_is_valid.
      - by apply option_valid_message_None.
      - by rewrite Hsi; constructor.
      - rewrite Hsi, MC_transition_equation_3.
        unfold MC_transition_clause_1; cbn.
        by rewrite e.
    }
    assert (Hvalids' : MC_non_initial_valid_state (state_update MCVLSM s i
      {| st_obs := st_obs (s i); st_rs := Some (mkRS 0 muddy) |})).
    {
      split.
      - eapply (@valid_trace_last_pstate _ (@finite_valid_trace_init_to));
          [by typeclasses eauto |].
        split; [| by cbn; red; apply Hinit].
        rewrite Heqitem.
        by eapply finite_valid_trace_from_to_singleton.
      - intros Hinits'.
        apply Forall_finite in Hinits'.
        contradict Hinits'.
        apply Exists_not_Forall, Exists_exists.
        exists i; split; [by apply elem_of_enum |].
        by cbn; state_update_simpl.
    }
    apply MC_safety in Hvalids'; [| done].
    destruct Hvalids' as (tr & sf & Htr & Hsf).
    exists ([item] ++ tr), sf.
    do 2 (split; [| done]).
    eapply finite_valid_trace_from_to_app; [| done].
    rewrite Heqitem.
    by apply finite_valid_trace_from_to_singleton.
  - remember (Build_transition_item (T := composite_type MCVLSM)
      (existT i init) None (state_update MCVLSM s i (mkSt (st_obs (s i))
      (Some (mkRS 0 undecided)))) None) as item.
    assert (Hvalidtr : input_valid_transition MC_composite_vlsm (existT i init) (s, None)
      (state_update MCVLSM s i {| st_obs := st_obs (s i); st_rs := Some (mkRS 0 undecided) |},
      None)).
    {
      repeat split; cbn; [| | | done | by rewrite Hcons.. |].
      - by apply initial_state_is_valid.
      - by apply option_valid_message_None.
      - by rewrite Hsi; constructor.
      - rewrite Hsi, MC_transition_equation_3.
        unfold MC_transition_clause_1; cbn.
        repeat case_match; [lia |].
        by inversion H9.
    }
    assert (Hvalids' : MC_non_initial_valid_state (state_update MCVLSM s i
      {| st_obs := st_obs (s i); st_rs := Some (mkRS 0 undecided) |})).
    {
      split.
      - eapply (@valid_trace_last_pstate _ (@finite_valid_trace_init_to));
          [by typeclasses eauto |].
        split; [| by cbn; red; apply Hinit].
        rewrite Heqitem.
        by eapply finite_valid_trace_from_to_singleton.
      - intros Hinits'.
        apply Forall_finite in Hinits'.
        contradict Hinits'.
        apply Exists_not_Forall, Exists_exists.
        exists i; split; [by apply elem_of_enum |].
        by cbn; state_update_simpl.
    }
    apply MC_safety in Hvalids'; [| done].
    destruct Hvalids' as (tr & sf & Htr & Hsf).
    exists ([item] ++ tr), sf.
    do 2 (split; [| done]).
    eapply finite_valid_trace_from_to_app; [| done].
    rewrite Heqitem.
    by apply finite_valid_trace_from_to_singleton.
Qed.

End sec_muddy.
