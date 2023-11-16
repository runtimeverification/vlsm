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

Definition MC_initial_state_prop (s : State) : Prop := st_rs s = None.

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
    by intro x; split; [| done]; intros Hx; apply Hx; apply elem_of_enum.
  - by typeclasses eauto.
Qed.

Definition MuddyUnion (s : composite_state MCVLSM) : indexSet :=
  ⋃ (map (fun i => st_obs (s i)) (enum index)).

Lemma MuddyUnion_elem (s : composite_state MCVLSM) (i j : index) :
  i ∈ st_obs (s j) -> i ∈ MuddyUnion s.
Proof.
  intros Hobs; apply elem_of_union_list; exists (st_obs (s j)); split; [| done].
  apply elem_of_list_fmap. exists j. by split; [| by apply elem_of_enum].
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
  split; destruct m; simpl.
  - destruct (s msg_index0) eqn:?; destruct st_rs0; simpl; [|done].
    destruct r; intros [[Hs Hr]|[Hs Hr]].
    + by subst; eapply MC_no_equivocation_inductive_msg_eq; eauto.
    + by subst; eapply MC_no_equivocation_inductive_undecided; eauto.
  - destruct (s msg_index0) eqn:?; destruct st_rs0 eqn:?.
    + by destruct r; intros Hne; inversion Hne; subst; itauto congruence.
    + by intros Hne; subst; inversion Hne; subst; itauto congruence.
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
  - unfold MuddyUnion. rewrite empty_union_list, Forall_forall.
    unfold MuddyUnion in Hnempty.
    rewrite empty_union_list, Forall_forall in Hnempty.
    contradict Hnempty. intros x Hx.
    apply elem_of_list_fmap in Hx as (j & -> & _).
    unfold MC_obs_equivalence in Hobs. rewrite Hobs.
    apply Hnempty. apply elem_of_list_fmap. exists j.
    by split; [| apply elem_of_enum].
  - intros j x. rewrite <- MC_obs_equiv_preserves_muddy by done.
    unfold MC_obs_equivalence in Hobs.
    by rewrite <- Hobs; apply Hcons.
Qed.

Lemma MC_trans_preserves_obs_equiv (s : composite_state MCVLSM) :
  forall (l : composite_label MCVLSM) (s' : composite_state MCVLSM) (m m' : option Message),
  composite_transition (MCVLSM) l (s, m) = (s', m') -> MC_obs_equivalence s s'.
Proof.
  intros; unfold composite_transition in H9.
  destruct l as [i li]; destruct transition eqn: Htrans;
    cbn in Htrans; inversion H9; subst; clear H9.
  apply MC_state_update_preserves_obs_equiv.
  destruct s0, (s i).
  revert Htrans.
  by apply FunctionalElimination_MC_transition; intros; inversion Htrans;
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
  split.
  - intros [Hnempty Hconss].
    split.
    + by apply MC_in_futures_preserves_muddy in Hfutures; rewrite <- Hfutures.
    + pose proof Hfutures as Hfutures'.
      apply MC_in_futures_preserves_obs_equiv in Hfutures.
      unfold MC_obs_equivalence in Hfutures. setoid_rewrite <- Hfutures.
      apply MC_in_futures_preserves_muddy in Hfutures'.
      by setoid_rewrite <- Hfutures'.
  - intros [Hnempty Hconss'].
    split.
    + by apply MC_in_futures_preserves_muddy in Hfutures; rewrite Hfutures.
    + pose proof Hfutures as Hfutures'.
      apply MC_in_futures_preserves_obs_equiv in Hfutures.
      unfold MC_obs_equivalence in Hfutures. setoid_rewrite Hfutures.
      apply MC_in_futures_preserves_muddy in Hfutures'.
      by setoid_rewrite Hfutures'.
Qed.

Lemma MC_non_initial_valid_consistent :
  forall (s : composite_state MCVLSM), MC_non_initial_valid_state s -> consistent s.
Proof.
  intros s [Hvalid Hnon_initial].
  induction Hvalid using valid_state_prop_ind; [done|].
  destruct Ht as [(_ & _ & Hv & Hc) Ht];
    destruct (decide (composite_initial_state_prop MCVLSM s)).
  - destruct l as [i []]; simpl in Hv.
    + eapply MC_obs_equiv_preserves_consistency; [| done].
      by eapply MC_trans_preserves_obs_equiv with (s := s)
        (l := existT i init) (m := om) (m' := om').
    + by inversion Hv; specialize (c i); rewrite <- H9 in c.
    + by inversion Hv; specialize (c i); rewrite <- H9 in c.
  - eapply MC_obs_equiv_preserves_consistency; [| by apply IHHvalid].
    by apply MC_trans_preserves_obs_equiv with (s := s)
      (l := l) (m := om) (m' := om').
Qed.

Lemma MC_muddy_number_of_muddy_seen (s : composite_state MCVLSM) (j : index) :
  consistent s ->
  j ∈ MuddyUnion s ->
  size (st_obs (s j)) = size (MuddyUnion s) - 1.
Proof.
  intros [Hnempty Hn]; intro n.
  by rewrite Hn, size_difference;
    [rewrite size_singleton | rewrite singleton_subseteq_l].
Qed.

Lemma MC_muddy_number_of_muddy_seen_iff (s : composite_state MCVLSM) (j : index) :
  consistent s ->
  j ∈ MuddyUnion s <-> size (st_obs (s j)) = size (MuddyUnion s) - 1.
Proof.
  split; [by apply MC_muddy_number_of_muddy_seen |].
  destruct H9 as [Hnempty Hn].
  intros Hsize.
  rewrite Hn, size_difference_alt in Hsize.
  destruct (decide (size (MuddyUnion s) = 0));
    [by apply size_non_empty_iff in Hnempty|].
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
  intros [Hnempty Hn]; intro n.
  rewrite Hn, size_difference_alt.
  replace (size (MuddyUnion s ∩ {[j]})) with 0; [lia |].
  by symmetry; apply size_empty_iff; set_solver.
Qed.

Lemma MC_clean_number_of_muddy_seen_iff (s : composite_state MCVLSM) (j : index) :
  consistent s ->
  j ∉ MuddyUnion s <-> size (st_obs (s j)) = size (MuddyUnion s).
Proof.
  split; [by apply MC_clean_number_of_muddy_seen |].
  destruct H9 as [Hnempty Hn].
  intros Hsize.
  rewrite Hn, size_difference_alt in Hsize.
  destruct (decide (size (MuddyUnion s) = 0)).
  - by apply size_non_empty_iff in Hnempty.
  - cut (size (MuddyUnion s ∩ {[j]}) = 0).
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
  intros Hcons n; destruct (decide (n ∈ MuddyUnion s)).
  - by apply MC_muddy_number_of_muddy_seen in e; [rewrite e; lia |].
  - by apply MC_clean_number_of_muddy_seen in n0; [rewrite n0; lia |].
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
  by intros; rewrite H9, H10; simpl; rewrite MC_transition_equation_9;
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
  by intros; rewrite H9, H10; simpl; rewrite MC_transition_equation_9;
    unfold MC_transition_clause_3; repeat case_decide; try itauto; lia.
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
  by intros; rewrite H9, H10; simpl; rewrite MC_transition_equation_8;
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
  intros; rewrite H9, H10; simpl; rewrite MC_transition_equation_8;
   unfold MC_transition_clause_4; repeat case_decide; try itauto.
  by destruct (decide (size (st_obs s) = 0));
   [apply non_empty_inhabited, size_non_empty_iff in H11 | lia].
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
  by intros; rewrite H9, H10; simpl; rewrite MC_transition_equation_7;
    unfold MC_transition_clause_5; repeat case_decide; try itauto; lia.
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
  by intros; rewrite H9, H10; simpl; rewrite MC_transition_equation_7;
    unfold MC_transition_clause_5; repeat case_decide; try itauto; lia.
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
  by intros; rewrite H9, H10; simpl; rewrite MC_transition_equation_7;
    unfold MC_transition_clause_5; repeat case_decide; try itauto; lia.
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
  intros s i; unfold MC_component_invariant, MC_component_invariant_helper.
  case_match; split.
  - by intros; apply component_invariant_undecided in H9.
  - by intros; inversion H10; [| rewrite H11 in H9..].
  - by intros; apply component_invariant_muddy in H9; destruct H10.
  - by intros; inversion H10; split; rewrite H11 in H9.
  - by intros; apply component_invariant_clean in H9; destruct H10.
  - by intros; inversion H10; split; rewrite H11 in H9.
Qed.

Definition MC_composite_invariant (s : composite_state MCVLSM) : Prop :=
  forall i, initial_state_prop (MCVLSM i) (s i) \/ MC_component_invariant s i.

Definition MC_composite_invariant_inductive (s : composite_state MCVLSM) : Prop :=
  forall i, initial_state_prop (MCVLSM i) (s i) \/ MC_component_invariant_inductive s i.

Lemma MC_composite_invariant_preservation_muddy_from_undecided
  (s sm : composite_state MCVLSM) (i j : index) (o : indexSet) :
  o ≡ st_obs (s i) ->
  j ∈ o -> consistent s ->
  (forall k, st_obs (sm k) ≡ st_obs (s k)) ->
  size o - 1 < size (st_obs (sm j)) ->
  size (MuddyUnion s) - 1 = size o.
Proof.
  intros Heqo Hin Hconsistent Hobs_equiv Hinvs.
  destruct (id Hconsistent) as [_ Hcons]. rewrite Heqo in *.
  clear o Heqo.
  remember (size (st_obs (s i))) as o.
  rewrite Hobs_equiv, Hcons, size_difference in Hinvs; cycle 1.
  - apply singleton_subseteq_l; unfold MuddyUnion; rewrite elem_of_union_list.
    exists (st_obs (s i)); split; [| done].
    by apply elem_of_list_fmap; exists i; split; [| apply elem_of_enum].
  - rewrite size_singleton in Hinvs.
    apply MC_number_of_muddy_seen with (n := i) in Hconsistent.
    by destruct Hconsistent; lia.
Qed.

Lemma MC_composite_invariant_preservation_muddy_from_clean (s sm : composite_state MCVLSM)
  (i j : index) (o : indexSet) :
  o ≡ st_obs (s i) -> j ∉ o -> consistent s ->
  (forall k, st_obs (sm k) ≡ st_obs (s k)) ->
  size o < size (st_obs (sm j)) ->
  size (MuddyUnion s) - 1 = size o.
Proof.
  intros Heqo Hin Hconsistent Hobs_equiv Hinvs.
  destruct (id Hconsistent) as [_ Hcons].
  rewrite Heqo in *.
  clear o Heqo.
  rewrite Hobs_equiv in Hinvs.
  destruct (decide (i = j)); [by subst; lia |].
  remember (size (st_obs (s i))) as o.
  rewrite  Hcons, size_difference_alt in Hinvs.
  replace (size (MuddyUnion s ∩ {[j]})) with 0 in Hinvs.
  - by apply MC_number_of_muddy_seen with (n := i) in Hconsistent as [? ?]; lia.
  - symmetry; apply size_empty_iff.
    by rewrite Hcons in Hin; set_solver.
Qed.

Lemma non_initial_state_has_init_tr (is s : composite_state MCVLSM)
  (tr : list (composite_transition_item MCVLSM)) :
  finite_valid_trace_init_to MC_composite_vlsm is s tr -> forall (i : index),
  ~ MC_initial_state_prop (s i) ->
  exists (item : composite_transition_item MCVLSM), item ∈ tr /\ projT2 (l item) = init.
Proof.
  intros Htr i Hnoninit. induction Htr using finite_valid_trace_init_to_rev_ind;
    [by contradiction Hnoninit; apply Hsi |].
  destruct (decide (MC_initial_state_prop (s i))).
  - destruct Ht as [(_ & _ & Hv & _) Ht], l as (j & lj); cbn in Ht, Hv.
    destruct MC_transition as (si', om') eqn: Htj.
    inversion Ht; subst; clear Ht.
    destruct (decide (i = j)); subst; state_update_simpl; [| done].
    unfold MC_initial_state_prop in m. destruct (s j). cbn in *.
    subst. inversion Hv. subst.
    eexists. rewrite elem_of_app, elem_of_list_singleton.
    by itauto.
  - destruct (IHHtr n) as (item & Hitem & Hinit).
    by exists item; rewrite elem_of_app; itauto.
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
  intros. apply valid_state_has_trace in H9 as (is & tr & Htr).
  remember (length tr) as len_tr.
  revert s tr Heqlen_tr Htr.
  induction len_tr as [len_tr Hind] using (well_founded_induction Wf_nat.lt_wf). intros.
  subst len_tr.
  destruct_list_last tr tr' lst Htr_lst;
    [by destruct Htr as [Htr Hinit]; inversion Htr; subst; left |].
  intro i; destruct Htr as [Htr Hinit].
  apply finite_valid_trace_from_to_app_split in Htr as [Htr' Hlst].
  remember (finite_trace_last is tr') as s'.
  assert (Hinvs : MC_composite_invariant s').
  {
    eapply Hind; cycle 2; [by split | | done].
    by rewrite app_length; cbn; lia.
  }
  apply valid_trace_get_last in Hlst as Heqs.
  apply valid_trace_forget_last, first_transition_valid in Hlst.
  cbn in Heqs, Hlst. rewrite Heqs in Hlst. destruct lst. cbn in *.
  assert (HMuddyUnion : size (MuddyUnion s) = size (MuddyUnion s')).
  {
    symmetry. apply set_size_proper. apply MC_obs_equiv_preserves_muddy.
    apply MC_trans_preserves_obs_equiv with l input output.
    by apply Hlst.
  }
  unfold MC_component_invariant, MC_component_invariant_helper. rewrite HMuddyUnion.
  destruct l as [j lj]. destruct Hlst as [(_ & _ & Hv & Hc) Ht]. cbn in Ht.
  destruct MC_transition eqn: Htj.
  inversion Ht as [Hdest]; subst s o.
  destruct (decide (j = i)); [subst j |]; state_update_simpl; [| by apply (Hinvs i)].
  clear - Htr' Hinit Hdest Hv Hc Htj Hinvs Hind.
  right.
  pose proof (Hinvs' := Hinvs).
  specialize (Hinvs i).
  funelim (MC_transition i lj (s' i) input);
  inversion Hv; try by congruence.
  - (* emit *)
    rewrite <- H10 in H0; inversion H0; subst; clear H0; rewrite Htj in Heqcall.
    inversion Heqcall; subst; cbn in *.
    clear Heqcall Htj; unfold MC_component_invariant in Hinvs; rewrite <- H10 in Hinvs.
    by cbn in Hinvs; destruct Hinvs.
  - (* receive *)
    rewrite <- H10 in H0; inversion H0; subst; clear H0; rewrite Htj in Heqcall.
    inversion Heqcall; subst; cbn in *.
    clear Heqcall Htj; unfold MC_component_invariant in Hinvs; rewrite <- H10 in Hinvs.
    by cbn in Hinvs; destruct Hinvs.
  - (* receive *)
    rewrite <- H10 in H0; inversion H0; subst; clear H0; rewrite Htj in Heqcall.
    inversion Heqcall; subst; cbn in *.
    clear Heqcall Htj; unfold MC_component_invariant in Hinvs; rewrite <- H10 in Hinvs.
    by cbn in Hinvs; destruct Hinvs.
  - (* init *)
    rewrite <- H10 in H0; inversion H0; subst; clear H0; rewrite Htj in Heqcall.
    inversion Heqcall.
    inversion Heqcall; subst; cbn in *.
    clear Heqcall Htj Hinvs; split; [done |]. destruct Hc as [Hunion Hc].
    specialize (Hc i); rewrite <- H10 in Hc.
    cbn in Hc; rewrite Hc; rewrite size_difference, size_singleton; [done |].
    apply singleton_subseteq_l.
    by apply size_empty_iff in Heq; rewrite Heq in Hc; set_solver.
  - (* init *)
    rewrite <- H10 in H0; inversion H0; subst; clear H0; rewrite Htj in Heqcall.
    by inversion Heqcall; subst; cbn in *; lia.
  - (* receive *)
    rewrite <- H10 in H0; inversion H0; subst; clear H0; rewrite Htj in Heqcall.
    unfold MC_component_invariant in Hinvs; rewrite <- H10 in Hinvs; cbn in Hinvs.
    destruct Hinvs; [done |].
    assert (consistent s') as Hcons.
    {
      destruct (decide (composite_initial_state_prop MCVLSM s')).
      - by specialize (c i); rewrite <- H10 in c.
      - apply MC_non_initial_valid_consistent; split; [| done];
        by apply valid_trace_last_pstate in Htr'.
    }
    destruct (id Hcons) as [HMuddy_s' Hconsistent]; specialize (Hconsistent i) as Hconsi.
    rewrite <- H10 in Hconsi; cbn in Hconsi.
    assert (Hinvs : MC_component_invariant_helper (mkSt (st_obs (s' j))
      (Some (mkRS r' undecided))) (MuddyUnion s')).
    {
      unfold MC_component_invariant_helper.
      cbn in Hc.
      destruct (s' j) as [oj [(rj, statusj) |]] eqn: Hsj; [| done].
      assert (r' <= rj) by (destruct Hc as [[] | []]; lia).
      destruct (Hinvs' j) as [Hjinit | Hinvsj]; [by rewrite Hsj in Hjinit |].
      unfold MC_component_invariant, MC_component_invariant_helper in Hinvsj.
      rewrite Hsj in Hinvsj. cbn in Hinvsj.
      cbn.
      destruct Hc as [[] | []]; [by subst; lia |].
      by destruct (statusj); lia.
    }
    assert (o0 ≡ st_obs (s' i)). { by rewrite <- H10. }
    by repeat case_decide; inversion Heqcall; subst; cbn in *;
    clear Heqcall; try lia;
    (split; [lia |]);
    eapply MC_composite_invariant_preservation_muddy_from_undecided.
  - (* receive *)
    rewrite <- H10 in H0; inversion H0; subst; clear H0; rewrite Htj in Heqcall.
    unfold MC_component_invariant in Hinvs; rewrite <- H10 in Hinvs; cbn in Hinvs.
    destruct Hinvs; [done |].
    assert (consistent s') as Hcons.
    {
      destruct (decide (composite_initial_state_prop MCVLSM s')).
      - by specialize (c i); rewrite <- H10 in c.
      - apply MC_non_initial_valid_consistent. split; [| done].
        by apply valid_trace_last_pstate in Htr'.
    }
    destruct (id Hcons) as [HMuddy_s' Hconsistent]; specialize (Hconsistent i) as Hconsi.
    rewrite <- H10 in Hconsi; cbn in Hconsi.
    assert (Hinvs : MC_component_invariant_helper (mkSt (st_obs (s' j))
      (Some (mkRS r' undecided))) (MuddyUnion s')).
    {
      unfold MC_component_invariant_helper.
      cbn in Hc.
      destruct (s' j) as [oj [(rj, statusj) |]] eqn: Hsj; [| done].
      assert (r' <= rj) by (destruct Hc as [[] | []]; lia).
      destruct (Hinvs' j) as [Hjinit | Hinvsj]; [by rewrite Hsj in Hjinit |].
      unfold MC_component_invariant, MC_component_invariant_helper in Hinvsj.
      rewrite Hsj in Hinvsj. cbn in Hinvsj.
      cbn.
      destruct Hc as [[] | []]; [by subst; lia |].
      by destruct (statusj); lia.
    }
    assert (o0 ≡ st_obs (s' i)). { by rewrite <- H10. }
    repeat case_decide; inversion Heqcall; subst; cbn in *;
    clear Heqcall; try lia;
    (split; [lia |]); [done |].
    by eapply MC_composite_invariant_preservation_muddy_from_clean.
  - (* receive *)
    rewrite <- H10 in H0. inversion H0. subst. clear H0. rewrite Htj in Heqcall.
    unfold MC_component_invariant in Hinvs; rewrite <- H10 in Hinvs.
    cbn in Hinvs. destruct Hinvs; [done |].
    assert (consistent s') as Hcons.
    {
      destruct (decide (composite_initial_state_prop MCVLSM s')).
      - by specialize (c i); rewrite <- H10 in c.
      - apply MC_non_initial_valid_consistent; split; [| done].
        by apply valid_trace_last_pstate in Htr'.
    }
    destruct (id Hcons) as [HMuddy_s' Hconsistent]; specialize (Hconsistent i) as Hconsi.
    rewrite <- H10 in Hconsi; cbn in Hconsi.
    assert (Hinvs : MC_component_invariant_helper (mkSt (st_obs (s' j))
      (Some (mkRS r' muddy))) (MuddyUnion s')).
    {
      cbn in Hc.
      unfold MC_component_invariant_helper.
      destruct (s' j) as [oj [(rj, statusj) |]] eqn: Hsj; [| done].
      destruct Hc as [[] | []]; [| done].
      assert (r' <= rj) by lia.
      subst.
      destruct (Hinvs' j) as [Hjinit | Hinvsj]; [by rewrite Hsj in Hjinit |].
      unfold MC_component_invariant in Hinvsj.
      rewrite Hsj in Hinvsj. cbn in Hinvsj.
      by cbn; lia.
    }
    assert (o0 ≡ st_obs (s' i)). { by rewrite <- H10. }
    repeat case_decide; inversion Heqcall; subst; cbn in *;
    by clear Heqcall; try lia;
    (split; [lia |]);
    ( destruct Hinvs as [Hstobs Hmuddy];
      rewrite <- Hmuddy in Hstobs;
      destruct (decide (size (MuddyUnion s') = 0)); [| lia];
      apply size_non_empty_iff in HMuddy_s').
  - (* receive *)
    rewrite <- H10 in H0; inversion H0; subst; clear H0.
    rewrite Htj in Heqcall; inversion Heqcall; subst; cbn in *.
    clear Heqcall Htj; unfold MC_component_invariant in Hinvs.
    by rewrite <- H10 in Hinvs; cbn in Hinvs; destruct Hinvs.
  - (* receive *)
    rewrite <- H10 in H0; inversion H0; subst; clear H0; rewrite Htj in Heqcall.
    inversion Heqcall; cbn in *; subst.
    clear Heqcall Htj; unfold MC_component_invariant in Hinvs; rewrite <- H10 in Hinvs.
    by cbn in Hinvs; destruct Hinvs.
  - (* receive *)
    rewrite <- H10 in H0; inversion H0; subst; clear H0; rewrite Htj in Heqcall.
    unfold MC_component_invariant in Hinvs; rewrite <- H10 in Hinvs; cbn in Hinvs.
    destruct Hinvs; [done |].
    assert (consistent s') as Hcons.
    {
      destruct (decide (composite_initial_state_prop MCVLSM s')).
      - by specialize (c i); rewrite <- H10 in c.
      - apply MC_non_initial_valid_consistent; split; [| done].
        by apply valid_trace_last_pstate in Htr'.
    }
    destruct (id Hcons) as [HMuddy_s' Hconsistent]. specialize (Hconsistent i) as Hconsi.
    rewrite <- H10 in Hconsi; cbn in Hconsi.
    assert (Hinvs : MC_component_invariant_helper (mkSt (st_obs (s' j))
      (Some (mkRS r' clean))) (MuddyUnion s')).
    {
      unfold MC_component_invariant_helper.
      cbn in Hc.
      destruct (s' j) as [oj [(rj, statusj) |]] eqn: Hsj; [| done].
      destruct Hc as [[] | []]; [| done].
      assert (r' <= rj) by lia.
      subst.
      destruct (Hinvs' j) as [Hjinit | Hinvsj]; [by rewrite Hsj in Hjinit |].
      unfold MC_component_invariant, MC_component_invariant_helper in Hinvsj.
      rewrite Hsj in Hinvsj. cbn in Hinvsj.
      by cbn; lia.
    }
    assert (o0 ≡ st_obs (s' i)). { by rewrite <- H10. }
    by repeat case_decide; inversion Heqcall; subst; cbn in *;
    clear Heqcall; try lia;
    (split; [lia |]);
    ( destruct Hinvs as [Hstobs Hmuddy];
      rewrite <- Hmuddy in Hstobs;
      destruct (decide (size (MuddyUnion s') = 0)); [| lia];
      apply size_non_empty_iff in HMuddy_s').
Qed.

Lemma MC_composite_invariant_preservation_inductive (s : composite_state MCVLSM) :
  valid_state_prop MC_composite_vlsm s -> MC_composite_invariant_inductive s.
Proof.
  intros Hv.
  intros i.
  pose proof (MC_composite_invariant_preservation _ Hv i) as Hc.
  destruct Hc; [by left|].
  right.
  by apply MC_component_invariant_equiv_MC_component_invariant_inductive.
Qed.

(** ** Auxiliary progress results *)

Lemma MC_valid_noequiv_muddy (s : composite_state MCVLSM) (m : Message) :
  valid_state_prop MC_composite_vlsm s ->
  msg_status m = muddy ->
  MC_no_equivocation s m ->
  msg_round m = size (MuddyUnion s) - 1 /\ msg_index m ∈ MuddyUnion s.
Proof.
  intros Hs Hmuddy Hnoequiv.
  pose proof Hs as Hs'.
  apply MC_composite_invariant_preservation in Hs.
  destruct (Hs (msg_index m)) as [Hinit | Hinvariant].
  - assert (Hsminit : MC_initial_state_prop (s (msg_index m))) by apply Hinit.
    unfold MC_initial_state_prop in Hsminit.
    unfold MC_no_equivocation in Hnoequiv.
    repeat case_match; [| done].
    cbn in *.
    by destruct Hnoequiv as [[Hnoequivst Hnoequivr] | [Hnoequivst Hnoequivr]];
      rewrite H10 in Hsminit.
  - unfold MC_component_invariant, MC_component_invariant_helper in Hinvariant.
    unfold MC_no_equivocation in Hnoequiv.
    repeat case_match; try done; cbn in *; subst;
    only 1,3:
      by destruct Hnoequiv as [[Hnoequivst Hnoequivr] | [Hnoequivst Hnoequivr]];
        [subst; rewrite H11 in H9 |].
    destruct Hnoequiv as [[Hnoequivst Hnoequivr] | [Hnoequivst Hnoequivr]]; [| done].
    subst; rewrite H11 in Hinvariant; cbn in Hinvariant.
    split; destruct Hinvariant as [Hn Hstobs].
    + by rewrite <- Hstobs in Hn.
    + assert (Hcons : consistent s).
      {
        apply (MC_non_initial_valid_consistent s).
        unfold MC_non_initial_valid_state; split; [done |].
        cbn.
        intros Hforall.
        apply Forall_finite in Hforall.
        contradict Hforall.
        apply Exists_not_Forall, Exists_exists.
        exists msg_index0; split; [by apply elem_of_enum |].
        cbn.
        by rewrite H11.
      }
      destruct Hcons as [Hnempty Hcons].
      replace st_obs0 with (st_obs (s msg_index0)) in Hstobs; [| by rewrite H11].
      rewrite Hcons in Hstobs.
      rewrite size_difference_alt in Hstobs.
      apply size_non_empty_iff in Hnempty.
      assert (Hintersectgeq1 : size (MuddyUnion s ∩ {[msg_index0]}) >= 1) by lia.
      assert (Hintersectleq1 : MuddyUnion s ∩ {[msg_index0]} ⊆ {[msg_index0]}) by set_solver.
      apply subseteq_size in Hintersectleq1. rewrite size_singleton in Hintersectleq1.
      assert (Hintersecteq1 : size (MuddyUnion s ∩ {[msg_index0]}) = 1) by lia.
      apply size_1_elem_of in Hintersecteq1.
      by set_solver.
Qed.

Lemma MC_valid_noninitial_state_undecided_round_less_obs (s : composite_state MCVLSM) (i : index) :
  valid_state_prop MC_composite_vlsm s ->
  ~ MC_initial_state_prop (s i) ->
  state_status (st_rs (s i)) = undecided ->
  state_round (st_rs (s i)) < size (st_obs (s i)).
Proof.
  intros Hvalid Hundecided.
  apply MC_composite_invariant_preservation_inductive in Hvalid.
  specialize (Hvalid i); destruct Hvalid; [done |].
  by inversion H9; [| congruence ..].
Qed.

(**
  The definitions [MC_build_muddy_muddy_trace] and [MC_build_clean_muddy_trace] are
  useful in the proof of the lemma [MC_build_valid_message], where, having a valid
  state, we aim to obtain a valid message with status undecided, emitted earlier
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
  let s := (state_update MCVLSM is helper
   (mkSt (st_obs (is helper)) (Some (mkRS 0 undecided))))
  in
  let item0 := Build_transition_item (T := composite_type MCVLSM)
    (existT helper init) None s None
  in
  let item1 := Build_transition_item (T := composite_type MCVLSM)
   (existT target init) None  (state_update MCVLSM s target (mkSt (st_obs (s target))
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

Lemma MC_build_muddy_muddy_trace_last_target (is : composite_state MCVLSM)
  (target helper : index) (round : nat) :
  exists (obs : indexSet),
  (finite_trace_last is (MC_build_muddy_muddy_trace is target helper round)) target
    =
  mkSt obs (Some (mkRS round undecided)).
Proof.
  destruct round; cbn.
  - by state_update_simpl; eexists.
  - rewrite map_app; cbn. rewrite last_last.
    by state_update_simpl; eexists.
Qed.

Lemma MC_build_muddy_muddy_trace_last_helper (is : composite_state MCVLSM)
  (target helper : index) (round : nat) : helper <> target ->
  exists (obs : indexSet),
  (finite_trace_last is (MC_build_muddy_muddy_trace is target helper round)) helper
    =
  mkSt obs (Some (mkRS (round - 1) undecided)).
Proof.
  intros Hneq.
  destruct round; cbn.
  - by state_update_simpl; eexists.
  - rewrite map_app. cbn. rewrite last_last.
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
  apply input_valid_transition_out with (l := existT i emit) (s := s) (s' := s)
    (om := None).
  repeat split; subst; [done | ..].
  - by apply option_valid_message_None.
  - by cbn in *; rewrite Hsi; constructor.
  - cbn in *. rewrite !Hsi. rewrite MC_transition_equation_5.
    by rewrite state_update_id.
Qed.

Lemma MC_build_muddy_muddy_trace_valid (is : composite_state MCVLSM)
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
  - cbn.
    specialize (Hinit helper) as Hinithelper. cbn in Hinithelper.
    unfold MC_initial_state_prop in Hinithelper.
    specialize (Hinit target) as Hinittarget. cbn in Hinittarget.
    unfold MC_initial_state_prop in Hinittarget.
    pose proof Hcons as Hcons'.
    destruct Hcons' as [Hmuddyunion Hconsobs].
    specialize (Hconsobs helper) as Hconshelper.
    specialize (Hconsobs target) as Hconstarget.
    assert (size (MuddyUnion is) >= 2) by lia.
    eapply valid_trace_forget_last.
    apply finite_valid_trace_init_to_alt_equiv.
    constructor; [| done].
    repeat (apply mvt_extend).
    + by apply option_valid_message_None.
    + cbn. destruct (is helper) as [o_helper [|]] eqn: Hishelper; [done |].
      rewrite MC_transition_equation_3. unfold MC_transition_clause_1.
      destruct (decide (size o_helper = 0)).
      * replace o_helper with (st_obs (is helper)) in e; [| by rewrite Hishelper].
        rewrite Hconsobs, size_difference, size_singleton in e; [by lia |].
        by rewrite <- elem_of_subseteq_singleton.
      * by cbn; repeat case_match; [lia | inversion H10].
    + cbn. split; [| done].
      replace (is helper) with ({| st_obs := st_obs (is helper); st_rs := None |}).
      constructor.
      by destruct (is helper); cbn in *; subst.
    + by apply option_valid_message_None.
    + cbn. state_update_simpl.
      destruct (is target) as [o_target [|]] eqn: Histarget; [done |].
      rewrite MC_transition_equation_3. unfold MC_transition_clause_1.
      destruct (decide (size o_target = 0)).
      * replace o_target with (st_obs (is target)) in e; [| by rewrite Histarget].
        rewrite Hconsobs, size_difference, size_singleton in e; [by lia |].
        by rewrite <- elem_of_subseteq_singleton.
      * by cbn; repeat case_match; [lia | inversion H10].
    + cbn. state_update_simpl. split.
      * replace (is target) with ({| st_obs := st_obs (is target); st_rs := None |}).
        constructor.
        by destruct (is target); cbn in *; subst.
      * apply (MC_obs_equiv_preserves_consistency is); [| done].
        by apply MC_state_update_preserves_obs_equiv.
    + by apply mvt_empty.
  - specialize (IHround helper target Hhelper Htarget).
    spec IHround; [done |].
    spec IHround; [lia |].
    cbn.
    apply valid_trace_add_default_last in IHround as [IH IHinit].
    eapply valid_trace_forget_last.
    split; [| done].
    eapply finite_valid_trace_from_to_app; [done |].
    apply valid_trace_add_default_last.
    apply finite_valid_trace_singleton.
    destruct (MC_build_muddy_muddy_trace_last_helper is helper target round)
      as (obs & Hlasthelper); [done |].
    destruct (MC_build_muddy_muddy_trace_last_target is helper target round)
      as (obs' & Hlast).
    repeat split.
    + by apply valid_trace_last_pstate in IH.
    + apply valid_trace_last_pstate in IH as Hfinal.
      remember (finite_trace_last _ _) as final.
      by apply MC_valid_message_from_valid_state with (s := final) (obs := obs').
    + cbn in *. rewrite Hlasthelper.
      by constructor.
    + unfold MC_constraint, MC_no_equivocation.
      cbn in *.
      rewrite Hlast.
      by left.
    + cbn in *. rewrite Hlasthelper.
      rewrite MC_transition_equation_7. unfold MC_transition_clause_5.
      assert (Hobsequiv : st_obs (is target) ≡ obs).
      {
        replace obs with (st_obs (finite_trace_last is
          (MC_build_muddy_muddy_trace is helper target round) target));
        [| by rewrite Hlasthelper].
        apply MC_in_futures_preserves_obs_equiv. by eexists.
      }
      rewrite decide_True, decide_False, decide_True.
      * by cbn; replace (round + 1) with (S round) by lia.
      * split; [by lia |].
        rewrite MC_in_futures_preserves_muddy in Hround; [| by eexists].
        pose proof (MC_muddy_number_of_muddy_seen is target Hcons Htarget) as Hnrmuddy.
        rewrite <- MC_in_futures_preserves_muddy in Hround; [| by eexists].
        by rewrite <- Hobsequiv; lia.
      * by lia.
      * rewrite <- Hobsequiv. destruct Hcons as [Hnempty Hcons].
        by rewrite Hcons; set_solver.
Qed.

Fixpoint MC_build_clean_muddy_trace (is : composite_state MCVLSM)
  (target helper : index) (round : nat) : list (composite_transition_item MCVLSM) :=
match round with
| 0 =>
  let s := (state_update MCVLSM is helper
   (mkSt (st_obs (is helper)) (Some (mkRS 0 undecided))))
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

Lemma MC_build_clean_muddy_trace_last_target (is : composite_state MCVLSM)
  (target helper : index) (round : nat) :
  exists (obs : indexSet),
  (finite_trace_last is (MC_build_clean_muddy_trace is target helper round)) target
    =
  mkSt obs (Some (mkRS round undecided)).
Proof.
  destruct round; cbn.
  - by state_update_simpl; eexists.
  - rewrite map_app. cbn. rewrite last_app. cbn.
    by state_update_simpl; eexists.
Qed.

Lemma MC_build_clean_muddy_trace_last_helper (is : composite_state MCVLSM)
  (target helper : index) (round : nat) : helper <> target ->
  exists (obs : indexSet),
  (finite_trace_last is (MC_build_clean_muddy_trace is target helper round)) helper
    =
  mkSt obs (Some (mkRS (round - 1) undecided)).
Proof.
  intros Hneq.
  destruct round; cbn.
  - by state_update_simpl; eexists.
  - rewrite map_app. cbn. rewrite last_app. cbn.
    state_update_simpl.
    by replace (round - 0) with round by lia; eexists.
Qed.

Lemma MC_build_clean_muddy_trace_valid (is : composite_state MCVLSM)
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
  - cbn.
    specialize (Hinit helper) as Hinithelper. cbn in Hinithelper.
    unfold MC_initial_state_prop in Hinithelper.
    specialize (Hinit target) as Hinittarget. cbn in Hinittarget.
    unfold MC_initial_state_prop in Hinittarget.
    pose proof Hcons as Hcons'.
    destruct Hcons' as [Hmuddyunion Hconsobs].
    specialize (Hconsobs helper) as Hconshelper.
    specialize (Hconsobs target) as Hconstarget.
    eapply valid_trace_forget_last.
    apply finite_valid_trace_init_to_alt_equiv.
    constructor; [| done].
    repeat (apply mvt_extend).
    + by apply option_valid_message_None.
    + cbn. destruct (is helper) as [o_helper [|]] eqn: Hishelper; [done |].
      rewrite MC_transition_equation_3. unfold MC_transition_clause_1.
      destruct (decide (size o_helper = 0)).
      * replace o_helper with (st_obs (is helper)) in e; [| by rewrite Hishelper].
        rewrite Hconsobs, size_difference, size_singleton in e; [by lia |].
        by rewrite <- elem_of_subseteq_singleton.
      * by cbn; repeat case_match; [lia | inversion H9].
    + cbn. split; [| done].
      replace (is helper) with ({| st_obs := st_obs (is helper); st_rs := None |}).
      constructor.
      by destruct (is helper); cbn in *; subst.
    + by apply option_valid_message_None.
    + cbn. state_update_simpl.
      destruct (is target) as [o_target [|]] eqn: Histarget; [done |].
      rewrite MC_transition_equation_3. unfold MC_transition_clause_1.
      destruct (decide (size o_target = 0)).
      * replace o_target with (st_obs (is target)) in e; [| by rewrite Histarget].
        rewrite Hconsobs, size_difference, size_singleton in e; [by lia |].
        rewrite size_difference_alt in e.
        assert (Hsizeintersect : size (MuddyUnion is ∩ {[target]}) >= 2) by lia.
        assert (Hintersectleq1 : MuddyUnion is ∩ {[target]} ⊆ {[target]}) by set_solver.
        apply subseteq_size in Hintersectleq1. rewrite size_singleton in Hintersectleq1.
        by lia.
      * by cbn; repeat case_match; [lia | inversion H9].
    + cbn. state_update_simpl. split.
      * replace (is target) with ({| st_obs := st_obs (is target); st_rs := None |}).
        constructor.
        by destruct (is target); cbn in *; subst.
      * apply (MC_obs_equiv_preserves_consistency is); [| done].
        by apply MC_state_update_preserves_obs_equiv.
    + by apply mvt_empty.
  - spec IHround; [lia |].
    cbn.
    apply valid_trace_add_default_last in IHround as [IH IHinit].
    eapply valid_trace_forget_last.
    split; [| done].
    eapply finite_valid_trace_from_to_app; [done |].
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
          {| st_obs := st_obs
              (finite_trace_last is
                 (MC_build_clean_muddy_trace is target
                    helper round) helper);
            st_rs := Some (mkRS round undecided) |}, None)).
    {
      repeat split.
      - by apply valid_trace_last_pstate in IH.
      - apply valid_trace_last_pstate in IH as Hfinal.
        remember (finite_trace_last _ _) as final.
        by apply MC_valid_message_from_valid_state with (s := final) (obs := obs').
      - by cbn in *; rewrite Hlasthelper; constructor.
      - by cbn in *; subst; rewrite Hlast; cbn; left.
      - cbn. rewrite Hlasthelper.
        rewrite MC_transition_equation_7. unfold MC_transition_clause_5.
        assert (Hobsequiv : st_obs (is helper) ≡ obs).
        {
          replace obs with (st_obs (finite_trace_last is
            (MC_build_clean_muddy_trace is target helper round) helper));
            [| by rewrite Hlasthelper].
          apply MC_in_futures_preserves_obs_equiv. by eexists.
        }
        destruct Hcons as [Hnempty Hcons].
        assert (Htargetobs : target ∉ obs).
        {
          rewrite <- Hobsequiv, Hcons.
          by set_solver.
        }
        rewrite decide_False by done.
        destruct round; [by rewrite decide_True by lia; cbn; state_update_simpl |].
        rewrite decide_False by lia. rewrite decide_True; [done |].
        split; [by lia |]. rewrite <- Hobsequiv, Hcons.
        rewrite Hcons in Hround.
        rewrite size_difference by set_solver; rewrite size_difference_alt in Hround.
        rewrite size_singleton in *.
        by lia.
    }
    constructor; [| done].
    apply finite_valid_trace_from_to_singleton.
    repeat split.
    + by eapply input_valid_transition_destination.
    + apply valid_trace_last_pstate in IH as Hfinal.
      remember (state_update _ _ _ _) as final.
      apply input_valid_transition_out with (l := existT helper emit) (s := final) (s' := final)
        (om := None).
      repeat split; subst.
      * by eapply input_valid_transition_destination.
      * by apply option_valid_message_None.
      * by cbn in *; state_update_simpl; constructor.
      * cbn in *. state_update_simpl. rewrite MC_transition_equation_5.
        f_equal.
        by rewrite state_update_twice.
    + cbn in *; subst. rewrite Hlasthelper. cbn.
      state_update_simpl. rewrite Hlast.
      by constructor.
    + by cbn in *; state_update_simpl; left.
    + cbn. state_update_simpl. rewrite Hlast.
      rewrite MC_transition_equation_7. unfold MC_transition_clause_5.
      assert (Hobsequiv : st_obs (is target) ≡ obs').
      {
        replace obs' with (st_obs (finite_trace_last is
          (MC_build_clean_muddy_trace is target helper round) target));
          [| by rewrite Hlast].
        apply MC_in_futures_preserves_obs_equiv. by eexists.
      }
      destruct Hcons as [Hnempty Hcons].
      assert (Htargetobs : helper ∈ obs').
      {
        rewrite <- Hobsequiv, Hcons.
        by set_solver.
      }
      rewrite decide_True by done; rewrite decide_False by lia.
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
  apply valid_state_has_trace in Hvalid as (is & tr & [Hfromto Hinit]).
  destruct (id Hcons) as [Hnemptys Hconss].
  rewrite <- MC_in_futures_preserves_consistency in Hcons; [| by eexists].
  destruct (id Hcons) as [Hnempty Hcons'].
  assert (Hmuddyis : MuddyUnion is ≡ MuddyUnion s).
  {
    by apply MC_in_futures_preserves_muddy; exists tr.
  }
  rewrite Hconss in Hround.
  rewrite <- Hmuddyis in Hround.
  assert (Hj : exists (j : index), j ∈ st_obs (is i)).
  {
    setoid_rewrite Hcons'.
    apply set_choose, size_non_empty_iff.
    by lia.
  }
  destruct Hj as (j & Hj).
  apply MuddyUnion_elem in Hj as Hhelper.
  rewrite Hcons' in Hj.
  assert (Hdiff : i <> j) by set_solver.
  destruct (decide (i ∈ MuddyUnion is)).
  - pose proof (MC_build_muddy_muddy_trace_valid is i j round Hinit Hcons e Hhelper Hdiff)
      as Hvalidtr.
    destruct (MC_build_muddy_muddy_trace_last_target is i j round) as (obsf & Hlasti).
    eapply MC_valid_message_from_valid_state; [| done].
    destruct Hvalidtr; [| by apply finite_valid_trace_last_pstate].
    by rewrite size_difference, size_singleton in Hround; [| set_solver].
  - destruct (decide (size (MuddyUnion is) <= 1)).
    + assert (Hsizemuddy : size (MuddyUnion is) = 1).
      {
        apply size_non_empty_iff in Hnempty.
        by lia.
      }
      assert (MuddyUnion is ≡ {[j]}).
      {
        apply size_1_elem_of in Hsizemuddy as (x & Hx).
        rewrite Hx in Hhelper.
        by apply elem_of_singleton in Hhelper; subst.
      }
      assert (round = 0) as -> by (rewrite size_difference_alt in Hround; lia).
      apply MC_valid_message_from_valid_state with
        (s := state_update MCVLSM is i (mkSt (st_obs (is i)) (Some (mkRS 0 undecided))))
        (obs := st_obs (is i)); [| by state_update_simpl].
      apply input_valid_transition_destination with (l := existT i init) (s := is)
        (om := None) (om' := None).
      repeat split; subst; [by apply initial_state_is_valid | ..].
      * by apply option_valid_message_None.
      * specialize (Hinit i). cbn in *.
        unfold MC_initial_state_prop in Hinit.
        destruct (is i).
        cbn in *; subst.
        by constructor.
      * done.
      * by cbn in *; apply Hcons'.
      * by apply Hcons'.
      * cbn.
        specialize (Hinit i).
        destruct (is i) eqn: Hisi.
        cbn in *; unfold MC_initial_state_prop in Hinit; cbn in Hinit; subst.
        rewrite MC_transition_equation_3. unfold MC_transition_clause_1.
        replace st_obs0 with (st_obs (is i)); [| by rewrite Hisi].
        replace (size (st_obs (is i))) with 1; [done |].
        rewrite Hcons'.
        rewrite size_difference_alt.
        rewrite Hsizemuddy.
        assert (Hintersectempty : MuddyUnion is ∩ {[i]} ≡ ∅) by set_solver.
        apply size_empty_iff in Hintersectempty.
        rewrite Hintersectempty.
        by lia.
    + pose proof (MC_build_clean_muddy_trace_valid is i j round Hinit Hcons n Hhelper) as Hvalidtr.
      destruct (MC_build_clean_muddy_trace_last_target is i j round) as (obsf & Hlasti).
      eapply MC_valid_message_from_valid_state; [| done].
      by destruct Hvalidtr;
        [rewrite <- Hcons' in Hround | lia | apply finite_valid_trace_last_pstate].
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
  destruct (s j) as [oj [(rj, statusj) |]] eqn: Hsjf; [| done].
  destruct Hnoequiv as [[-> ->] | [-> Hrm]].
  - by apply MC_valid_message_from_valid_state with (s := s) (obs := oj).
  - assert (Hcons : consistent s).
    {
      apply (MC_non_initial_valid_consistent s).
      unfold MC_non_initial_valid_state; split; [done |].
      cbn.
      intros Hforall.
      apply Forall_finite in Hforall.
      contradict Hforall.
      apply Exists_not_Forall, Exists_exists.
      exists j; split; [by apply elem_of_enum |].
      cbn.
      by rewrite Hsjf.
    }
    destruct (id Hcons) as [Hnempty Hcons'].
    apply MC_composite_invariant_preservation in Hs as Hinvariants.
    destruct (Hinvariants j) as [| Hinvariant]; [by rewrite Hsjf in H9 |].
    unfold MC_component_invariant, MC_component_invariant_helper in Hinvariant.
    rewrite Hsjf in Hinvariant. cbn in Hinvariant.
    apply (MC_build_valid_message s); [| done |].
    + split; [done |].
      unfold composite_initial_state_prop.
      intros Hforall.
        apply Forall_finite in Hforall.
        contradict Hforall.
        apply Exists_not_Forall.
        apply Exists_exists.
        exists j; split; [by apply elem_of_enum |].
        cbn.
        by rewrite Hsjf.
    + case_match.
      * replace oj with (st_obs (s j)) in Hinvariant; [| by rewrite Hsjf].
        rewrite Hcons' in Hinvariant.
        rewrite Hcons'.
        by lia.
      * destruct Hinvariant as [Hroundstatusj Hsizemuddyj].
        rewrite <- Hroundstatusj in Hsizemuddyj; subst.
        by replace oj with (st_obs (s j)) in Hrm; [| by rewrite Hsjf].
      * destruct Hinvariant as [Hroundstatusj Hsizemuddyj].
        rewrite <- Hroundstatusj in Hsizemuddyj; subst.
        by replace oj with (st_obs (s j)) in Hrm; [| by rewrite Hsjf].
Qed.

(** ** Progress *)

Lemma MC_undecided_muddy_to_muddy_increase_round (s : composite_state MCVLSM)
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
  apply MC_transition_undecided_receive_muddy_round_obs
    with i (s i) (mkMsg (message_index (input item) i) (message_round (input item))
    (message_status (input item))) in Hsundecided as Htr; try done. cbn in Hsundecided.
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

Lemma MC_undecided_muddy_to_clean_increase_round (s : composite_state MCVLSM)
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
  apply MC_transition_undecided_receive_muddy_round_obs_minus_one
    with i (s i) (mkMsg (message_index (input item) i) (message_round (input item))
    (message_status (input item))) in Hsundecided as Htr; try done. cbn in Hsundecided.
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

Lemma MC_undecided_muddy_increase_round (s : composite_state MCVLSM)
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
  intros Hl Hvalid Hsundecided Hmmuddy Hmindex [Hmround1 | Hmround2].
  - by apply MC_undecided_muddy_to_clean_increase_round.
  - by apply MC_undecided_muddy_to_muddy_increase_round.
Qed.

Lemma MC_undecided_undecided_increase_round (s : composite_state MCVLSM)
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
  apply MC_transition_undecided_receive_undecided_round_lt_obs_minus_one
    with i (s i) (mkMsg (message_index input i) (message_round input)
    (message_status input)) in Hsundecided as Htr; try done; cbn in Hsundecided.
  - cbn in *; subst i l.
    assert (Hrounds : state_round (st_rs (s x)) < size (st_obs (s x))).
    {
      by apply MC_valid_noninitial_state_undecided_round_less_obs; [| inversion Hv |].
    }
    inversion Hv; subst; cbn in Hsundecided.
    rewrite <- H9 in *; clear H9; destruct rs, m; cbn in *.
    by rewrite Htr in Ht; inversion Ht; subst; state_update_simpl; cbn; lia.
  - apply MC_valid_noninitial_state_undecided_round_less_obs; [done | | done].
    cbn in *. subst l.
    by inversion Hv.
Qed.

Lemma MC_undecided_undecided_to_muddy_increase_round (s : composite_state MCVLSM)
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
  apply MC_transition_undecided_receive_undecided_round_obs_minus_one
    with i (s i) (mkMsg (message_index input i) (message_round input)
    (message_status input)) in Hsundecided as Htr; try done; cbn in Hsundecided.
  - cbn in *; subst i l.
    assert (Hrounds : state_round (st_rs (s x)) < size (st_obs (s x))).
    {
      by apply MC_valid_noninitial_state_undecided_round_less_obs; [| inversion Hv |].
    }
    inversion Hv; subst; cbn in Hsundecided.
    rewrite <- H9 in *; clear H9; destruct rs, m; cbn in *.
    by rewrite Htr in Ht; inversion Ht; subst; state_update_simpl; cbn; lia.
  - apply MC_valid_noninitial_state_undecided_round_less_obs; [done | | done].
    cbn in *. subst l.
    by inversion Hv.
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
  unfold MC_final_state. rewrite <- Forall_finite. intros Hs Hall.
  destruct (decide (exists i, MC_initial_state_prop (s i))).
  - destruct e as (i & He). destruct (size (st_obs (s i))) eqn: Hobssi.
    + exists (Build_transition_item (T := composite_type MCVLSM) (existT i init) None
        (state_update MCVLSM s i (mkSt (st_obs (s i)) (Some (mkRS 0 muddy)))) None).
      cbn; state_update_simpl; cbn.
      unfold state_round_inc. unfold MC_initial_state_prop in He.
      rewrite He; split; [| lia]. repeat split; [apply Hs | ..].
      * by apply option_valid_message_None.
      * cbn. destruct (s i). cbn in *. subst. by constructor.
      * by apply MC_non_initial_valid_consistent in Hs as [].
      * by apply MC_non_initial_valid_consistent in Hs as []; set_solver.
      * by apply MC_non_initial_valid_consistent in Hs as []; set_solver.
      * cbn. destruct (s i). cbn in *. subst. funelim (MC_transition i init
          {| st_obs := st_obs0; st_rs := None |} None); try done.
        -- by rewrite <- Heqcall; inversion H11.
        -- by inversion H10; congruence.
    + exists (Build_transition_item (T := composite_type MCVLSM) (existT i init) None
        (state_update MCVLSM s i (mkSt (st_obs (s i)) (Some (mkRS 0 undecided)))) None).
      cbn; state_update_simpl; cbn.
      unfold state_round_inc. unfold MC_initial_state_prop in He.
      rewrite He; split; [| lia]. repeat split; [apply Hs | ..].
      * by apply option_valid_message_None.
      * cbn. destruct (s i). cbn in *. subst. by constructor.
      * by apply MC_non_initial_valid_consistent in Hs as [].
      * apply MC_non_initial_valid_consistent in Hs as []; set_solver.
      * apply MC_non_initial_valid_consistent in Hs as []; set_solver.
      * cbn. destruct (s i). cbn in *. subst. funelim (MC_transition i init
          {| st_obs := st_obs0; st_rs := None |} None); try done.
        -- by inversion H10; congruence.
        -- by rewrite <- Heqcall; inversion H11.
  - apply not_Forall_Exists in Hall; [| by typeclasses eauto].
    apply Exists_exists in Hall as (i & _ & Hi). cbn in Hi.
    assert (Hundecided : state_status (st_rs (s i)) = undecided).
    {
      by destruct (decide (state_status (st_rs (s i)) = undecided)).
    }
    destruct (decide (exists (j : index), state_status (st_rs (s j)) = muddy)).
    assert (Hcons : consistent s).
    {
      by apply MC_non_initial_valid_consistent.
    }
    + destruct e as (j & He). destruct (decide (i ∈ st_obs (s j))).
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
          intro Ht.
          destruct (id Ht) as [(_ & Hm & Hv & Hc) _]. unfold MC_constraint, l, input in Hc.
          apply MC_valid_noequiv_muddy in Hc; [| done ..].
          cbn in Hc. destruct Hc as [Hroundj Hj].
          destruct (id Hcons) as [Hmuddy Hobs].
          split; [done |].
          apply MC_undecided_muddy_to_muddy_increase_round in Ht; try done.
          - cbn in Ht; state_update_simpl; cbn in Ht; unfold state_round_inc; case_match; [| lia].
            remember (state_round (st_rs (s j))) as roundj.
            by unfold state_round in Ht; cbn in Ht; lia.
          - cbn. destruct (decide (i = j)); [by subst |].
            rewrite Hobs in *.
            clear - Hj n e. by set_solver.
          - cbn. rewrite Hroundj. rewrite MC_muddy_number_of_muddy_seen; [done.. |].
            rewrite (Hobs j) in e. clear - e. by set_solver.
        }
        assert (Hnoequiv : MC_no_equivocation s {|
          msg_index := j;
          msg_round := state_round (st_rs (s j));
          msg_status := muddy
        |}).
        {
          unfold MC_no_equivocation.
          by repeat case_match; [rewrite <- H10; left; rewrite H10, <- He |].
        }
        destruct (s i) eqn: Hsi. destruct st_rs0; [| by contradict n; eexists; rewrite Hsi].
        destruct r as [ri sti]. cbn in Hundecided; subst.
        repeat split; try done.
        -- by cbn; eapply MC_valid_noequiv_valid.
        -- by cbn; rewrite Hsi; constructor.
        -- cbn. rewrite Hsi. rewrite MC_transition_equation_8. unfold MC_transition_clause_4.
           apply MC_composite_invariant_preservation in Hvalid.
           destruct (Hvalid j) as [? | Hinvariant]; [by contradict n; eexists |].
           unfold MC_component_invariant, MC_component_invariant_helper in Hinvariant.
           rewrite He in Hinvariant.
           destruct Hinvariant as [Hroundj Hobsj]. symmetry in Hobsj.
           apply MC_muddy_number_of_muddy_seen_iff in Hobsj as Hjmuddy; [| done].
           rewrite Hroundj, Hobsj in *.
           replace st_obs0 with (st_obs (s i)) by (rewrite Hsi; done).
           rewrite decide_True; [rewrite decide_True; [done |] |].
           ++ by symmetry; apply MC_muddy_number_of_muddy_seen_iff;
                [| by apply MuddyUnion_elem in e].
           ++ destruct Hcons as [Hinit Hcons]. rewrite Hcons.
              by destruct (decide (i = j)); [subst; rewrite Hsi in He | set_solver].
      * exists (Build_transition_item (T := composite_type MCVLSM) (existT i receive)
          (Some (mkMsg j (state_round (st_rs (s j))) muddy))
          (state_update MCVLSM s i (mkSt (st_obs (s i))
          (Some (mkRS (state_round (st_rs (s j)) + 1) clean)))) None).
        cbn; state_update_simpl; cbn.
        unfold MC_non_initial_valid_state in Hs.
        destruct Hs as [Hvalid Hnoninitial].
        destruct (id Hcons) as [Hmuddy Hobs].
        cut (input_valid_transition_item MC_composite_vlsm s
          (MC_transition_item_update s j i muddy (mkRS (state_round (st_rs (s j)) + 1) clean))).
        {
          intro Ht.
          destruct (id Ht) as [(_ & Hm & Hv & Hc) _]. unfold MC_constraint, l, input in Hc.
          apply MC_valid_noequiv_muddy in Hc; [| done ..].
          cbn in Hc. destruct Hc as [Hroundj Hj].
          split; [done |].
          apply MC_undecided_muddy_to_clean_increase_round in Ht; try done.
          - cbn in Ht; state_update_simpl; cbn in Ht; unfold state_round_inc.
            case_match; [| lia].
            remember (state_round (st_rs (s j))) as roundj.
            by unfold state_round in Ht; cbn in Ht; lia.
          - cbn. destruct (decide (i = j)); [by subst; rewrite He in Hundecided |].
            rewrite Hobs in *.
            clear - Hj n n1. by set_solver.
          - cbn. rewrite Hroundj. rewrite MC_clean_number_of_muddy_seen; [done .. |].
            rewrite (Hobs j) in n0. destruct (decide (i = j)); [by subst; congruence |].
            clear - n0 n1.
            by set_solver.
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
        destruct (s i) eqn: Hsi. destruct st_rs0; [| by contradict n; eexists; rewrite Hsi].
        destruct r as [ri sti]. cbn in Hundecided; subst.
        repeat split; try done.
        -- by cbn; eapply MC_valid_noequiv_valid.
        -- by cbn; rewrite Hsi; constructor.
        -- cbn. rewrite Hsi. rewrite MC_transition_equation_8. unfold MC_transition_clause_4.
           apply MC_composite_invariant_preservation in Hvalid.
           destruct (Hvalid j) as [? | Hinvariant]; [by contradict n; eexists |].
           unfold MC_component_invariant, MC_component_invariant_helper in Hinvariant.
           rewrite He in Hinvariant.
           destruct Hinvariant as [Hroundj Hobsj]. symmetry in Hobsj.
           apply MC_muddy_number_of_muddy_seen_iff in Hobsj as Hjmuddy; [| done].
           rewrite Hroundj, Hobsj in *.
           replace st_obs0 with (st_obs (s i)) by (rewrite Hsi; done).
           rewrite decide_True; [rewrite decide_False; [rewrite decide_True |] |]; [done | ..].
           ++ destruct (decide (i = j)).
              ** by subst; rewrite Hsi in He.
              ** rewrite Hobs in n0.
                 assert (HinotinMuddy : i ∉ MuddyUnion s) by set_solver.
                 by apply MC_clean_number_of_muddy_seen in HinotinMuddy; [rewrite HinotinMuddy |].
           ++ destruct (decide (i = j)).
              ** by subst; rewrite Hsi in He.
              ** rewrite Hobs in n0.
                 assert (HinotinMuddy : i ∉ MuddyUnion s) by set_solver.
                 apply MC_clean_number_of_muddy_seen in HinotinMuddy; [| done].
                 by destruct (decide (size (MuddyUnion s) = 0)); [apply size_empty_iff in e | lia].
           ++ rewrite Hobs. destruct (decide (i = j)).
              ** by subst; rewrite Hsi in He.
              ** by set_solver.
    + apply MC_non_initial_valid_consistent in Hs as Hcons;
      destruct (id Hcons) as [Hmuddy Hobs].
      assert (Hjmuddy : exists (j : index), j ∈ MuddyUnion s).
      {
        by apply set_choose in Hmuddy.
      }
      destruct Hjmuddy as (j & Hjmuddyunion).
      unfold MC_non_initial_valid_state in Hs.
      destruct Hs as [Hvalid Hnoninit]; pose proof Hvalid as Hvalid'.
      apply MC_composite_invariant_preservation_inductive in Hvalid'.
      assert (Hmuddyobs : exists (k : index), k ∈ st_obs (s j)).
      {
        apply set_choose. apply size_non_empty_iff.
        destruct (Hvalid' j) as [Hinit | Hinvariant]; [by contradiction n; eexists |].
        inversion Hinvariant; [lia | | by contradict n0; eexists].
        apply MC_muddy_number_of_muddy_seen in Hjmuddyunion; [| done].
        by apply size_non_empty_iff in Hmuddy; lia.
      }
      destruct Hmuddyobs as (k & Hkobs).
      assert (Hkundecided : state_status (st_rs (s k)) = undecided).
      {
        destruct (Hvalid' k) as [? | Hinvariantk]; [by contradict n; eexists |].
        unfold MC_component_invariant in Hinvariantk.
        inversion Hinvariantk; [done | | by contradict n0; eexists].
        apply MuddyUnion_elem, MC_muddy_number_of_muddy_seen in Hkobs; [| done].
        rewrite Hkobs in H11.
        by apply size_non_empty_iff in Hmuddy; lia.
      }
      assert (Hkinvariant : state_round (st_rs (s k)) < size (st_obs (s k))).
      {
        destruct (Hvalid' k) as [? | Hkinvariant]; [by contradict n; eexists |].
        inversion Hkinvariant; [done | | by contradict n0; eexists].
        apply MuddyUnion_elem, MC_muddy_number_of_muddy_seen in Hkobs; [| done].
        by rewrite Hkobs in H11; apply size_non_empty_iff in Hmuddy; lia.
      }
      assert (Hjundecided : state_status (st_rs (s j)) = undecided).
      {
        destruct (Hvalid' j) as [? | Hinvariantj]; [by contradict n; eexists |].
        unfold MC_component_invariant in Hinvariantj.
        inversion Hinvariantj; [done | | by contradict n0; eexists].
        apply MC_muddy_number_of_muddy_seen in Hjmuddyunion; [| done].
        rewrite Hjmuddyunion in H11.
        by apply size_non_empty_iff in Hmuddy; lia.
      }
      assert (Hjinvariant : state_round (st_rs (s j)) < size (st_obs (s j))).
      {
        destruct (Hvalid' j) as [? | Hjinvariant]; [by contradict n; eexists |].
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
        destruct (decide (j = k)); [| set_solver].
        by rewrite e, Hobs in Hkobs; set_solver.
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
               intro Ht; destruct (id Ht) as [(_ & Hm & Hv & Hc) _].
               unfold MC_constraint, input in Hc.
               apply MC_valid_noequiv_valid in Hc; [| done..].
               cbn in Hc; destruct Hc as [Hroundj Hj].
               split; [done |].
               apply MC_undecided_undecided_to_muddy_increase_round in Ht; try done.
               cbn in Ht; state_update_simpl; cbn in Ht.
               unfold state_round_inc; case_match; [| by lia].
               remember (state_round (st_rs (s j))) as roundj; unfold state_round in Ht.
               by cbn in Ht; lia.
             }
             assert (Hnoequiv :  MC_no_equivocation s
               (mkMsg j (state_round (st_rs (s j))) undecided)).
            {
              by unfold MC_no_equivocation; repeat case_match; cbn in *;
                [left | contradict n; eexists; rewrite H10].
            }
            pose proof Hkundecided as Hkundecided'.
            destruct (s k) eqn: Hsk in Hkundecided'.
            destruct st_rs0; [| by contradict n; eexists; rewrite Hsk].
            destruct r as [rk stk].
            repeat split; only 1,4: done; cbn;
              [by eapply MC_valid_noequiv_valid | by rewrite Hsk; constructor |].
            pose proof Hkundecided as Hkundecided''.
            rewrite Hsk; rewrite Hsk in Hkundecided; cbn in Hkundecided; rewrite Hkundecided.
            rewrite MC_transition_equation_7. unfold MC_transition_clause_5.
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
              intro Ht; destruct (id Ht) as [(_ & Hm & Hv & Hc) _].
              unfold MC_constraint, input in Hc.
              apply MC_valid_noequiv_valid in Hc; [| done..].
              cbn in Hc; destruct Hc as [Hroundj Hj].
              split; [done |].
              apply MC_undecided_undecided_increase_round in Ht; try done; [.. | cbn in *; lia].
              cbn in Ht; state_update_simpl; cbn in Ht; unfold state_round_inc.
              case_match; [| by lia].
              remember (state_round (st_rs (s j))) as roundj; unfold state_round in Ht.
              by cbn in Ht; lia.
            }
            assert (Hnoequiv :  MC_no_equivocation s
              (mkMsg j (state_round (st_rs (s j))) undecided)).
            {
              unfold MC_no_equivocation; repeat case_match; cbn in n1.
              - by rewrite <- H10; left; rewrite H10.
              - by contradict n; eexists; rewrite H10.
            }
            pose proof Hkundecided as Hkundecided'.
            destruct (s k) eqn: Hsk in Hkundecided'.
            destruct st_rs0; [| by contradict n; eexists; rewrite Hsk].
            destruct r as [rk stk].
            repeat split; only 1,4: done; cbn;
              [by eapply MC_valid_noequiv_valid | by rewrite Hsk; constructor |].
            pose proof Hjundecided as Hjundecided'.
            rewrite Hsk; rewrite Hsk in Hkundecided; cbn in Hkundecided; rewrite Hkundecided.
            rewrite MC_transition_equation_7. unfold MC_transition_clause_5.
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
  destruct (Hvalid i) as [Hinit | Hinv].
  - unfold state_round_inc.
    cbn in Hinit; unfold MC_initial_state_prop in Hinit.
    rewrite Hinit.
    by lia.
  - unfold MC_component_invariant, MC_component_invariant_helper in Hinv.
    unfold state_round_inc.
    destruct st_rs as [[round status] |]; [| by lia].
    cbn in *.
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
    destruct item, l.
    split; [done |].
    intros Hinit.
    specialize (Hinit x).
    cbn in Hinit; unfold MC_initial_state_prop in Hinit.
    cbn in Hround.
    destruct (destination x).
    cbn in *.
    unfold state_round_inc in Hround.
    cbn in Hround; subst.
    by lia.
  }
  eapply Hind in Hdestvalid; [.. | done].
  {
    destruct Hdestvalid as (tr & sf & Htr & Hsf).
    by exists (item :: tr), sf; split; [destruct item; constructor |].
  }
  destruct item, l.
  cbn in *.
  destruct Hitem as [Hv Ht].
  unfold transition in Ht.
  apply MC_trans_preserves_obs_equiv in Ht as Hobs.
  cbn in Ht.
  destruct MC_transition eqn: Htx.
  inversion Ht; subst.
  state_update_simpl.
  clear - Hround Hobs Hrounds Hrounddest.
  cbn in Hobs.
  unfold steps_until_final_composite.
  assert (Hxelem : x ∈ enum index) by apply elem_of_enum.
  pose proof (NoDup_enum index) as Hnodup.
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
      intros ->. unfold steps_until_final_component in *.
      by destruct s0 as
        (obs0 & [[round0 status0] |]), (s a) as
          (obsa & [[rounda statusa] |]);
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
      - rewrite Hsi. rewrite MC_transition_equation_3.
        unfold MC_transition_clause_1. cbn.
        by rewrite e.
    }
    assert (Hvalids' : MC_non_initial_valid_state (state_update MCVLSM s i
      {| st_obs := st_obs (s i); st_rs := Some (mkRS 0 muddy) |})).
    {
      split.
      - assert (Hfinite :
          finite_valid_trace_init_to MC_composite_vlsm s (state_update MCVLSM s i
          {| st_obs := st_obs (s i); st_rs := Some (mkRS 0 muddy) |}) [item]).
        {
          split; [| done].
          rewrite Heqitem.
          by eapply finite_valid_trace_from_to_singleton.
        }
        by apply valid_trace_last_pstate in Hfinite.
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
      - rewrite Hsi. rewrite MC_transition_equation_3.
        unfold MC_transition_clause_1. cbn.
        repeat case_match; [lia |].
        by inversion H9.
    }
    assert (Hvalids' : MC_non_initial_valid_state (state_update MCVLSM s i
      {| st_obs := st_obs (s i); st_rs := Some (mkRS 0 undecided) |})).
    {
      split.
      - assert (Hfinite : finite_valid_trace_init_to MC_composite_vlsm s (state_update MCVLSM s i
          {| st_obs := st_obs (s i); st_rs := Some (mkRS 0 undecided) |}) [item]).
        {
          split; [| done].
          rewrite Heqitem.
          by eapply finite_valid_trace_from_to_singleton.
        }
        by apply valid_trace_last_pstate in Hfinite.
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
