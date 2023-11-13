From VLSM.Lib Require Import Itauto.
From stdpp Require Import prelude finite base fin_sets fin_maps nmap.
From Coq Require Import Streams FunctionalExtensionality Eqdep_dec.
From VLSM.Lib Require Import Preamble ListExtras.
From VLSM.Core Require Import VLSM Plans VLSMProjections Composition.
From VLSM.Examples Require Import Consensus.

(** * Consensus by Voting

  A specification of a consensus algorithm where a set of nodes, the *acceptors*,
  agree on a value by voting.

  The algorithm uses numbered rounds of voting.
  Each acceptor casts at most one vote per round.
  A value is chosen when a sufficient set of acceptors, a *quorum*, have voted for
  the same value in the same round.

  This specification is closer to something implementable than the Consensus module,
  but still has some restrictions on the allowed transitions of an acceptor
  that can only be checked with access to the states of all acceptors.
  We model this as a composite VLSM with a composition constraint.
*)

(** Ballot numbers. *)
Definition Ballot := N.

(** Ballot numbers extended with a minimal element "-1" that comes before others. *)
Definition Ballot' := option Ballot.

Definition Ballot'_to_Z (b : Ballot') : Z := from_option Z.of_N (-1)%Z b.
Definition Ballot_to_Z (b : Ballot) : Z := Z.of_N b.

Coercion Ballot_to_Z : Ballot >-> Z.
Coercion Ballot'_to_Z : Ballot' >-> Z.

Ltac ballot_lia := unfold Ballot_to_Z in *; lia.

Lemma Ballot_lt_wf : wf (fun (x y : Ballot) => (x < y)%Z).
Proof.
  generalize N.lt_wf_0.
  by apply (wf_projected N.lt id), N2Z.inj_lt.
Qed.

Definition Ballot_peano_ind :
  forall (P : Ballot -> Prop),
    P 0%N -> (forall (b : Ballot), P b -> P (N.succ b)) -> forall b, P b
  := N.peano_ind.

(** ballot-indexed-map *)
Definition Bmap : Type -> Type := @Nmap.

#[export] Instance Bmap_eq_dec : ∀ {A : Type}, EqDecision A -> EqDecision (Bmap A) := _.

#[export] Instance Bfmap : FMap Bmap := _.
#[export] Instance Blookup : ∀ {A : Type}, Lookup Ballot A (Bmap A) := _.
#[export] Instance Bempty : ∀ {A : Type}, Empty (Bmap A) := _.
#[export] Instance Bpartial_alter : ∀ {A : Type}, PartialAlter Ballot A (Bmap A) := _.
#[export] Instance Bomap : OMap Bmap := _.
#[export] Instance Bmerge : Merge Bmap := _.
#[export] Instance FinMap_Ballot_Bmap : FinMap Ballot Bmap := _.

Notation Bset := (mapset.mapset Bmap).

#[export] Instance Bmap_dom {A : Type} : Dom (Bmap A) Bset := _.
#[export] Instance FinMapDom_Bmap_Bset : fin_map_dom.FinMapDom Ballot Bmap Bset := _.

Lemma Ballot'_Zeq_iff (b : Ballot') (x : Ballot) :
  (b : Z) = (x : Z) <-> b = Some x.
Proof.
  by destruct b; cbn; [rewrite (inj_iff Z.of_N) |]; split; (congruence || ballot_lia).
Qed.

Definition mmap_insert
  {I A SA : Type} {MI : Type -> Type}
  `{FinMap I MI} `{FinSet A SA} (i : I) (a : A) (m : MI SA) :=
  <[ i := {[ a ]} ∪ m !!! i ]> m.

Lemma elem_of_mmap_insert
  {I A SA : Type} {MI : Type -> Type}
  `{FinMap I MI} `{FinSet A SA} (m : MI SA) (i j : I) (a b : A) :
    b ∈ mmap_insert i a m !!! j <-> (a = b /\ i = j) \/ (b ∈ m !!! j).
Proof.
  unfold mmap_insert.
  destruct (decide (i = j)) as [<- | Hij].
  - rewrite lookup_total_insert.
    by destruct (decide (a = b)); set_solver.
  - rewrite lookup_total_insert_ne by done.
    by set_solver.
Qed.

Section sec_voting_spec.

Context
  (Value : Type)
  (VSet : Type) `{FinSet Value VSet}
  {VSDec : RelDecision (∈@{VSet})}
  .

Section sec_acceptor_vlsm.

Record acceptor_state : Type :=
{
  votes : Bmap VSet;
  maxBal : Ballot';
}.

(** Defining several predicates over single voting states. *)
Section sec_acceptor_state_predicates.

Context
  (S : acceptor_state)
  .

Definition voted_for (b : Ballot) (v : Value) := v ∈ votes S !!! b.

#[export] Instance voted_for_dec (b : Ballot) (v : Value) : Decision (voted_for b v) :=
  VSDec _ _.

Definition did_not_vote_in (b : Ballot) : Prop :=
  forall v : Value, ~ voted_for b v.

End sec_acceptor_state_predicates.

(**
  Acceptor labels:
  - [SkipToRound b] means: commit to not voting in any ballots before [b]
  - [Vote b v] means: vote for [v] in ballot [b].
*)
Inductive acceptor_label : Type :=
| SkipToRound (b : Ballot)
| Vote (b : Ballot) (v : Value).

#[export] Program Instance acceptor_label_dec : EqDecision acceptor_label :=
  fun x y =>
    match x, y with
    | SkipToRound x_b, SkipToRound y_b =>
        if decide (x_b = y_b) then left _ else right _
    | Vote x_b x_v, Vote y_b y_v =>
        if decide (x_b = y_b) then
          if decide (x_v = y_v) then left _
          else right _
        else right _
    | SkipToRound _, Vote _ _ => right _
    | Vote _ _, SkipToRound _ => right _
    end.
Solve Obligations with congruence.

Definition acceptor_type : VLSMType False :=
  {| state := acceptor_state
   ; label := acceptor_label
   |}.

Definition acceptor_s0 : acceptor_state :=
  {| votes := ∅
   ; maxBal := None
   |}.

Definition acceptor_initial_state_prop (S : acceptor_state) : Prop :=
  S = acceptor_s0.

Definition acceptor_locally_valid : acceptor_label -> acceptor_state * option False -> Prop :=
  fun l '(s, _) =>
    match l with
    | SkipToRound b => (maxBal s < b)%Z
    | Vote b v => (maxBal s <= b)%Z /\ did_not_vote_in s b
    end.

Definition acceptor_transition
  : acceptor_label -> acceptor_state * option False -> acceptor_state * option False :=
  fun l '(s, _) =>
    let s_votes := votes s in
    match l with
    | SkipToRound b => ({| votes := s_votes; maxBal := Some b; |}, None)
    | Vote b v => ({| votes := mmap_insert b v s_votes; maxBal := Some b; |}, None)
    end.

Definition acceptor_vlsm_machine : VLSMMachine acceptor_type :=
  {| initial_state_prop := eq acceptor_s0
   ; s0 := populate (exist _ acceptor_s0 eq_refl)
   ; initial_message_prop := (fun _ => False)
   ; transition := acceptor_transition
   ; valid := acceptor_locally_valid
   |}.

Definition acceptor_vlsm : VLSM False := mk_vlsm acceptor_vlsm_machine.

End sec_acceptor_vlsm.

(* Little predicates *)
Definition voted_none_but (sa : acceptor_state) (b : Ballot) (v : Value) :=
  forall w : Value, voted_for sa b w -> w = v.

Definition vote_committed (sa : acceptor_state) (b : Ballot) := (maxBal sa > b)%Z.

Context
  (Acceptor : Type) `{finite.Finite Acceptor}
  (ASet : Type) `{FinSet Acceptor ASet}
  .

Section sec_voting_vlsm.

Context
  (Quorum : ASet -> Prop)
  (IM := fun (_ : Acceptor) => acceptor_vlsm)
  .

#[local] Notation composition_constraint :=
  (composite_label IM -> composite_state IM * option False -> Prop).

Definition allQuorum (Q : sig Quorum) (P : Acceptor -> Prop) : Prop :=
  forall a : Acceptor, a ∈ `Q -> P a.

Definition consensus_blocking_quorum
  (s : composite_state IM) (b : Ballot) (v : Value) (Q : sig Quorum) : Prop :=
    allQuorum Q (fun a : Acceptor => vote_committed (s a) b)
    /\ allQuorum Q (fun a : Acceptor => voted_none_but (s a) b v).

Definition SafeAt (s : composite_state IM) (v : Value) (b : Ballot) : Prop :=
  forall (d : Ballot), (d < b)%Z -> exists Q : sig Quorum, consensus_blocking_quorum s d v Q.

(** SafeAt as defined in the paper *)
Inductive SafeAt_alt (s : composite_state IM) (v : Value) : Ballot -> Prop :=
| SafeStart : SafeAt_alt s v 0%N
| SafeQuorum : forall (b : Ballot) (Q : sig Quorum) (c' : Ballot'),
    (c' < b)%Z ->
    allQuorum Q (fun a : Acceptor => (maxBal (s a) >= b)%Z) ->
    (forall (d : Ballot), (c' < d)%Z -> (d < b)%Z ->
      allQuorum Q (fun a => did_not_vote_in (s a) d)) ->
    (c' <> None ->
     SafeAt_alt s v (default 0%N c')
       /\ allQuorum Q (fun a : Acceptor => voted_none_but (s a) (default 0%N c') v)) ->
    SafeAt_alt s v b.

(*
  I think SafeAt is equivalent to saying that at each earlier step c there is a quorum of
  nodes that have passed round c and only voted for v or for nothing at round c.
*)

Lemma safeAt_alt_fwd :
  forall s v b,
    SafeAt_alt s v b -> SafeAt s v b.
Proof.
  intros s v b.
  induction (Ballot_lt_wf b) as [b _ IHb].
  intros Hsafe.
  induction Hsafe as [| b Q c' Hc' H_maxBal Hno_vote Hc_votes]; intros d Hd; [by ballot_lia |].
  assert ((c' <= d) \/ (c' > d))%Z as [H_use_Q | H_d_lt_c] by lia.
  - exists Q.
    split.
    + intros a Ha; generalize (H_maxBal a Ha).
      by unfold vote_committed; lia.
    + apply Z.le_lteq in H_use_Q as [| ->%Ballot'_Zeq_iff].
      * intros a Ha w Hw.
        by apply Hno_vote in Hw.
      * by destruct Hc_votes as [_ Hc_votes].
  - destruct c' as [c |]; simpl in *; [| by ballot_lia].
    change (Z.of_N c) with (c : Z) in *.
    by apply (IHb c Hc'); [apply Hc_votes | lia].
Qed.

Lemma safeAt_alt_rev :
  forall s v b,
    SafeAt s v b -> SafeAt_alt s v b.
Proof.
  intros s v b.
  induction b using Ballot_peano_ind; intros H_Sb; [by apply SafeStart |].
  destruct (H_Sb b) as (Q & H_Q_maxBal & H_Q_votes); [by ballot_lia |].
  apply SafeQuorum with (Q := Q) (c' := Some b); simpl.
  - by ballot_lia.
  - intros a Ha; generalize (H_Q_maxBal a Ha).
    by unfold vote_committed; destruct (maxBal (s a)); simpl; ballot_lia.
  - by ballot_lia.
  - intros _; split; [| done].
    apply IHb.
    intros d Hd; apply H_Sb.
    by ballot_lia.
Qed.

Lemma SafeAt_alt_iff : 
  forall s v b,
    SafeAt s v b <-> SafeAt_alt s v b.
Proof.
  split.
  - by apply safeAt_alt_rev.
  - by apply safeAt_alt_fwd.
Qed.

Definition voting_composition_constraint
  : composite_label IM -> composite_state IM * option False -> Prop :=
  fun '(existT i l) '(s, _) =>
    match l with
    | SkipToRound _ => True (* Local checks suffice here *)
    | Vote b v => (* Voting needs to check that value v is consistent with all other acceptors. *)
        (forall j, j <> i -> voted_none_but (s j) b v)
        /\ SafeAt s v b
    end.

Definition voting_vlsm : VLSM False := composite_vlsm IM voting_composition_constraint.

End sec_voting_vlsm.

(** How to recognize consensus, also for the refinement mapping. *)
Context
  (Quorum : ASet -> Prop)
  (QDec : forall Q, Decision (Quorum Q))
  (* The key quorum assumption is that any two quorums have a nonempty intersection. *)
  (QA : forall (Q1 Q2 : sig Quorum), exists a : Acceptor, a ∈ `Q1 ∩ `Q2)
  (* For convenience we also assume that any superset of a quorum is a quorum. *)
  (QClosed : Proper (subseteq ==> impl) Quorum)
  (IM : Acceptor -> VLSM False := fun _ => acceptor_vlsm).

Definition ballot_chose (s : composite_state IM) (b : Ballot) (v : Value) : Prop :=
  exists (Q : sig Quorum), allQuorum Quorum Q (fun a : Acceptor => voted_for (s a) b v).

Definition ballots_with_votes (s : composite_state IM) : Nset :=
  union_list ((fun a : Acceptor => dom (votes (s a))) <$> enum Acceptor).

Lemma ballot_chose_inrange :
  forall s b v,
    ballot_chose s b v -> b ∈ ballots_with_votes s.
Proof.
  unfold ballot_chose.
  intros s b v [Q HQ].
  assert (exists a, a ∈ `Q) as [a Ha]
    by (setoid_rewrite <- (intersection_idemp (`Q)); apply QA).
  apply elem_of_union_list.
  eexists; split; [by eapply elem_of_list_fmap_1, (elem_of_enum a) |].
  apply fin_map_dom.elem_of_dom.
  generalize (HQ a Ha).
  unfold voted_for.
  rewrite lookup_total_alt.
  destruct (votes (s a) !! b); cbn; [done |].
  by rewrite elem_of_empty.
Qed.

#[export] Instance ballot_chose_dec :
  forall s b v,
    Decision (ballot_chose s b v).
Proof.
  intros s b v; unfold ballot_chose.
  pose (voters := list_to_set (filter (fun a => voted_for (s a) b v) (enum Acceptor)) : ASet).
  assert (Hvoters : forall Q, allQuorum Quorum Q (fun a => voted_for (s a) b v) <-> `Q ⊆ voters).
  {
    intros [Q HQ]; simpl.
    split.
    - intros HallQ a Ha.
      specialize (HallQ a Ha).
      apply elem_of_list_to_set, elem_of_list_filter.
      by split; [| apply elem_of_enum].
    - intros Hsub a Ha.
      specialize (Hsub a Ha).
      apply elem_of_list_to_set, elem_of_list_filter in Hsub.
      by apply Hsub.
  }
  destruct (QDec voters) as [yes | no].
  - left; exists (exist _ voters yes).
    by apply Hvoters.
  - right.
    contradict no.
    destruct no as [Q' HQ'].
    apply Hvoters in HQ'.
    generalize (proj2_sig Q').
    by eapply QClosed.
Qed.

Definition ballot_proposals (s : composite_state IM) (b : Ballot) : VSet :=
  union_list ((fun a => votes (s a) !!! b) <$> enum Acceptor).

Lemma ballot_chose_in_proposals :
  forall s b v,
    ballot_chose s b v -> v ∈ ballot_proposals s b.
Proof.
  unfold ballot_chose, ballot_proposals.
  intros s b v [Q HQ].
  destruct (QA Q Q) as [a Ha].
  rewrite (intersection_idemp (`Q)) in Ha.
  specialize (HQ a Ha); simpl in HQ.
  unfold voted_for in HQ.
  apply elem_of_union_list.
  exists (votes (s a) !!! b).
  split; [| done].
  refine (elem_of_list_fmap_1 _ _ a _).
  by apply elem_of_enum.
Qed.

Definition chosen_by_ballot (s : state (voting_vlsm Quorum)) (b : Ballot) : VSet :=
  set_filter (fun v => ballot_chose s b v) _ (ballot_proposals s b).

Definition chosen (s : state (voting_vlsm Quorum)) : VSet :=
  union_list (chosen_by_ballot s <$> elements (ballots_with_votes s)).

Lemma chosen_iff :
  forall (s : state (voting_vlsm Quorum)) (v : Value),
    v ∈ chosen s <-> exists b, ballot_chose s b v.
Proof.
  intros s v.
  split.
  - intros Hv.
    unfold chosen in Hv.
    apply elem_of_union_list in Hv as (C_by_b & HC & Hb).
    apply elem_of_list_fmap in HC as (b & -> & _).
    exists b.
    unfold chosen_by_ballot in Hb.
    apply elem_of_filter in Hb.
    by apply Hb.
  - intros [b Hb].
    apply ballot_chose_inrange in Hb as Hb_dom.
    unfold chosen.
    apply elem_of_union_list.
    exists (chosen_by_ballot s b).
    split; [by apply elem_of_list_fmap_1, elem_of_elements |].
    unfold chosen_by_ballot.
    apply elem_of_filter.
    by apply ballot_chose_in_proposals in Hb as Hv.
Qed.

(** Each acceptor can vote for at most one value in any given ballot *)
(* VInv1 *)
Definition acceptor_no_conflict_prop (s : state (voting_vlsm Quorum)) : Prop :=
  forall (a : Acceptor) (b : Ballot) (v w : Value),
    voted_for (s a) b v -> voted_for (s a) b w -> v = w.

(* VInv2 *)
(** Every vote is for a safe value *)
Definition acceptor_votes_safe_prop (s : state (voting_vlsm Quorum)) : Prop :=
  forall (a : Acceptor) (b : Ballot) (v : Value),
    voted_for (s a) b v -> SafeAt Quorum s v b.

Lemma step_cases :
  forall [li s om s' om'],
    input_valid_transition (voting_vlsm Quorum) li (s, om) (s', om') ->
    let (i, l) := li in
    s' = state_update IM s i ((acceptor_transition l (s i, om)).1) /\
    match l with
    | SkipToRound b' =>
        (maxBal (s i) < b')%Z
    | Vote b v =>
        (maxBal (s i) <= b)%Z /\
          did_not_vote_in (s i) b /\
          SafeAt Quorum s v b
    end.
Proof.
  intros [i l] s om s' om' [(_ & _ & Hlv & Hcv) Htrans].
  split.
  - by destruct l; inversion Htrans.
  - destruct l.
    + by apply Hlv.
    + by split_and!; [apply Hlv.. | apply Hcv].
Qed.

Lemma step_cases' :
  forall [li s om s' om'],
    input_valid_transition (voting_vlsm Quorum) li (s, om) (s', om') ->
    let (i, l) := li in
    match l with
    | SkipToRound b' =>
        (maxBal (s i) < b')%Z
          /\ s' = state_update IM s i {| votes := votes (s i); maxBal := Some b'; |}
    | Vote b v =>
        (maxBal (s i) <= b)%Z /\
          did_not_vote_in (s i) b /\
          (forall j, j <> i -> voted_none_but (s j) b v) /\
          SafeAt Quorum s v b /\
          s' = state_update IM s i {| votes := mmap_insert b v (votes (s i)); maxBal := Some b |}
    end.
Proof.
  intros [i l] s om s' om' [(_ & _ & Hvalid) Htrans].
  rewrite (surjective_pairing (transition _ _)) in Htrans.
  apply (f_equal fst) in Htrans.
  cbn [fst] in Htrans.
  subst s'.
  by destruct l; simpl; repeat split; apply Hvalid.
Qed.

Lemma step_cases'' :
  forall [li s om s' om'],
    input_valid_transition (voting_vlsm Quorum) li (s, om) (s', om') ->
  forall a,
    let (i, l) := li in
    if decide (a = i)
    then s' a =
      {|
        maxBal := Some
          match l with
          | SkipToRound b' => b'
          | Vote b _ => b
          end;
        votes :=
          match l with
          | SkipToRound _ => votes (s a)
          | Vote b v => mmap_insert b v (votes (s a))
          end;
      |}
    else s' a = s a.
Proof.
  intros [i l] s om s' om' Ht a.
  apply step_cases in Ht as [-> _].
  destruct (decide (a = i)); [| by rewrite state_update_neq].
  subst i; rewrite state_update_eq.
  destruct (s a) as [mb_a votes_a].
  destruct om as [[] |].
  by destruct l; simpl.
Qed.

Lemma prev_votes:
  forall [li s om s' om'],
    input_valid_transition (voting_vlsm Quorum) li (s, om) (s', om') ->
  forall a b v,
    voted_for (s' a) b v ->
    match li with
    | existT i (SkipToRound _) => voted_for (s a) b v
    | existT i (Vote bv vv) =>
        (a = i /\ b = bv /\ v = vv) \/ ((a ≠ i \/ b ≠ bv) /\ voted_for (s a) b v)
    end.
Proof.
  intros [i l] s om s' om' [Hs' Ht]%step_cases a b v.
  rewrite Hs'; clear Hs'.
  destruct (decide (a = i)); [| by rewrite state_update_neq; destruct l; auto].
  subst i; rewrite state_update_eq.
  destruct l; simpl; [done |].
  unfold voted_for, mmap_insert; cbn.
  destruct (decide (b0 = b));
    [| by rewrite lookup_total_insert_ne by done; right; set_solver].
  subst b0; rewrite lookup_total_insert.
  assert (votes (s a) !!! b ≡@{VSet} ∅) as -> by (apply elem_of_equiv_empty, Ht).
  by left; set_solver.
Qed.

(**
  A stronger claim which is that
  two votes on the same ballot cannot be for different values,
  even if they are from different acceptors.
  This is not needed to prove safety, only for liveness.
*)
(* VInv3 *)
Definition ballot_no_conflict_prop (s : state (voting_vlsm Quorum)) : Prop :=
  forall (a1 a2 : Acceptor) (b : Ballot) (v1 v2 : Value),
    voted_for (s a1) b v1 -> voted_for (s a2) b v2 -> v1 = v2.

Corollary corr_conflict_props (s : state (voting_vlsm Quorum)) :
  ballot_no_conflict_prop s -> acceptor_no_conflict_prop s.
Proof.
  by unfold acceptor_no_conflict_prop, ballot_no_conflict_prop; eauto.
Qed.

(** invariance of VInv1 *)
Lemma inv_acceptor_no_conflict :
  forall s,
    valid_state_prop (voting_vlsm Quorum) s ->
    acceptor_no_conflict_prop s.
Proof.
  intros s Hs.
  induction Hs using valid_state_prop_ind; intros a b v w.
  - rewrite <- (Hs a); clear Hs s a.
    intro Hv; exfalso; contradict Hv.
    unfold voted_for; cbn.
    rewrite lookup_total_empty. (* matching a typo in stdpp *)
    simpl.
    by apply not_elem_of_empty.
  - intros Hv Hw.
    apply (prev_votes Ht a b) in Hv, Hw.
    specialize (IHHs a b v w).
    by destruct l as [i []]; [auto | itauto congruence].
Qed.

(** VInv4 in the paper *)
Definition maxBal_limits_votes_prop (s : state (voting_vlsm Quorum)) : Prop :=
  forall a (b : Ballot),
    (maxBal (s a) < b)%Z -> did_not_vote_in (s a) b.

Lemma inv_max_bal_limits_votes :
  forall s,
    valid_state_prop (voting_vlsm Quorum) s ->
    maxBal_limits_votes_prop s.
Proof.
  unfold maxBal_limits_votes_prop.
  intros s Hs.
  induction Hs using valid_state_prop_ind; intros a b.
  - intros _ v.
    rewrite <- (Hs a).
    unfold voted_for; cbn.
    rewrite lookup_total_empty; cbn.
    by apply not_elem_of_empty.
  - destruct l as [i l].
    apply step_cases in Ht as [Hs' Hl].
    destruct (decide (a = i)); [subst i |].
    + rewrite Hs', state_update_eq; clear Hs'.
      destruct l as [b' | bv vv]; simpl in *.
      * intros Hb'.
        apply IHHs.
        revert Hl.
        by destruct (maxBal (s a)); simpl; ballot_lia.
      * intros Hb v.
        unfold voted_for, mmap_insert; simpl.
        rewrite lookup_total_insert_ne by ballot_lia.
        apply IHHs.
        generalize (proj1 Hl).
        by destruct (maxBal (s a)); simpl; ballot_lia.
    + rewrite Hs', state_update_neq by done.
      by apply IHHs.
Qed.

Lemma cbq_blocks :
  forall s b v w,
    (exists Q, consensus_blocking_quorum Quorum s b v Q) ->
    ballot_chose s b w ->
    v = w.
Proof.
  intros s b v w (Q & _ & Hblock) [QQ Hchose].
  destruct (QA Q QQ) as [a Ha].
  apply elem_of_intersection in Ha as [Ha_Q Ha_QQ].
  symmetry.
  by eapply Hblock; [| apply Hchose].
Qed.

(* does not need invariants yet *)
Lemma VT0 :
  forall s,
    valid_state_prop (voting_vlsm Quorum) s ->
    forall (v w : Value) (b c : Ballot),
      (b > c)%N -> SafeAt Quorum s v b -> ballot_chose s c w -> v = w.
Proof.
  intros s Hs v w b.
  set (P b := forall (c : Ballot),
    (b > c)%N -> SafeAt Quorum s v b -> ballot_chose s c w -> v = w).
  fold (P b).
  induction b using N.peano_ind; [by intro; lia |].
  intros c Hc Hsafe Hchosen.
  apply N.gt_lt, N.lt_succ_r, N.lt_eq_cases in Hc as [Hc%N.lt_gt | ->].
  - apply (IHb c Hc); [| done].
    by intros d Hd; apply Hsafe; ballot_lia.
  - eapply cbq_blocks; [| by apply Hchosen].
    by apply Hsafe; ballot_lia.
Qed.

Lemma Q_nonempty :
  forall (Q : sig Quorum), exists a, a ∈ `Q.
Proof.
  intros Q.
  destruct (QA Q Q) as [a Ha].
  by exists a; apply intersection_idemp.
Qed.

Lemma VT1 :
  forall s,
    valid_state_prop (voting_vlsm Quorum) s ->
    acceptor_no_conflict_prop s ->
    acceptor_votes_safe_prop s ->
    forall (v w : Value),
      v ∈ chosen s -> w ∈ chosen s -> v = w.
Proof.
  intros s Hs Hinv1 Hinv2 v w Hv Hw.
  apply chosen_iff in Hv as [b Hchose_v].
  apply chosen_iff in Hw as [c Hchose_w].
  destruct (Hchose_v) as [Q Hv].
  destruct (Hchose_w) as [R Hw].
  destruct (Q_nonempty Q) as [av Hav].
  destruct (Q_nonempty R) as [aw Haw].
  apply Hv in Hav.
  apply Hw in Haw.
  simpl in Hv, Hw.
  assert (SafeAt Quorum s v b) by (eapply Hinv2; done).
  assert (SafeAt Quorum s w c) by (eapply Hinv2; done).
  destruct (N.lt_total b c) as [H_b_lt_c | [H_bc | H_c_lt_b]].
  - apply N.lt_gt in H_b_lt_c.
    symmetry.
    by eapply VT0.
  - destruct (QA Q R) as [a Ha].
    apply elem_of_intersection in Ha as [Ha_Q Ha_R].
    subst c.
    apply (Hinv1 a b).
    + by apply Hv.
    + by apply Hw.
  - apply N.lt_gt in H_c_lt_b.
    by eapply VT0.
Qed.

Lemma prev_vote_committed :
  forall [l s s' om om'],
    input_valid_transition (voting_vlsm Quorum) l (s, om) (s', om') ->
    forall a b v, vote_committed (s a) b -> voted_for (s' a) b v -> voted_for (s a) b v.
Proof.
  intros * Ht *.
  apply step_cases' in Ht.
  unfold vote_committed, voted_for.
  destruct l as [i []].
  - destruct Ht as [Hb ->].
    destruct (decide (a = i)); [| by rewrite state_update_neq].
    by subst i; rewrite state_update_eq.
  - destruct Ht as (Hbal & Hnv & _ & _ & ->).
    destruct (decide (a = i)); [| by rewrite state_update_neq].
    subst i; rewrite state_update_eq.
    destruct (maxBal (s a)) as [mb_a |]; [| by simpl; ballot_lia].
    simpl in Hbal |- *.
    intros Hb.
    assert (b <> b0)%Z by ballot_lia.
    rewrite elem_of_mmap_insert.
    by itauto.
Qed.

Lemma safe_at_preserved :
  forall [l s s' om om'],
    input_valid_transition (voting_vlsm Quorum) l (s, om) (s', om') ->
    forall b v, SafeAt Quorum s b v -> SafeAt Quorum s' b v.
Proof.
  intros l s s' om om' Ht b v Hsafe d Hd.
  destruct (Hsafe d Hd) as (Q & Hbal & Hvotes).
  exists Q.
  split; intros a Ha; specialize (Hbal a Ha); specialize (Hvotes a Ha); simpl in Hbal, Hvotes.
  - revert Hbal.
    unfold vote_committed.
    pose proof (step_cases'' Ht a) as Hstep.
    destruct l as [i l].
    destruct (decide (a = i)); [| by congruence].
    rewrite Hstep; cbn; clear Hstep.
    apply step_cases' in Ht.
    subst a.
    by destruct l; simpl in Ht |- *;
      destruct Ht as [Ht _]; revert Ht;
      destruct (maxBal (s i)); simpl; ballot_lia.
  - unfold voted_none_but.
    intros w Hw.
    by apply Hvotes, (prev_vote_committed Ht).
Qed.

(* Need invariance of VInv2 VInv3 VInv4 *)

Lemma inv_acceptor_votes_safe :
  forall s,
    valid_state_prop (voting_vlsm Quorum) s ->
    acceptor_votes_safe_prop s.
Proof.
  intros s Hs.
  induction Hs using valid_state_prop_ind; unfold acceptor_votes_safe_prop; intros a b v.
  - intros Hvote; contradict Hvote.
    rewrite <- (Hs a).
    unfold voted_for; cbn.
    rewrite lookup_total_empty; cbn.
    by apply not_elem_of_empty.
  - intros Hvote.
    apply (prev_votes Ht) in Hvote.
    pose proof (Hpres := safe_at_preserved Ht v b).
    specialize (IHHs a b v).
    destruct l as [i [b' | b' w]]; [by auto |].
    assert (Hw : SafeAt Quorum s w b') by (apply step_cases in Ht; apply Ht).
    by decompose [and or] Hvote; subst; auto.
Qed.

Lemma vote_stable :
  forall l s om s' om',
    input_valid_transition (voting_vlsm Quorum) l (s, om) (s', om') ->
    forall a (b : Ballot) v,
      voted_for (s a) b v -> voted_for (s' a) b v.
Proof.
  intros * Ht a b v.
  pose proof (sigT_prod_sigT l); destruct (prod_of_sigT l) as [i li]; subst l.
  apply step_cases'' with (a := a) in Ht; cbn in Ht.
  destruct (decide (a = i)); [| by congruence].
  unfold voted_for.
  destruct li; rewrite Ht; cbn; [done |].
  by rewrite elem_of_mmap_insert; itauto.
Qed.

Lemma choice_stable :
  forall l s om s' om',
    input_valid_transition (voting_vlsm Quorum) l (s, om) (s', om') ->
    forall b v,
      ballot_chose s b v -> ballot_chose s' b v.
Proof.
  intros l s om s' om' Ht b v [Q HQ].
  exists Q; intros a Ha.
  by eapply vote_stable, HQ.
Qed.

Lemma voting_safe :
  forall s,
    valid_state_prop (voting_vlsm Quorum) s ->
    forall b1 v1 b2 v2,
      ballot_chose s b1 v1 -> ballot_chose s b2 v2 ->
      v1 = v2.
Proof.
  intros s Hs.
  match goal with
  |- forall b1 v1 b2 v2, @?P b1 v1 b2 v2 =>
      cut (forall (b1 : Ballot) v1 (b2 : Ballot) v2, (b1 < b2)%Z -> P b1 v1 b2 v2)
  end.
  - intros Hwlog * Hv1 Hv2.
    destruct (Z.lt_total b1 b2) as [| [Heq |]]; [by eauto | clear Hwlog | by symmetry; eauto].
    apply (inj_iff Ballot_to_Z) in Heq; subst b2.
    destruct Hv1 as [Q_v1 Hv1], Hv2 as [Q_v2 Hv2].
    destruct (QA Q_v1 Q_v2) as [a [Ha_Q1 Ha_Q2]%elem_of_intersection].
    by eapply (inv_acceptor_no_conflict _ Hs); eauto.
  - intros b1 v1 b2 v2 H_lt [Q_v1 H_v1] [Q_v2 H_v2].
    destruct (Q_nonempty Q_v2) as [a2 Ha2].
    pose proof (inv_acceptor_votes_safe _ Hs a2 _ _ (H_v2 _ Ha2) b1 H_lt) as [Q12 H_b1_v2].
    destruct (QA Q_v1 Q12) as [a [Ha_Q1 Ha_Q12]%elem_of_intersection].
    destruct H_b1_v2 as [_ H_b1_v2].
    by apply (H_b1_v2 _ Ha_Q12) in H_v1.
Qed.

Lemma chosen_subsingleton :
  forall s,
    valid_state_prop (voting_vlsm Quorum) s ->
    forall v, v ∈ chosen s -> chosen s ≡ {[ v ]}.
Proof.
  intros s Hs v Hv.
  pose proof (Hsafe := voting_safe s Hs).
  rewrite set_equiv; intros x; rewrite elem_of_singleton.
  split; [| by intros ->].
  intros Hx.
  apply chosen_iff in Hv as [bv Hv].
  apply chosen_iff in Hx as [bx Hx].
  by eapply Hsafe.
Qed.

End sec_voting_spec.

Section sec_voting_simulates_consensus.

Context
  (V : Type)
  (VSet : Type) `{FinSet V VSet}
  {VSDec : RelDecision (∈@{VSet})}
  (CV : VLSM False := consensus_vlsm V VSet)
  (Acceptor : Type) `{finite.Finite Acceptor}
  (ASet : Type) `{FinSet Acceptor ASet}
  (Quorum : ASet -> Prop) (QDec : forall Q, Decision (Quorum Q))
  (QA : forall (Q1 Q2 : sig Quorum), exists a, a ∈ `Q1 ∩ `Q2)
  (QClosed : Proper (subseteq ==> impl) Quorum)
  (VV := voting_vlsm V VSet Acceptor ASet Quorum)
  .

Lemma check_quorum (Q : ASet) : {Quorum Q} + {forall Q', Q' ⊆ Q -> ¬ Quorum Q'}.
Proof.
  by destruct (QDec Q); [left | right; intros Q' ->].
Defined.

Definition state_project (s : state VV) : state CV :=
  chosen V VSet Acceptor ASet Quorum QDec QClosed s.

Definition label_state_project (s : state VV) (l : label VV) : label CV :=
  let cs := state_project s in
  if decide (elements cs = [])
  then
    let s' := fst (transition VV l (s, None)) in
    match elements (state_project s') with
    | v :: _ => Some (Decided _ v)
    | _ => None
    end
  else None.

Context
  (H_VSet_L : LeibnizEquiv VSet)
  .

Lemma voting_step_in_consensus :
  forall l s om s' om',
    input_valid_transition (voting_vlsm _ VSet _ ASet Quorum) l (s, om) (s', om') ->
    valid_state_prop (consensus_vlsm _ VSet) (state_project s) ->
    input_valid_transition (consensus_vlsm _ VSet)
      (label_state_project s l) (state_project s, om) (state_project s', om').
Proof.
  intros l s [] s' [] Ht H_proj_s; [done.. |].
  cut (let lc := label_state_project s l in
       match lc with Some (Decided _ _) => state_project s ≡ ∅ | None => True end
       /\ consensus_transition _ VSet lc (state_project s, None) = (state_project s', None)).
  {
    pose proof (option_valid_message_None (consensus_vlsm V VSet)).
    by intros NewGoal; repeat split; [| | apply NewGoal..].
  }
  apply input_valid_transition_origin in Ht as Hs.
  apply input_valid_transition_destination in Ht as Hs'.
  pose proof (Hs_safe := voting_safe _ VSet _ ASet Quorum QA QClosed s Hs).
  pose proof (Hs'_safe := voting_safe _ VSet _ ASet Quorum QA QClosed s' Hs').
  pose proof (Hchoice_stable := choice_stable _ VSet _ ASet Quorum _ _ _ _ _ Ht).
  intro lc_def; remember lc_def as lc; subst lc_def; revert Heqlc.
  unfold label_state_project.
  replace (transition VV l _) with (s', @None False) by (symmetry; apply Ht).
  simpl.
  remember (state_project s) as cs eqn:H_eqn_cs; cbn in cs.
  remember (state_project s') as cs' eqn:H_eqn_cs'; cbn in cs'.
  destruct (decide (elements cs = [])) as [Hcs | Hcs]; [destruct (elements cs') eqn: Hcs' |].
  - intros ->; simpl.
    split; [done |].
    simpl; f_equal; apply leibniz_equiv_iff.
    apply elements_empty_iff in Hcs, Hcs'.
    by etransitivity.
  - intros ->; simpl.
    apply elements_empty_iff in Hcs.
    split; [done |].
    f_equal; apply leibniz_equiv_iff.
    rewrite Hcs, right_id by (apply union_empty_r).
    assert (v ∈ cs') as Hv_cs'.
    {
      apply elem_of_elements.
      rewrite Hcs'.
      by apply elem_of_list_here.
    }
    symmetry.
    unfold state_project in H_eqn_cs'.
    subst cs'.
    by apply chosen_subsingleton.
  - intros ->; simpl.
    split; [done |].
    f_equal; apply leibniz_equiv_iff.
    rewrite elements_empty_iff in Hcs.
    apply set_choose in Hcs as [v Hv].
    assert (v ∈ cs') as Hv'.
    {
      subst cs cs'; unfold state_project in *.
      apply chosen_iff in Hv as [bv Hv]; [| done].
      apply Hchoice_stable in Hv.
      apply chosen_iff; [done |].
      by exists bv.
    }
    transitivity (@singleton _ _ H1 v); [| symmetry].
    + by subst cs; apply chosen_subsingleton.
    + by subst cs'; apply chosen_subsingleton.
Qed.

Lemma voting_initial_in_consensus :
  forall s,
    initial_state_prop (voting_vlsm _ VSet _ ASet Quorum) s ->
    initial_state_prop (consensus_vlsm _ VSet) (state_project s).
Proof.
  intros s Hs.
  change (state_project s ≡ ∅).
  apply elem_of_equiv_empty; intros v Hv.
  apply chosen_iff in Hv as [bv Hv]; [| done].
  destruct Hv as [Q HvQ], (QA Q Q) as [a Ha].
  lapply (HvQ a); [| by set_solver].
  unfold voted_for.
  rewrite <- (Hs a); cbn.
  rewrite lookup_total_empty.
  by apply elem_of_empty.
Qed.

Lemma voting_simulates_consensus :
  forall s,
    valid_state_prop (voting_vlsm _ VSet _ ASet Quorum) s ->
    valid_state_prop (consensus_vlsm _ VSet) (state_project s).
Proof.
  intros s Hs; induction Hs using valid_state_prop_ind.
  - apply initial_state_is_valid.
    by apply voting_initial_in_consensus.
  - by eapply input_valid_transition_destination, voting_step_in_consensus.
Qed.

End sec_voting_simulates_consensus.
