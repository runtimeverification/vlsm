From stdpp Require Import prelude.
From Coq Require Import FinFun Streams Logic.Epsilon Arith.Compare_dec Lia.
From VLSM Require Import Lib.Preamble Lib.ListExtras Lib.ListSetExtras Lib.RealsExtras.
From VLSM Require Import Core.VLSM Core.Composition Core.VLSMProjections Core.ProjectionTraces.

(** * VLSM Decisions on Consensus Values *)

(* Need to add consensus values (and decision functions) to VLSM definitions? *)

Definition decision {message} (T : VLSMType message) (C : Type)
  := @state _ T -> option C.

Definition vdecision {message} (V : VLSM message) (C : Type)
  := decision (type V) C.

Section CommuteSingleton.

  Context
    {message : Type}
    (V : VLSM message)
    (C : Type).

  (* 3.2.1 Decision finality *)

  (* Definition of finality per document. *)
  Definition final_original : vdecision V C -> Prop :=
    fun (D : vdecision V C) => forall (tr : valid_trace V),
        forall (n1 n2 : nat) (s1 s2 : state) (c1 c2 : C),
          (trace_nth (proj1_sig tr) n1 = Some s1) ->
          (trace_nth (proj1_sig tr) n2 = Some s2) ->
          (D s1 = (Some c1)) ->
          (D s2 = (Some c2)) ->
          c1 = c2.

  (* Definition of finality using in_futures, which plays better with the estimator property *)
  Definition final: vdecision V C -> Prop :=
  fun (D : vdecision V C) => forall (s1 s2 : vstate V) (c1 c2 : C),
        in_futures V s1 s2 ->
        (D s1 = (Some c1)) ->
        (D s2 = (Some c2)) ->
        c1 = c2.

  (* 3.3.1 Initial state bivalence *)
  Definition bivalent : vdecision V C -> Prop :=
    fun (D : vdecision V C) =>
      (* All initial states decide on None *)
      (forall (s0 : state),
        vinitial_state_prop V s0 ->
        D s0 = None) /\
      (* Every valid trace (already beginning from an initial state) contains a state deciding on each consensus value *)
      (forall (c : C) ,
          exists (tr : valid_trace V) (s : state) (n : nat),
            (trace_nth (proj1_sig tr) n) = Some s /\ D s = (Some c)).

  (* 3.3.2 No stuck states *)

  Definition stuck_free : vdecision V C -> Prop :=
    fun (D : vdecision V C) =>
      (forall (s : state),
          exists (tr : valid_trace V)
                 (decided_state : state)
                 (n_s n_decided : nat)
                 (c : C),
         trace_nth (proj1_sig tr) n_s = Some s /\
         trace_nth (proj1_sig tr) n_decided = Some decided_state /\
         n_decided >= n_s /\
         D decided_state = Some c).

  (* 3.3.3 Protocol definition symmetry *)
  (* How do we formalize this property set-theoretically? *)

  Definition behavior : vdecision V C -> Prop :=
    fun _ => True.

  Definition symmetric : vdecision V C -> Prop :=
    fun (D : vdecision V C) =>
    exists (f : vdecision V C -> vdecision V C),
      behavior D = behavior (f D).

End CommuteSingleton.

Section CommuteIndexed.

  Context
    {message : Type}
    `{EqDecision index}
    (IM : index -> VLSM message)
    (constraint : composite_label IM -> composite_state IM * option message -> Prop)
    (C : Type)
    (X := composite_vlsm IM constraint)
    (ID : forall i : index, vdecision (IM i) C).

  (* ** Decision consistency

  First, let us introduce a definition of consistency which
  looks at states as belonging to a trace.
  *)

  Definition consistent_original :=
      forall (tr : valid_trace X),
      forall (n1 n2 : nat),
      forall (j k : index),
      forall (s1 s2 : vstate X),
      forall (c1 c2 : C),
      j <> k ->
      trace_nth (proj1_sig tr) n1 = (Some s1) ->
      trace_nth (proj1_sig tr) n2 = (Some s2) ->
      (ID j) (s1 j) = (Some c1) ->
      (ID k) (s2 k) = (Some c2) ->
      c1 = c2.

  (**

  Now let us give an alternative definition based on [in_futures]:
  *)

  Definition consistent :=
      forall
        (s1 s2 : vstate X)
        (Hfuture : in_futures X s1 s2)
        (j k : index)
        (Hneq : j <> k)
        (c1 c2 : C)
        (HDecided1 : (ID j) (s1 j) = Some c1)
        (HDecided2 : (ID k) (s2 k) = Some c2)
        , c1 = c2.


  (**
  Next two results show that the two definitions above are equivalent.
  *)

  Lemma consistent_to_original
    (Hconsistent : consistent)
    : consistent_original.
  Proof.
    intros tr n1 n2 j k s1 s2 c1 c2 Hneq Hs1 Hs2 HD1 HD2.
    destruct (decide (n1 <= n2)).
    - specialize (in_futures_witness_reverse X s1 s2 tr n1 n2 l Hs1 Hs2)
      ; intros Hfutures.
      specialize (Hconsistent s1 s2 Hfutures j k Hneq c1 c2 HD1 HD2).
      assumption.
    - assert (Hle : n2 <= n1) by lia.
      clear n.
      specialize (in_futures_witness_reverse X s2 s1 tr n2 n1 Hle Hs2 Hs1)
      ; intros Hfutures.
      assert (Hneq' : k <> j)
        by (intro Heq; elim Hneq; symmetry; assumption).
      specialize (Hconsistent s2 s1 Hfutures k j Hneq' c2 c1 HD2 HD1).
      symmetry.
      assumption.
    Qed.

  Lemma original_to_consistent
    (Horiginal : consistent_original)
    : consistent.
  Proof.
    unfold consistent; intros.
    specialize (in_futures_witness X s1 s2 Hfuture)
    ; intros [tr [n1 [n2 [Hle [Hs1 Hs2]]]]].
    specialize (Horiginal tr n1 n2 j k s1 s2 c1 c2 Hneq Hs1 Hs2 HDecided1 HDecided2).
    assumption.
  Qed.

  (** The following is an attempt to include finality in the definition of consistency by dropping the requirement
      that (j <> k). **)

  Definition final_and_consistent :=
      forall
        (s1 s2 : vstate X)
        (Hfuture : in_futures X s1 s2)
        (j k : index)
        (c1 c2 : C)
        (HDecided1 : (ID j) (s1 j) = Some c1)
        (HDecided2 : (ID k) (s2 k) = Some c2)
        , c1 = c2.

  Lemma final_and_consistent_implies_final
      (Hcons : final_and_consistent)
      (i : index)
      (Hfr : projection_friendly_prop (component_projection IM constraint i))
      : final (composite_vlsm_constrained_projection IM constraint i) C (ID i).
  Proof.
    intros s1 s2 c1 c2 Hfuturesi HD1 HD2.
    specialize
      (projection_friendly_in_futures (component_projection IM constraint i)
        Hfr s1 s2 Hfuturesi)
    ; intros [sX1 [sX2 [Hs1 [Hs2 HfuturesX]]]].
    subst.
    apply (Hcons sX1 sX2 HfuturesX i i c1 c2 HD1 HD2).
  Qed.

  Lemma final_and_consistent_implies_consistent
      (Hcons : final_and_consistent)
      : consistent.
  Proof.
    unfold consistent; intros.
    apply (Hcons s1 s2 Hfuture j k c1 c2 HDecided1 HDecided2).
  Qed.

  Definition live :=
    forall (tr : @Trace _ (type X)),
      complete_trace_prop X tr ->
      exists (s : vstate X) (n : nat) (i : index) (c : C),
        trace_nth tr n = Some s /\
        (ID i) (s i) = Some c.

End CommuteIndexed.

(* Section 5 *)

Section Estimators.

  (* Defining the estimator function as a relation *)
  Class Estimator state C :=
    { estimator : state -> C -> Prop
    ; estimator_total : forall s : state, exists c : C, estimator s c
    }.

  Context
    {message : Type}
    (X : VLSM message)
    (C : Type)
    (D : vdecision X C)
    (E : Estimator (vstate X) C)
    (estimates := @estimator _ _ E)
    .

  Definition decision_estimator_property
    := forall
      (sigma : vstate X)
      (c : C)
      (HD : D sigma = Some c)
      (sigma' : vstate X)
      (Hreach : in_futures X sigma sigma')
      (c' : C)
      (Hc' : estimates sigma' c'),
      c' = c.

  Lemma estimator_only_has_decision
    (Hde : decision_estimator_property)
    (s : valid_state X)
    (c c_other : C)
    (Hc  : D (proj1_sig s) = (Some c))
    (Hc_other : estimates (proj1_sig s) c_other)
    : c_other = c.
  Proof.
    intros.
    destruct s as [s Hs].
    apply Hde with (sigma := s) (sigma':= s); try assumption.
    apply in_futures_refl.
    assumption.
  Qed.

  Lemma estimator_surely_has_decision
    (Hde : decision_estimator_property)
    (s : valid_state X)
    (c : C)
    (Hc  : D (proj1_sig s) = (Some c))
    : estimates (proj1_sig s) c.
   Proof.
    intros.
    assert(Hc_other : exists (c_other : C), (estimates (proj1_sig s) c_other)). {
      apply estimator_total.
    }
    destruct Hc_other as [c_other Hc_other].
    destruct s as [s Hs].
    assert (Heq : c_other = c). {
      apply Hde with (sigma := s) (sigma' := s); try assumption.
      apply in_futures_refl.
      assumption.
    }
    rewrite <- Heq.
    assumption.
   Qed.

  (* We use the following intermediate result,
     proven above (in two steps) via the estimator property:
     (1) If D(state) = Some c then Estimator(state) = {c}.

     We then fix s1 and s2, such that (in_futures s1 s2) and both are decided and note the following:
     (2) Estimator(s2) = {Decision(s2)}, by (1)
     (3) Estimator(s2) = {Decision(s1)}, by the estimator property.

     Thus Decision(s2) = Decision(s1).
   *)

  Theorem decision_estimator_finality
    : decision_estimator_property -> final X C D.
  Proof.
    intros.
    unfold final.
    intros.
    specialize (in_futures_valid_snd X s1 s2 H0); intro Hps2.
    apply estimator_only_has_decision with (s := (exist _ s2 Hps2)).
    assumption.
    assumption.
    unfold decision_estimator_property in H.
    assert(c2 = c1). {
      apply H with (sigma := s1) (sigma' := s2).
      assumption.
      assumption.
      apply (estimator_surely_has_decision H (exist _ s2 Hps2)).
      assumption.
    }
    rewrite <- H3.
    apply estimator_surely_has_decision.
    assumption.
    assumption.
   Qed.
End Estimators.

Section composite_estimators.

  Context
    {message : Type}
    `{EqDecision index}
    (IM : index -> VLSM message)
    (constraint : composite_label IM -> composite_state IM * option message -> Prop)
    (C : Type)
    (X := composite_vlsm IM constraint)
    (ID : forall i : index, vdecision (IM i) C)
    (IE : forall i : index, Estimator (vstate (IM i)) C).

  Definition composite_projection_decision_estimator_property
    (i : index)
    (Xi := composite_vlsm_constrained_projection IM constraint i)
    := decision_estimator_property Xi C (ID i) (IE i).

End composite_estimators.
