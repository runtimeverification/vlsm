From stdpp Require Import prelude.
From Coq Require Import Streams FunctionalExtensionality FinFun Eqdep.
From VLSM Require Import Lib.Preamble Lib.StreamExtras Lib.ListExtras.
From VLSM Require Import Core.VLSM Core.Plans Core.Composition Core.VLSMProjections.

Section projections.

(** * Composite VLSM projections

In this section we define a VLSM representing the projection of a composite VLSM
to a single node ([composite_vlsm_constrained_projection]), and we study the
relation between their traces.

Let us fix an indexed set of VLSMs <<IM>> and their composition <<X>> using <<constraint>>.

*)

  Context {message : Type}
          {index : Type}
          {IndEqDec : EqDecision index}
          (IM : index -> VLSM message)
          (T := composite_type IM)
          (constraint : composite_label IM -> composite_state IM * option message -> Prop)
          (X := composite_vlsm IM constraint)
  .


  Definition projected_state_prop (j : index) (sj : vstate (IM j)) := exists (s : valid_state X), proj1_sig s j = sj.
  Definition projected_states (j : index) := { sj : vstate (IM j) | projected_state_prop j sj }.

(**
The definition [VLSM1_projection_valid] is deprecated and should not be used.
*)
  Definition VLSM1_projection_valid
             (i : index)
             (li : vlabel (IM i))
             (siomi : vstate (IM i) * option message)
    := vvalid (IM i) li siomi
       /\ projected_state_prop i (fst (vtransition (IM i) li siomi))
       /\ option_valid_message_prop X (snd (vtransition (IM i) li siomi)).


(**
The [VLSMType] of a projection of <<X>> to component <<i>> is the
type of the <<i>>th component of <<X>>.
We defined the signature of the projection to be the same as that of the component,
with the exception that the [initial_message]s for the projection are defined
to be all [valid_message]s of <<X>>:

*)
  Definition composite_vlsm_constrained_projection_sig
    (i : index)
    : VLSMSign (type (IM i))
    :=
    {|   initial_state_prop := vinitial_state_prop (IM i)
     ;   initial_message_prop := fun pmi => exists xm : valid_message X, proj1_sig xm = pmi
     ;   s0 := @s0 _ _ (sign (IM i))
    |}.

(**
[projection_valid]ity is defined as the projection of [input_valid]ity of <<X>>:
*)

  Definition projection_valid
    (i : index)
    (li : vlabel (IM i))
    (siomi : vstate (IM i) * option message)
    :=
    let (si, omi) := siomi in
    exists (s : vstate X),
      s i = si /\ input_valid X (existT i li) (s, omi).

  (**
   The following two lemmas ([projection_valid_impl_VLSM1_projection_valid]
   and [VLSM1_projection_valid_impl_projection_valid]) relate the definition
   of validity in a projection VLSM to the original definition from the VLSM1
   paper: the conclusion is that the VLSM1 definition is weaker.
   *)


  Lemma projection_valid_impl_VLSM1_projection_valid
        (i : index)
        (li : vlabel (IM i))
        (siomi : vstate (IM i) * option message)
    :
      projection_valid i li siomi -> VLSM1_projection_valid i li siomi.
  Proof.
    unfold projection_valid.
    unfold VLSM1_projection_valid.
    destruct siomi as [si omi].
    intros [s [Hsi Hpv]].
    destruct (id Hpv) as [Hs [Homi Hvalid]].
    simpl in Hvalid.
    unfold constrained_composite_valid in Hvalid.
    destruct Hvalid as [Hcvalid Hconstraint].
    simpl in Hcvalid.
    split.
    { subst si. apply Hcvalid. }
    unfold projected_state_prop.
    unfold vvalid in Hcvalid.
    unfold valid_state.
    remember (@composite_label _ index IM) as CL in |-.
    remember (existT i li) as er.
    remember (vtransition X er (s,omi)) as sm'.
    remember (fst sm') as s'.

    destruct sm' as [s'' om'].
    simpl in Heqs'. subst s''.

    assert (Hivt : input_valid_transition X er (s,omi) (s', om')).
    {
      unfold input_valid_transition.
      split.
      { apply Hpv. }
      unfold vtransition in Heqsm'.
      symmetry.
      apply Heqsm'.
    }

    pose proof (Hps' := input_valid_transition_destination X Hivt).

    split.
    {
      exists (exist _ s' Hps').

      pose proof (H := @composite_transition_state_eq message index IndEqDec IM constraint er).
      specialize (H s s' omi om' Hivt). rewrite Heqer in H. simpl in H.
      rewrite <- Hsi. rewrite <- H. simpl. reflexivity.
    }
    unfold option_valid_message_prop.

    fold (vstate X).
    assert (Hveq: snd (vtransition (IM i) li (si, omi)) = snd (vtransition X er (s, omi))).
    {
      rewrite Heqer.
      destruct (vtransition (IM i) li (si, omi)) eqn:Heq1.
      destruct (vtransition X (existT i li) (s, omi)) eqn:Heq2.
      simpl.
      unfold vtransition in Heq2. unfold transition in Heq2. unfold machine in Heq2.
      simpl in Heq2.
      rewrite Hsi in Heq2.
      rewrite Heq1 in Heq2.
      inversion Heq2.
      reflexivity.
    }
    rewrite Hveq.
    rewrite <- Heqsm'.
    exists s'. simpl.
    apply input_valid_transition_outputs_valid_state_message in Hivt.
    assumption.
  Qed.

  Lemma VLSM1_projection_valid_impl_projection_valid
        (i : index)
        (li : vlabel (IM i))
        (siomi : vstate (IM i) * option message)
    :
      VLSM1_projection_valid i li siomi ->
      (exists s : valid_state X,
          proj1_sig s i = (fst siomi)
          /\ constraint (existT i li) (proj1_sig s, (snd siomi))) ->
      option_valid_message_prop X (snd siomi) ->
      projection_valid i li siomi.
  Proof.
    unfold projection_valid.
    unfold VLSM1_projection_valid.
    destruct siomi as [si omi].
    intros H Hpsp Hpmp.
    simpl in Hpsp.
    unfold projected_state_prop in H.
    destruct H as [Hvalid [[s Hs] Homp]].
    destruct Hpsp as [s' [Hs' Hconstraint]].
    exists (proj1_sig s').
    split.
    { apply Hs'. }
    unfold input_valid.
    split.
    { exact (proj2_sig s'). }

    simpl in Hpmp.
    split.
    { apply Hpmp. }
    unfold valid. unfold machine. simpl.
    unfold constrained_composite_valid.
    unfold composite_valid.
    rewrite <- Hs' in Hvalid.
    split.
    { apply Hvalid. }
    apply Hconstraint.
  Qed.

(**
Since [projection_valid]ity is derived from [input_valid]ity, which in turn
depends on [valid]ity in the component, it is easy to see that
[projection_valid]ity implies [valid]ity in the component.
*)
  Lemma projection_valid_implies_valid
    (i : index)
    (li : vlabel (IM i))
    (siomi : vstate (IM i) * option message)
    (Hcomposite : projection_valid i li siomi)
    : vvalid (IM i) li siomi.
  Proof.
    destruct siomi as [si omi].
    destruct Hcomposite as [s [Hsi [_ [_ Hvalid]]]].
    subst; simpl in *.
    destruct Hvalid as [Hvalid Hconstraint].
    assumption.
  Qed.

(**
We define the projection of <<X>> to index <<i>> as the [VLSM] whose signature
is the [composite_vlsm_constrained_projection_sig]nature corresponding to <<i>>,
having the same transition function as <<IM i>>, the <<i>>th component of <<IM>>.
*)
  Definition composite_vlsm_constrained_projection_machine
    (i : index)
    : VLSMClass (composite_vlsm_constrained_projection_sig i) :=
    {|  transition :=  vtransition (IM i)
     ;  valid := projection_valid i
    |}.

  Definition composite_vlsm_constrained_projection
    (i : index)
    : VLSM message
    := mk_vlsm (composite_vlsm_constrained_projection_machine i).

End projections.

(** ** VLSM Projection Traces

This section defines the projection of a composite trace to a single component
([finite_trace_projection_list]) and prove several properties about it,
including that it determines a [VLSM_projection] between the composite VLSM and
its projection (Lemma [component_projection]), as well as between the composite
VLSM pre-loaded with all messages and the original component VLSM preloaded
with all messages (Lemma [preloaded_component_projection]).

We then study the extension of these definitions and results to infinite traces.

Finally, we prove some consequences of the [projection_friendly_prop]erty for
the specific case of projecting a trace to a single component.
*)

Section ProjectionTraces.

Context
  {message : Type}
  {index : Type}
  {IndEqDec : EqDecision index}
  (IM : index -> VLSM message)
  (constraint : composite_label IM -> composite_state IM * option message -> Prop)
  (X := composite_vlsm IM constraint)
  (j : index)
  (Xj := composite_vlsm_constrained_projection IM constraint j)
  .

Definition composite_project_label
  (l : composite_label IM) : option (vlabel (IM j))
  :=
  let i := projT1 l in
  match decide (j = i) with
  | left e => Some (eq_rect_r _ (projT2 l) e)
  | _ => None
  end.

Definition from_projection
  (a : composite_transition_item IM)
  : Prop
  := j = projT1 (l a).

Instance dec_from_projection (a : transition_item) : Decision (from_projection a) :=
  decide (from_projection a).

Lemma initial_state_projection
  (s : vstate X)
  (Hinit : vinitial_state_prop X s)
  : vinitial_state_prop (IM j) (s j).
Proof.
  specialize (Hinit j).
  assumption.
Qed.

(**
Since all [valid_message]s of <<X>> become [initial_message]s in <<Xj>>, the
following result is not surprising.
*)
Lemma valid_message_projection
  (iom : option message)
  (HpmX : option_valid_message_prop X iom)
  : option_valid_message_prop Xj iom.
Proof.
  apply option_initial_message_is_valid.
  destruct iom as [m|];[|exact I].
  exists (exist _ m HpmX).
  reflexivity.
Qed.

(** The projection on component <<j>> of valid traces from <<X>> is valid
for the <<j>>th projection
*)
Lemma component_projection : VLSM_projection X Xj composite_project_label (fun s => s j).
Proof.
  apply basic_VLSM_projection; intro; intros.
  - destruct lX as (i, li).
    unfold composite_project_label in HlX.
    simpl in HlX. case_decide; [|congruence].
    subst. inversion HlX. subst. clear HlX.
    eexists; intuition.
  - destruct lX as (i, li).
    unfold composite_project_label in H.
    simpl in H. destruct (decide _); [|congruence].
    subst. inversion H. subst. clear H.
    apply proj2 in H0.
    simpl in H0.
    cbn.
    destruct (vtransition _ _ _) as (si', _om').
    inversion H0. rewrite state_update_eq. reflexivity.
  - destruct lX as (i, li).
    unfold composite_project_label in H.
    simpl in H. destruct (decide _); [congruence|].
    clear H. apply proj2 in H0. cbn in H0.
    destruct (vtransition _ _ _) as (si', _om').
    inversion H0. rewrite state_update_neq by congruence.
    reflexivity.
  - apply initial_state_projection. assumption.
  - apply valid_message_projection. apply Hv.
Qed.

(* The projection of a finite valid trace remains a valid trace *)
Lemma finite_valid_trace_projection
  (s : vstate X)
  (trx : list (vtransition_item X))
  (Htr : finite_valid_trace_from X s trx)
   : finite_valid_trace_from Xj (s j) (VLSM_projection_trace_project component_projection trx).
Proof.
  revert Htr.
  apply (VLSM_projection_finite_valid_trace_from component_projection).
Qed.

Lemma valid_state_projection
  (s : vstate X)
  (Hps : valid_state_prop X s)
  : valid_state_prop Xj (s j).
Proof.
  revert Hps. apply (VLSM_projection_valid_state component_projection).
Qed.

Lemma in_futures_projection
  (s1 s2 : state)
  (Hfutures : in_futures X s1 s2)
  : in_futures Xj (s1 j) (s2 j).
Proof.
  revert Hfutures.
  apply (VLSM_projection_in_futures component_projection).
Qed.

End ProjectionTraces.

Section PreLoadedProjectionTraces.

Context
  {message : Type}
  {index : Type}
  {IndEqDec : EqDecision index}
  (IM : index -> VLSM message)
  (j : index)
  .

(* The projection of a preloaded finite valid trace remains a preloaded valid trace *)
Lemma preloaded_component_projection : VLSM_projection (pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM)) (pre_loaded_with_all_messages_vlsm (IM j)) (composite_project_label IM j) (fun s => s j).
Proof.
  apply basic_VLSM_projection_preloaded; intro; intros.
  - destruct lX as (i, li).
    unfold composite_project_label in H.
    simpl in H. destruct (decide _); [|congruence].
    subst. inversion H. subst. clear H.
    apply H0.
  - destruct lX as (i, li).
    unfold composite_project_label in H.
    simpl in H. destruct (decide _); [|congruence].
    subst. inversion H. subst. clear H.
    cbn in H0.
    cbn.
    destruct (vtransition _ _ _) as (si', _om').
    inversion H0. rewrite state_update_eq. reflexivity.
  - destruct lX as (i, li).
    unfold composite_project_label in H.
    simpl in H. destruct (decide _); [congruence|].
    clear H. cbn in H0.
    destruct (vtransition _ _ _) as (si', _om').
    inversion H0. rewrite state_update_neq by congruence.
    reflexivity.
  - apply initial_state_projection. assumption.
Qed.

Definition composite_transition_item_projection_from_eq
  (item : composite_transition_item IM)
  (i := projT1 (l item))
  j
  (e : j = i)
  : vtransition_item (IM j)
  :=
  let lj := eq_rect_r _ (projT2 (l item)) e in
  @Build_transition_item _ (type (IM j)) lj (input item) (destination item j) (output item).

Definition composite_transition_item_projection
  (item : composite_transition_item IM)
  (i := projT1 (l item))
  : vtransition_item (IM i)
  :=
  composite_transition_item_projection_from_eq item i eq_refl.

Lemma composite_transition_item_projection_iff
  (item : composite_transition_item IM)
  (i := projT1 (l item))
  : @pre_VLSM_projection_transition_item_project _ (composite_type IM) _
      (composite_project_label IM i) (fun s => s i)
      item
    = Some (composite_transition_item_projection item).
Proof.
  destruct item. subst i. destruct l as (i, li).
  simpl. unfold pre_VLSM_projection_transition_item_project, composite_project_label.
  simpl.
  destruct (decide _); [|congruence].
  f_equal. unfold composite_transition_item_projection, composite_transition_item_projection_from_eq.
  simpl.
  f_equal.
  replace e with (eq_refl (A := index) (x := i)); [reflexivity|].
  apply Eqdep_dec.UIP_dec.
  assumption.
Qed.

Lemma composite_transition_item_projection_neq
  (item : composite_transition_item IM)
  (Hneq: j <> projT1 (l item))
  : @pre_VLSM_projection_transition_item_project _ (composite_type IM) _
      (composite_project_label IM j) (fun s => s j)
      item
    = None.
Proof.
  destruct item. destruct l as (i, li).
  unfold pre_VLSM_projection_transition_item_project, composite_project_label.
  simpl in *.
  destruct (decide _); [congruence|].
  reflexivity.
Qed.

Definition finite_trace_projection_list (tr : list (composite_transition_item IM))
  : list (vtransition_item (IM j)) :=
  @pre_VLSM_projection_trace_project _ (composite_type IM) _
    (composite_project_label IM j) (fun s => s j) tr.

Lemma preloaded_valid_state_projection
  (s : state)
  (Hps : valid_state_prop (pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM)) s)
  : valid_state_prop (pre_loaded_with_all_messages_vlsm (IM j)) (s j).
Proof.
  revert Hps. apply (VLSM_projection_valid_state preloaded_component_projection).
Qed.

Lemma preloaded_finite_valid_trace_projection
  (s : composite_state IM)
  (trx : list (composite_transition_item IM))
  (Htr : finite_valid_trace_from (pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM)) s trx)
   : finite_valid_trace_from (pre_loaded_with_all_messages_vlsm (IM j)) (s j) (VLSM_projection_trace_project preloaded_component_projection trx).
Proof.
  revert Htr. apply (VLSM_projection_finite_valid_trace_from preloaded_component_projection).
Qed.

Lemma preloaded_finite_valid_trace_from_to_projection
  (s s' : composite_state IM)
  (trx : list (composite_transition_item IM))
  (Htr : finite_valid_trace_from_to (pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM)) s s' trx)
   : finite_valid_trace_from_to (pre_loaded_with_all_messages_vlsm (IM j)) (s j) (s' j) (VLSM_projection_trace_project preloaded_component_projection trx).
Proof.
  revert Htr. apply (VLSM_projection_finite_valid_trace_from_to preloaded_component_projection).
Qed.

Lemma preloaded_finite_valid_trace_init_to_projection
  (s s' : composite_state IM)
  (trx : list (composite_transition_item IM))
  (Htr : finite_valid_trace_init_to (pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM)) s s' trx)
   : finite_valid_trace_init_to (pre_loaded_with_all_messages_vlsm (IM j)) (s j) (s' j) (VLSM_projection_trace_project preloaded_component_projection trx).
Proof.
  revert Htr. apply (VLSM_projection_finite_valid_trace_init_to preloaded_component_projection).
Qed.

Lemma pre_loaded_with_all_messages_projection_input_valid_transition_eq
  (s1 s2 : composite_state IM)
  (om1 om2 : option message)
  (l : label)
  (Ht : input_valid_transition (pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM)) l (s1, om1) (s2, om2))
  (Hl : projT1 l = j)
  : input_valid_transition (pre_loaded_with_all_messages_vlsm (IM (projT1 l))) (projT2 l) (s1 (projT1 l), om1) (s2 (projT1 l), om2).
Proof.
  specialize
    (VLSM_projection_input_valid_transition preloaded_component_projection l) as Hivt.
  subst j. specialize (Hivt (projT2 l)).
  spec Hivt.
  { unfold composite_project_label. destruct (decide _); [| elim n; reflexivity].
    replace e with (eq_refl (A := index) (x := projT1 l)); [reflexivity|].
    apply Eqdep_dec.UIP_dec. assumption.
  }
  apply Hivt in Ht. assumption.
Qed.

Lemma pre_loaded_with_all_messages_projection_input_valid_transition_neq
  [s1 s2 : composite_state IM]
  [om1 om2 : option message]
  [l : label]
  (Ht : input_valid_transition (pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM)) l (s1, om1) (s2, om2))
  [i : index]
  (Hi : i <> projT1 l)
  : s1 i = s2 i.
Proof.
  destruct Ht as [[Hs1 [Hom1 [Hv _]]] Ht].
  simpl in Hv. simpl in Ht. cbn in Ht.
  destruct l as [il l].
  destruct (vtransition _ _ _) as (si', om') eqn:Htj.
  inversion Ht. subst; clear Ht.
  simpl in Hi.
  rewrite state_update_neq by congruence.
  reflexivity.
Qed.

End PreLoadedProjectionTraces.

Section ProjectionTraces_membership.

Context
  {message : Type}
  {index : Type}
  {IndEqDec : EqDecision index}
  (IM : index -> VLSM message)
  (constraint : composite_label IM -> composite_state IM * option message -> Prop)
  (X := composite_vlsm IM constraint)
  .

Lemma finite_trace_projection_list_in
  (tr : list (composite_transition_item IM))
  (itemX : composite_transition_item IM)
  (HitemX : itemX ∈ tr)
  (j := projT1 (l itemX))
  : (@Build_transition_item _ (type (IM j)) (projT2 (l itemX)) (input itemX) (destination itemX j) (output itemX)) ∈ (VLSM_projection_trace_project (preloaded_component_projection IM j) tr).
Proof.
  apply elem_of_map_option.
  exists itemX. split; [assumption|].
  unfold pre_VLSM_projection_transition_item_project, composite_project_label.
  subst j.
  case_decide; [|elim H; reflexivity].
  replace H with (eq_refl (A := index) (x := projT1 (l itemX)))
  ; [reflexivity|].
  apply Eqdep_dec.UIP_dec. assumption.
Qed.

Lemma finite_trace_projection_list_in_rev
  (tr : list (composite_transition_item IM))
  (j : index)
  (itemj : vtransition_item (IM j))
  (Hitemj : itemj ∈ (VLSM_projection_trace_project (preloaded_component_projection IM j) tr))
  : exists (itemX : composite_transition_item IM), itemX ∈ tr /\
    output itemX = output itemj /\
    input itemX = input itemj /\
    destination itemX j = destination itemj /\
    exists (Hl1 : j = projT1 (l itemX)),
    eq_rect_r _ (projT2 (l itemX)) Hl1 = l itemj.
Proof.
  apply elem_of_map_option in Hitemj as [itemX [HitemX HitemX_pr]].
  exists itemX. split; [assumption|].
  unfold pre_VLSM_projection_transition_item_project in HitemX_pr.
  destruct (composite_project_label _ _ _) as [lY|] eqn:Hly; [|congruence].
  inversion HitemX_pr. subst. clear HitemX_pr.
  repeat split.
  unfold composite_project_label in Hly.
  case_decide; [|congruence].
  exists H.
  inversion Hly. reflexivity.
Qed.

End ProjectionTraces_membership.

Section binary_free_composition_projections.

(** ** Projections of Free composition of two VLSMs

This projections are used in defining the [byzantine_trace_prop]erties.

*)
  Context
    {message : Type}
    (M1 M2 : VLSM message)
    .

  Definition binary_free_composition_fst : VLSM message :=
    composite_vlsm_constrained_projection (binary_IM M1 M2) (free_constraint _) first.

  Definition binary_free_composition_snd : VLSM message :=
    composite_vlsm_constrained_projection (binary_IM M1 M2) (free_constraint _) second.

End binary_free_composition_projections.

Section fixed_projection.

Context {message : Type}
        {index : Type}
        {IndEqDec : EqDecision index}
        (IM : index -> VLSM message)
        (T := composite_type IM)
        (constraint : composite_label IM -> composite_state IM * option message -> Prop)
        (X := composite_vlsm IM constraint)
.

(** ** Projection traces are Byzantine

Let us fix an index <<j>> and let <<Xj>> be the projection of <<X>> on
component <<j>>.

In this section we establish some basic properties for projections, building up
to Lemma [proj_pre_loaded_with_all_messages_incl], which guarantees that all
[valid_trace]s of <<Xj>> are also [valid_trace]s for the
[pre_loaded_with_all_messages_vlsm] associated to the component <<IM j>>.
In particular this ensures that the byzantine traces of <<IM j>> include all
[valid_trace]s of <<Xj>> (see Lemma [pre_loaded_with_all_messages_alt_eq]).

*)

Context
  (j : index)
  (Xj := composite_vlsm_constrained_projection IM constraint j)
  .

Lemma projection_valid_input_valid
  (l : vlabel Xj)
  (som : vstate Xj * option message)
  (Hv : vvalid Xj l som)
  : input_valid Xj l som.
Proof.
  destruct som as (s, om).
  destruct (id Hv) as [sX [Hsi [Hps [Hopm _]]]].
  repeat split.
  - subst. apply valid_state_projection. assumption.
  - apply valid_message_projection. assumption.
  - assumption.
Qed.

Lemma projection_valid_implies_composition_valid_message
  (l : label)
  (s : state)
  (om : option message)
  (Hv : vvalid Xj l (s, om))
  : option_valid_message_prop X om.
Proof.
  destruct Hv as [sx [Hs [HpsX [HpmX Hv]]]].
  assumption.
Qed.

Lemma projection_valid_implies_projection_valid_message
  (l : label)
  (s : state)
  (om : option message)
  (Hv : vvalid Xj l (s, om))
  : option_valid_message_prop Xj om.
Proof.
  apply valid_message_projection.
  revert Hv.
  apply projection_valid_implies_composition_valid_message.
Qed.

Lemma projection_valid_implies_projection_valid_state
  (lj : label)
  (sj : state)
  (om : option message)
  (Hv : vvalid Xj lj (sj, om))
  : valid_state_prop Xj sj.
Proof.
  destruct Hv as [s [Heq_sj [Hs _]]].
  subst sj. revert Hs. apply valid_state_projection.
Qed.

Lemma projection_valid_implies_projection_valid_state_message_outputs
    (l : label)
    (s : state)
    (om : option message)
    (Hv : vvalid Xj l (s, om))
    s' om'
    (Ht : vtransition (IM j) l (s, om) = (s', om'))
    : valid_state_message_prop Xj s' om'.
Proof.
  apply projection_valid_implies_projection_valid_state in Hv as Hs.
  destruct Hs as [_om Hs].
  apply projection_valid_implies_projection_valid_message in Hv as Hom.
  destruct Hom as [_s Hom].
  apply (valid_generated_state_message Xj  _ _ Hs _ _ Hom _ Hv _ _ Ht).
Qed.

Lemma projection_valid_implies_destination_projection_valid_state
    (l : label)
    (s : state)
    (om : option message)
    (Hv : vvalid Xj l (s, om))
    s' om'
    (Ht : vtransition (IM j) l (s, om) = (s', om'))
    : valid_state_prop Xj s'.
Proof.
  apply projection_valid_implies_projection_valid_state_message_outputs
    with (s' := s') (om' := om') in Hv; [|assumption].
  eexists. apply Hv.
Qed.

Lemma projection_valid_implies_destination_projection_valid_message
    (l : label)
    (s : state)
    (om : option message)
    (Hv : vvalid Xj l (s, om))
    s' om'
    (Ht : vtransition (IM j) l (s, om) = (s', om'))
    : option_valid_message_prop Xj om'.
Proof.
  apply projection_valid_implies_projection_valid_state_message_outputs
    with (s' := s') (om' := om') in Hv; [|assumption].
  eexists. apply Hv.
Qed.

(**
Interestingly enough, <<Xj>> cannot produce any additional messages than
the initial ones available from <<X>>.
*)
Lemma valid_message_projection_rev
  (iom : option message)
  (Hpmj: option_valid_message_prop Xj iom)
  : option_valid_message_prop X iom.
Proof.
  destruct iom as [m|];[|apply option_valid_message_None].
  destruct Hpmj as [sj Hpmj].
  inversion Hpmj; subst.
  - destruct Hom as [pm <-]. apply @proj2_sig.
  - destruct Hv as [sX [Heqs Hv]].
    subst s.
    set (lX := existT j l) in Hv.
    eexists.
    apply (input_valid_state_message_outputs X _ _ _ Hv).
    simpl. replace (vtransition (IM j) _ _) with (sj, Some m). reflexivity.
Qed.

(**
As a stepping stone towards proving trace inclusion between <<Xj>> and
the [pre_loaded_with_all_messages_vlsm] associated to <<IM j>>, we prove that the
[valid_state_message_prop]erty is transferred.
*)
Lemma proj_pre_loaded_with_all_messages_valid_state_message_preservation
  (PreLoaded := pre_loaded_with_all_messages_vlsm (IM j))
  (s : state)
  (om : option message)
  (Hps : valid_state_message_prop Xj s om)
  : valid_state_message_prop PreLoaded s om.
Proof.
  induction Hps.
  - apply (valid_initial_state_message PreLoaded).
    assumption. destruct om;exact I.
  - apply (valid_generated_state_message PreLoaded) with s _om _s om l; try assumption.
    eapply (projection_valid_implies_valid IM). exact Hv.
Qed.

(**
We can now finally prove the main result for this section:
*)
Lemma proj_pre_loaded_with_all_messages_incl
  (PreLoaded := pre_loaded_with_all_messages_vlsm (IM j))
  : VLSM_incl Xj PreLoaded.
Proof.
  apply (basic_VLSM_incl (machine Xj) (machine PreLoaded)); intro; intros.
  - assumption.
  - apply initial_message_is_valid; exact I.
  - eapply (projection_valid_implies_valid IM).
    apply Hv.
  - apply H.
Qed.

End fixed_projection.

Section projection_friendliness_sufficient_condition.

Context {message : Type}
        {index : Type}
        {IndEqDec : EqDecision index}
        (IM : index -> VLSM message)
        (T := composite_type IM)
        (constraint : composite_label IM -> composite_state IM * option message -> Prop)
        (X := composite_vlsm IM constraint)
.


(** ** A sufficient condition for the [projection_friendly_prop]erty. *)

Context
  (j : index)
  (Xj := composite_vlsm_constrained_projection IM constraint j)
  .

(**
This condition states that [input_valid]ity in a projection <<Xj>>
can be lifted to any [valid_state] in <<X>> which projects to the
corresponding <<Xj>> state.
*)

Definition projection_friendliness_sufficient_condition
  := forall
    (lj : vlabel (IM j))
    (sj : vstate (IM j))
    (om : option message)
    (Hiv : input_valid Xj lj (sj, om))
    (s : vstate X)
    (Hs : valid_state_prop X s)
    (Hsi : s j = sj)
    , vvalid X (existT j lj) (s, om).

Lemma projection_friendliness_sufficient_condition_valid_state
  (Hfr : projection_friendliness_sufficient_condition)
  (s : state)
  (Hp : valid_state_prop Xj s)
  : valid_state_prop X (lift_to_composite_state IM j s).
Proof.
  induction Hp using valid_state_prop_ind.
  - apply initial_state_is_valid. apply (lift_to_composite_state_initial IM j). assumption.
  - destruct Ht as [Hvj Ht].
    specialize (Hfr _ _ _ Hvj _ IHHp).
    spec Hfr; [apply state_update_eq|].
    exists om'.
    destruct Hvj as [_ [_ Hvj]].
    apply (projection_valid_implies_composition_valid_message IM) in Hvj as Hom.
    destruct IHHp as [_om HsX].
    destruct Hom as [_s Hom].
    specialize (valid_generated_state_message X _ _ HsX _ _ Hom _ Hfr) as Hgen.
    apply Hgen.
    simpl.
    unfold lift_to_composite_state at 1.
    rewrite state_update_eq.
    replace (vtransition (IM j) _ _) with (s', om').
    f_equal.
    apply state_update_twice.
Qed.

(**
The result below shows that the [projection_friendliness_sufficient_condition]
might be too strong, in the sense that it allows any trace from the
projection to be lifted direclty to <<X>>
(all other machines stay in their initial state).
*)
Lemma projection_friendliness_lift_to_composite_vlsm_full_projection
  (Hfr : projection_friendliness_sufficient_condition)
  : VLSM_full_projection Xj X (lift_to_composite_label IM j) (lift_to_composite_state IM j).
Proof.
  apply basic_VLSM_full_projection; intro; intros.
  - apply (Hfr _ _ _ Hv); [|apply state_update_eq].
    apply (projection_friendliness_sufficient_condition_valid_state Hfr).
    apply Hv.
  - unfold lift_to_composite_label, vtransition. simpl.
    unfold lift_to_composite_state at 1. rewrite state_update_eq.
    replace (vtransition (IM j) _ _) with (s', om')
      by (symmetry; apply H).
    f_equal. unfold lift_to_composite_state. apply state_update_twice.
  - apply (lift_to_composite_state_initial IM j). assumption.
  - destruct Hv as [Hs [Homj [sX [Heqs [HsX [Hom Hv]]]]]]. exact Hom.
Qed.

End projection_friendliness_sufficient_condition.
