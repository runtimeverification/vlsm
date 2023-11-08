From VLSM.Lib Require Import Itauto.
From stdpp Require Import prelude finite.
From VLSM.Lib Require Import EquationsExtras.
From VLSM.Lib Require Import Preamble ListSetExtras.
From VLSM.Core Require Import VLSM PreloadedVLSM Composition VLSMEmbedding.

(** * Traceable VLSMs

  This section introduces [TraceableVLSM]s, characterized by the fact that from
  any constrained state we can derive the possible (valid) transitions leading
  to that state.

  We derive several properties of these machines and their composition,
  including the possibility of extracting a constrained trace from a constrained
  state (see [reachable_composite_state_to_trace]) as well as that of extracting
  a trace with monotonic global equivocation
  (see [state_to_minimal_equivocation_trace_equivocation_monotonic]).
*)

(**
  A class with a measure of size for states which is monotonic for valid transitions.
*)
Class TransitionMonotoneVLSM `(X : VLSM message) (state_size : state X -> nat) : Prop :=
{
  transition_monotonicity :
    forall s1 s2 : state X, valid_transition_next X s1 s2 -> state_size s1 < state_size s2
}.

#[global] Hint Mode TransitionMonotoneVLSM - ! - : typeclass_instances.

#[export] Instance pre_loaded_TransitionMonotoneVLSM
  `(X : VLSM message) (state_size : state X -> nat)
  `{!TransitionMonotoneVLSM X state_size}
  : TransitionMonotoneVLSM (pre_loaded_with_all_messages_vlsm X) state_size.
Proof.
  constructor; intros s1 s2 Ht.
  by apply transition_monotonicity, valid_transition_next_preloaded_iff.
Qed.

Lemma transition_monotone_in_futures
  `(X : VLSM message) `{TransitionMonotoneVLSM _ X}
  [s sf : state X] (Hfutures : in_futures X s sf) :
  state_size s <= state_size sf.
Proof.
  destruct Hfutures as [tr Htr].
  induction Htr; [done |].
  by apply input_valid_transition_forget_input,
    transition_next, transition_monotonicity in Ht; lia.
Qed.

Lemma transition_monotone_empty_trace
  `(X : VLSM message) `{TransitionMonotoneVLSM _ X} :
  forall [s : state X] [tr : list (transition_item X)],
    finite_valid_trace_from_to X s s tr -> tr = [].
Proof.
  intros s tr Htr; remember s as f; rewrite Heqf in Htr at 1.
  induction Htr using finite_valid_trace_from_to_ind; [done | subst].
  assert (state_size s <= state_size s')
    by (apply transition_monotone_in_futures; [| eexists]; done).
  by apply input_valid_transition_forget_input,
    transition_next, transition_monotonicity in Ht; lia.
Qed.

(**
  A class characterizing VLSMs with reversible transitions. A VLSM is traceable
  when given a constrained state, one can compute a set of constrained transitions
  leading to it.

  We assume that such machines are [TransitionMonotoneVLSM]s and that the
  set of constrained transitions associated to a constrained state is empty
  iff the state is initial.
*)
Class TraceableVLSM
  `(X : VLSM message)
  (state_destructor : state X -> list (transition_item X * state X))
  (state_size : state X -> nat)
  : Prop :=
{
  tv_monotone :> TransitionMonotoneVLSM X state_size;
  tv_state_destructor_destination :
    forall (s' s : state X) (item : transition_item X),
      (item, s) ∈ state_destructor s' -> destination item = s';
  tv_state_destructor_transition :
    forall s' : state X,
      valid_state_prop (pre_loaded_with_all_messages_vlsm X) s' ->
      forall (s : state X) (item : transition_item X),
        (item, s) ∈ state_destructor s' ->
        input_valid_transition_item (pre_loaded_with_all_messages_vlsm X) s item;
  tv_state_destructor_initial :
    forall (s : state X) (Hs : valid_state_prop (pre_loaded_with_all_messages_vlsm X) s),
      initial_state_prop X s <-> state_destructor s = [];
}.

#[global] Hint Mode TraceableVLSM - ! - - : typeclass_instances.

Section sec_traceable_vlsm_props.

Context
  `(X : VLSM message)
  (state_size : state X -> nat)
  (state_destructor : state X -> list (transition_item X * state X))
  `{!TraceableVLSM X state_destructor state_size}
  (R := pre_loaded_with_all_messages_vlsm X)
  .

Lemma tv_state_destructor_size :
  forall s' : state X, valid_state_prop R s' ->
  forall (s : state X) (item : transition_item X),
    (item, s) ∈ state_destructor s' -> state_size s < state_size s'.
Proof.
  intros.
  apply transition_monotonicity.
  erewrite <- tv_state_destructor_destination by done.
  econstructor.
  by eapply valid_transition_preloaded_iff, input_valid_transition_forget_input,
    tv_state_destructor_transition.
Qed.

(**
  Given any constrained state we can extract a trace leading to it by recursively
  following the transitions leading to it.
*)
Equations state_to_trace (s' : state X) (Hs' : valid_state_prop R s') :
  state X * list (transition_item X) by wf (state_size s') lt :=
state_to_trace s' Hs' with inspect (state_destructor s') :=
|               [] eq: _         => (s', [])
| ((item, s) :: _) eq: Hdestruct =>
  let (is, tr) := state_to_trace s _ in (is, tr ++ [item]).
Next Obligation.
Proof.
  cbn; intros.
  eapply tv_state_destructor_transition; [done |].
  by rewrite Hdestruct; left.
Qed.
Next Obligation.
Proof.
  cbn; intros.
  eapply tv_state_destructor_size; [done |].
  by rewrite Hdestruct; left.
Qed.

(** Traces extracted using [state_to_trace] are constrained traces. *)
Lemma reachable_state_to_trace :
  forall (s : state X) (Hs : valid_state_prop R s) is tr,
    state_to_trace s Hs = (is, tr) -> finite_valid_trace_init_to R is s tr.
Proof.
  intros s Hs.
  apply_funelim (state_to_trace s Hs); clear s Hs.
  - intros s' Hdestruct ? ? ? ? Heqis_tr.
    inversion Heqis_tr; subst; split.
    + by apply finite_valid_trace_from_to_empty with (X := R).
    + by eapply @tv_state_destructor_initial with (X := X).
  - intros ? ? ? ? ? ? Hind ? ? ? Heqis_tr.
    destruct (state_to_trace s _) as [_is _tr]; inversion Heqis_tr; subst; clear Heqis_tr.
    split; [| by eapply Hind].
    replace s' with (destination item)
      by (eapply tv_state_destructor_destination; rewrite Hdestruct; left).
    eapply (finite_valid_trace_from_to_app R); [by apply Hind |].
    cut (input_valid_transition_item R s item).
    {
      by destruct item; cbn; apply (finite_valid_trace_from_to_singleton R).
    }
    eapply tv_state_destructor_transition; [done |].
    by rewrite Hdestruct; left.
Qed.

End sec_traceable_vlsm_props.

(** * Composition of TraceableVLSMs *)

Section sec_traceable_vlsm_composition.

Context
  {message : Type}
  `{finite.Finite index}
  (IM : index -> VLSM message)
  (state_destructor : forall i, state (IM i) -> list (transition_item (IM i) * state (IM i)))
  (state_size : forall i, state (IM i) -> nat)
  `{forall i, TraceableVLSM (IM i) (state_destructor i) (state_size i)}
  (Free := free_composite_vlsm IM)
  (RFree := pre_loaded_with_all_messages_vlsm Free)
  .

(**
  The following definitions and lemmas lift the corresponding notions and
  results from [TraceableVLSM]s to their composition.
*)

Definition lift_to_composite_transition_item_state
  (s : composite_state IM) (i : index) (item_s : transition_item (IM i) * state (IM i))
  : composite_transition_item IM * composite_state IM :=
  (lift_to_composite_transition_item IM s i item_s.1,
    lift_to_composite_state IM s i item_s.2).

Definition composite_state_destructor (s' : composite_state IM) (i : index)
  : list (composite_transition_item IM * composite_state IM) :=
  map (lift_to_composite_transition_item_state s' i) (state_destructor i (s' i)).

Definition composite_state_size (s : composite_state IM) :=
  foldr Nat.add 0 (map (fun i => state_size i (s i)) (enum index)).

Lemma composite_state_update_size_monotone :
  forall (s : composite_state IM) (i : index) (si : state (IM i)),
  state_size i (s i) < state_size i si ->
  composite_state_size s < composite_state_size (lift_to_composite_state  IM s i si).
Proof.
  intros s i si Hlt.
  unfold composite_state_size.
  generalize (NoDup_enum index); generalize (elem_of_enum i); generalize (enum index).
  induction l; inversion 1 as []; subst.
  - inversion 1 as [| ? ? Hna _]; subst; cbn.
    rewrite state_update_eq.
    replace (foldr Nat.add 0 (map (fun i : index => state_size i (s i)) l))
       with (foldr Nat.add 0 (map (fun i : index =>
               state_size i (lift_to_composite_state IM s a si i)) l))
    ; [lia |].
    revert Hna; clear; induction l; [done |].
    intros []%not_elem_of_cons.
    by cbn; rewrite state_update_neq, IHl.
  - inversion 1; subst.
    cbn; rewrite state_update_neq by congruence.
    by apply Nat.add_lt_mono_l, IHl.
Qed.

Lemma composite_tv_state_destructor_destination :
  forall (s' s : composite_state IM) (item : composite_transition_item IM) i,
     (item, s) ∈ composite_state_destructor s' i -> destination item = s'.
Proof.
  intros *; unfold composite_state_destructor; rewrite elem_of_list_fmap.
  intros ([itemi si] & [= -> ->] & Hin).
  cbn; unfold lift_to_composite_state.
  by erewrite tv_state_destructor_destination, state_update_id.
Qed.

Lemma composite_tv_state_destructor_transition :
  forall (s' : composite_state IM), valid_state_prop RFree s' ->
  forall (s : composite_state IM) (item : composite_transition_item IM) (i : index),
  (item, s) ∈ composite_state_destructor s' i ->
  input_valid_transition_item RFree s item.
Proof.
  intros s' Hs' s item i.
  unfold composite_state_destructor; rewrite elem_of_list_fmap.
  intros ([itemi si] & [=-> ->] & Hin).
  eapply (VLSM_weak_embedding_input_valid_transition
           (lift_to_preloaded_free_weak_embedding IM i s' Hs')).
  eapply @tv_state_destructor_transition; [done | | done].
  by eapply valid_state_project_preloaded_to_preloaded_free.
Qed.

Lemma composite_tv_state_destructor_index  :
  forall (s' s : composite_state IM) (item : composite_transition_item IM) i,
    (item, s) ∈ composite_state_destructor s' i -> projT1 (l item) = i.
Proof.
  intros *.
  unfold composite_state_destructor; rewrite elem_of_list_fmap.
  by intros ((itemi, si) & [= ->] & Hin).
Qed.

Lemma composite_tv_state_destructor_state_update :
  forall (s' : composite_state IM), valid_state_prop RFree s' ->
  forall (s : composite_state IM) (item : composite_transition_item IM) (i : index),
  (item, s) ∈ composite_state_destructor s' i ->
  s' = state_update IM s i (destination item i).
Proof.
  intros s' Hs' s item i Hin.
  replace s' with (destination item) in *
    by (eapply composite_tv_state_destructor_destination; done).
  eapply composite_tv_state_destructor_index  in Hin as Hl.
  eapply composite_tv_state_destructor_transition in Hin as [_ Ht]; [| done].
  destruct item, l; cbn in *; destruct (transition _ _ _); inversion Ht; subst.
  by state_update_simpl.
Qed.

Lemma composite_tv_state_destructor_initial :
  forall (s : composite_state IM), valid_state_prop RFree s ->
  forall i,
    initial_state_prop (IM i) (s i)
      <->
    composite_state_destructor s i = [].
Proof.
  unfold composite_state_destructor; split; intros Hinit.
  - replace (state_destructor i (s i))
      with (@nil (transition_item (IM i) * state (IM i))); [done |].
    symmetry; apply tv_state_destructor_initial; [| done].
    by eapply valid_state_project_preloaded_to_preloaded_free.
  - apply tv_state_destructor_initial.
    + by eapply valid_state_project_preloaded_to_preloaded_free.
    + by eapply fmap_nil_inv.
Qed.

Lemma composite_tv_state_destructor_reflects_initiality :
  forall (s' : composite_state IM), valid_state_prop RFree s' ->
  forall (i : index) (s : composite_state IM) (item : composite_transition_item IM),
    (item, s) ∈ composite_state_destructor s' i ->
    forall j, initial_state_prop (IM j) (s' j) -> s j = s' j.
Proof.
  intros s' Hs' i s item Hdestruct.
  apply composite_tv_state_destructor_state_update in Hdestruct as Heqs'; [| done].
  intros j Hinit; destruct (decide (i = j)); subst; [| by state_update_simpl].
  apply composite_tv_state_destructor_initial in Hinit; [| done].
  by rewrite Hinit in Hdestruct; inversion Hdestruct.
Qed.

Lemma composite_tv_state_destructor_size :
  forall (s' : composite_state IM), valid_state_prop RFree s' ->
  forall (s : composite_state IM) (item : composite_transition_item IM) (i : index),
    (item, s) ∈ composite_state_destructor s' i ->
    composite_state_size s < composite_state_size s'.
Proof.
  intros s' Hs' s item i.
  unfold composite_state_destructor; rewrite elem_of_list_fmap.
  intros ([itemi si] & [= -> ->] & Hin).
  replace s' with (state_update IM (state_update IM s' i si) i (s' i)) at 2.
  - apply composite_state_update_size_monotone.
    state_update_simpl.
    eapply tv_state_destructor_size; [done | | done].
    by eapply valid_state_project_preloaded_to_preloaded_free.
  - by rewrite state_update_twice, state_update_id.
Qed.

Lemma composite_state_destructor_lookup_reachable :
  forall s' : composite_state IM, valid_state_prop RFree s' ->
  forall i n item s, composite_state_destructor s' i !! n = Some (item, s) ->
    input_valid_transition_item RFree s item.
Proof.
  intros s' Hs' i n item s Hdestruct.
  by eapply composite_tv_state_destructor_transition, elem_of_list_lookup_2.
Qed.

Lemma composite_state_destructor_head_reachable :
  forall s' : composite_state IM, valid_state_prop RFree s' ->
  forall i item s, head (composite_state_destructor s' i) = Some (item, s) ->
  input_valid_transition_item RFree s item.
Proof.
  intros s' Hs' i item s Hdestruct.
  by eapply composite_tv_state_destructor_transition, head_Some_elem_of.
Qed.

(**
  Given a [composite_state] for a composition of [TraceableVLSM]s,
  [composite_state_destructor] will return a set of possible transitions leading
  to that state. Therefore, when trying to reconstruct a particular trace leading
  to the given state, we must choose one among the possible transitions.

  Let us define the type of such a choice function, which takes a composite
  constrained state and a list of indices as arguments and returns one of the
  indices and a position in the list of possible transitions to the state for
  that particular index.
*)

Definition choice_function : Type :=
  forall s' : composite_state IM, valid_state_prop RFree s' -> list index -> index * nat.

(**
  Given a [choice_function] and a particular instance of its arguments,
  we say that the choice function is choosing well, provided that:

  - if the set of indices is non-empty, then the returned index must belong to it

  - if the component state corresponding to the returned index in not initial, then
    the returned position must identify a transition leading to the given state

  - the choice does not depend on the particular proof for the composite constrained state
*)
Record ChoosingWell
  (choose : choice_function)
  (s' : composite_state IM)
  (Hs' : valid_state_prop RFree s')
  (indices : list index)
  : Prop :=
{
  cw_proof_independent :
    forall Hs'' : valid_state_prop RFree s',
      choose s' Hs' indices = choose s' Hs'' indices;
  cw_chosen_index_in_indices :
    indices <> [] -> (choose s' Hs' indices).1 ∈ indices;
  cw_chosen_position_exists :
    forall (i : index) (n : nat),
      choose s' Hs' indices = (i, n) ->
      ~ initial_state_prop (IM i) (s' i) ->
      is_Some (composite_state_destructor s' i !! n);
}.

Lemma choosing_well_position_exists :
  forall
    (choose : choice_function)
    (s' : composite_state IM) (Hs' : valid_state_prop RFree s')
    (indices : list index) (Hwell : ChoosingWell choose s' Hs' indices)
    (i_n :=  choose s' Hs' indices),
      composite_state_destructor s' i_n.1 <> [] ->
      composite_state_destructor s' i_n.1 !! i_n.2 <> None.
Proof.
  intros choose s' Hs' indices Hchoose i_n Hdestruct.
  eapply not_eq_None_Some, cw_chosen_position_exists; [done | |].
  - by destruct (choose _ _ _).
  - by contradict Hdestruct; apply composite_tv_state_destructor_initial.
Qed.

(**
  This is a property of the set of indices argument to a [choice_function],
  guaranteeing that the component states for the non-included indices are initial.
*)
Definition not_in_indices_initial_prop
  (s' : composite_state IM)
  (indices : list index)
  : Prop :=
  forall i, i ∉ indices -> initial_state_prop (IM i) (s' i).

(**
  The constrained transitions leading to a composite constrained state reflect
  the [not_in_indices_initial_prop]erty, or, alternately, the
  [composite_state_destructor] function reflects it.
*)
Lemma composite_tv_state_destructor_preserves_not_in_indices_initial  :
  forall
    (s' : composite_state IM) (Hs' : valid_state_prop RFree s')
    (i : index) (n : nat)
    (s : composite_state IM) (item : composite_transition_item IM),
      composite_state_destructor s' i !! n = Some (item, s) ->
    forall (indices : list index),
      not_in_indices_initial_prop s' indices ->
      not_in_indices_initial_prop s indices.
Proof.
  intros s' Hs' * Heq indices Hinits' j Hj.
  by erewrite composite_tv_state_destructor_reflects_initiality;
    [apply Hinits' | | eapply elem_of_list_lookup_2 | apply Hinits'].
Qed.

(**
  Removing an index whose associated set of transitions is empty
  (so that the corresponding component state is initial) preserves
  [not_in_indices_initial_prop].
*)
Lemma set_remove_preserves_not_in_indices_initial :
  forall (s' : composite_state IM), valid_state_prop RFree s' ->
  forall (i : index), composite_state_destructor s' i = [] ->
  forall (indices : list index),
  not_in_indices_initial_prop s' indices ->
  not_in_indices_initial_prop s' (StdppListSet.set_remove i indices).
Proof.
  intros s' Hs' i Hdestruct indices Hinit j Hj.
  destruct (decide (j ∈ indices)); [| by apply Hinit].
  destruct (decide (j = i)); [by subst; apply composite_tv_state_destructor_initial |].
  by contradict Hj; subst; apply StdppListSet.set_remove_3.
Qed.

(**
  A [choice_function] is choosing well if it is [ChoosingWell] for any
  instance of its arguments (a constrained state and a set of indices)
  satisfying the [not_in_indices_initial_prop]erty.
*)
Definition choosing_well (choose : choice_function) : Prop :=
  forall (s' : composite_state IM) (Hs' : valid_state_prop RFree s') (indices : list index),
    NoDup indices -> not_in_indices_initial_prop s' indices ->
      ChoosingWell choose s' Hs' indices.

(**
  Given a composite constrained state, a [choice_function] and an initial
  set of indices, we can extract a trace leading to that state by following
  backwards the transitions yielded by the choice function until the states
  corresponding to any of the given indices become initial states.
*)
Equations indexed_composite_state_to_trace
  (choose : choice_function)
  (s' : composite_state IM) (Hs' : valid_state_prop RFree s')
  (indices : list index)
  : composite_state IM * list (composite_transition_item IM)
  by wf (length indices + composite_state_size s') lt :=
| choose, s', Hs', [] => (s', [])
| choose, s', Hs', indices with inspect (choose s' Hs' indices) =>
  | i_n eq: Hchoice with inspect (composite_state_destructor s' i_n.1 !! i_n.2) =>
    | (Some (item, s)) eq: Hdestruct with indexed_composite_state_to_trace choose s _ indices => {
      | (is, tr) => (is, tr ++ [item]) }
    |             None eq: Hdestruct with inspect (decide (i_n.1 ∈ indices)) =>
      | (right _) eq: Hni => (s', [])
      |  (left _) eq: Hi with inspect (decide (composite_state_destructor s' i_n.1 = [])) =>
        | (right _) eq: Hn  => (s', [])
        |  (left _) eq: Hnn => indexed_composite_state_to_trace choose s' Hs'
                                 (StdppListSet.set_remove i_n.1 indices).
Next Obligation.
Proof.
  by cbn; intros; eapply input_valid_transition_origin, composite_state_destructor_lookup_reachable.
Qed.
Next Obligation.
Proof.
  cbn; intros.
  cut (composite_state_size s < composite_state_size s'); [lia |].
  by eapply composite_tv_state_destructor_size, elem_of_list_lookup_2.
Qed.
Next Obligation.
Proof.
  intros.
  cut (S (length (StdppListSet.set_remove i_n.1 indices)) <= length indices);
    [unfold indices; lia |].
  by rewrite <- set_remove_length; [lia |].
Qed.

(**
  For any composite constrained state <<s>> and for any index <<i>> for which the
  component state <<s i>> has the [initial_state_prop]erty, the component state of
  index <<i>> of the origin state of the trace extracted from <<s>> is equal
  to <<s i>>.
*)
Lemma indexed_composite_state_to_trace_reflects_initiality_1 :
  forall (choose : choice_function)
    (s : composite_state IM) (Hs : valid_state_prop RFree s)
    (indices : list index),
  forall (i : index), initial_state_prop (IM i) (s i) ->
    forall is tr, indexed_composite_state_to_trace choose s Hs indices = (is, tr) ->
    is i = s i.
Proof.
  intros ? ? ? ?.
  apply_funelim (indexed_composite_state_to_trace choose s Hs indices);
    clear choose s Hs indices; intros ? ? ?.
  - by inversion 2.
  - intros * -> Hind _ _ i Hi is' tr' [= -> <-].
    replace (s' i) with (s i) in *.
    + by eapply Hind.
    + by eapply composite_tv_state_destructor_reflects_initiality;
        [| eapply elem_of_list_lookup_2 |].
  - by inversion 5.
  - by intros idx indices [j nj] Hdestruct _ Hj _ _ -> Hind _ _ _ _ i Hi is tr Heqis_tr; eapply Hind.
  - by inversion 6.
Qed.

(**
  The components of an origin of a trace extracted through [indexed_composite_state_to_trace]
  are initial for any index from the set of indices provided as argument.
*)
Lemma indexed_composite_state_to_trace_result_state :
  forall (choose : choice_function), choosing_well choose ->
  forall (s : composite_state IM) (Hs : valid_state_prop RFree s),
  forall (indices : list index), NoDup indices ->
    not_in_indices_initial_prop s indices ->
    forall is tr, indexed_composite_state_to_trace choose s Hs indices = (is, tr) ->
    forall i, i ∈ indices -> initial_state_prop (IM i) (is i).
Proof.
  intros ? Hchoose *; revert Hchoose.
  apply_funelim (indexed_composite_state_to_trace choose s Hs indices);
    clear choose s Hs indices.
  - by intros ? ? ? ? ? ? ? ? ? ? Hi; inversion Hi.
  - intros choose s' Hs' idx indices (j, nj) item s Hdestruct -> is tr -> Hind
      _ _ Hchoose Hnodup Hinitial is' tr' [= -> <-] i Hi.
    by eapply Hind; [| | eapply composite_tv_state_destructor_preserves_not_in_indices_initial  | |].
  - by intros; subst; elim n; apply cw_chosen_index_in_indices; [apply Hchoose |].
  - intros choose s' Hs' idx indices (j, nj) Hdestruct _ Hj _ _ -> Hind
      _ _ _ _ Hchoose Hnodup Hinitial is tr Heqis_tr i Hi.
    rewrite Heqis_tr in Hind.
    remember (StdppListSet.set_remove _ _) as removed.
    destruct (decide (i ∈ removed)).
    + subst; eapply Hind; [done | | | done | done].
      * by apply StdppListSet.set_remove_nodup.
      * by apply set_remove_preserves_not_in_indices_initial.
    + replace i with j in * by (destruct (decide (i = j));
        [| contradict n; subst; apply StdppListSet.set_remove_3]; done).
      by erewrite indexed_composite_state_to_trace_reflects_initiality_1;
        [.. | done]; apply composite_tv_state_destructor_initial.
  - by intros; subst; clear Heq1; contradict Hdestruct;
      eapply choosing_well_position_exists; [apply Hchoose |].
Qed.

(**
  Assuming [not_in_indices_initial_prop], the origin state of the
  trace given by [indexed_composite_state_to_trace] is initial.
*)
Lemma indexed_composite_state_to_trace_result_state_is_initial :
  forall (choose : choice_function), choosing_well choose ->
  forall (s : composite_state IM) (Hs : valid_state_prop RFree s),
  forall (indices : list index), NoDup indices ->
    not_in_indices_initial_prop s indices ->
    forall is tr, indexed_composite_state_to_trace choose s Hs indices = (is, tr) ->
    composite_initial_state_prop IM is.
Proof.
  intros * ? ? ? ? ? Hinitial ** i.
  destruct (decide (i ∈ indices)).
  - by eapply indexed_composite_state_to_trace_result_state.
  - assert (initial_state_prop (IM i) (s i)) by (apply Hinitial; done).
    by erewrite indexed_composite_state_to_trace_reflects_initiality_1.
Qed.

(**
  For any composite constrained state <<s>> and for any index <<i>> for which the
  component state <<s i>> satisfies [initial_state_prop], the component state of
  index <<i>> of any state of the trace extracted from <<s>> is equal to <<s i>>.
*)
Lemma indexed_composite_state_to_trace_reflects_initiality_2 :
  forall (choose : choice_function)
    (s : composite_state IM) (Hs : valid_state_prop RFree s)
    (indices : list index),
  forall (i : index), initial_state_prop (IM i) (s i) ->
    forall is tr,
      indexed_composite_state_to_trace choose s Hs indices = (is, tr) ->
      forall item, item ∈ tr ->
      destination item i = s i.
Proof.
  intros ? ? ? ?.
  apply_funelim (indexed_composite_state_to_trace choose s Hs indices);
    clear choose s Hs indices;
    [by inversion 4; inversion 1 | ..];
    intros ? ? ? idx indices [j nj].
  - intros * -> Hind _ _ i Hi is' tr' [=] _item H_item; subst is' tr'.
    apply elem_of_app in H_item as [H_item | H_item].
    + replace (s' i) with (s i) in *.
      * by eapply Hind.
      * by eapply composite_tv_state_destructor_reflects_initiality;
          [| eapply elem_of_list_lookup_2 |].
    + apply elem_of_list_singleton in H_item as ->.
      erewrite composite_tv_state_destructor_destination; [done |].
      by eapply elem_of_list_lookup_2.
  - by inversion 5; inversion 1.
  - by eauto.
  - by inversion 6; inversion 1.
Qed.

(**
  The trace extracted from a state using [indexed_composite_state_to_trace]
  ends in that state.
*)
Lemma indexed_composite_state_to_trace_last :
  forall (choose : choice_function) (Hwell : choosing_well choose)
    (s' : composite_state IM) (Hs' : valid_state_prop RFree s')
    (indices : list index)
    (Hnodup : NoDup indices)
    (Hinit : not_in_indices_initial_prop s' indices),
    forall is tr,
      indexed_composite_state_to_trace choose s' Hs' indices = (is, tr) ->
      finite_trace_last is tr = s'.
Proof.
  intros choose Hwell s' Hs' indices; revert Hwell.
  apply_funelim (indexed_composite_state_to_trace choose s' Hs' indices);
    clear choose s' Hs' indices;
    [by inversion 5 | ..];
    intros ? ? ? idx indices [j jn].
  - intros * -> Hind _ _ _ _ _ ? ? [= -> <-].
    rewrite finite_trace_last_is_last.
    by eapply composite_tv_state_destructor_destination, elem_of_list_lookup_2.
  - by inversion 7.
  - intros * Hind _ _ _ _ **; apply Hind; [done | | | done].
    + by apply StdppListSet.set_remove_nodup.
    + by apply set_remove_preserves_not_in_indices_initial.
  - by inversion 8.
Qed.

(**
  For any given composite constrained state,
  [indexed_reachable_composite_state_to_trace] yields a constrained trace
  leading to it.
*)
Lemma indexed_reachable_composite_state_to_trace :
  forall (choose : choice_function), choosing_well choose ->
  forall (s : composite_state IM) (Hs : valid_state_prop RFree s),
  forall (indices : list index), NoDup indices ->
    not_in_indices_initial_prop s indices ->
    forall is tr, indexed_composite_state_to_trace choose s Hs indices = (is, tr) ->
    finite_valid_trace_from_to RFree is s tr.
Proof.
  intros choose Hchoose s Hs indices; revert Hchoose.
  apply_funelim (indexed_composite_state_to_trace choose s Hs indices);
    clear choose s Hs indices; intros choose s' Hs';
    [by inversion 4; subst; constructor | ..];
    intros idx indices.
  - intros ? ? ? ? _ ? ? -> Hind _ _ Hchoose Hnodup Hinitial is' tr' [= -> <-].
    eapply composite_tv_state_destructor_preserves_not_in_indices_initial  in Hinitial; [| done..].
    apply elem_of_list_lookup_2 in Hdestruct.
    replace s' with (destination item) in *
      by (eapply composite_tv_state_destructor_destination; done).
    eapply composite_tv_state_destructor_transition in Hdestruct; [| done].
    destruct item; cbn in *.
    by apply (extend_right_finite_trace_from_to RFree) with s; [apply Hind |].
  - by intros; contradiction n; subst;
      apply cw_chosen_index_in_indices; [apply Hchoose |].
  - intros ? Hdestruct _ Hj _ _ -> Hind _ _ _ _ **; eapply Hind; [done | | | done].
    + by apply StdppListSet.set_remove_nodup.
    + by apply set_remove_preserves_not_in_indices_initial.
  - by intros; clear Heq1; contradict Hdestruct; subst;
      eapply choosing_well_position_exists; [apply Hchoose |].
Qed.

(**
  Given a composite constrained state, and a [choice_function], we can extract a
  constrained trace leading to that state by instantiating
  [indexed_composite_state_to_trace] with the set of all indices.
*)
Definition composite_state_to_trace
  (choose : choice_function)
  (s : composite_state IM) (Hs : valid_state_prop RFree s)
  : composite_state IM * list (composite_transition_item IM) :=
  indexed_composite_state_to_trace choose s Hs (enum index).

Lemma reachable_composite_state_to_trace :
  forall (choose : choice_function), choosing_well choose ->
  forall (s : composite_state IM) (Hs : valid_state_prop RFree s),
  forall is tr, composite_state_to_trace choose s Hs = (is, tr) ->
  finite_valid_trace_init_to RFree is s tr.
Proof.
  intros ? Hchoose * Heqis_tr.
  pose proof (Hnodup := NoDup_enum index).
  assert (Hinitial : not_in_indices_initial_prop s (enum index))
    by (intros j Hj; contradict Hj; apply elem_of_enum).
  split.
  - by eapply indexed_reachable_composite_state_to_trace.
  - by eapply indexed_composite_state_to_trace_result_state_is_initial.
Qed.

(**
  The property of a [choice_function] with respect to a predicate on composite
  states which states that for any chosen transition, if the predicate holds for
  the source of the transition then it must also hold for its target.

  See [MinimalEquivocationTrace.minimal_equivocation_choice_monotone] for an
  example of such a function.
*)
Definition chosen_transition_preserves_P
  (P : composite_state IM -> Prop) (choose : choice_function) : Prop :=
  forall (is : list index), NoDup is ->
  forall (s' : composite_state IM) (Hs' : valid_state_prop RFree s'),
    not_in_indices_initial_prop s' is ->
    forall (i : index) (Hi : i ∈ is) (n : nat),
      choose s' Hs' is  = (i, n) ->
      forall (s : composite_state IM) (item : composite_transition_item IM),
        composite_state_destructor s' i !! n = Some (item, s) ->
        P s -> P s'.

(**
  If a [choice_function] is choosing well and satisfying
  [chosen_transition_preserves_P] w.r.t. a predicate <<P>> then the corresponding
  trace obtained through [composite_state_to_trace] will also preserve <<P>>
  at every step.

  See [MinimalEquivocationTrace.state_to_minimal_equivocation_trace_equivocation_monotonic]
  for an example of such a function.
*)
Lemma composite_state_to_trace_P_monotonic :
  forall (P : composite_state IM -> Prop),
  forall (choose : choice_function), choosing_well choose ->
    chosen_transition_preserves_P P choose ->
  forall (s : composite_state IM) (Hs : valid_state_prop RFree s),
  forall is tr, composite_state_to_trace choose s Hs = (is, tr) ->
  forall (pre suf : list (composite_transition_item IM))
    (item : composite_transition_item IM),
    tr = pre ++ [item] ++ suf ->
    P (finite_trace_last is pre)-> P (destination item).
Proof.
  unfold composite_state_to_trace.
  intros P choose Hwell HchooseP s' Hs' is tr Heqis_tr pre suf item Heqtr Heqv.
  revert is tr Heqis_tr pre suf item Heqtr Heqv.
  generalize (NoDup_enum index) as Hnodup.
  assert (Hinitial : not_in_indices_initial_prop s' (enum index))
    by (intros i contra; contradict contra; apply elem_of_enum).
  revert Hinitial; generalize (enum index); intro indices; revert Hwell HchooseP.
  apply_funelim (indexed_composite_state_to_trace choose s' Hs' indices);
    clear choose s' Hs' indices;
    [by intros; inversion Heqis_tr; subst; destruct pre | ..];
    intros choose s' Hs' idx indices (j, nj); cbn.
  - intros item s Hdestruct Hchoice is tr Heq ? _ _ ? ? ? ? ? ? [= <- <-] **;
      rewrite Heq in Hind.
    eapply composite_tv_state_destructor_preserves_not_in_indices_initial in Hinitial as Hinitials;
      [| done..].
    ListExtras.destruct_list_last suf suf' last_suf Heqsuf; subst suf; simplify_list_eq;
      [| by eapply Hind].
    assert (destination item0 = s') as ->
      by (eapply composite_tv_state_destructor_destination, elem_of_list_lookup_2; done).
    erewrite indexed_composite_state_to_trace_last in Heqv by done.
    eapply HchooseP; [done | done | | done | done | done].
    destruct (decide (j ∈ idx :: indices)); [done |].
    eapply Hinitial, composite_tv_state_destructor_initial in n; [| done].
    by clear -Hdestruct n; rewrite n in Hdestruct.
  - by intros; inversion Heqis_tr; subst; destruct pre.
  - intros Hdestruct _ Hj _ _ -> Hind _ _ _ _ **.
    eapply set_remove_preserves_not_in_indices_initial in Hinitial; [| done..].
    eapply StdppListSet.set_remove_nodup with (a := j) in Hnodup.
    by eapply Hind.
  - by intros; inversion Heqis_tr; subst; destruct pre.
Qed.

End sec_traceable_vlsm_composition.
