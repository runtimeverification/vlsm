From stdpp Require Import prelude.
From VLSM Require Import Core.VLSM Core.VLSMProjections Core.Equivocators.Common.
From VLSM Require Import Core.Equivocation Core.EquivocationProjections Core.Equivocators.MessageProperties.

(** * Equivocator State Append Determines a Projection

In this module, we show that we can "append" two equivocator traces by
simulating the second at the end of the first.

The transformation on the states of the second trace is obtained by
[equivocator_state_append]ing each state to the last state of the first trace.
*)

Section equivocator_state_append_projection.

Context
  {message : Type}
  (X : VLSM message)
  .

Definition equivocator_state_append_label
  (base_s : equivocator_state X)
  (l : equivocator_label X)
  : equivocator_label X
  :=
  match l with
  | Spawn _ => l
  | ContinueWith i lx => ContinueWith (i + equivocator_state_n base_s) lx
  | ForkWith i lx => ForkWith (i + equivocator_state_n base_s) lx
  end.

Lemma equivocator_state_append_valid l s om base_s
  : equivocator_valid X l (s, om) ->
    equivocator_valid X (equivocator_state_append_label base_s l) (equivocator_state_append base_s s, om).
Proof.
  destruct l; cbn; [exact id|..]
  ; (destruct (equivocator_state_project s n) as [sn|] eqn:Hn; [|contradiction])
  ; rewrite (equivocator_state_append_project_2 _ base_s s _ n eq_refl)
  ; rewrite Hn
  ; exact id.
Qed.

Lemma equivocator_state_append_transition l s om s' om' base_s
  : equivocator_valid X l (s, om) ->
    equivocator_transition X l (s, om) = (s', om') ->
    equivocator_transition X (equivocator_state_append_label base_s l)
      (equivocator_state_append base_s s, om) = (equivocator_state_append base_s s', om').
Proof.
  destruct l; cbn; intros Hv Ht
  ; [inversion_clear Ht; f_equal; apply equivocator_state_append_extend_commute|..]
  ; (destruct (equivocator_state_project s n) as [sn|] eqn:Hn; [|contradiction])
  ;  rewrite (equivocator_state_append_project_2 _ base_s s _ n eq_refl)
  ;  rewrite Hn
  ;  destruct (vtransition _ _ _) as (sn', _om') eqn:Hti
  ;  inversion_clear Ht; f_equal.
  - apply equivocator_state_append_update_commute.
  - apply equivocator_state_append_extend_commute.
Qed.

Lemma equivocator_state_append_initial_state_in_futures
    (seed : message -> Prop)
    (base_s : equivocator_state X)
    (Hbase_s : valid_state_prop (pre_loaded_vlsm (equivocator_vlsm X) seed) base_s)
    s
    : vinitial_state_prop (equivocator_vlsm X) s ->
      in_futures (pre_loaded_vlsm (equivocator_vlsm X) seed) base_s (equivocator_state_append base_s s).
Proof.
  exists
    [(@Build_transition_item _ (type (equivocator_vlsm X))
      (Spawn (equivocator_state_zero s))
      None
      (equivocator_state_append base_s s)
      None)].
  apply (finite_valid_trace_from_to_singleton (pre_loaded_vlsm (equivocator_vlsm X) seed)).
  repeat split.
  - assumption.
  - apply option_valid_message_None.
  - apply H.
  - cbn. f_equal. symmetry. apply equivocator_state_append_singleton_is_extend. apply H.
Qed.

Lemma equivocator_state_append_transition_initial_state
    (seed : message -> Prop)
    (base_s : equivocator_state X)
    (Hbase_s : valid_state_prop (pre_loaded_vlsm (equivocator_vlsm X) seed) base_s)
    s
    : vinitial_state_prop (equivocator_vlsm X) s ->
      valid_state_prop (pre_loaded_vlsm (equivocator_vlsm X) seed)
        (equivocator_state_append base_s s).
Proof.
  intros Hs. apply in_futures_valid_snd with base_s.
  apply equivocator_state_append_initial_state_in_futures; assumption.
Qed.

Lemma equivocator_state_append_preloaded_with_weak_projection
  (seed : message -> Prop)
  (base_s : equivocator_state X)
  (Hbase_s : valid_state_prop (pre_loaded_vlsm (equivocator_vlsm X) seed) base_s)
  : VLSM_weak_full_projection (pre_loaded_vlsm (equivocator_vlsm X) seed) (pre_loaded_vlsm (equivocator_vlsm X) seed)
        (equivocator_state_append_label base_s) (equivocator_state_append base_s).
Proof.
  apply basic_VLSM_weak_full_projection; intro; intros.
  - apply equivocator_state_append_valid. apply Hv.
  - apply equivocator_state_append_transition; apply H.
  - apply equivocator_state_append_transition_initial_state; assumption.
  - apply initial_message_is_valid; assumption.
Qed.

Lemma equivocator_state_append_preloaded_weak_projection
  (base_s : equivocator_state X)
  (Hbase_s : valid_state_prop (pre_loaded_with_all_messages_vlsm (equivocator_vlsm X)) base_s)
  : VLSM_weak_full_projection (pre_loaded_with_all_messages_vlsm (equivocator_vlsm X)) (pre_loaded_with_all_messages_vlsm (equivocator_vlsm X))
        (equivocator_state_append_label base_s) (equivocator_state_append base_s).
Proof.
  specialize (pre_loaded_with_all_messages_vlsm_is_pre_loaded_with_True (equivocator_vlsm X)) as Heq.
  constructor.
  intros sX trX HtrX.
  apply (VLSM_eq_finite_valid_trace_from Heq) in HtrX.
  apply (VLSM_eq_finite_valid_trace_from Heq).
  revert sX trX HtrX.
  apply equivocator_state_append_preloaded_with_weak_projection.
  apply (VLSM_eq_valid_state Heq). assumption.
Qed.

Lemma equivocator_state_append_weak_projection
  (base_s : equivocator_state X)
  (Hbase_s : valid_state_prop (equivocator_vlsm X) base_s)
  : VLSM_weak_full_projection (equivocator_vlsm X) (equivocator_vlsm X)
        (equivocator_state_append_label base_s) (equivocator_state_append base_s).
Proof.
  specialize (vlsm_is_pre_loaded_with_False (equivocator_vlsm X)) as Heq.
  constructor.
  intros sX trX HtrX.
  apply (VLSM_eq_finite_valid_trace_from Heq) in HtrX.
  apply (VLSM_eq_finite_valid_trace_from Heq).
  revert sX trX HtrX.
  apply equivocator_state_append_preloaded_with_weak_projection.
  apply (VLSM_eq_valid_state Heq). assumption.
Qed.

Lemma equivocator_state_append_in_futures
  (seed : message -> Prop)
  base_s (Hbase_s : valid_state_prop (pre_loaded_vlsm (equivocator_vlsm X) seed) base_s)
  s (Hs : valid_state_prop (pre_loaded_vlsm (equivocator_vlsm X) seed) s)
  : in_futures (pre_loaded_vlsm (equivocator_vlsm X) seed) base_s (equivocator_state_append base_s s).
Proof.
  apply valid_state_has_trace in Hs as [is [tr [Htr His]]].
  specialize (equivocator_state_append_preloaded_with_weak_projection seed _ Hbase_s) as Hproj.
  apply (VLSM_weak_full_projection_finite_valid_trace_from_to Hproj) in Htr.
  apply in_futures_trans with (equivocator_state_append base_s is).
  - apply equivocator_state_append_initial_state_in_futures; assumption.
  - eexists; exact Htr.
Qed.

Lemma equivocator_state_append_sent_left
  {Hbs : HasBeenSentCapability X}
  base_s (Hbase_s : valid_state_prop (pre_loaded_with_all_messages_vlsm (equivocator_vlsm X)) base_s)
  s (Hs : valid_state_prop (pre_loaded_with_all_messages_vlsm (equivocator_vlsm X)) s)
  : forall m, equivocator_has_been_sent X base_s m ->
    equivocator_has_been_sent X (equivocator_state_append base_s s) m.
Proof.
  specialize (pre_loaded_with_all_messages_vlsm_is_pre_loaded_with_True (equivocator_vlsm X)) as Heq.
  apply (VLSM_eq_valid_state Heq) in Hbase_s.
  apply (VLSM_eq_valid_state Heq) in Hs.
  apply (equivocator_state_append_in_futures _ _ Hbase_s) in Hs.
  apply (VLSM_eq_in_futures Heq) in Hs.
  apply (in_futures_preserving_oracle_from_stepwise _ (equivocator_vlsm X) (field_selector output) (equivocator_has_been_sent X))
  ; [|assumption].
  apply equivocator_has_been_sent_stepwise_props.
Qed.

Lemma equivocator_state_append_sent_right
  {Hbs : HasBeenSentCapability X}
  (HbsE := equivocator_HasBeenSentCapability X)
  base_s (Hbase_s : valid_state_prop (pre_loaded_with_all_messages_vlsm (equivocator_vlsm X)) base_s)
  s (Hs : valid_state_prop (pre_loaded_with_all_messages_vlsm (equivocator_vlsm X)) s)
  : forall m, equivocator_has_been_sent X s m ->
    equivocator_has_been_sent X (equivocator_state_append base_s s) m.
Proof.
  specialize (equivocator_state_append_preloaded_weak_projection _ Hbase_s) as Hproj.
  intros m Hm.
  specialize (VLSM_weak_full_projection_has_been_sent Hproj _ Hs _ Hm) as HmY.
  assumption.
Qed.

End equivocator_state_append_projection.
