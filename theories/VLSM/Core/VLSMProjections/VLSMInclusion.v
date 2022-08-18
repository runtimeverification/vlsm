From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From VLSM.Core Require Import VLSM VLSMProjections.VLSMEmbedding VLSMProjections.VLSMTotalProjection.

(** * VLSM Inclusion

When both VLSMs have the same state and label types they also share the
same [Trace] type, and sets of traces can be compared without conversion.
Then VLSM <<X>> is _included_ in VLSM <<Y>> if every [valid_trace] available to <<X>>
is also available to <<Y>>.
*)
Section VLSM_inclusion.

Context
  {message : Type}
  {vtype : VLSMType message}
  .

Definition VLSM_incl_part
  (MX MY : VLSMMachine vtype)
  (X := mk_vlsm MX) (Y := mk_vlsm MY)
  :=
  forall t : Trace,
    valid_trace_prop X t -> valid_trace_prop Y t.
#[local] Notation VLSM_incl X Y := (VLSM_incl_part (machine X) (machine Y)).

Lemma VLSM_incl_refl
  (MX : VLSMMachine vtype)
  (X := mk_vlsm MX)
  : VLSM_incl X X.
Proof.
  firstorder.
Qed.

Lemma VLSM_incl_trans
  (MX MY MZ : VLSMMachine vtype)
  (X := mk_vlsm MX) (Y := mk_vlsm MY) (Z := mk_vlsm MZ)
  : VLSM_incl X Y -> VLSM_incl Y Z -> VLSM_incl X Z.
Proof.
  firstorder.
Qed.

Lemma VLSM_incl_finite_traces_characterization
  (MX MY : VLSMMachine vtype)
  (X := mk_vlsm MX) (Y := mk_vlsm MY)
  : VLSM_incl X Y <->
    forall (s : vstate X)
    (tr : list (vtransition_item X)),
    finite_valid_trace X s tr -> finite_valid_trace Y s tr.
Proof.
  split; intros Hincl.
  - intros. by apply (Hincl (Finite s tr)).
  - intros tr Htr.
    destruct tr as [is tr | is tr]; simpl in *.
    + revert Htr. apply Hincl.
    + destruct Htr as [HtrX HisX].
      assert (His_tr: finite_valid_trace X is []).
      { split; [| done]. constructor.
        by apply initial_state_is_valid.
      }
      apply Hincl in His_tr.
      destruct His_tr as [_ HisY].
      split; [| done].
      apply infinite_valid_trace_from_prefix_rev.
      intros.
      pose proof (infinite_valid_trace_from_prefix _ _ _ HtrX n) as HfinX.
      apply (Hincl _ _ (conj HfinX HisX)).
Qed.

(** A [VLSM_incl]usion is equivalent to a [VLSM_full_projection] in which both the
label and state projection functions are identities.
*)
Lemma VLSM_incl_full_projection_iff
  (MX MY : VLSMMachine vtype)
  (X := mk_vlsm MX) (Y := mk_vlsm MY)
  : VLSM_incl X Y <-> VLSM_full_projection X Y id id.
Proof.
  assert (Hid : forall tr, tr = pre_VLSM_full_projection_finite_trace_project _ _ id id tr).
  { induction tr; [done |]. destruct a. by cbn; f_equal. }
  split.
  - constructor; intros.
    apply (proj1 (VLSM_incl_finite_traces_characterization (machine X) (machine Y)) H) in H0.
    replace (pre_VLSM_full_projection_finite_trace_project _ _ _ _ trX) with trX; [done |].
    apply Hid.
  - intro Hproject. apply VLSM_incl_finite_traces_characterization.
    intros. apply (VLSM_full_projection_finite_valid_trace Hproject) in H.
    replace (VLSM_full_projection_finite_trace_project Hproject _) with tr in H; [done |].
    apply Hid.
Qed.

Definition VLSM_incl_is_full_projection
  {MX MY : VLSMMachine vtype}
  (X := mk_vlsm MX) (Y := mk_vlsm MY)
  (Hincl : VLSM_incl X Y)
  : VLSM_full_projection X Y id id
  := proj1 (VLSM_incl_full_projection_iff MX MY) Hincl.

Lemma VLSM_incl_is_full_projection_finite_trace_project
  {MX MY : VLSMMachine vtype}
  (X := mk_vlsm MX) (Y := mk_vlsm MY)
  (Hincl : VLSM_incl X Y)
  : forall tr,
    VLSM_full_projection_finite_trace_project (VLSM_incl_is_full_projection Hincl) tr = tr.
Proof.
  induction tr; [done |].
  simpl. f_equal; [| done].
  by destruct a.
Qed.

End VLSM_inclusion.

Notation VLSM_incl X Y := (VLSM_incl_part (machine X) (machine Y)).

Section VLSM_incl_preservation.

(** ** VLSM inclusion preservation *)

Context
  {message : Type}
  {T : VLSMType message}
  (MX MY : VLSMMachine T)
  (X := mk_vlsm MX)
  (Y := mk_vlsm MY)
  .

Definition weak_incl_valid_preservation : Prop :=
  weak_full_projection_valid_preservation X Y id id.

Definition strong_incl_valid_preservation : Prop :=
  strong_full_projection_valid_preservation X Y id id.

Definition weak_incl_transition_preservation : Prop :=
  weak_full_projection_transition_preservation X Y id id.

Definition strong_incl_transition_preservation : Prop :=
  strong_full_projection_transition_preservation X Y id id.

Definition strong_incl_initial_state_preservation : Prop :=
  strong_projection_initial_state_preservation X Y id.

Definition weak_incl_initial_message_preservation : Prop :=
  weak_full_projection_initial_message_preservation X Y id.

Definition strong_incl_initial_message_preservation : Prop :=
  strong_full_projection_initial_message_preservation X Y.

End VLSM_incl_preservation.

Section VLSM_incl_properties.

(** ** VLSM inclusion properties *)

Context
  {message : Type} [vtype : VLSMType message]
  [MX MY : VLSMMachine vtype]
  (Hincl : VLSM_incl_part MX MY)
  (X := mk_vlsm MX)
  (Y := mk_vlsm MY)
  .

(** VLSM inclusion specialized to finite trace. *)

Lemma VLSM_incl_finite_valid_trace
  (s : vstate X)
  (tr : list (vtransition_item X))
  (Htr : finite_valid_trace X s tr)
  : finite_valid_trace Y s tr.
Proof.
  apply (VLSM_full_projection_finite_valid_trace (VLSM_incl_is_full_projection Hincl))
    in Htr.
  by rewrite (VLSM_incl_is_full_projection_finite_trace_project Hincl) in Htr.
Qed.

Lemma VLSM_incl_finite_valid_trace_init_to
  (s f : vstate X)
  (tr : list (vtransition_item X))
  (Htr : finite_valid_trace_init_to X s f tr)
  : finite_valid_trace_init_to Y s f tr.
Proof.
  apply (VLSM_full_projection_finite_valid_trace_init_to (VLSM_incl_is_full_projection Hincl))
    in Htr.
  by rewrite (VLSM_incl_is_full_projection_finite_trace_project Hincl) in Htr.
Qed.

Lemma VLSM_incl_valid_state
  (s : vstate X)
  (Hs : valid_state_prop X s)
  : valid_state_prop Y s.
Proof.
  revert Hs. apply (VLSM_full_projection_valid_state (VLSM_incl_is_full_projection Hincl)).
Qed.

Lemma VLSM_incl_initial_state
  (is : vstate X)
  : vinitial_state_prop X is -> vinitial_state_prop Y is.
Proof.
  apply (VLSM_full_projection_initial_state (VLSM_incl_is_full_projection Hincl)).
Qed.

Lemma VLSM_incl_finite_valid_trace_from
  (s : vstate X)
  (tr : list (vtransition_item X))
  (Htr : finite_valid_trace_from X s tr)
  : finite_valid_trace_from Y s tr.
Proof.
  apply (VLSM_full_projection_finite_valid_trace_from (VLSM_incl_is_full_projection Hincl))
    in Htr.
  by rewrite (VLSM_incl_is_full_projection_finite_trace_project Hincl) in Htr.
Qed.

Lemma VLSM_incl_finite_valid_trace_from_to
  (s f : vstate X)
  (tr : list (vtransition_item X))
  (Htr : finite_valid_trace_from_to X s f tr)
  : finite_valid_trace_from_to Y s f tr.
Proof.
  apply (VLSM_full_projection_finite_valid_trace_from_to (VLSM_incl_is_full_projection Hincl))
    in Htr.
  by rewrite (VLSM_incl_is_full_projection_finite_trace_project Hincl) in Htr.
Qed.

Lemma VLSM_incl_in_futures
  (s1 s2 : vstate X)
  : in_futures X s1 s2 -> in_futures Y s1 s2.
Proof.
  apply (VLSM_full_projection_in_futures (VLSM_incl_is_full_projection Hincl)).
Qed.

Lemma VLSM_incl_input_valid_transition
  : forall l s im s' om,
  input_valid_transition X l (s,im) (s',om) ->
  input_valid_transition Y l (s,im) (s',om).
Proof.
  apply
    (VLSM_full_projection_input_valid_transition (VLSM_incl_is_full_projection Hincl)).
Qed.

Lemma VLSM_incl_input_valid
  : forall l s im,
  input_valid X l (s,im) ->
  input_valid Y l (s,im).
Proof.
  apply
    (VLSM_full_projection_input_valid (VLSM_incl_is_full_projection Hincl)).
Qed.

(**
  [VLSM_incl] almost implies inclusion of the [valid_state_message_prop] sets.
  Some additional hypotheses are required because [VLSM_incl] only
  refers to traces, and [valid_initial_state_message] means that
  [valid_state_message_prop] includes some pairs that do not appear in any
  transition.
 *)
Lemma VLSM_incl_valid_state_message
  (Hmessage : strong_incl_initial_message_preservation MX MY)
  : forall s om, valid_state_message_prop X s om -> valid_state_message_prop Y s om.
Proof.
  intros s om.
  by apply (VLSM_full_projection_valid_state_message (VLSM_incl_is_full_projection Hincl)).
Qed.

Lemma VLSM_incl_can_produce
  (s : state)
  (om : option message)
  : option_can_produce X s om -> option_can_produce Y s om.
Proof.
  apply (VLSM_full_projection_can_produce (VLSM_incl_is_full_projection Hincl)).
Qed.

Lemma VLSM_incl_can_emit
  (m : message)
  : can_emit X m -> can_emit Y m.
Proof.
  apply (VLSM_full_projection_can_emit (VLSM_incl_is_full_projection Hincl)).
Qed.

Definition VLSM_incl_valid_message
  (Hinitial_valid_message : strong_incl_initial_message_preservation MX MY)
  : forall (m : message),
    valid_message_prop X m -> valid_message_prop Y m.
Proof.
  intros m [s Hm].
  by exists s; revert Hm; apply VLSM_incl_valid_state_message.
Qed.

Lemma VLSM_incl_infinite_valid_trace_from
  s ls
  : infinite_valid_trace_from X s ls ->
    infinite_valid_trace_from Y s ls.
Proof.
  intros Hls.
  apply (VLSM_full_projection_infinite_valid_trace_from (VLSM_incl_is_full_projection Hincl)) in Hls.
  revert Hls.
  apply infinite_valid_trace_from_EqSt.
  apply Streams.ntheq_eqst.
  unfold VLSM_full_projection_infinite_trace_project, pre_VLSM_full_projection_infinite_trace_project.
  intro n. rewrite Streams.Str_nth_map.
  by destruct (Streams.Str_nth _ _).
Qed.

Lemma VLSM_incl_infinite_valid_trace
  s ls
  : infinite_valid_trace X s ls -> infinite_valid_trace Y s ls.
Proof.
  intros [Htr His]. split.
  - revert Htr. apply VLSM_incl_infinite_valid_trace_from.
  - revert His. apply VLSM_incl_initial_state.
Qed.

Lemma VLSM_incl_valid_trace
  : forall t, valid_trace_prop X t -> valid_trace_prop Y t.
Proof.
  intros [s tr | s tr]; simpl.
  - apply VLSM_incl_finite_valid_trace.
  - apply VLSM_incl_infinite_valid_trace.
Qed.

End VLSM_incl_properties.

(** We instantiate the above for VLSM inclusions
*)
Section basic_VLSM_incl.

Context
  {message : Type}
  {T : VLSMType message}
  (MX MY : VLSMMachine T)
  (X := mk_vlsm MX)
  (Y := mk_vlsm MY)
  .

Lemma basic_VLSM_incl
  (Hinitial_state : strong_incl_initial_state_preservation MX MY)
  (Hinitial_valid_message : weak_incl_initial_message_preservation MX MY)
  (Hvalid : weak_incl_valid_preservation MX MY)
  (Htransition : weak_incl_transition_preservation MX MY)
  : VLSM_incl X Y.
Proof.
  by apply VLSM_incl_full_projection_iff, basic_VLSM_full_projection.
Qed.

Lemma basic_VLSM_strong_incl
  (Hinitial_state : strong_incl_initial_state_preservation MX MY)
  (Hinitial_valid_message : strong_incl_initial_message_preservation MX MY)
  (Hvalid : strong_incl_valid_preservation MX MY)
  (Htransition : strong_incl_transition_preservation MX MY)
  : VLSM_incl X Y.
Proof.
  by apply VLSM_incl_full_projection_iff, basic_VLSM_strong_full_projection.
Qed.

Lemma basic_VLSM_incl_preloaded
  (Hinitial_state : strong_incl_initial_state_preservation MX MY)
  (Hvalid : strong_incl_valid_preservation MX MY)
  (Htransition : strong_incl_transition_preservation MX MY)
  : VLSM_incl (pre_loaded_with_all_messages_vlsm X) (pre_loaded_with_all_messages_vlsm Y).
Proof.
  by apply VLSM_incl_full_projection_iff, (basic_VLSM_full_projection_preloaded X Y id id).
Qed.

Lemma basic_VLSM_incl_preloaded_with
  (P Q : message -> Prop)
  (PimpliesQ : forall m : message, P m -> Q m)
  (Hvalid : strong_incl_valid_preservation MX MY)
  (Htransition : strong_incl_transition_preservation  MX MY)
  (Hstate : strong_incl_initial_state_preservation MX MY)
  (Hmessage : strong_incl_initial_message_preservation MX MY)
  : VLSM_incl (pre_loaded_vlsm X P) (pre_loaded_vlsm Y Q).
Proof.
  by apply VLSM_incl_full_projection_iff,
           (basic_VLSM_full_projection_preloaded_with X Y _ _ PimpliesQ id id).
Qed.

End basic_VLSM_incl.

Section VLSM_incl_preloaded_properties.

Context
  {message : Type}
  (X : VLSM message)
  .

Lemma vlsm_incl_pre_loaded_with_all_messages_vlsm
  : VLSM_incl X (pre_loaded_with_all_messages_vlsm X).
Proof.
  apply VLSM_incl_finite_traces_characterization.
  intros. split; [|apply H].
  apply preloaded_weaken_valid_trace_from. destruct X. apply H.
Qed.

Lemma pre_loaded_vlsm_incl_relaxed
  (P Q : message -> Prop)
  (PimpliesQorValid : forall m : message, P m -> Q m \/ valid_message_prop (pre_loaded_vlsm X Q) m)
  : VLSM_incl (pre_loaded_vlsm X P) (pre_loaded_vlsm X Q).
Proof.
  apply basic_VLSM_incl.
  1, 3-4: cbv; itauto.
  intros _ _ m _ _ [Him | Hp].
  - by apply initial_message_is_valid; left.
  - apply PimpliesQorValid in Hp as [Hq | Hvalid]; [| done].
    by apply initial_message_is_valid; right.
Qed.

Lemma pre_loaded_vlsm_incl
  (P Q : message -> Prop)
  (PimpliesQ : forall m : message, P m -> Q m)
  : VLSM_incl (pre_loaded_vlsm X P) (pre_loaded_vlsm X Q).
Proof.
  apply pre_loaded_vlsm_incl_relaxed; itauto.
Qed.

Lemma pre_loaded_vlsm_idem_l
  (P : message -> Prop)
  : VLSM_incl (pre_loaded_vlsm (pre_loaded_vlsm X P) P) (pre_loaded_vlsm X P).
Proof.
  apply basic_VLSM_strong_incl; cbv; itauto.
Qed.

Lemma pre_loaded_vlsm_idem_r
  (P : message -> Prop)
  : VLSM_incl (pre_loaded_vlsm X P) (pre_loaded_vlsm (pre_loaded_vlsm X P) P).
Proof.
  apply basic_VLSM_incl_preloaded_with; cbv; itauto.
Qed.

Lemma pre_loaded_with_all_messages_vlsm_is_pre_loaded_with_True_l
  : VLSM_incl (pre_loaded_with_all_messages_vlsm X) (pre_loaded_vlsm X (fun m => True)).
Proof.
  apply basic_VLSM_strong_incl; cbv; itauto.
Qed.

Lemma pre_loaded_with_all_messages_vlsm_is_pre_loaded_with_True_r
  : VLSM_incl (pre_loaded_vlsm X (fun m => True)) (pre_loaded_with_all_messages_vlsm X).
Proof.
  apply basic_VLSM_strong_incl; cbv; itauto.
Qed.

Lemma pre_loaded_vlsm_incl_pre_loaded_with_all_messages
  (P : message -> Prop)
  : VLSM_incl (pre_loaded_vlsm X P) (pre_loaded_with_all_messages_vlsm X).
Proof.
  apply basic_VLSM_strong_incl; cbv; itauto.
Qed.

Lemma vlsm_incl_pre_loaded
  (P : message -> Prop)
  : VLSM_incl X (pre_loaded_vlsm X P).
Proof.
  eapply VLSM_incl_trans; [| by apply pre_loaded_vlsm_incl].
  apply basic_VLSM_strong_incl; cbv; itauto.
Qed.

Lemma pre_loaded_with_all_messages_vlsm_idem_l
  : VLSM_incl (pre_loaded_with_all_messages_vlsm (pre_loaded_with_all_messages_vlsm X)) (pre_loaded_with_all_messages_vlsm X).
Proof.
  apply basic_VLSM_strong_incl; cbv; itauto.
Qed.

Lemma pre_loaded_with_all_messages_vlsm_idem_r
  : VLSM_incl (pre_loaded_with_all_messages_vlsm X) (pre_loaded_with_all_messages_vlsm (pre_loaded_with_all_messages_vlsm X)).
Proof.
  apply basic_VLSM_incl_preloaded; cbv; itauto.
Qed.

Lemma pre_loaded_with_all_messages_can_emit
  (m : message)
  (Hm : can_emit X m)
  : can_emit (pre_loaded_with_all_messages_vlsm X) m.
Proof.
  apply (VLSM_incl_can_emit vlsm_incl_pre_loaded_with_all_messages_vlsm).
  by rewrite mk_vlsm_machine.
Qed.

Lemma preloaded_weaken_finite_valid_trace_from
  (from : state) (tr : list transition_item)
  : finite_valid_trace_from X from tr ->
    finite_valid_trace_from (pre_loaded_with_all_messages_vlsm X) from tr.
Proof.
  intros; eapply VLSM_incl_finite_valid_trace_from;
    [apply vlsm_incl_pre_loaded_with_all_messages_vlsm |].
  by destruct X.
Qed.

Lemma preloaded_weaken_finite_valid_trace_from_to
  (from to : state) (tr : list transition_item)
  : finite_valid_trace_from_to X from to tr ->
    finite_valid_trace_from_to (pre_loaded_with_all_messages_vlsm X) from to tr.
Proof.
  intros; eapply VLSM_incl_finite_valid_trace_from_to;
    [apply vlsm_incl_pre_loaded_with_all_messages_vlsm |].
  by destruct X.
Qed.

End VLSM_incl_preloaded_properties.
