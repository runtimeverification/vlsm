From VLSM.Lib Require Import Itauto.
From stdpp Require Import prelude.
From VLSM.Core Require Import VLSM.
From VLSM.Core.VLSMProjections Require Import VLSMEmbedding VLSMTotalProjection.

(** * Core: VLSM Inclusion

  When both VLSMs have the same state and label types they also share the
  same [Trace] type, and sets of traces can be compared without conversion.
  Then VLSM <<X>> is _included_ in VLSM <<Y>> if every [valid_trace] available to <<X>>
  is also available to <<Y>>.
*)

Section sec_VLSM_inclusion.

Context
  {message : Type}
  {T : VLSMType message}
  .

Definition VLSM_incl_part
  (MX MY : VLSMMachine T)
  (X := mk_vlsm MX) (Y := mk_vlsm MY)
  :=
  forall t : Trace,
    valid_trace_prop X t -> valid_trace_prop Y t.

#[local] Notation VLSM_incl X Y := (VLSM_incl_part (vmachine X) (vmachine Y)).

Lemma VLSM_incl_refl
  (MX : VLSMMachine T)
  (X := mk_vlsm MX)
  : VLSM_incl X X.
Proof.
  by firstorder.
Qed.

Lemma VLSM_incl_trans
  (MX MY MZ : VLSMMachine T)
  (X := mk_vlsm MX) (Y := mk_vlsm MY) (Z := mk_vlsm MZ)
  : VLSM_incl X Y -> VLSM_incl Y Z -> VLSM_incl X Z.
Proof.
  by firstorder.
Qed.

Lemma VLSM_incl_finite_traces_characterization
  (MX MY : VLSMMachine T)
  (X := mk_vlsm MX) (Y := mk_vlsm MY)
  : VLSM_incl X Y <->
    forall (s : state X)
    (tr : list (transition_item X)),
    finite_valid_trace X s tr -> finite_valid_trace Y s tr.
Proof.
  split; intros Hincl.
  - by intros; apply (Hincl (Finite s tr)).
  - intros tr Htr.
    destruct tr as [is tr | is tr]; simpl in *.
    + by apply Hincl.
    + destruct Htr as [HtrX HisX].
      assert (His_tr : finite_valid_trace X is []).
      {
        split; [| done].
        by constructor; apply initial_state_is_valid.
      }
      apply Hincl in His_tr.
      destruct His_tr as [_ HisY].
      split; [| done].
      apply infinite_valid_trace_from_prefix_rev.
      intros.
      pose proof (infinite_valid_trace_from_prefix _ _ _ HtrX n) as HfinX.
      by apply Hincl.
Qed.

(**
  A [VLSM_incl]usion is equivalent to a [VLSM_embedding] in which both the
  label and state projection functions are identities.
*)
Lemma VLSM_incl_embedding_iff
  (MX MY : VLSMMachine T)
  (X := mk_vlsm MX) (Y := mk_vlsm MY)
  : VLSM_incl X Y <-> VLSM_embedding X Y id id.
Proof.
  assert (Hid : forall tr : list (transition_item T),
    tr = pre_VLSM_embedding_finite_trace_project _ _ id id tr).
  {
    induction tr; [done |].
    by destruct a; cbn; f_equal.
  }
  split.
  - constructor; intros.
    apply (proj1 (VLSM_incl_finite_traces_characterization X Y) H) in H0.
    replace (pre_VLSM_embedding_finite_trace_project _ _ _ _ trX) with trX; [done |].
    by apply Hid.
  - intro Hproject. apply VLSM_incl_finite_traces_characterization.
    intros. apply (VLSM_embedding_finite_valid_trace Hproject) in H.
    replace (VLSM_embedding_finite_trace_project Hproject _) with tr in H; [done |].
    by apply Hid.
Qed.

Lemma VLSM_incl_is_embedding
  {MX MY : VLSMMachine T}
  (X := mk_vlsm MX) (Y := mk_vlsm MY) :
    VLSM_incl X Y -> VLSM_embedding X Y id id.
Proof.
  exact (proj1 (VLSM_incl_embedding_iff MX MY)).
Qed.

Lemma VLSM_incl_is_embedding_finite_trace_project
  {MX MY : VLSMMachine T}
  (X := mk_vlsm MX) (Y := mk_vlsm MY)
  (Hincl : VLSM_incl X Y)
  : forall tr,
    VLSM_embedding_finite_trace_project (VLSM_incl_is_embedding Hincl) tr = tr.
Proof.
  induction tr; [done |].
  simpl. f_equal; [| done].
  by destruct a.
Qed.

End sec_VLSM_inclusion.

Notation VLSM_incl X Y := (VLSM_incl_part (vmachine X) (vmachine Y)).

Section sec_VLSM_incl_preservation.

(** ** VLSM inclusion preservation *)

Context
  {message : Type}
  {T : VLSMType message}
  (MX MY : VLSMMachine T)
  (X := mk_vlsm MX)
  (Y := mk_vlsm MY)
  .

Definition weak_incl_valid_preservation : Prop :=
  weak_embedding_valid_preservation X Y id id.

Definition strong_incl_valid_preservation : Prop :=
  strong_embedding_valid_preservation X Y id id.

Definition weak_incl_transition_preservation : Prop :=
  weak_embedding_transition_preservation X Y id id.

Definition strong_incl_transition_preservation : Prop :=
  strong_embedding_transition_preservation X Y id id.

Definition strong_incl_initial_state_preservation : Prop :=
  strong_projection_initial_state_preservation X Y id.

Definition weak_incl_initial_message_preservation : Prop :=
  weak_embedding_initial_message_preservation X Y id.

Definition strong_incl_initial_message_preservation : Prop :=
  strong_embedding_initial_message_preservation X Y.

End sec_VLSM_incl_preservation.

Section sec_VLSM_incl_properties.

(** ** VLSM inclusion properties *)

Context
  {message : Type} [T : VLSMType message]
  [MX MY : VLSMMachine T]
  (Hincl : VLSM_incl_part MX MY)
  (X := mk_vlsm MX)
  (Y := mk_vlsm MY)
  .

(** VLSM inclusion specialized to finite trace. *)

Lemma VLSM_incl_finite_valid_trace
  (s : state X)
  (tr : list (transition_item X))
  (Htr : finite_valid_trace X s tr)
  : finite_valid_trace Y s tr.
Proof.
  apply (VLSM_embedding_finite_valid_trace (VLSM_incl_is_embedding Hincl))
    in Htr.
  by rewrite (VLSM_incl_is_embedding_finite_trace_project Hincl) in Htr.
Qed.

Lemma VLSM_incl_finite_valid_trace_init_to
  (s f : state X)
  (tr : list (transition_item X))
  (Htr : finite_valid_trace_init_to X s f tr)
  : finite_valid_trace_init_to Y s f tr.
Proof.
  apply (VLSM_embedding_finite_valid_trace_init_to (VLSM_incl_is_embedding Hincl))
    in Htr.
  by rewrite (VLSM_incl_is_embedding_finite_trace_project Hincl) in Htr.
Qed.

Lemma VLSM_incl_valid_state
  (s : state X)
  (Hs : valid_state_prop X s)
  : valid_state_prop Y s.
Proof.
  by apply (VLSM_embedding_valid_state (VLSM_incl_is_embedding Hincl)).
Qed.

Lemma VLSM_incl_initial_state
  (is : state X)
  : initial_state_prop X is -> initial_state_prop Y is.
Proof.
  by apply (VLSM_embedding_initial_state (VLSM_incl_is_embedding Hincl)).
Qed.

Lemma VLSM_incl_finite_valid_trace_from
  (s : state X)
  (tr : list (transition_item X))
  (Htr : finite_valid_trace_from X s tr)
  : finite_valid_trace_from Y s tr.
Proof.
  apply (VLSM_embedding_finite_valid_trace_from (VLSM_incl_is_embedding Hincl))
    in Htr.
  by rewrite (VLSM_incl_is_embedding_finite_trace_project Hincl) in Htr.
Qed.

Lemma VLSM_incl_finite_valid_trace_from_to
  (s f : state X)
  (tr : list (transition_item X))
  (Htr : finite_valid_trace_from_to X s f tr)
  : finite_valid_trace_from_to Y s f tr.
Proof.
  apply (VLSM_embedding_finite_valid_trace_from_to (VLSM_incl_is_embedding Hincl))
    in Htr.
  by rewrite (VLSM_incl_is_embedding_finite_trace_project Hincl) in Htr.
Qed.

Lemma VLSM_incl_in_futures
  (s1 s2 : state X)
  : in_futures X s1 s2 -> in_futures Y s1 s2.
Proof.
  by apply (VLSM_embedding_in_futures (VLSM_incl_is_embedding Hincl)).
Qed.

Lemma VLSM_incl_input_valid_transition
  : forall l s im s' om,
  input_valid_transition X l (s, im) (s', om) ->
  input_valid_transition Y l (s, im) (s', om).
Proof.
  by apply (VLSM_embedding_input_valid_transition (VLSM_incl_is_embedding Hincl)).
Qed.

Lemma VLSM_incl_input_valid
  : forall l s im,
  input_valid X l (s, im) ->
  input_valid Y l (s, im).
Proof.
  by apply (VLSM_embedding_input_valid (VLSM_incl_is_embedding Hincl)).
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
  by apply (VLSM_embedding_valid_state_message (VLSM_incl_is_embedding Hincl)).
Qed.

Lemma VLSM_incl_can_produce
  (s : state T)
  (om : option message)
  : option_can_produce X s om -> option_can_produce Y s om.
Proof.
  by apply (VLSM_embedding_can_produce (VLSM_incl_is_embedding Hincl)).
Qed.

Lemma VLSM_incl_can_emit
  (m : message)
  : can_emit X m -> can_emit Y m.
Proof.
  by apply (VLSM_embedding_can_emit (VLSM_incl_is_embedding Hincl)).
Qed.

Lemma VLSM_incl_valid_message :
  strong_incl_initial_message_preservation MX MY ->
  forall (m : message),
    valid_message_prop X m -> valid_message_prop Y m.
Proof.
  intros Hinitial_valid_message m [s Hm].
  by exists s; revert Hm; apply VLSM_incl_valid_state_message.
Qed.

Lemma VLSM_incl_infinite_valid_trace_from
  s ls
  : infinite_valid_trace_from X s ls ->
    infinite_valid_trace_from Y s ls.
Proof.
  intros Hls.
  apply (VLSM_embedding_infinite_valid_trace_from (VLSM_incl_is_embedding Hincl)) in Hls.
  revert Hls.
  apply infinite_valid_trace_from_EqSt.
  apply Streams.ntheq_eqst.
  unfold VLSM_embedding_infinite_trace_project, pre_VLSM_embedding_infinite_trace_project.
  intro n. rewrite Streams.Str_nth_map.
  by destruct (Streams.Str_nth _ _).
Qed.

Lemma VLSM_incl_infinite_valid_trace
  s ls
  : infinite_valid_trace X s ls -> infinite_valid_trace Y s ls.
Proof.
  intros [Htr His]. split.
  - by apply VLSM_incl_infinite_valid_trace_from.
  - by apply VLSM_incl_initial_state.
Qed.

Lemma VLSM_incl_valid_trace
  : forall t, valid_trace_prop X t -> valid_trace_prop Y t.
Proof.
  intros [s tr | s tr]; simpl.
  - by apply VLSM_incl_finite_valid_trace.
  - by apply VLSM_incl_infinite_valid_trace.
Qed.

End sec_VLSM_incl_properties.

(** We instantiate the above for VLSM inclusions *)
Section sec_basic_VLSM_incl.

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
  by apply VLSM_incl_embedding_iff, basic_VLSM_embedding.
Qed.

Lemma basic_VLSM_strong_incl
  (Hinitial_state : strong_incl_initial_state_preservation MX MY)
  (Hinitial_valid_message : strong_incl_initial_message_preservation MX MY)
  (Hvalid : strong_incl_valid_preservation MX MY)
  (Htransition : strong_incl_transition_preservation MX MY)
  : VLSM_incl X Y.
Proof.
  by apply VLSM_incl_embedding_iff, basic_VLSM_strong_embedding.
Qed.

End sec_basic_VLSM_incl.
