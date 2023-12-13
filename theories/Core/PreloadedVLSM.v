From VLSM.Lib Require Import Itauto.
From stdpp Require Import prelude.
From VLSM.Lib Require Import Preamble ListExtras.
From VLSM.Core Require Import VLSM VLSMProjections.

(** * Core: Preloaded VLSMs

  Given a VLSM <<X>>, we introduce the _pre-loaded_ version of it, which is
  identical to <<X>>, except that all messages are initial. The high degree
  of freedom allowed to the pre-loaded version lets it experience everything
  experienced by <<X>> but also other kinds of behavior, including _Byzantine_
  behavior, which makes it a useful concept in Byzantine fault tolerance analysis.
*)

Definition pre_loaded_vlsm_machine
  {message : Type} {T : VLSMType message} (M : VLSMMachine T) (initial : message -> Prop)
  : VLSMMachine T :=
{|
  initial_state_prop := @initial_state_prop _ _ M;
  initial_message_prop := fun m => @initial_message_prop _ _ M  m \/ initial m;
  s0 := @s0 _ _ M;
  transition := @transition _ _ M;
  valid := @valid _ _ M;
|}.

Definition pre_loaded_vlsm {message : Type} (X : VLSM message) (initial : message -> Prop)
  : VLSM message :=
    mk_vlsm (pre_loaded_vlsm_machine X initial).

Section sec_pre_loaded_with_all_messages_vlsm.

Context
  {message : Type}
  (X : VLSM message)
  .

Definition pre_loaded_with_all_messages_vlsm : VLSM message :=
  pre_loaded_vlsm X (fun _ => True).

(**
  A message which can be emitted during a protocol run of the
  [pre_loaded_with_all_messages_vlsm] is called a [byzantine_message],
  because as shown by [byzantine_pre_loaded_with_all_messages] and
  [pre_loaded_with_all_messages_alt_eq], byzantine traces for a [VLSM]
  are precisely the valid traces of the [pre_loaded_with_all_messages_vlsm],
  hence a byzantine message is any message which a byzantine trace [can_emit].
*)

Definition byzantine_message_prop
  (m : message)
  : Prop
  := can_emit pre_loaded_with_all_messages_vlsm m.

Definition byzantine_message : Type
  := sig byzantine_message_prop.

Lemma pre_loaded_with_all_messages_message_valid_initial_state_message
  (om : option message)
  : valid_state_message_prop pre_loaded_with_all_messages_vlsm (proj1_sig (vs0 X)) om.
Proof.
  by apply valid_initial_state_message; [apply proj2_sig | destruct om]; cbn; [right |].
Qed.

Lemma pre_loaded_with_all_messages_valid_state_message_preservation
  (s : state X)
  (om : option message)
  (Hps : valid_state_message_prop X s om)
  : valid_state_message_prop pre_loaded_with_all_messages_vlsm s om.
Proof.
  induction Hps.
  - apply (valid_initial_state_message pre_loaded_with_all_messages_vlsm); cbn; [done |].
    by destruct om; cbn; [right |].
  - by apply (valid_generated_state_message pre_loaded_with_all_messages_vlsm) with s _om _s om l.
Qed.

Lemma pre_loaded_with_all_messages_valid_state_prop
  (s : state X)
  (Hps : valid_state_prop X s)
  : valid_state_prop pre_loaded_with_all_messages_vlsm s.
Proof.
  unfold valid_state_prop in *.
  destruct Hps as [om Hprs].
  exists om.
  apply pre_loaded_with_all_messages_valid_state_message_preservation.
  by itauto.
Qed.

Lemma any_message_is_valid_in_preloaded (om : option message) :
  option_valid_message_prop pre_loaded_with_all_messages_vlsm om.
Proof.
  eexists.
  by apply pre_loaded_with_all_messages_message_valid_initial_state_message.
Qed.

Lemma preloaded_weaken_valid_state_message_prop s om :
  valid_state_message_prop X s om ->
  valid_state_message_prop pre_loaded_with_all_messages_vlsm s om.
Proof.
  induction 1.
  - refine (valid_initial_state_message pre_loaded_with_all_messages_vlsm s Hs om _).
    by destruct om; cbn; [right |].
  - by eapply valid_generated_state_message; cycle 2; eauto.
Qed.

Lemma preloaded_weaken_input_valid_transition
      l s om s' om' :
  input_valid_transition X l (s, om) (s', om') ->
  input_valid_transition pre_loaded_with_all_messages_vlsm l (s, om) (s', om').
Proof.
  unfold input_valid_transition.
  intros [[[_om valid_s] [_ Hvalid]] Htrans].
  repeat split; [| | done..].
  - by exists _om; apply preloaded_weaken_valid_state_message_prop.
  - by apply any_message_is_valid_in_preloaded.
Qed.

Lemma preloaded_weaken_valid_trace_from s tr
  : finite_valid_trace_from X s tr ->
    finite_valid_trace_from pre_loaded_with_all_messages_vlsm s tr.
Proof.
  intros H. induction H using finite_valid_trace_from_rev_ind.
  - apply (finite_valid_trace_from_empty pre_loaded_with_all_messages_vlsm).
    destruct H as [om H]. exists om.
    by revert H; apply preloaded_weaken_valid_state_message_prop.
  - apply (finite_valid_trace_from_app_iff pre_loaded_with_all_messages_vlsm).
    split; [done |].
    apply (finite_valid_trace_singleton pre_loaded_with_all_messages_vlsm).
    by revert Hx; apply preloaded_weaken_input_valid_transition.
Qed.

Lemma pre_trace_segments_with_valid_inputs_are_valid s f tr
  (Htr : finite_valid_trace_from_to pre_loaded_with_all_messages_vlsm s f tr)
  (Hs : valid_state_prop X s)
  (Hobs : Forall (fun item => option_valid_message_prop X (input item)) tr)
  : finite_valid_trace_from_to X s f tr.
Proof.
  revert Hs Hobs; induction Htr using finite_valid_trace_from_to_ind;
    [by intros; apply (finite_valid_trace_from_to_empty X) |].
  rewrite Forall_cons; intros ? [].
  cut (input_valid_transition X l (s', iom) (s, oom)).
  {
    intro; apply (finite_valid_trace_from_to_extend X); [| done].
    by apply IHHtr; [eapply input_valid_transition_destination |].
  }
  destruct Ht as [(_ & _ & Hv) Ht].
  repeat split; [done | | done..].
  by destruct iom as [m |]; [| apply option_valid_message_None].
Qed.

Lemma pre_traces_with_valid_inputs_are_valid s f tr
  (Htr : finite_valid_trace_init_to pre_loaded_with_all_messages_vlsm s f tr)
  (Hobs : Forall (fun item => option_valid_message_prop X (input item)) tr)
  : finite_valid_trace_init_to X s f tr.
Proof.
  destruct Htr as [Htr Hinit]; split; [| done].
  by apply pre_trace_segments_with_valid_inputs_are_valid;
    [| apply initial_state_is_valid |].
Qed.

End sec_pre_loaded_with_all_messages_vlsm.

Section sec_pre_loaded_valid_transition.

Context
  `(X : VLSM message)
  (R := pre_loaded_with_all_messages_vlsm X)
  .

Lemma valid_transition_preloaded_iff :
  forall l s1 iom s2 oom,
    valid_transition X l s1 iom s2 oom <-> valid_transition R l s1 iom s2 oom.
Proof. by firstorder. Qed.

Lemma valid_transition_next_preloaded_iff :
  forall s1 s2, valid_transition_next X s1 s2 <-> valid_transition_next R s1 s2.
Proof.
  by intros; split; intros []; econstructor; apply valid_transition_preloaded_iff.
Qed.

End sec_pre_loaded_valid_transition.

Section sec_pre_loaded_vlsm_total_projection.

Context
  {message : Type}
  (X Y : VLSM message)
  (P Q : message -> Prop)
  (label_project : label X -> option (label Y))
  (state_project : state X -> state Y)
  (Hvalid : strong_projection_valid_preservation X Y label_project state_project)
  (Htransition_Some : strong_projection_transition_preservation_Some X Y label_project state_project)
  (Htransition_None : strong_projection_transition_consistency_None _ _ label_project state_project)
  (Hstate : strong_projection_initial_state_preservation X Y state_project)
  (Hmessage : weak_projection_valid_message_preservation
                (pre_loaded_vlsm X P) (pre_loaded_vlsm Y Q) label_project state_project)
  .

Lemma basic_VLSM_projection_type_preloaded :
  VLSM_projection_type (pre_loaded_with_all_messages_vlsm X) Y label_project state_project.
Proof.
  constructor.
  intros is tr Htr.
  induction Htr using finite_valid_trace_from_rev_ind; [done |].
  rewrite pre_VLSM_projection_finite_trace_project_app, finite_trace_last_is_last,
    finite_trace_last_app, <- IHHtr; cbn.
  unfold pre_VLSM_projection_transition_item_project.
  destruct (label_project _) as [lY |] eqn: Hl; [done |].
  by rewrite Htransition_None; [.. | apply Hx].
Qed.

Lemma basic_VLSM_projection_preloaded :
  VLSM_projection
    (pre_loaded_with_all_messages_vlsm X)
    (pre_loaded_with_all_messages_vlsm Y) label_project state_project.
Proof.
  specialize (basic_VLSM_projection_type_preloaded) as Htype.
  constructor; [done |].
  intros sX trX HtrX.
  split; [| by apply Hstate; apply HtrX].
  induction HtrX using finite_valid_trace_rev_ind;
    [by constructor; apply initial_state_is_valid, Hstate |].
  rewrite pre_VLSM_projection_finite_trace_project_app.
  apply finite_valid_trace_from_app_iff.
  split; [done |].
  cbn; unfold pre_VLSM_projection_transition_item_project; cbn.
  apply finite_valid_trace_last_pstate in IHHtrX.
  rewrite <- (final_state_project _ _ _ _ Htype) in IHHtrX |- * by apply HtrX.
  destruct (label_project l) as [lY |] eqn: Hl;
    [| by apply (finite_valid_trace_from_empty (pre_loaded_with_all_messages_vlsm Y))].
  apply (finite_valid_trace_singleton (pre_loaded_with_all_messages_vlsm Y)).
  destruct Hx as [[_ [_ Hv]] Ht].
  repeat split; [done | ..].
  - destruct iom as [im |]; [| by apply option_valid_message_None].
    by apply any_message_is_valid_in_preloaded.
  - by eapply Hvalid.
  - by eapply Htransition_Some.
Qed.

Lemma basic_VLSM_projection_type_preloaded_with :
  VLSM_projection_type (pre_loaded_vlsm X P) Y label_project state_project.
Proof.
  constructor.
  intros is tr Htr.
  induction Htr using finite_valid_trace_from_rev_ind; [done |].
  rewrite pre_VLSM_projection_finite_trace_project_app, finite_trace_last_is_last,
    finite_trace_last_app, <- IHHtr.
  cbn; unfold pre_VLSM_projection_transition_item_project.
  destruct (label_project _) as [lY |] eqn: Hl; [done |].
  by rewrite Htransition_None; [.. | apply Hx].
Qed.

Lemma basic_VLSM_projection_preloaded_with :
  VLSM_projection (pre_loaded_vlsm X P) (pre_loaded_vlsm Y Q) label_project state_project.
Proof.
  specialize (basic_VLSM_projection_type_preloaded_with) as Htype.
  constructor; [done |].
  intros sX trX HtrX.
  split; [| by apply Hstate; apply HtrX].
  induction HtrX using finite_valid_trace_rev_ind;
    [by constructor; apply initial_state_is_valid, Hstate |].
  rewrite pre_VLSM_projection_finite_trace_project_app.
  apply (finite_valid_trace_from_app_iff (pre_loaded_vlsm Y Q)).
  split; [done |].
  cbn; unfold pre_VLSM_projection_transition_item_project; cbn.
  apply finite_valid_trace_last_pstate in IHHtrX.
  apply proj1 in Hx as Hpv.
  destruct Hx as [[_ [_ Hv]] Ht].
  rewrite <- (final_state_project _ _ _ _ Htype) in IHHtrX |- * by apply HtrX.
  destruct (label_project l) as [lY |] eqn: Hl;
    [| by apply (finite_valid_trace_from_empty (pre_loaded_vlsm Y Q))].
  apply (finite_valid_trace_singleton (pre_loaded_vlsm Y Q)).
  repeat split; [done | ..].
  - destruct iom as [im |]; [| by apply option_valid_message_None].
    by eapply Hmessage.
  - by eapply Hvalid.
  - by eapply Htransition_Some.
Qed.

End sec_pre_loaded_vlsm_total_projection.

Section sec_pre_loaded_vlsm_embedding.

Context
  {message : Type}
  (X Y : VLSM message)
  (P Q : message -> Prop)
  (PimpliesQ : forall m : message, P m -> Q m)
  (label_project : label X -> label Y)
  (state_project : state X -> state Y)
  (Hvalid : strong_embedding_valid_preservation X Y label_project state_project)
  (Htransition : strong_embedding_transition_preservation  X Y label_project state_project)
  (Hstate : strong_projection_initial_state_preservation X Y state_project)
  (Hmessage : strong_embedding_initial_message_preservation X Y)
  .

Lemma basic_VLSM_embedding_preloaded :
  VLSM_embedding (pre_loaded_with_all_messages_vlsm X) (pre_loaded_with_all_messages_vlsm Y)
    label_project state_project.
Proof.
  constructor.
  intros sX trX HtrX.
  split; [| by apply Hstate; apply HtrX].
  induction HtrX using finite_valid_trace_rev_ind;
    [by constructor; apply initial_state_is_valid, Hstate |].
  setoid_rewrite map_app.
  apply finite_valid_trace_from_app_iff.
  split; cbn; [done |].
  apply (finite_valid_trace_singleton (pre_loaded_with_all_messages_vlsm Y)).
  destruct Hx as [[_ [_ Hv]] Ht].
  apply Hvalid in Hv.
  apply Htransition in Ht.
  rewrite (pre_VLSM_embedding_finite_trace_last _ _ label_project state_project) in Hv, Ht.
  repeat split; [| | done..].
  - by apply finite_valid_trace_last_pstate in IHHtrX.
  - by apply any_message_is_valid_in_preloaded.
Qed.

Lemma basic_VLSM_embedding_preloaded_with :
  VLSM_embedding (pre_loaded_vlsm X P) (pre_loaded_vlsm Y Q) label_project state_project.
Proof.
  constructor.
  intros sX trX HtrX.
  apply valid_trace_add_default_last in HtrX.
  split; [| by apply Hstate; apply HtrX].
  induction HtrX using finite_valid_trace_init_to_rev_strong_ind;
    [by constructor; apply initial_state_is_valid, Hstate |].
  setoid_rewrite map_app.
  apply finite_valid_trace_from_app_iff.
  split; cbn; [done |].
  apply (finite_valid_trace_singleton (pre_loaded_vlsm Y Q)).
  destruct Ht as [[_ [_ Hv]] Ht].
  apply Hvalid in Hv.
  apply Htransition in Ht.
  apply valid_trace_get_last in HtrX1.
  subst s; cbn.
  rewrite (pre_VLSM_embedding_finite_trace_last _ _ label_project state_project) in Hv, Ht.
  repeat split; [by apply finite_valid_trace_last_pstate in IHHtrX1 | | done..].
  destruct iom as [m |]; [| by apply option_valid_message_None].
  unfold empty_initial_message_or_final_output in Heqiom.
  destruct_list_last iom_tr iom_tr' iom_lst Heqiom_tr.
  - by apply option_initial_message_is_valid; destruct Heqiom as [Him | Hp]; cbn; itauto.
  - eapply valid_trace_output_is_valid; [done |].
    setoid_rewrite map_app.
    by apply Exists_app; right; left.
Qed.

End sec_pre_loaded_vlsm_embedding.

Section sec_pre_loaded_vlsm_inclusion.

Context
  {message : Type}
  {T : VLSMType message}
  (MX MY : VLSMMachine T)
  (X := mk_vlsm MX)
  (Y := mk_vlsm MY)
  .

Lemma basic_VLSM_incl_preloaded
  (Hinitial_state : strong_incl_initial_state_preservation MX MY)
  (Hvalid : strong_incl_valid_preservation MX MY)
  (Htransition : strong_incl_transition_preservation MX MY)
  : VLSM_incl (pre_loaded_with_all_messages_vlsm X) (pre_loaded_with_all_messages_vlsm Y).
Proof.
  by apply VLSM_incl_embedding_iff, (basic_VLSM_embedding_preloaded X Y id id).
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
  by apply VLSM_incl_embedding_iff, (basic_VLSM_embedding_preloaded_with X Y _ _ PimpliesQ id id).
Qed.

End sec_pre_loaded_vlsm_inclusion.

Section sec_VLSM_incl_preloaded_properties.

Context
  {message : Type}
  (X : VLSM message)
  .

Lemma vlsm_incl_pre_loaded :
  forall (P : message -> Prop),
    VLSM_incl X (pre_loaded_vlsm X P).
Proof.
  by intros; apply basic_VLSM_strong_incl; cbv; itauto.
Qed.

Lemma vlsm_incl_pre_loaded_with_all_messages_vlsm :
  VLSM_incl X (pre_loaded_with_all_messages_vlsm X).
Proof.
  by apply vlsm_incl_pre_loaded.
Qed.

Lemma pre_loaded_vlsm_incl_relaxed
  (P Q : message -> Prop)
  (PimpliesQorValid : forall m : message, P m -> Q m \/ valid_message_prop (pre_loaded_vlsm X Q) m)
  : VLSM_incl (pre_loaded_vlsm X P) (pre_loaded_vlsm X Q).
Proof.
  apply basic_VLSM_incl; cycle 1; [| by cbv; itauto..].
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
  by apply pre_loaded_vlsm_incl_relaxed; itauto.
Qed.

Lemma pre_loaded_vlsm_idem_l :
  forall (P : message -> Prop),
    VLSM_incl (pre_loaded_vlsm (pre_loaded_vlsm X P) P) (pre_loaded_vlsm X P).
Proof.
  by intros; apply basic_VLSM_strong_incl; cbv; itauto.
Qed.

Lemma pre_loaded_vlsm_idem_r :
  forall (P : message -> Prop),
    VLSM_incl (pre_loaded_vlsm X P) (pre_loaded_vlsm (pre_loaded_vlsm X P) P).
Proof.
  by intros; apply basic_VLSM_incl_preloaded_with; cbv; itauto.
Qed.

Lemma pre_loaded_vlsm_incl_pre_loaded_with_all_messages :
  forall (P : message -> Prop),
    VLSM_incl (pre_loaded_vlsm X P) (pre_loaded_with_all_messages_vlsm X).
Proof.
  by intros; apply pre_loaded_vlsm_incl.
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
  (from : state X) (tr : list transition_item)
  : finite_valid_trace_from X from tr ->
    finite_valid_trace_from (pre_loaded_with_all_messages_vlsm X) from tr.
Proof.
  by intros; eapply VLSM_incl_finite_valid_trace_from;
    [apply vlsm_incl_pre_loaded_with_all_messages_vlsm | destruct X].
Qed.

Lemma preloaded_weaken_finite_valid_trace_from_to
  (from to : state X) (tr : list transition_item)
  : finite_valid_trace_from_to X from to tr ->
    finite_valid_trace_from_to (pre_loaded_with_all_messages_vlsm X) from to tr.
Proof.
  by intros; eapply VLSM_incl_finite_valid_trace_from_to;
    [apply vlsm_incl_pre_loaded_with_all_messages_vlsm | destruct X].
Qed.

End sec_VLSM_incl_preloaded_properties.

Section sec_VLSM_eq_preloaded_properties.

Context
  {message : Type}
  (X : VLSM message)
  .

Lemma pre_loaded_vlsm_with_valid_eq
  (P Q : message -> Prop)
  (QimpliesValid : forall m, Q m -> valid_message_prop (pre_loaded_vlsm X P) m)
  : VLSM_eq (pre_loaded_vlsm X (fun m => P m \/ Q m)) (pre_loaded_vlsm X P).
Proof.
  split; cbn.
  - by apply pre_loaded_vlsm_incl_relaxed; itauto.
  - by apply pre_loaded_vlsm_incl; itauto.
Qed.

Lemma pre_loaded_vlsm_idem
  (P : message -> Prop)
  : VLSM_eq (pre_loaded_vlsm (pre_loaded_vlsm X P) P) (pre_loaded_vlsm X P).
Proof.
  split; cbn.
  - by apply pre_loaded_vlsm_idem_l.
  - by apply pre_loaded_vlsm_idem_r.
Qed.

Lemma pre_loaded_with_all_messages_eq_validating_pre_loaded_vlsm
  (P : message -> Prop)
  (Hvalidating :
    forall (l : label _) (s : state _) (m : message)
      (Hv : input_valid (pre_loaded_with_all_messages_vlsm X) l (s, Some m)),
      valid_message_prop (pre_loaded_vlsm X P) m)
  : VLSM_eq (pre_loaded_with_all_messages_vlsm X) (pre_loaded_vlsm X P).
Proof.
  split; cbn; [| by apply pre_loaded_vlsm_incl_pre_loaded_with_all_messages].
  apply basic_VLSM_incl.
  - by intro.
  - by intros l s m Hv _ _; eapply Hvalidating.
  - by intros l s om (_ & _ & ?).
  - by intros l s om s' om' [_ Ht].
Qed.

Lemma vlsm_is_pre_loaded_with_False :
  VLSM_eq X (pre_loaded_vlsm X (fun _ => False)).
Proof.
  by cbn; split; apply basic_VLSM_strong_incl; cbv; itauto.
Qed.

Lemma vlsm_is_pre_loaded_with_False_initial_message :
  strong_embedding_initial_message_preservation X (pre_loaded_vlsm X (fun _ => False)).
Proof.
  by intros m Hm; left.
Qed.

Lemma vlsm_is_pre_loaded_with_False_initial_message_rev :
  strong_embedding_initial_message_preservation (pre_loaded_vlsm X (fun _ => False)) X.
Proof.
  by intros m [Hm | Hfalse].
Qed.

Lemma vlsm_is_pre_loaded_with_False_valid_state_message s om :
  valid_state_message_prop X s om <->
  valid_state_message_prop (pre_loaded_vlsm X (fun _ => False)) s om.
Proof.
  pose proof vlsm_is_pre_loaded_with_False as Heq.
  destruct X as (T, M); simpl in *.
  by split; (apply VLSM_incl_valid_state_message; [| cbv; tauto]); apply Heq.
Qed.

End sec_VLSM_eq_preloaded_properties.

(** ** Constrained traces, states and messages

  We will use the word "constrained" to denote concepts which correspond to
  validity in the VLSM preloaded with all messages.
*)

Section sec_constrained_defs.

Context
  `(X : VLSM message)
  .

Definition input_constrained :=
  input_valid (pre_loaded_with_all_messages_vlsm X).

Definition input_constrained_transition :=
  input_valid_transition (pre_loaded_with_all_messages_vlsm X).

Definition input_constrained_transition_to :=
  input_valid_transition_to (pre_loaded_with_all_messages_vlsm X).

Definition input_constrained_transition_item :=
  input_valid_transition_item (pre_loaded_with_all_messages_vlsm X).

Definition finite_constrained_trace_from_to :=
  finite_valid_trace_from_to (pre_loaded_with_all_messages_vlsm X).

Definition finite_constrained_trace_from :=
  finite_valid_trace_from (pre_loaded_with_all_messages_vlsm X).

Definition finite_constrained_trace_init_to :=
  finite_valid_trace_init_to (pre_loaded_with_all_messages_vlsm X).

Definition finite_constrained_trace :=
  finite_valid_trace (pre_loaded_with_all_messages_vlsm X).

Definition constrained_state_prop :=
  valid_state_prop (pre_loaded_with_all_messages_vlsm X).

Definition constrained_message_prop :=
  can_emit (pre_loaded_with_all_messages_vlsm X).

Definition constrained_state_message_prop :=
  valid_state_message_prop (pre_loaded_with_all_messages_vlsm X).

End sec_constrained_defs.

(** ** Direct definitions of constrained traces, states and messages

  In the above formalization, "valid" concepts are defined first, then
  "constrained" ones are derived from them, expressed as validity within the
  [pre_loaded_with_all_messages_vlsm].

  In this section we state the original mathematical definitions (as presented
  in the #<a href="https://doi.org/10.48550/arXiv.2202.12662">VLSM paper</a>#)
  and we show them equivalent with the ones defined above.
*)

Section sec_constrained_direct_defs.

Context
  `(X : VLSM message)
  .

(**
  A sequence of constrained transitions, without any requirements on the
  starting state.
*)
Inductive constrained_transitions_from_to :
  state X -> state X -> list (transition_item X) -> Prop :=
| ct_empty : forall s, constrained_transitions_from_to s s []
| ct_extend : forall s s' om om' l f tr, transition X l (s, om) = (s', om') ->
    valid X l (s, om) -> constrained_transitions_from_to s' f tr ->
    constrained_transitions_from_to s f
      ((Build_transition_item l om s' om') :: tr).

(**
  A constrained state is a sequence of constrained transitions originating in
  an initial state.
*)
Definition finite_constrained_trace_init_to_direct
  (s f : state X) (tr : list (transition_item X)) :=
  constrained_transitions_from_to s f tr /\ initial_state_prop X s.

Lemma finite_constrained_trace_init_to_direct_right_impl :
  forall (s f : state X) (tr : list (transition_item X)),
    finite_constrained_trace_init_to X s f tr -> finite_constrained_trace_init_to_direct s f tr.
Proof.
  intros s f tr [Htr Hinit].
  constructor; [| done]; clear Hinit.
  induction Htr.
  - by apply ct_empty.
  - by apply ct_extend; [apply Ht..|].
Qed.

Lemma finite_constrained_trace_init_to_direct_left_impl :
  forall (s f : state X) (tr : list (transition_item X)),
    finite_constrained_trace_init_to_direct s f tr -> finite_constrained_trace_init_to X s f tr.
Proof.
  intros s f tr [Htr Hs].
  split; [| done].
  apply (initial_state_is_valid (pre_loaded_with_all_messages_vlsm X)) in Hs.
  revert s Hs Htr.
  induction tr; intros; inversion Htr; subst.
  - by apply (finite_valid_trace_from_to_empty (pre_loaded_with_all_messages_vlsm X)).
  - apply (finite_valid_trace_from_to_extend (pre_loaded_with_all_messages_vlsm X)); cycle 1.
    + by repeat split; [| apply any_message_is_valid_in_preloaded | ..].
    + apply IHtr; [| done].
      apply valid_state_prop_iff; right.
      exists l, (s, om), om'.
      by repeat split; [| apply any_message_is_valid_in_preloaded | ..].
Qed.

Lemma finite_constrained_trace_init_to_direct_equiv :
  forall (s f : state X) (tr : list (transition_item X)),
    finite_constrained_trace_init_to_direct s f tr <-> finite_constrained_trace_init_to X s f tr.
Proof.
  split.
  - by apply finite_constrained_trace_init_to_direct_left_impl.
  - by apply finite_constrained_trace_init_to_direct_right_impl.
Qed.

(** A constrained state is a state reachable through a constrained trace. *)
Definition constrained_state_prop_direct (f : state X) : Prop :=
  exists (s : state X) (tr : list (transition_item X)),
    finite_constrained_trace_init_to_direct s f tr.

Lemma constrained_state_prop_direct_equiv :
  forall (s : state X),
    constrained_state_prop_direct s <-> constrained_state_prop X s.
Proof.
  intros s.
  unfold constrained_state_prop_direct;
    setoid_rewrite finite_constrained_trace_init_to_direct_equiv; split.
  - by intros (? & ? & []); eapply finite_valid_trace_from_to_last_pstate.
  - by intro Hs; apply valid_state_has_trace in Hs as (? & ? & ?); eexists _, _.
Qed.

(**
  A constrained message is one which can be emitted by a constrained trace.
*)

Definition constrained_message_prop_direct (m : message) : Prop :=
  exists (s f : state X) (tr : list (transition_item X)) (item : transition_item X),
    finite_constrained_trace_init_to_direct s f (tr ++ [item]) /\ output item = Some m.

Lemma constrained_message_prop_direct_equiv :
  forall (m : message),
    constrained_message_prop_direct m <-> constrained_message_prop X m.
Proof.
  intros m.
  unfold constrained_message_prop_direct, constrained_message_prop; rewrite can_emit_iff.
  setoid_rewrite finite_constrained_trace_init_to_direct_equiv.
  setoid_rewrite non_empty_valid_trace_from_can_produce; split.
  - intros (is & s & tr & item & Htr & Hm).
    exists s, is, (tr ++ [item]), item; split_and!; [..| done].
    + by eapply valid_trace_forget_last.
    + by apply last_error_is_last.
    + apply finite_valid_trace_init_to_last in Htr.
      by erewrite <- finite_trace_last_is_last.
  - intros (s & is & tr' & item & Htr & Hlast & Hs & Hm).
    destruct_list_last tr' tr item_ Heqtr; subst; [done |].
    rewrite last_error_is_last in Hlast; apply Some_inj in Hlast as ->.
    apply valid_trace_add_default_last in Htr.
    by eexists _, _, _, _.
Qed.

(** *** Definitions of valid traces, messages, and states based on constrained ones

  Here we state the original mathematical definitions (as presented in the
  #<a href="https://doi.org/10.48550/arXiv.2202.12662">VLSM paper</a>#)
  for valid traces, states, and messages, deriving them from the "constrained"
  notions, and we showing them equivalent with the ones defined in the VLSM module.
*)

(**
  A valid trace is a constrained trace whose [input]s are all valid messages;
  a valid message is either an initial message or an [output] of a valid trace.
*)
Inductive
  finite_valid_trace_init_to_from_constrained :
    state X -> state X -> list (transition_item X) -> Prop :=
| fvtit_def : forall (s f : state X) (tr : list (transition_item X)),
    finite_constrained_trace_init_to_direct s f tr ->
    (forall item, item ∈ tr ->
      option_valid_message_prop_from_constrained (input item)) ->
    finite_valid_trace_init_to_from_constrained s f tr
with
  option_valid_message_prop_from_constrained : option message -> Prop :=
| ovmp_def_initial :
  forall om, option_initial_message_prop X om ->
    option_valid_message_prop_from_constrained om
| ovmp_def_emit :
  forall (s f : state X) (tr : list (transition_item X)),
   finite_valid_trace_init_to_from_constrained s f tr ->
   forall (item : transition_item X), item ∈ tr ->
   option_valid_message_prop_from_constrained (output item).

Lemma finite_valid_trace_init_to_from_constrained_right_impl :
  forall (s f : state X) (tr : list (transition_item X)),
  finite_valid_trace_init_to X s f tr ->
  finite_valid_trace_init_to_from_constrained s f tr.
Proof.
  intros * Htr.
  induction Htr using finite_valid_trace_init_to_rev_strong_ind;
    [by repeat constructor; [| inversion H] |].
  constructor.
  - clear -Htr1 Ht.
    apply finite_constrained_trace_init_to_direct_equiv.
    destruct X.
    eapply VLSM_incl_finite_valid_trace_init_to;
      [by apply vlsm_incl_pre_loaded_with_all_messages_vlsm |].
    destruct Htr1 as [Htr1 Hinit]; split; [| done].
    eapply finite_valid_trace_from_to_app; [done |].
    by apply finite_valid_trace_from_to_singleton.
  - inversion IHHtr1 as [? ? ? _ IHoutput]; subst; clear IHHtr1.
    intro item; rewrite elem_of_app, elem_of_list_singleton.
    intros [| ->]; [by apply IHoutput |].
    unfold empty_initial_message_or_final_output in Heqiom.
    destruct_list_last iom_tr iom_tr' item Heq; [by constructor 1 |].
    subst iom; econstructor 2; [done |].
    by rewrite elem_of_app, elem_of_list_singleton; right.
Qed.

Lemma finite_valid_trace_init_to_from_constrained_left_impl :
  forall (s f : state X) (tr : list (transition_item X)),
  finite_valid_trace_init_to_from_constrained s f tr -> finite_valid_trace_init_to X s f tr
with option_valid_message_prop_from_constrained_left_impl :
  forall om, option_valid_message_prop_from_constrained om -> option_valid_message_prop X om.
Proof.
  - intros * Htr; inversion Htr as [? ? ? [Htrc Hinit] Hmsgs]; subst; clear Htr.
    apply pre_traces_with_valid_inputs_are_valid;
      [by apply finite_constrained_trace_init_to_direct_left_impl |].
    rewrite Forall_forall in *; intros.
    by apply option_valid_message_prop_from_constrained_left_impl, Hmsgs.
  - intros om Hom.
    inversion Hom as [? Hinit | ? ? ? Hemit ? Hitem]; subst;
      [by apply option_initial_message_is_valid |].
    destruct (output item) as [m |] eqn:Houtput;
      [| by apply option_valid_message_None].
    eapply option_valid_message_Some, valid_trace_output_is_valid;
      [| by apply Exists_exists; eexists].
    by eapply valid_trace_forget_last, finite_valid_trace_init_to_from_constrained_left_impl.
Qed.

Lemma finite_valid_trace_init_to_from_constrained_equiv :
  forall (s f : state X) (tr : list (transition_item X)),
  finite_valid_trace_init_to_from_constrained s f tr <-> finite_valid_trace_init_to X s f tr.
Proof.
  split.
  - by apply finite_valid_trace_init_to_from_constrained_left_impl.
  - by apply finite_valid_trace_init_to_from_constrained_right_impl.
Qed.

Lemma option_valid_message_prop_from_constrained_right_impl :
  forall om, option_valid_message_prop X om -> option_valid_message_prop_from_constrained om.
Proof.
  intros [m |] Hm; [| by apply ovmp_def_initial].
  apply emitted_messages_are_valid_iff in Hm as [| Hm]; [by apply ovmp_def_initial |].
  apply can_emit_has_trace in Hm as (is & tr & item & Htr & <-).
  apply valid_trace_add_default_last, finite_valid_trace_init_to_from_constrained_right_impl in Htr.
  econstructor 2; [done |].
  by rewrite elem_of_app, elem_of_list_singleton; right.
Qed.

Lemma option_valid_message_prop_from_constrained_equiv :
  forall om, option_valid_message_prop_from_constrained om <-> option_valid_message_prop X om.
Proof.
  split.
  - by apply option_valid_message_prop_from_constrained_left_impl.
  - by apply option_valid_message_prop_from_constrained_right_impl.
Qed.

(** A valid state is a state reachable through a valid trace. *)
Definition valid_state_prop_from_constrained (s : state X) : Prop :=
  exists (is : state X) (tr : list (transition_item X)),
    finite_valid_trace_init_to_from_constrained is s tr.

Lemma valid_state_prop_from_constrained_left_impl :
  forall (s : state X), valid_state_prop_from_constrained s -> valid_state_prop X s.
Proof.
  intros s (is & tr & Htr).
  by apply finite_valid_trace_init_to_from_constrained_equiv, valid_trace_last_pstate in Htr.
Qed.

Lemma valid_state_prop_from_constrained_right_impl :
  forall (s : state X), valid_state_prop X s -> valid_state_prop_from_constrained s.
Proof.
  intros s Hs.
  apply valid_state_has_trace in Hs as (is & tr & Htr).
  by exists is, tr; apply finite_valid_trace_init_to_from_constrained_equiv.
Qed.

Lemma valid_state_prop_from_constrained_equiv :
  forall (s : state X), valid_state_prop_from_constrained s <-> valid_state_prop X s.
Proof.
  split.
  - by apply valid_state_prop_from_constrained_left_impl.
  - by apply valid_state_prop_from_constrained_right_impl.
Qed.

End sec_constrained_direct_defs.

Lemma vlsm_is_preloaded_with_valid `(X : VLSM message) :
  VLSM_eq X (pre_loaded_vlsm X (valid_message_prop X)).
Proof.
  split; [by apply basic_VLSM_strong_incl; intros ?; only 2: left |].
  apply basic_VLSM_incl; intros ? **; cbn; [done | ..].
  - destruct HmX as [Hinit | HmX].
    + by apply initial_message_is_valid.
    + by destruct X.
  - by apply Hv.
  - by apply H.
Qed.
