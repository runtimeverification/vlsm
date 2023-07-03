From VLSM.Lib Require Import Itauto.
From stdpp Require Import prelude.
From VLSM.Lib Require Import Preamble ListExtras.
From VLSM.Core Require Import VLSM VLSMProjections.

(** * Pre-loaded VLSMs

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

Inductive preloaded_valid_state_prop : state X -> Prop :=
| preloaded_valid_initial_state
    (s : state X)
    (Hs : initial_state_prop (VLSMMachine := pre_loaded_with_all_messages_vlsm) s) :
       preloaded_valid_state_prop s
| preloaded_protocol_generated
    (l : label X)
    (s : state X)
    (Hps : preloaded_valid_state_prop s)
    (om : option message)
    (Hv : valid (VLSMMachine := pre_loaded_with_all_messages_vlsm) l (s, om))
    s' om'
    (Ht : transition (VLSMMachine := pre_loaded_with_all_messages_vlsm) l (s, om) = (s', om'))
  : preloaded_valid_state_prop s'.

Lemma preloaded_valid_state_prop_iff (s : state X) :
  valid_state_prop pre_loaded_with_all_messages_vlsm s
  <-> preloaded_valid_state_prop s.
Proof.
  split.
  - intros [om Hvalid].
    induction Hvalid.
    + by apply preloaded_valid_initial_state.
    + by apply preloaded_protocol_generated with l s om om'.
  - induction 1.
    + by exists None; apply valid_initial_state_message.
    + exists om'. destruct IHpreloaded_valid_state_prop as [_om Hs].
      specialize (any_message_is_valid_in_preloaded om) as [_s Hom].
      by apply (valid_generated_state_message pre_loaded_with_all_messages_vlsm) with s _om _s om l.
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

Lemma pre_traces_with_valid_inputs_are_valid is s tr
  (Htr : finite_valid_trace_init_to pre_loaded_with_all_messages_vlsm is s tr)
  (Hobs : forall m,
    trace_has_message (field_selector input) m tr ->
    valid_message_prop X m)
  : finite_valid_trace_init_to X is s tr.
Proof.
  revert s Htr Hobs.
  induction tr using rev_ind; intros; split
  ; [| by apply Htr | | by apply Htr]
  ; destruct Htr as [Htr Hinit].
  - inversion Htr; subst.
    by apply (finite_valid_trace_from_to_empty X), initial_state_is_valid.
  - apply finite_valid_trace_from_to_last in Htr as Hlst.
    apply finite_valid_trace_from_to_app_split in Htr.
    destruct Htr as [Htr Hx].
    specialize (IHtr _ (conj Htr Hinit)).
    spec IHtr; [by intros; apply Hobs, trace_has_message_prefix |].
    destruct IHtr as [IHtr _];
    apply finite_valid_trace_from_to_forget_last in IHtr.
    apply finite_valid_trace_from_add_last; [| done].
    inversion Hx; subst f tl s'.
    apply (extend_right_finite_trace_from X); [done |].
    destruct Ht as [[_ [_ Hv]] Ht].
    apply finite_valid_trace_last_pstate in IHtr as Hplst.
    repeat split. 1, 3-4: done.
    destruct iom as [m |]; [| apply option_valid_message_None].
    apply option_valid_message_Some, Hobs.
    red; rewrite Exists_app, Exists_cons.
    by subst; cbn; itauto.
Qed.

End sec_pre_loaded_with_all_messages_vlsm.

Section sec_pre_loaded_valid_transition.

Context
  `(X : VLSM message)
  (R := pre_loaded_with_all_messages_vlsm X)
  .

Lemma ValidTransition_preloaded_iff :
  forall l s1 iom s2 oom,
    ValidTransition X l s1 iom s2 oom <-> ValidTransition R l s1 iom s2 oom.
Proof. by firstorder. Qed.

Lemma ValidTransitionNext_preloaded_iff :
  forall s1 s2, ValidTransitionNext X s1 s2 <-> ValidTransitionNext R s1 s2.
Proof.
  by intros; split; intros []; econstructor; apply ValidTransition_preloaded_iff.
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

(** ** Finite constrained traces

  The ability to preload VLSM with all possible messages allows us to encode behavior
  such as finite constrained traces, which are, by definition, finite valid traces
  where all messages are valid (initial).
*)

Definition finite_constrained_trace_init_to `(X : VLSM message) :=
  finite_valid_trace_init_to (pre_loaded_with_all_messages_vlsm X).

(**
  In order to simplify proofs regarding valid/constrained traces we have
  an equivalent definition for both [finite_valid_trace_init_to] and
  [finite_constrained_trace_init_to].
*)

Inductive constrained_transitions_from_to `(X : VLSM message) :
  state X -> state X -> list (transition_item X) -> Prop :=
| ct_empty : forall s, constrained_transitions_from_to X s s []
| ct_extend : forall s s' om om' l f tr, transition X l (s, om) = (s', om') ->
    valid X l (s, om) -> constrained_transitions_from_to X s' f tr ->
    constrained_transitions_from_to X s f
      ((Build_transition_item l om s' om') :: tr).

Definition finite_constrained_trace_init_to_alt
  `(X : VLSM message) (s f : state X) (tr : list (transition_item X)) :=
  constrained_transitions_from_to X s f tr /\ initial_state_prop X s.

Inductive message_valid_transitions_from_to `(X : VLSM message) :
  state X -> state X -> list (transition_item X) -> Prop :=
| mvt_empty : forall s, message_valid_transitions_from_to X s s []
| mvt_extend : forall s s' om om' l f tr, option_valid_message_prop X om ->
    transition X l (s, om) = (s', om') -> valid X l (s, om) ->
      message_valid_transitions_from_to X s' f tr -> message_valid_transitions_from_to X s f
        ((Build_transition_item l om s' om') :: tr).

Definition finite_valid_trace_init_to_alt
  `(X : VLSM message) (s f : state X) (tr : list (transition_item X)) :=
  message_valid_transitions_from_to X s f tr /\ initial_state_prop X s.

Definition constrained_state_prop `(X : VLSM message) :=
  valid_state_prop (pre_loaded_with_all_messages_vlsm X).

Definition constrained_message_prop `(X : VLSM message) :=
  can_emit (pre_loaded_with_all_messages_vlsm X).

(**
  Equivalence proof between [finite_constrained_trace_init_to] and
  [finite_constrained_trace_init_to_alt].
*)

Lemma constrained_transitions_init_to_right_impl
  `(X : VLSM message) (s f : state X) (tr : list (transition_item X)) :
  finite_constrained_trace_init_to X s f tr -> finite_constrained_trace_init_to_alt X s f tr.
Proof.
  intros [Htr Hinit].
  constructor; [| done]; clear Hinit.
  induction Htr.
  - by apply (ct_empty X).
  - by apply (ct_extend X); [apply Ht..|].
Qed.

Lemma constrained_transitions_init_to_left_impl
  `(X : VLSM message) (s f : state X) (tr : list (transition_item X)) :
  finite_constrained_trace_init_to_alt X s f tr -> finite_constrained_trace_init_to X s f tr.
Proof.
  intros [Htr Hs].
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

Lemma constrained_transitions_init_to_equiv
  `(X : VLSM message) (s f : state X) (tr : list (transition_item X)) :
  finite_constrained_trace_init_to X s f tr <-> finite_constrained_trace_init_to_alt X s f tr.
Proof.
  split.
  - by apply constrained_transitions_init_to_right_impl.
  - by apply constrained_transitions_init_to_left_impl.
Qed.

(**
  Equivalence proof between [finite_valid_trace_init_to] and
  [finite_valid_trace_init_to_alt].
*)

Lemma valid_transitions_init_to_right_impl
  `(X : VLSM message) (s f : state X) (tr : list (transition_item X)) :
  finite_valid_trace_init_to X s f tr -> finite_valid_trace_init_to_alt X s f tr.
Proof.
  intros [Htr Hinit].
  constructor; [| done]; clear Hinit.
  induction Htr.
  - by constructor.
  - by constructor; [apply Ht.. |].
Qed.

Lemma valid_transitions_init_to_left_impl
  `(X : VLSM message) (s f : state X) (tr : list (transition_item X)) :
  finite_valid_trace_init_to_alt X s f tr -> finite_valid_trace_init_to X s f tr.
Proof.
  intros [Htr Hs].
  split; [| done].
  apply (initial_state_is_valid X) in Hs.
  revert s Hs Htr.
  induction tr; intros; inversion Htr; subst.
  - by apply (finite_valid_trace_from_to_empty X).
  - apply (finite_valid_trace_from_to_extend X); [| done].
    apply IHtr; [| done].
    apply valid_state_prop_iff; right.
    by exists l, (s, om), om'.
Qed.

Lemma valid_transitions_init_to_equiv
  `(X : VLSM message) (s f : state X) (tr : list (transition_item X)) :
  finite_valid_trace_init_to X s f tr <-> finite_valid_trace_init_to_alt X s f tr.
Proof.
  split.
  - by apply valid_transitions_init_to_right_impl.
  - by apply valid_transitions_init_to_left_impl.
Qed.
