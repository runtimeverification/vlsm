From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From VLSM.Core Require Import VLSM VLSMProjections Composition (* Equivocation MessageDependencies*).

(** * VLSM Projection Validators

In the sequel we fix VLSMs <<X>> and <<Y>> and some <<label_project>>
and <state_project>> [VLSM_projection] mappings from <<X>> to <<Y>>.

The Transition Input Validation property validates an input corresponding to
a projection by ensuring that that input can be "lifted" to the original vlsm.
*)

Section sec_input_validation_definitions.

Context
  `{X : VLSM message}
  {TY : VLSMType message}
  .

#[local] Notation labelTY := (@label _ TY).
#[local] Notation stateTY := (@state _ TY).

Context
  (label_project : vlabel X -> option labelTY)
  (state_project : vstate X -> stateTY)
  .

Record InputValidation
  (lY : labelTY)
  (sY : stateTY)
  (om : option message)
  (lX : vlabel X)
  (sX : vstate X)
  : Prop :=
{
  tiv_label_project : label_project lX = Some lY;
  tiv_state_project : state_project sX = sY;
  lifted_transition_input_valid : input_valid X lX (sX, om)
}.

Record TransitionValidation
  (lY : labelTY)
  (sY : stateTY)
  (om : option message)
  (lX : vlabel X)
  (sX : vstate X)
  (sX' : vstate X)
  (om' : option message)
  : Prop :=
{
  tv_tiv :> InputValidation lY sY om lX sX;
  tv_transition : vtransition X lX (sX, om) = (sX', om');
  tv_tiv_transition : input_valid_transition X lX (sX, om) (sX', om') :=
    conj (lifted_transition_input_valid lY sY om lX sX tv_tiv)
      tv_transition
}.

End sec_input_validation_definitions.

Section projection_validator.

Context
  `{X : VLSM message}
  (Y : VLSM message)
  (label_project : vlabel X -> option (vlabel Y))
  (state_project : vstate X -> vstate Y)
  (PreY := pre_loaded_with_all_messages_vlsm Y)
  .

(**
We say that <<Y>> is a validator <<X>> w.r.t. the projection determined
by <<label_project>> and <<state_project>> if [input_valid]ity in the
component (for reachable states) implies [TransitionInputValidation].
*)
Definition projection_validator_prop :=
  forall li si omi,
    input_valid PreY li (si,omi) ->
    exists lX sX, InputValidation label_project state_project li si omi lX sX.

(**
We say that <<Y>> is a [transition_validator] if any [valid]
transition (from a reachable state) in <<Y>> can be "lifted" to
an [input_valid_transition] in <<X>>.
*)
Definition transition_validator :=
  forall lY sY omi, input_valid PreY lY (sY, omi) ->
  exists lX sX sX' om',
    TransitionValidation label_project state_project lY sY omi lX sX sX' om'.

(** A message validator can check within a component whether the message
is valid for the composition.
*)
Definition message_validator_prop :=
  forall li si im,
    input_valid PreY li (si, Some im) ->
    valid_message_prop X im.

(** The [projection_validator_prop]erty is stronger. *)
Lemma projection_validator_is_message_validator
  : projection_validator_prop -> message_validator_prop.
Proof.
  intros Hvalidator li si im Hvi.
  by apply Hvalidator in Hvi as (_ & _ & [_ _ (_ & ? & _)]).
Qed.

Lemma projection_validator_messages_transitions
  : projection_validator_prop -> transition_validator.
Proof.
  intros Hvalidator li si omi Hpvi.
  apply Hvalidator in Hpvi as (l & s & Hiv).
  destruct (vtransition X l (s, omi)) as (s', omo) eqn:Ht.
  eexists l, s, s', omo; split with (tv_tiv := Hiv) (tv_transition := Ht).
Qed.

Lemma transition_validator_messages
  : transition_validator -> projection_validator_prop.
Proof.
  intros Hvalidator li si omi Hpvi.
  apply Hvalidator in Hpvi as (lX & sX & _ & _ & [? _ _]).
  by eexists _, _.
Qed.

End projection_validator.

(** ** Induced VLSM validators

Given an existing [VLSM], a target [VLSM_type], a <<state_project>>ion map, and
a partial <<label_project>>ion map, and some corresponding reverse maps
<<state_lift>> and <<label_lift>> we can build a new VLSM over the target type,
induced by the source VLSM, its missing components being defined based on the
source components.

If additionally some consistency ([weak_projection_transition_consistency_None]
and [weak_projection_transition_consistency_Some]) properties are satisfied,
then the induced VLSM is a [VLSM_projection] of the source one.
*)
Section sec_projection_induced_validator.

Section sec_projection_induced_validator_pre_definitions.

Context
  {message : Type}
  {TX TY : VLSMType message}
  .

#[local] Notation labelTX := (@label _ TX).
#[local] Notation stateTX := (@state _ TX).
#[local] Notation labelTY := (@label _ TY).
#[local] Notation stateTY := (@state _ TY).

Context
  (label_project : labelTX -> option labelTY)
  (state_project : stateTX -> stateTY)
  (label_lift : labelTY -> labelTX)
  (state_lift : stateTY -> stateTX)
  .

(** <<label_project>> is a left-inverse of <<label_lift>> *)
Definition induced_validator_label_lift_prop : Prop :=
  forall lY, label_project (label_lift lY) = Some lY.

(** <<state_project>> is a left-inverse of <<state_lift>> *)
Definition induced_validator_state_lift_prop : Prop :=
  forall sY, state_project (state_lift sY) = sY.

End sec_projection_induced_validator_pre_definitions.

Context
  {message : Type}
  (X : VLSM message)
  (TY : VLSMType message)
  .

#[local] Notation labelTY := (@label _ TY).
#[local] Notation stateTY := (@state _ TY).
#[local] Notation transition_itemTY := (@transition_item _ TY).

Context
  (label_project : vlabel X -> option labelTY)
  (state_project : vstate X -> stateTY)
  (trace_project := pre_VLSM_projection_finite_trace_project _ _ label_project state_project)
  (label_lift : labelTY -> vlabel X)
  (state_lift : stateTY -> vstate X)
  .

Definition projection_induced_initial_state_prop (sY : stateTY) : Prop :=
  exists sX, state_project sX = sY /\ vinitial_state_prop X sX.

Instance projection_induced_initial_state_inh : Inhabited (sig projection_induced_initial_state_prop)
  := populate (exist _ (state_project (` (vs0 X))) (ex_intro _ _ (conj (eq_refl _) (proj2_sig _)))).

Definition projection_induced_initial_message_prop : message -> Prop := const False.

Definition projection_induced_transition
  (lY : labelTY)
  (somY : stateTY * option message)
  : stateTY * option message :=
  let (sY, om) := somY in
  let (s'X, om') := vtransition X (label_lift lY) (state_lift sY, om) in
  (state_project s'X, om').

Definition projection_induced_valid
  (lY : labelTY)
  (somY : stateTY * option message)
  : Prop :=
  exists lX sX, InputValidation label_project state_project lY somY.1 somY.2 lX sX.

Definition projection_induced_validator_machine : VLSMMachine TY :=
  {| initial_message_prop := projection_induced_initial_message_prop
   ; initial_state_prop := projection_induced_initial_state_prop
   ; transition := projection_induced_transition
   ;  valid := projection_induced_valid
  |}.

Definition projection_induced_validator : VLSM message :=
  mk_vlsm projection_induced_validator_machine.

Definition pre_projection_induced_validator : VLSM message :=
  pre_loaded_with_all_messages_vlsm projection_induced_validator.

Lemma projection_induced_validator_is_validating :
  projection_validator_prop pre_projection_induced_validator label_project state_project.
Proof. by intros li si omi (_ & _ & Hv). Qed.

(** When we have a [VLSM_projection] to the [projection_induced_validator],
[valid]ity is [input_valid]ity.
*)
Lemma induced_validator_valid_is_input_valid
  (Hproj : VLSM_projection X pre_projection_induced_validator label_project state_project)
  l s om
  : vvalid projection_induced_validator l (s, om) -> input_valid pre_projection_induced_validator l (s,om).
Proof.
  intro Hv.
  destruct (id Hv) as (lX & sX & [HlX  HsX (Hps & Hopm & _)]); cbn in HsX; subst.
  repeat split; [| | done].
  - by eapply VLSM_projection_valid_state.
  - destruct om as [m |]; [| apply option_valid_message_None].
    by apply option_initial_message_is_valid.
Qed.

Section sec_projection_induced_validator_as_projection.

(** Transitions through states and labels with the same projections using the
same message should lead to the same output message and states with the same
projections.
*)
Definition induced_validator_transition_consistency_Some : Prop :=
  forall lX1 lX2 lY, label_project lX1 = Some lY -> label_project lX2 = Some lY ->
  forall sX1 sX2, state_project sX1 = state_project sX2 ->
  forall iom sX1' oom1, vtransition X lX1 (sX1, iom) = (sX1', oom1) ->
  forall sX2' oom2, vtransition X lX2 (sX2, iom) = (sX2', oom2) ->
  state_project sX1' = state_project sX2' /\ oom1 = oom2.

(** A weaker version of [induced_validator_transition_consistency_Some].
Only used locally.
*)
#[local] Definition weak_projection_transition_consistency_Some
  : Prop :=
  forall lX lY, label_project lX = Some lY ->
  forall s1 om s1' om1', input_valid_transition X lX (s1, om) (s1', om1') ->
  forall s2' om2', vtransition X (label_lift lY) (state_lift (state_project s1), om) = (s2', om2') ->
  state_project s1' = state_project s2' /\ om1' = om2'.

#[local] Lemma basic_weak_projection_transition_consistency_Some
  : induced_validator_label_lift_prop label_project label_lift ->
    induced_validator_state_lift_prop state_project state_lift ->
    induced_validator_transition_consistency_Some ->
    weak_projection_transition_consistency_Some.
Proof.
  intros Hlbl Hst Htrans lX lY HlX_pr sX1 iom sX1' oom1 [_ Ht1] sX2' oom2 Ht2.
  eapply Htrans; [done | auto | symmetry; eauto | done | done].
Qed.

Context
  (Hlabel_lift : induced_validator_label_lift_prop label_project label_lift)
  (Hstate_lift : induced_validator_state_lift_prop state_project state_lift)
  (Htransition_consistency : induced_validator_transition_consistency_Some)
  (Htransition_Some  : weak_projection_transition_consistency_Some
    := basic_weak_projection_transition_consistency_Some Hlabel_lift Hstate_lift Htransition_consistency)
  .

(** Under transition-consistency assumptions, valid messages of the
[projection_induced_validator] coincide with those of the source [VLSM].
*)
Lemma projection_induced_valid_message_char
  : forall om, option_valid_message_prop projection_induced_validator om ->
    option_valid_message_prop X om.
Proof.
  intros om [s Hsom].
  induction Hsom.
  - by destruct om as [m |]; [done |]; apply option_valid_message_None.
  - destruct Hv as (lX & sX & [HlX_pr [=] (HsX & HomX & Hv)]).
    cbn in Ht; destruct (vtransition _ _ _) as [_s'X __om'] eqn: H_tX
    ; inversion Ht; subst; clear Ht.
    destruct (vtransition X lX (sX, om)) as [s'X _om'] eqn: HtX.
    assert (HivtX : input_valid_transition X lX (sX, om) (s'X, _om'))
        by (split_and!; done).
    replace om' with _om' by (eapply Htransition_Some; done).
    by eapply input_valid_transition_out.
Qed.

Context
  (Htransition_None : weak_projection_transition_consistency_None _ _ label_project state_project)
  (Htype : VLSM_projection_type X TY label_project state_project :=
    basic_VLSM_projection_type X TY label_project state_project Htransition_None)
  .

Lemma projection_induced_validator_is_projection
  : VLSM_projection X pre_projection_induced_validator label_project state_project.
Proof.
  apply basic_VLSM_projection; intro; intros.
  - by exists lX, s.
  - specialize (Htransition_Some _ _ H _ _ _ _ H0); cbn.
    destruct (vtransition _ _ _) as [s2' om2'].
    by destruct (Htransition_Some _ _ eq_refl) as [-> ->].
  - by eapply Htransition_None.
  - by exists s.
  - by destruct Hv as [_ [Hm _]]; apply initial_message_is_valid.
Qed.

Section projection_induced_friendliness.

Context
  (Hproj := projection_induced_validator_is_projection)
  .

Lemma induced_validator_transition_item_lift
  (item : transition_itemTY)
  : pre_VLSM_projection_transition_item_project _ _ label_project state_project
    (pre_VLSM_full_projection_transition_item_project _ _ label_lift state_lift item)
    = Some item.
Proof.
  destruct item.
  unfold pre_VLSM_full_projection_transition_item_project,
         pre_VLSM_projection_transition_item_project.
  by cbn; rewrite Hlabel_lift, Hstate_lift.
Qed.

Lemma induced_validator_trace_lift
  (tr : list transition_itemTY)
  : pre_VLSM_projection_finite_trace_project _ _ label_project state_project
    (pre_VLSM_full_projection_finite_trace_project _ _ label_lift state_lift tr)
    = tr.
Proof.
  induction tr; cbn; [done |].
  by rewrite induced_validator_transition_item_lift; f_equal.
Qed.

(** If there is a way to "lift" valid traces of the [projection_induced_validator]
to the original [VLSM], then the induced [VLSM_projection] is friendly.
*)
Lemma basic_projection_induces_friendliness
  : VLSM_full_projection pre_projection_induced_validator X label_lift state_lift ->
    projection_friendly_prop Hproj.
Proof.
  intros Hfull_proj isY trY HtrY.
  exists (state_lift isY), (VLSM_full_projection_finite_trace_project Hfull_proj trY).
  split_and!.
  - by apply (VLSM_full_projection_finite_valid_trace Hfull_proj).
  - done.
  - by apply induced_validator_trace_lift.
Qed.

End projection_induced_friendliness.

End sec_projection_induced_validator_as_projection.

End sec_projection_induced_validator.

Section sec_projection_induced_validator_incl.

Context
  {message : Type}
  {TX : VLSMType message}
  (TY : VLSMType message)
  .

#[local] Notation labelTX := (@label _ TX).
#[local] Notation stateTX := (@state _ TX).
#[local] Notation labelTY := (@label _ TY).
#[local] Notation stateTY := (@state _ TY).

Context
  (label_project : labelTX -> option labelTY)
  (state_project : stateTX -> stateTY)
  (trace_project := pre_VLSM_projection_finite_trace_project _ _ label_project state_project)
  (label_lift : labelTY -> labelTX)
  (state_lift : stateTY -> stateTX)
  (Hlabel_lift : induced_validator_label_lift_prop label_project label_lift)
  (Hstate_lift : induced_validator_state_lift_prop state_project state_lift)
  .

(** Under [weak_projection_transition_consistency_Some] assumptions,
[VLSM_incl]usion between source [VLSM]s implies [VLSM_incl]usion between
their projections induced by the same maps.
*)
Lemma projection_induced_validator_incl
  (MX1 MX2 : VLSMMachine TX)
  (X1 := mk_vlsm MX1) (X2 := mk_vlsm MX2)
  (XY1 : VLSM message :=
    pre_projection_induced_validator X1 TY label_project state_project label_lift state_lift)
  (XY2 : VLSM message :=
    pre_projection_induced_validator X2 TY label_project state_project label_lift state_lift)
  (Htransition_consistency1 :
    induced_validator_transition_consistency_Some X1 TY label_project state_project)
  (Htransition_consistency2 :
    induced_validator_transition_consistency_Some X2 TY label_project state_project)
  : VLSM_incl X1 X2 -> VLSM_incl XY1 XY2.
Proof.
  pose (Htransition_Some1 :=
    basic_weak_projection_transition_consistency_Some
      X1 TY _ _ _ _ Hlabel_lift Hstate_lift Htransition_consistency1).
  pose (Htransition_Some2 :=
    basic_weak_projection_transition_consistency_Some
      X2 TY _ _ _ _ Hlabel_lift Hstate_lift Htransition_consistency2).
  intros Hincl.
  apply VLSM_incl_finite_traces_characterization.
  assert (His : forall s, vinitial_state_prop XY1 s -> vinitial_state_prop XY2 s).
  {
    intros is (s1 & Hs1_pr & Hs1).
    by exists s1; split; [| apply VLSM_incl_initial_state].
  }
  intros is tr Htr.
  split; [| apply His, Htr].
  induction Htr using finite_valid_trace_rev_ind
  ; [by apply (finite_valid_trace_from_empty XY2), initial_state_is_valid, His |].
  apply (finite_valid_trace_from_app_iff XY2).
  split; [apply IHHtr |].
  apply (finite_valid_trace_singleton XY2).
  destruct Hx as [(_ & _ & lX & sX & [HlX_pr HsX_pr HpvX1]) Ht].
  cbn in Ht; destruct (vtransition _ _ _) as [_s'X _oom] eqn: H_tX1.
  inversion Ht; subst; clear Ht.
  destruct (vtransition X1 lX (sX, iom)) as [s'X _oom] eqn: HtX1.
  assert (HivtX1 : input_valid_transition X1 lX (sX, iom) (s'X, _oom)) by done.
  simpl in HsX_pr, H_tX1; rewrite <- HsX_pr in H_tX1.
  apply (Htransition_Some1 _ _ HlX_pr _ _ _ _ HivtX1) in H_tX1 as [Heq_s'X_pr ->].
  apply (VLSM_incl_input_valid_transition Hincl) in HivtX1.
  repeat split.
  - by eapply finite_valid_trace_last_pstate.
  - by apply any_message_is_valid_in_preloaded.
  - by exists lX, sX; split; [| | apply HivtX1]; itauto.
  - cbn in *; rewrite <- HsX_pr.
    destruct (vtransition X2 _ _) as [_s'X2 _oom] eqn: H_tX2.
    apply (Htransition_Some2 _ _ HlX_pr _ _ _ _ HivtX1) in H_tX2 as [? ->].
    congruence.
Qed.

(** Under [weak_projection_transition_consistency_Some] assumptions,
[VLSM_eq]uality between source [VLSM]s implies [VLSM_eq]uality between
their projections induced by the same maps.
*)
Lemma projection_induced_validator_eq
  (MX1 MX2 : VLSMMachine TX)
  (X1 := mk_vlsm MX1) (X2 := mk_vlsm MX2)
  (XY1 : VLSM message :=
    pre_projection_induced_validator X1 TY label_project state_project label_lift state_lift)
  (XY2 : VLSM message :=
    pre_projection_induced_validator X2 TY label_project state_project label_lift state_lift)
  (Htransition_consistency1 :
    induced_validator_transition_consistency_Some X1 TY label_project state_project)
  (Htransition_consistency2 :
    induced_validator_transition_consistency_Some X2 TY label_project state_project)
  : VLSM_eq X1 X2 -> VLSM_eq XY1 XY2.
Proof.
  intro Heq; apply VLSM_eq_incl_iff; split.
  - by apply (projection_induced_validator_incl MX1 MX2); [..| apply VLSM_eq_proj1].
  - by apply (projection_induced_validator_incl MX2 MX1); [..| apply VLSM_eq_proj2].
Qed.

End sec_projection_induced_validator_incl.

(** ** Projection validators and Byzantine behavior

In the sequel we assume that the [projection_induced_validator_is_projection] and
that initial states of <<Y>> can be lifted to <<X>>.
*)

Section induced_validator_validators.

Context
  `{X : VLSM message}
  (Y : VLSM message)
  (label_project : vlabel X -> option (vlabel Y))
  (state_project : vstate X -> vstate Y)
  (Htransition_None : weak_projection_transition_consistency_None _ _ label_project state_project)
  (label_lift : vlabel Y -> vlabel X)
  (state_lift : vstate Y -> vstate X)
  (Xi := pre_projection_induced_validator X (type Y) label_project state_project label_lift state_lift)
  (Hlabel_lift : induced_validator_label_lift_prop label_project label_lift)
  (Hstate_lift : induced_validator_state_lift_prop state_project state_lift)
  (Hinitial_lift : strong_projection_initial_state_preservation Y X state_lift)
  (Htransition_consistency :
    induced_validator_transition_consistency_Some _ _ label_project state_project)
  (Htransition_Some
    : weak_projection_transition_consistency_Some
        _ _ label_project state_project label_lift state_lift
    := basic_weak_projection_transition_consistency_Some
        _ _ _ _ _ _ Hlabel_lift Hstate_lift Htransition_consistency)
  (Hproji :=
    projection_induced_validator_is_projection
      _ _ _ _ _ _ Hlabel_lift Hstate_lift Htransition_consistency Htransition_None)
  (PreY := pre_loaded_with_all_messages_vlsm Y)
  (Hproj : VLSM_projection X PreY label_project state_project)
  .

(** If there is a [VLSM_projection] from <<X>> to <<PreY>> and the
[projection_induced_validator_is_projection], then a [transition] [valid] for the
[projection_induced_validator] has the same output as the transition on <<Y>>.
*)
Lemma projection_induced_valid_transition_eq
  : forall l s om, vvalid Xi l (s, om) ->
    vtransition Xi l (s, om) = vtransition Y l (s, om).
Proof.
  intros l s im (lX & sX & [Hlx HsX Hv]); cbn in HsX; subst s.
  replace (vtransition Y _ _) with
    (state_project (vtransition X lX (sX, im)).1, (vtransition X lX (sX, im)).2).
  - eapply (VLSM_projection_input_valid_transition Hproji); [done |].
    by erewrite injective_projections.
  - symmetry.
    eapply (VLSM_projection_input_valid_transition Hproj); [done |].
    by erewrite injective_projections.
Qed.

Lemma induced_validator_incl_preloaded_with_all_messages
  : VLSM_incl Xi PreY.
Proof.
  apply basic_VLSM_incl.
  - by intros is (s & <- & Hs); apply (VLSM_projection_initial_state Hproj).
  - by intros l s m Hv HsY HmX; apply initial_message_is_valid.
  - by intros l s om (_ & _ & lX & sX & [Hlx Heq Hv]) _ _; cbn in Heq; subst;
      simpl; eapply VLSM_projection_input_valid.
  - intros l s im s' om [(_ & _ & HvXi) HtXi]; cbn.
    by setoid_rewrite <- HtXi; rewrite <- projection_induced_valid_transition_eq.
Qed.

(** An alternative formulation of the [projection_validator_prop]erty with a
seemingly stronger hypothesis, states that <<Y>> is a validator for <<X>> if
for any <<li>>, <<si>>, <<iom>> such that <<li valid (si, iom)>> in <<Y>>
and <<si>> is a valid state in the induced projection <<Xi>>,
implies that <<li valid (si, om)>> in the induced projection <<Xi>>
(i.e., [projection_induced_valid]ity).
*)
Definition projection_validator_prop_alt :=
  forall li si iom,
    vvalid Y li (si, iom) ->
    valid_state_prop Xi si ->
    vvalid Xi li (si, iom).

(** Under validator assumptions, all reachable states for component <<Y>> are
valid states in the induced projection <<Xi>>.
*)
Lemma validator_alt_free_states_are_projection_states
  : projection_validator_prop_alt ->
    forall s, valid_state_prop PreY s -> valid_state_prop Xi s.
Proof.
  intros Hvalidator sY Hs.
  induction Hs using valid_state_prop_ind.
  - apply initial_state_is_valid.
    exists (state_lift s). auto.
  - destruct Ht as [[_ [_ Hvalid]] Htrans].
    destruct (Hvalidator _ _ _ Hvalid IHHs) as (lX & sX & [HlX HsX HvX]).
    replace s' with (state_project (vtransition X lX (sX, om)).1).
    + eapply input_valid_transition_destination,
        (VLSM_projection_input_valid_transition Hproji)
      ; [|split]; [done | done |].
      by apply injective_projections.
    + assert (HivtX : input_valid_transition X lX (sX, om) (vtransition X lX (sX, om)))
        by firstorder.
      destruct (vtransition _ _ _) as (sX', _om').
      eapply (VLSM_projection_input_valid_transition Hproj) in HivtX as [_ Hs']; [| done].
      rewrite HsX in Hs'; cbv in Htrans, Hs'; rewrite Htrans in Hs'.
      by inversion Hs'.
Qed.

(** Below we show that the two definitions above are actually equivalent. *)
Lemma projection_validator_prop_alt_iff
  : projection_validator_prop_alt <-> projection_validator_prop Y label_project state_project.
Proof.
  split; intros Hvalidator l si om Hvalid.
  - apply Hvalidator; [apply Hvalid |].
    apply validator_alt_free_states_are_projection_states; [done.. | apply Hvalid].
  - intro HXisi; cbn.
    apply Hvalidator.
    repeat split; [| apply any_message_is_valid_in_preloaded | done].
    by revert HXisi; apply VLSM_incl_valid_state,
      induced_validator_incl_preloaded_with_all_messages.
Qed.

Lemma validator_free_states_are_projection_states
  : projection_validator_prop Y label_project state_project ->
    forall s, valid_state_prop PreY s -> valid_state_prop Xi s.
Proof.
  rewrite <- projection_validator_prop_alt_iff by done.
  by apply validator_alt_free_states_are_projection_states.
Qed.

Section pre_loaded_with_all_messages_validator_proj.

Context
  (Hvalidator : projection_validator_prop Y label_project state_project)
  .

(**
We can show that <<PreY>> is included in <<Xi>> by applying the meta-lemma
[VLSM_incl_finite_traces_characterization], and by induction on the length
of a trace. The [projection_validator_prop]erty is used to translate
[input_valid]ity for the PreY machine into the [pre_projection_induced_validator].
*)
Lemma pre_loaded_with_all_messages_validator_proj_incl
  : VLSM_incl PreY Xi.
Proof.
  (* reduce inclusion to inclusion of finite traces. *)
  apply VLSM_incl_finite_traces_characterization.
  intros sY trY HtrY.
  split; cycle 1.
  - exists (state_lift sY).
    split; [apply Hstate_lift|].
    apply Hinitial_lift, HtrY.
  - induction HtrY using finite_valid_trace_rev_ind.
    + apply (finite_valid_trace_from_empty Xi), initial_state_is_valid.
      exists (state_lift si).
      auto.
    + apply (extend_right_finite_trace_from Xi); [done | split].
      * apply induced_validator_valid_is_input_valid; cbn; [done |].
        apply Hvalidator, Hx.
      * replace (sf, _) with (vtransition Y l (finite_trace_last si tr, iom))
          by apply Hx.
        apply projection_induced_valid_transition_eq; cbn.
        apply Hvalidator, Hx.
Qed.

(**
Given that any projection is included in the [pre_loaded_with_all_messages_vlsm]
of its component (Lemma [proj_pre_loaded_with_all_messages_incl]), we conclude
that <<PreY>> and <<Xi>> are trace-equal.  This means that all the
byzantine behavior of a component which is a validator
is exhibited by its corresponding projection.
*)
Lemma pre_loaded_with_all_messages_validator_proj_eq
  : VLSM_eq PreY Xi.
Proof.
  apply VLSM_eq_incl_iff; split.
  - apply pre_loaded_with_all_messages_validator_proj_incl.
  - apply induced_validator_incl_preloaded_with_all_messages.
Qed.

End pre_loaded_with_all_messages_validator_proj.

End induced_validator_validators.

(** ** Validator properties for the [component_projection].

In this section we specialize the validator-related results to the
components of a composition.
*)

Section component_projection_validator.

Context
  {message : Type}
  `{EqDecision index}
  (IM : index -> VLSM message)
  (constraint : composite_label IM -> composite_state IM * option message -> Prop)
  (X := composite_vlsm IM constraint)
  (i : index)
  (PreXi := pre_loaded_with_all_messages_vlsm (IM i))
  .

Definition composite_project_label (l : composite_label IM)
  : option (vlabel (IM i)) :=
  match decide (i = (projT1 l)) with
  | left e => Some (eq_rect_r _ (projT2 l) e)
  | _ => None
  end.

(**
The specialization of the more abstract [projection_induced_validator] to the
projection from a composition to a component.
*)
Definition composite_vlsm_induced_validator : VLSM message :=
  projection_induced_validator X (type (IM i))
    composite_project_label (fun s => s i)
    (lift_to_composite_label IM i) (lift_to_composite_state' IM i).

Definition pre_composite_vlsm_induced_validator : VLSM message :=
  pre_projection_induced_validator X (type (IM i))
    composite_project_label (fun s => s i)
    (lift_to_composite_label IM i) (lift_to_composite_state' IM i).

Lemma composite_project_label_eq lj
  : composite_project_label (existT i lj) = Some lj.
Proof.
  unfold composite_project_label; cbn.
  by rewrite (decide_True_pi eq_refl).
Qed.

Lemma component_label_projection_lift
  : induced_validator_label_lift_prop composite_project_label
    (lift_to_composite_label IM i).
Proof. by intros lj; apply composite_project_label_eq. Qed.

Lemma component_state_projection_lift
  : induced_validator_state_lift_prop (fun s : composite_state IM => s i)
    (lift_to_composite_state' IM i).
Proof. by intros sj; apply state_update_eq. Qed.

Lemma component_transition_projection_None
  : weak_projection_transition_consistency_None X (type (IM i))
    composite_project_label (λ s : vstate X, s i).
Proof.
  intros [j lj] HlX sX iom s'X oom [_ Ht]; cbn in Ht.
  destruct (vtransition _ _ _) as (si', om'); inversion Ht; subst.
  destruct (decide (i = j)); subst; state_update_simpl; [| done].
  unfold composite_project_label in HlX; cbn in HlX.
  by case_decide.
Qed.

Lemma component_transition_projection_Some
  : induced_validator_transition_consistency_Some X (type (IM i))
    composite_project_label (λ s : vstate X, s i).
Proof.
  intros [j1 lj1] [j2 lj2] lj; unfold composite_project_label; cbn.
  case_decide as Hj1; [| done]; subst j1.
  intros Hlj1; cbv in Hlj1;  apply Some_inj in Hlj1; subst lj1.
  case_decide as Hj2; [| done]; subst j2.
  intros Hlj2; cbv in Hlj2; apply Some_inj in Hlj2; subst lj2.
  intros sX1 sX2 <- iom.
  destruct (vtransition _ _ _) as [si' om'].
  intros sX1' oom1 Ht1; inversion Ht1; subst; clear Ht1.
  intros sX2' oom2 Ht2; inversion Ht2; subst; clear Ht2.
  by state_update_simpl.
Qed.

(** The [projection_induced_validator] by the [composite_project_label] and the
projection of the state to the component is indeed a [VLSM_projection].
*)
Lemma composite_projection_induced_validator_is_projection :
  VLSM_projection X pre_composite_vlsm_induced_validator
    composite_project_label (fun s => s i).
Proof.
  apply projection_induced_validator_is_projection.
  - apply component_label_projection_lift.
  - apply component_state_projection_lift.
  - apply component_transition_projection_Some.
  - apply component_transition_projection_None.
Qed.

End component_projection_validator.

Section sec_component_projection_validator_alt.
(**
** Direct definition of induced validator from composition to component

In this section we provide a definition of the induced validator from a
composition to a component obtained by strengthening the component instead of
deriving its elements via the projection [composite_vlsm_induced_projection_validator].

We then show this VLSM and some of its pre-loaded variants are [VLSM_eq]ual
(trace-equivalent) to the corresponding variants of the
[composite_vlsm_induced_validator].
*)

Context
  {message : Type}
  `{EqDecision index}
  (IM : index -> VLSM message)
  (constraint : composite_label IM -> composite_state IM * option message -> Prop)
  (X := composite_vlsm IM constraint)
  (i : index)
  (PreXi := pre_loaded_with_all_messages_vlsm (IM i))
  .

(**
The [composite_vlsm_induced_projection_valid]ity is defined as the projection of
the [input_valid]ity of <<X>>:
*)
Definition composite_vlsm_induced_projection_valid
  (li : vlabel (IM i))
  (siomi : vstate (IM i) * option message)
  :=
  let (si, omi) := siomi in
  exists s : vstate X,
    s i = si /\ input_valid X (existT i li) (s, omi).

(**
Since the [composite_vlsm_induced_projection_valid]ity is derived from
[input_valid]ity, which in turn depends on [valid]ity in the component, it is
easy to see that it implies [valid]ity in the component.
*)
Lemma projection_valid_implies_valid
  (li : vlabel (IM i))
  (siomi : vstate (IM i) * option message)
  (Hcomposite : composite_vlsm_induced_projection_valid li siomi)
  : vvalid (IM i) li siomi.
Proof. by destruct siomi, Hcomposite as (s & <- & _ & _ & []). Qed.

(**
We define the induced projection validator of <<X>> to index <<i>> as the [VLSM]
obtained by changing the validity predicate of <<IM i>> to
[composite_vlsm_induced_projection_valid].
*)
Definition composite_vlsm_induced_projection_validator_machine
  : VLSMMachine (type (IM i)) :=
{|
  initial_state_prop := vinitial_state_prop (IM i);
  initial_message_prop := vinitial_message_prop (IM i);
  s0 := populate (vs0 (IM i));
  transition :=  vtransition (IM i);
  valid := composite_vlsm_induced_projection_valid;
|}.

Definition composite_vlsm_induced_projection_validator : VLSM message :=
  mk_vlsm composite_vlsm_induced_projection_validator_machine.

Definition pre_composite_vlsm_induced_projection_validator : VLSM message :=
  pre_loaded_with_all_messages_vlsm composite_vlsm_induced_projection_validator.

Lemma preloaded_composite_vlsm_induced_projection_validator_iff
  (P : message -> Prop)
  (Hinits : forall m,  vinitial_message_prop (IM i) m -> P m)
  : VLSM_eq
      (pre_loaded_vlsm composite_vlsm_induced_projection_validator P)
      (pre_loaded_vlsm (composite_vlsm_induced_validator IM constraint i) P).
Proof.
  apply VLSM_eq_incl_iff; split; cbn; apply basic_VLSM_strong_incl.
  - intros s Hs; cbn in *; red.
    exists (lift_to_composite_state' IM i s).
    split; [by state_update_simpl |].
    by apply (composite_initial_state_prop_lift IM).
  - by intros m [Him | Hpm]; right; [apply Hinits |].
  - intros l s iom [sX [<- Hv]].
    exists (existT i l), sX.
    by split; [apply composite_project_label_eq |..].
  - intros l s iom s' oom.
    cbn; unfold lift_to_composite_state' at 1.
    state_update_simpl.
    intros Ht; setoid_rewrite Ht.
    by state_update_simpl.
  - by intros s [sX [<- HsX]]; cbn.
  - by intros m [| Hm]; [| right].
  - intros l s iom ([j li] & sX & [HlX [=] Hv]).
    exists sX; split; [done |].
    unfold composite_project_label in HlX; cbn in *.
    case_decide; [| congruence].
    by inversion HlX; subst.
  - intros l s iom s' oom Ht; cbn in *.
    unfold lift_to_composite_state' in Ht;
      state_update_simpl;
      destruct (vtransition _ _ _) as (si', om').
    by state_update_simpl.
Qed.

Lemma pre_composite_vlsm_induced_projection_validator_iff
  : VLSM_eq
      pre_composite_vlsm_induced_projection_validator
      (pre_composite_vlsm_induced_validator IM constraint i).
Proof.
  eapply VLSM_eq_trans;
    [apply pre_loaded_with_all_messages_vlsm_is_pre_loaded_with_True |].
  eapply VLSM_eq_trans;
    [by apply preloaded_composite_vlsm_induced_projection_validator_iff |].
  apply VLSM_eq_sym,
    (pre_loaded_with_all_messages_vlsm_is_pre_loaded_with_True
      (composite_vlsm_induced_validator IM constraint i)).
Qed.

Lemma component_projection :
  VLSM_projection X pre_composite_vlsm_induced_projection_validator
    (composite_project_label IM i) (fun s => s i).
Proof.
  eapply VLSM_projection_eq_trans.
  - apply composite_projection_induced_validator_is_projection.
  - apply VLSM_eq_sym, pre_composite_vlsm_induced_projection_validator_iff.
Qed.

Lemma composite_vlsm_induced_projection_validator_iff
  (Hno_inits : forall m, ~vinitial_message_prop (IM i) m)
  : VLSM_eq
      composite_vlsm_induced_projection_validator
      (composite_vlsm_induced_validator IM constraint i).
Proof.
  eapply VLSM_eq_trans;
    [apply (vlsm_is_pre_loaded_with_False composite_vlsm_induced_projection_validator)|].
  eapply VLSM_eq_trans;
    [by apply preloaded_composite_vlsm_induced_projection_validator_iff |].
  apply VLSM_eq_sym,
    (vlsm_is_pre_loaded_with_False
      (composite_vlsm_induced_validator IM constraint i)).
Qed.

Definition valid_preloaded_composite_vlsm_induced_projection_validator
  : VLSM message :=
  pre_loaded_vlsm composite_vlsm_induced_projection_validator (valid_message_prop X).

Lemma valid_preloaded_composite_vlsm_induced_projection_validator_iff
  : VLSM_eq
      valid_preloaded_composite_vlsm_induced_projection_validator
      pre_composite_vlsm_induced_projection_validator.
Proof.
  apply VLSM_eq_sym, pre_loaded_with_all_messages_eq_validating_pre_loaded_vlsm.
  intros _ _ m (_ & _ & _ & _ & _ & Hm & _).
  by apply initial_message_is_valid; right.
Qed.

End sec_component_projection_validator_alt.

(** ** VLSM self-validation *)

Section self_validator_vlsm.

Context
  {message : Type}
  (X : VLSM message)
  .

(**
Let us fix a (regular) VLSM <<X>>. <<X>> is a self-validator if for any
arguments satisfying [valid] where the state is reachable in the
[pre_loaded_with_all_messages_vlsm], the arguments are also
a [valid_state] and [valid_message] for the original VLSM.
*)

Definition self_validator_vlsm_prop :=
  forall (l : label) (s : state) (om : option message),
    input_valid (pre_loaded_with_all_messages_vlsm X) l (s, om) ->
    input_valid X l (s, om).

(**
In the sequel we will show that a VLSM with the [self_validator_vlsm_prop]erty
is trace-equal to its associated [pre_loaded_with_all_messages_vlsm], basically
meaning (due to Lemma [byzantine_pre_loaded_with_all_messages]) that all traces
with the [byzantine_trace_prop]erty associated to self-validator VLSMs are also
[valid_trace]s for that VLSM, meaning that the VLSM cannot exhibit
byzantine behavior.
*)

Context
  (Hvalidator : self_validator_vlsm_prop)
  (PreX := pre_loaded_with_all_messages_vlsm X)
  .

(**
Let <<PreX>> be the [pre_loaded_with_all_messages_vlsm] associated to X.
From Lemma [vlsm_incl_pre_loaded_with_all_messages_vlsm] we know that <<X>> is
included in <<PreX>>.

To prove the converse we use the [self_validator_vlsm_prop]erty to
verify the conditions of meta-lemma [VLSM_incl_finite_traces_characterization].
*)

Lemma pre_loaded_with_all_messages_self_validator_vlsm_incl
  : VLSM_incl PreX X.
Proof.
  unfold self_validator_vlsm_prop  in Hvalidator.
  destruct X as (T & M). simpl in *.
  (* redcuction to inclusion of finite traces. *)
  apply VLSM_incl_finite_traces_characterization.
  intros s tr [Htr Hs].
  split; [| done].
  (* reverse induction on the length of a trace. *)
  induction tr using rev_ind.
  - by constructor; apply initial_state_is_valid.
  - apply finite_valid_trace_from_app_iff in Htr as [Htr Hx].
    apply (finite_valid_trace_from_app_iff (mk_vlsm M)).
    split; [by apply IHtr |].
    apply (first_transition_valid (mk_vlsm M)).
    apply first_transition_valid in Hx as [Hvx Htx].
    split; [| done].
    (* using the [self_validator_vlsm_prop]erty. *)
    revert Hvx; apply Hvalidator.
Qed.

(**
We conclude that <<X>> and <<PreX>> are trace-equal.
*)

Lemma pre_loaded_with_all_messages_self_validator_vlsm_eq
  : VLSM_eq PreX X.
Proof.
  split.
  - apply pre_loaded_with_all_messages_self_validator_vlsm_incl.
  - pose (vlsm_incl_pre_loaded_with_all_messages_vlsm X) as Hincl.
    destruct X as (T, M).
    apply Hincl.
Qed.

End self_validator_vlsm.
