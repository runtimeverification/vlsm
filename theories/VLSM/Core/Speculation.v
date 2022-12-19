From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From VLSM.Lib Require Import Preamble.
From VLSM.Core Require Import VLSM Plans.

(** * Speculative VLSMs

  This module introduces the speculative VLSM construction. It models the
  speculative execution of transitions from the underlying VLSM which can then
  be committed or rolled back.
*)

Section sec_speculative.

Context
  {message : Type}
  (X : VLSM message).

Inductive SpeculativeLabel : Type :=
| Execute
| Rollback
| Commit
| Speculate (plan : list (vplan_item X)).

Inductive SpeculativeState : Type :=
| Actual (s : vstate X)
| Speculative
    (start current : vstate X) (plan : list (vplan_item X)) (outputs : list (option message)).

Definition speculative_initial_state_prop (s : SpeculativeState) : Prop :=
match s with
| Actual s' => vinitial_state_prop X s'
| _         => False
end.

#[export] Program Instance speculative_s0 :
  Inhabited {s : SpeculativeState | speculative_initial_state_prop s} :=
    populate (exist _ (Actual (`(vs0 X))) _).
Next Obligation.
Proof. by destruct (vs0 X). Qed.

Definition speculative_transition
  (sl : SpeculativeLabel) (ssim : SpeculativeState * option message)
  : SpeculativeState * option message :=
match sl, ssim with
| Speculate plan, (Actual s, None) =>
    (Speculative s s plan [], None)
| Execute, (Speculative start current (Build_plan_item lbl msg :: plan) outputs, None) =>
    let (current', om) := vtransition X lbl (current, msg) in
      (Speculative start current' plan (outputs ++ [om]), None)
| Rollback, (Speculative start _ (_ :: _) _, None) =>
    (Actual start, None)
| Commit, (Speculative _ current [] [], None) =>
    (Actual current, None)
| Commit, (Speculative start current [] (om :: outputs), None) =>
    (Speculative start current [] outputs, om)
| _, (s, _) => (s, None)
end.

Definition speculative_valid
  (sl : SpeculativeLabel) (ssim : SpeculativeState * option message) : Prop :=
match sl, ssim with
| Speculate plan, (Actual _, None) =>
    plan <> []
| Execute, (Speculative _ current (Build_plan_item lbl msg :: _) _, None) =>
    vvalid X lbl (current, msg)
| Rollback, (Speculative _ current (Build_plan_item lbl msg :: _) _, None) =>
    ~ vvalid X lbl (current, msg)
| Commit, (Speculative _ _ plan _, None) =>
    plan = []
| _, _ => False
end.

Definition speculative_vlsm_type : VLSMType message :=
{|
  state := SpeculativeState;
  label := SpeculativeLabel;
|}.

Definition speculative_vlsm_machine : VLSMMachine speculative_vlsm_type :=
{|
  initial_state_prop := speculative_initial_state_prop;
  s0 := speculative_s0;
  initial_message_prop := vinitial_message_prop X;
  transition := speculative_transition;
  valid := speculative_valid;
|}.

Definition speculative_vlsm : VLSM message :=
{|
  vtype := speculative_vlsm_type;
  vmachine := speculative_vlsm_machine;
|}.

Lemma speculative_option_valid_message_prop_None :
  option_valid_message_prop speculative_vlsm None.
Proof.
  destruct speculative_s0 as [[s Hinit]].
  red; exists s.
  by constructor.
Qed.

Lemma valid_state_prop_Actual :
  forall (s : vstate X),
    valid_state_prop X s -> valid_state_prop speculative_vlsm (Actual s).
Proof.
  intros s [om Hvsmp]; red.
  induction Hvsmp.
  - by exists None; constructor; cbn.
  - destruct IHHvsmp1 as [om1 Hom1], IHHvsmp2 as [om2 Hom2].
    exists om1.
    Print valid_state_message_prop.
    Check valid_generated_state_message _ _ _ Hom1 _ _ Hom2.
Admitted.

Lemma valid_state_prop_Speculative :
  forall (start current : vstate X) (plan : list (vplan_item X)) (outputs : list (option message)),
    valid_state_prop speculative_vlsm (Speculative start current plan outputs).
Proof.
  intros.
  red. exists None.
  Print valid_state_message_prop.
Admitted.

Lemma input_valid_transition_Speculate :
  forall (s : vstate X) (plan : list (vplan_item X)),
    valid_state_prop X s -> plan <> [] ->
      input_valid_transition speculative_vlsm
        (Speculate plan) (Actual s, None) (Speculative s s plan [], None).
Proof.
  intros s plan Hvsp Hplan.
  constructor; cbn; [| done].
  split_and!; [.. | done].
  - by apply valid_state_prop_Actual.
  - by apply speculative_option_valid_message_prop_None.
Qed.

Lemma input_valid_transition_Execute :
  forall (lbl : label) (start current current' : vstate X) (msg om : option message)
    (plan : list (vplan_item X)) (outputs : list (option message)),
    input_valid_transition X lbl (current, msg) (current', om) ->
      input_valid_transition speculative_vlsm Execute
        (Speculative start current (Build_plan_item lbl msg :: plan) outputs, None)
        (Speculative start current' plan (outputs ++ [om]), None).
Proof.
  intros lbl start current current' msg om plan outputs Hivt.
  inversion Hivt as [Hiv Ht].
  constructor; cbn; cycle 1.
  - unfold vtransition.
    change (@vtype message X) with (@type message X).
    by rewrite Ht.
  - destruct Hiv as (Hvsp & Hovmp & Hv).
    split_and!; cycle 1.
    + by apply speculative_option_valid_message_prop_None.
    + unfold vvalid.
      by change (@vtype message X) with (@type message X).
    + by apply valid_state_prop_Speculative.
Qed.

Lemma input_valid_transition_Commit_cons :
  forall (start current : vstate X) (om : option message) (outputs : list (option message)),
    valid_state_prop speculative_vlsm (Speculative start current [] (om :: outputs)) ->
      input_valid_transition speculative_vlsm Commit
        (Speculative start current [] (om :: outputs), None)
        (Speculative start current [] outputs, om).
Proof.
  constructor; cbn; [| done].
  split_and!; [done | | done].
  by apply speculative_option_valid_message_prop_None.
Qed.

Lemma input_valid_transition_Commit_nil :
  forall (start current : vstate X),
    valid_state_prop speculative_vlsm (Speculative start current [] []) ->
      input_valid_transition speculative_vlsm Commit
        (Speculative start current [] [], None) (Actual current, None).
Proof.
  constructor; cbn; [| done].
  split_and!; [done | | done].
  by apply speculative_option_valid_message_prop_None.
Qed.

Lemma input_valid_transition_Rollback :
  forall (start current : vstate X) (lbl : label) (msg : option message)
    (plan : list (vplan_item X)) (outputs : list (option message)),
      ~ vvalid X lbl (current, msg) ->
      input_valid_transition speculative_vlsm Rollback
        (Speculative start current (Build_plan_item lbl msg :: plan) outputs, None)
        (Actual start, None).
Proof.
  constructor; cbn; [| done].
  split_and!; [.. | done]; cycle 1.
  - by apply speculative_option_valid_message_prop_None.
  - by apply valid_state_prop_Speculative.
Qed.

Print Assumptions input_valid_transition_Speculate.
Print Assumptions input_valid_transition_Execute.
Print Assumptions input_valid_transition_Commit_cons.
Print Assumptions input_valid_transition_Commit_nil.
Print Assumptions input_valid_transition_Rollback.

Print transition_item.

Fixpoint speculative_lift_trace
  (start : vstate X) (tr : list (@transition_item _ (vtype X)))
  : list (@transition_item _ speculative_vlsm_type) :=
match tr with
| [] => []
| Build_transition_item lbl iom current oom :: tr' =>
    let plan := [Build_plan_item lbl iom]
    in
    let spec := @Build_transition_item _ speculative_vlsm_type
          (Speculate plan) None (Speculative start start plan []) None
    in
    let exec := @Build_transition_item _ speculative_vlsm_type
          Execute None (Speculative start current [] [oom]) None
    in
    let out := @Build_transition_item _ speculative_vlsm_type
          Commit None (Speculative start current [] []) oom
    in
    let commit := @Build_transition_item _ speculative_vlsm_type
          Commit None (Actual current) None
    in
      spec :: exec :: out :: commit :: speculative_lift_trace current tr'
end.

Lemma speculative_lift_input_valid_transition :
  forall (lbl : label) (s1 s2 : vstate X) (iom oom : option message),
    input_valid_transition X lbl (s1, iom) (s2, oom) ->
      exists tr : list transition_item,
        finite_valid_trace_from_to speculative_vlsm (Actual s1) (Actual s2) tr.
Proof.
  intros lbl s1 s2 iom oom [[Hvsp [Hovmp Hv]] Ht].
  pose (plan := [Build_plan_item lbl iom]).
  pose (spec := @Build_transition_item _ speculative_vlsm_type
    (Speculate plan) None (Speculative s1 s1 plan []) None).
  pose (exec := @Build_transition_item _ speculative_vlsm_type
    Execute None (Speculative s1 s2 [] [oom]) None).
  pose (out := @Build_transition_item _ speculative_vlsm_type
    Commit None (Speculative s1 s2 [] []) oom).
  pose (commit := @Build_transition_item _ speculative_vlsm_type
    Commit None (Actual s2) None).
  exists [spec; exec; out; commit].
  constructor; [| by eapply input_valid_transition_Speculate].
  constructor; cycle 1.
  + unfold plan; change [oom] with ([] ++ [oom]).
    by eapply input_valid_transition_Execute.
  + constructor; cycle 1.
    * apply input_valid_transition_Commit_cons. admit.
    * constructor.
      -- constructor. admit.
      -- red; cbn.
         split_and!; [admit | | done..].
         by apply speculative_option_valid_message_prop_None.
Admitted.

Lemma in_futures_speculative :
  forall (s1 s2 : vstate X),
    in_futures X s1 s2 -> in_futures speculative_vlsm (Actual s1) (Actual s2).
Proof.
  intros s1 s2 [tr Htr].
  unfold in_futures.
  induction Htr.
  - exists []; constructor.
    by apply valid_state_prop_Actual.
  - destruct IHHtr as [tr IH].
    Search input_valid_transition finite_valid_trace_from_to.
    pose (plan := [Build_plan_item l iom]).
    pose (spec := @Build_transition_item _ speculative_vlsm_type
      (Speculate plan) None (Speculative s' s' plan []) None).
    pose (exec := @Build_transition_item _ speculative_vlsm_type
      Execute None (Speculative s' s [] [oom]) None).
    pose (out := @Build_transition_item _ speculative_vlsm_type
      Commit None (Speculative s' s [] []) oom).
    pose (commit := @Build_transition_item _ speculative_vlsm_type
      Commit None (Actual s) None).
    exists (spec :: exec :: out :: commit :: tr).
    inversion Ht as [[Ht1 [Ht2 Ht3]] Ht4].
    constructor; [| by eapply input_valid_transition_Speculate].
    constructor; cycle 1.
    + unfold plan; change [oom] with ([] ++ [oom]).
      by eapply input_valid_transition_Execute.
    + constructor; cycle 1.
      * apply input_valid_transition_Commit_cons. admit.
      * constructor; [done |].
        red; cbn.
        split_and!; [admit | | done..].
        by apply speculative_option_valid_message_prop_None.
Admitted.

Lemma in_futures_speculative' :
  forall (s1 s2 : vstate X),
    in_futures X s1 s2 -> in_futures speculative_vlsm (Actual s1) (Actual s2).
Proof.
  intros s1 s2 [tr Htr].
  unfold in_futures.
  exists (speculative_lift_trace s1 tr).
  induction Htr.
  - cbn; constructor.
    by apply valid_state_prop_Actual.
  - inversion Ht as [[Ht1 [Ht2 Ht3]] Ht4].
    simpl.
    constructor; [| by eapply input_valid_transition_Speculate].
    constructor; cycle 1.
    + change [oom] with ([] ++ [oom]).
      by eapply input_valid_transition_Execute.
    + constructor; cycle 1.
      * apply input_valid_transition_Commit_cons. admit.
      * constructor; cbn; [done |].
        red; cbn.
        split_and!; [admit | | done..].
        by apply speculative_option_valid_message_prop_None.
Admitted.

End sec_speculative.
