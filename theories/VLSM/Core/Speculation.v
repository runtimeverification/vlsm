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
| Execute, (Speculative start current (Build_plan_item lbl msg :: plan) outputs, _) =>
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
| Execute, (Speculative _ current (Build_plan_item lbl msg :: _) _, msg') =>
    vvalid X lbl (current, msg) /\ msg = msg'
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

Lemma input_valid_transition_Speculate :
  forall (s : vstate X) (plan : list (vplan_item X)),
    valid_state_prop speculative_vlsm (Actual s) -> plan <> [] ->
      input_valid_transition speculative_vlsm
        (Speculate plan) (Actual s, None) (Speculative s s plan [], None).
Proof.
  intros s plan Hvsp Hplan.
  constructor; cbn; [| done].
  split_and!; [done | | done].
  by apply speculative_option_valid_message_prop_None.
Qed.

Lemma input_valid_transition_Execute :
  forall (lbl : label) (start current current' : vstate X) (msg msg' om : option message)
    (plan : list (vplan_item X)) (outputs : list (option message)),
    valid_state_prop speculative_vlsm
      (Speculative start current ({| label_a := lbl; input_a := msg' |} :: plan) outputs) ->
    option_valid_message_prop speculative_vlsm msg' ->
    msg = msg' ->
    input_valid_transition X lbl (current, msg) (current', om) ->
      input_valid_transition speculative_vlsm Execute
        (Speculative start current (Build_plan_item lbl msg :: plan) outputs, msg')
        (Speculative start current' plan (outputs ++ [om]), None).
Proof.
  intros lbl start current current' msg msg' om plan outputs Hvsp Hovmp -> [Hiv Ht].
  constructor; cbn; cycle 1.
  - unfold vtransition.
    change (@vtype message X) with (@type message X).
    by rewrite Ht.
  - destruct Hiv as (Hvsp' & Hovmp' & Hv).
    by split_and!.
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
      valid_state_prop speculative_vlsm
        (Speculative start current ({| label_a := lbl; input_a := msg |} :: plan) outputs) ->
      ~ vvalid X lbl (current, msg) ->
      input_valid_transition speculative_vlsm Rollback
        (Speculative start current (Build_plan_item lbl msg :: plan) outputs, None)
        (Actual start, None).
Proof.
  constructor; cbn; [| done].
  split_and!; [done | | done].
  by apply speculative_option_valid_message_prop_None.
Qed.

Definition speculative_lift_transition_item
  (start : vstate X) (ti : vtransition_item X)
  : list (vtransition_item speculative_vlsm) :=
match ti with
| Build_transition_item lbl iom current oom =>
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
      [spec; exec; out; commit]
end.

Fixpoint speculative_lift_trace
  (start : vstate X) (tr : list (vtransition_item X))
  : list (vtransition_item speculative_vlsm) :=
match tr with
| [] => []
| ti :: tr' =>
    speculative_lift_transition_item start ti ++ speculative_lift_trace (destination ti) tr'
end.

Lemma speculative_lift_trace_app :
  forall (start : vstate X) (tr1 tr2 : list (vtransition_item X)),
    speculative_lift_trace start (tr1 ++ tr2) =
    speculative_lift_trace start tr1 ++ speculative_lift_trace (finite_trace_last start tr1) tr2.
Proof.
  intros start tr1; revert start.
  induction tr1 as [| ti tr1']; simpl; intros; [done |].
  by rewrite <- app_assoc, IHtr1', finite_trace_last_cons.
Qed.

Lemma speculative_lift_input_valid_transition :
  forall (lbl : label) (s1 s2 : vstate X) (iom oom : option message),
    input_valid_transition X lbl (s1, iom) (s2, oom) ->
      finite_valid_trace_from_to speculative_vlsm (Actual s1) (Actual s2)
        (speculative_lift_transition_item s1 (Build_transition_item lbl iom s2 oom)).
Proof.
  intros lbl s1 s2 iom oom [[Hvsp [Hovmp Hv]] Ht].
  constructor; [| admit].
  constructor; cycle 1.
  + unfold plan; change [oom] with ([] ++ [oom]).
    eapply input_valid_transition_Execute; admit.
  + constructor; cycle 1.
    * apply input_valid_transition_Commit_cons. admit.
    * constructor.
      -- constructor. admit.
      -- red; cbn.
         split_and!; [admit | | done..].
         by apply speculative_option_valid_message_prop_None.
Admitted.

Lemma finite_valid_trace_init_to_speculative :
  forall (s1 s2 : vstate X) (tr : list (vtransition_item X)),
    finite_valid_trace_init_to X s1 s2 tr ->
      finite_valid_trace_init_to speculative_vlsm (Actual s1) (Actual s2)
        (speculative_lift_trace s1 tr).
Proof.
  Check finite_valid_trace_init_to.
  Check finite_valid_trace_init_to_rev_strong_ind.
  intros s1 s2 tr Htr.
  induction Htr using finite_valid_trace_init_to_rev_strong_ind; cbn.
  - constructor; [| done].
    constructor.
    by apply initial_state_is_valid.
  - split; [| by apply IHHtr1].
    rewrite speculative_lift_trace_app.
    apply finite_valid_trace_from_to_app with (Actual s); [by apply IHHtr1 |].
    constructor; cycle 1.
    {
      replace s with (finite_trace_last is tr) in * by admit.
      apply input_valid_transition_Speculate; [| done].
      by apply valid_trace_last_pstate in IHHtr1.
    }
    constructor; cycle 1.
    {
      replace sf with (finite_trace_last is tr) in * by admit.
      change [oom] with ([] ++ [oom]).
      apply input_valid_transition_Execute; cycle 3.
      + replace s with (finite_trace_last is tr) in * by admit.
        done.
      + cbn.







unfold empty_initial_message_or_final_output in Heqiom.
        From VLSM.Lib Require Import ListExtras.
        destruct_list_last iom_tr iom_tr' item Heqtr; subst.
        * apply option_initial_message_is_valid in Heqiom.
          exists iom.
      
    }
Qed.

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
    exists (speculative_lift_transition_item s' (Build_transition_item l iom s oom) ++ tr).
    apply (finite_valid_trace_from_to_app speculative_vlsm (Actual s)); [| done].
    by apply speculative_lift_input_valid_transition.
Qed.

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
  - apply (finite_valid_trace_from_to_app speculative_vlsm (Actual s)); [| done].
    by apply speculative_lift_input_valid_transition.
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
Admitted.

Lemma valid_state_prop_Speculative :
  forall (start current : vstate X) (plan : list (vplan_item X)) (outputs : list (option message)),
    valid_state_prop speculative_vlsm (Speculative start current plan outputs).
Proof.
  intros.
  red. exists None.
Admitted.

End sec_speculative.
