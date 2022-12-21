From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From VLSM.Lib Require Import Preamble ListExtras.
From VLSM.Core Require Import VLSM Plans.

(** * Speculative VLSMs

  This module introduces the speculative VLSM construction. It models the
  speculative execution of transitions from the underlying VLSM which can then
  be committed or rolled back.
*)

(** ** Definitions *)

Section sec_speculative.

(**
  The speculative VLSM construction takes a VLSM <<X>>, called the underlying
  VLSM, and produces a new VLSM, called [speculative_vlsm].
*)

Context
  {message : Type}
  (X : VLSM message).

(**
  [speculative_vlsm] has two kinds of states:
  - [Actual] states correspond to states of the underlying VLSM. These are the
    states that are "certain", i.e. once an [Actual] states is reached, previous
    speculative execution cannot be rolled back anymore.
  - [Speculative] states are the states in which speculative execution occurs.
    They are not "certain" in the sense that there is still a possibility of
    rollback to the previous [Actual] state.

  [Speculative] states contain the following information:
  - [start] is a state of the underlying VLSM from which speculative execution
    was started
  - [current] is a state of the underlying VLSM reached by the speculative
    execution so far
  - [plan] is a list of remaining transitions from the underlying VLSM to be
    performed
  - [outputs] is a list of messages that were output during the speculative
    execution so far
*)

Inductive SpeculativeState : Type :=
| Actual (s : vstate X)
| Speculative
    (start current : vstate X) (plan : list (vplan_item X)) (outputs : list (option message)).

(**
  [speculative_vlsm] has four kinds of labels:
  - [Speculate] starts speculative execution. It contains a <<plan>> of what is
    to be speculatively executed
  - [Execute] performs a transition from the underlying VLSM
  - [Commit] outputs messages that were produced during speculative execution
    (if there are any) and finishes speculative execution (if there are no more
    messages to be output)
  - [Rollback] cancels ongoing speculative execution, discarding any messages
    that were produced, and returns to the previous [Actual] state
*)

Inductive SpeculativeLabel : Type :=
| Execute
| Rollback
| Commit
| Speculate (plan : list (vplan_item X)).

(**
  The initial states of [speculative_vlsm] are [Actual states that correspond
  to the initial states of the underlying VLSM.
*)

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

(** ** Lemmas *)

(**
  We can lift a [transition_item] from the underlying VLSM [X] to a list
  of four [transition_item]s in the [speculative_vlsm]. This corresponds
  to the fact that a single transition in the underlying VLSM can be lifted
  to a trace of length four in the [speculative_vlsm].

  The four steps are:
  - Speculate a plan
  - Execute the only item from this plan
  - Output the message from this execution
  - Commit the result
*)
Definition speculative_lift_transition_item
  (start : vstate X) (ti : vtransition_item X)
  : list (vtransition_item speculative_vlsm) :=
match ti with
| Build_transition_item lbl iom current oom =>
    let plan   := [Build_plan_item lbl iom] in
    let spec   := @Build_transition_item _ speculative_vlsm_type
                    (Speculate plan) None (Speculative start start plan []) None in
    let exec   := @Build_transition_item _ speculative_vlsm_type
                    Execute iom (Speculative start current [] [oom]) None in
    let output := @Build_transition_item _ speculative_vlsm_type
                    Commit None (Speculative start current [] []) oom in
    let commit := @Build_transition_item _ speculative_vlsm_type
                    Commit None (Actual current) None in
      [spec; exec; output; commit]
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

Lemma input_valid_transition_Speculate :
  forall (s : vstate X) (plan : list (vplan_item X)),
    valid_state_prop speculative_vlsm (Actual s) -> plan <> [] ->
      input_valid_transition speculative_vlsm
        (Speculate plan) (Actual s, None) (Speculative s s plan [], None).
Proof.
  intros s plan Hvsp Hplan.
  constructor; cbn; [| done].
  split_and!; [done | | done].
  by apply option_valid_message_None.
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
  constructor; cbn.
  - destruct Hiv as (Hvsp' & Hovmp' & Hv).
    by split_and!.
  - by replace (vtransition _ _ _) with (current', om).
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
  by apply option_valid_message_None.
Qed.

Lemma input_valid_transition_Commit_nil :
  forall (start current : vstate X),
    valid_state_prop speculative_vlsm (Speculative start current [] []) ->
      input_valid_transition speculative_vlsm Commit
        (Speculative start current [] [], None) (Actual current, None).
Proof.
  constructor; cbn; [| done].
  split_and!; [done | | done].
  by apply option_valid_message_None.
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
  by apply option_valid_message_None.
Qed.

Lemma speculative_lift_input_valid_transition :
  forall (lbl : label) (s1 s2 : vstate X) (iom oom : option message),
    valid_state_prop speculative_vlsm (Actual s1) ->
    option_valid_message_prop speculative_vlsm iom ->
    input_valid_transition X lbl (s1, iom) (s2, oom) ->
      finite_valid_trace_from_to speculative_vlsm (Actual s1) (Actual s2)
        (speculative_lift_transition_item s1 (Build_transition_item lbl iom s2 oom)).
Proof.
  intros lbl s1 s2 iom oom Hvsp Hovmp Hivt.
  assert (Hivt1 :
    input_valid_transition speculative_vlsm (Speculate [{| label_a := lbl; input_a := iom |}])
      (Actual s1, None)
      (Speculative s1 s1 [{| label_a := lbl; input_a := iom |}] [], None)).
  {
    by apply input_valid_transition_Speculate.
  }
  assert (Hivt2 :
    input_valid_transition speculative_vlsm Execute
      (Speculative s1 s1 [{| label_a := lbl; input_a := iom |}] [], iom)
      (Speculative s1 s2 [] [oom], None)).
  {
    unfold plan; change [oom] with ([] ++ [oom]).
    eapply input_valid_transition_Execute; [| done..].
    by eapply input_valid_transition_destination.
  }
  assert (Hivt3 :
    input_valid_transition speculative_vlsm Commit
    (Speculative s1 s2 [] [oom], None)
    (Speculative s1 s2 [] [], oom)).
  {
    apply input_valid_transition_Commit_cons.
    by eapply input_valid_transition_destination.
  }
  assert (Hivt4 :
    input_valid_transition speculative_vlsm Commit
      (Speculative s1 s2 [] [], None)
      (Actual s2, None)).
  {
    apply input_valid_transition_Commit_nil.
    by eapply input_valid_transition_destination.
  }
  repeat (constructor; try done).
  by eapply input_valid_transition_destination.
Qed.

Lemma finite_valid_trace_init_to_speculative_lift_trace :
  forall (s1 s2 : vstate X) (tr : list (vtransition_item X)),
    finite_valid_trace_init_to X s1 s2 tr ->
      finite_valid_trace_init_to speculative_vlsm (Actual s1) (Actual s2)
        (speculative_lift_trace s1 tr).
Proof.
  intros s1 s2 tr Htr.
  induction Htr using finite_valid_trace_init_to_rev_strong_ind; cbn.
  - split; [| done].
    constructor.
    by apply initial_state_is_valid.
  - split; [| by apply IHHtr1].
    rewrite speculative_lift_trace_app.
    apply finite_valid_trace_from_to_app with (Actual s); [by apply IHHtr1 |].
    apply valid_trace_get_last in Htr1 as <-.
    apply speculative_lift_input_valid_transition; [.. | done].
    + by apply valid_trace_last_pstate in IHHtr1.
    + unfold empty_initial_message_or_final_output in Heqiom.
      destruct_list_last iom_tr iom_tr' item Heqtr; subst;
        [by apply option_initial_message_is_valid |].
      destruct item as [? ? ? []]; cbn; [| by apply option_valid_message_None].
      eapply valid_trace_output_is_valid.
      * by eapply valid_trace_forget_last, IHHtr2.
      * red; rewrite speculative_lift_trace_app, Exists_app.
        by do 3 right; left; cbn.
Qed.

End sec_speculative.
