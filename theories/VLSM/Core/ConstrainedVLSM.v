From VLSM.Lib Require Import Itauto.
From stdpp Require Import prelude.
From Coq Require Import Streams.
From VLSM.Lib Require Import Preamble.
From VLSM.Core Require Import VLSM PreloadedVLSM VLSMInclusion VLSMEmbedding VLSMEquality.

(** * Constrained VLSM

  Given a base VLSM <<X>>, we can further constrain its validity
  condition with the given predicate, producing a new VLSM.
*)

Section sec_constrained_vlsm.

Context
  {message : Type}
  (X : VLSM message)
  (constraint : label X -> state X * option message -> Prop).

Definition constrained_vlsm_type : VLSMType message :=
  vtype X.

Definition constrained_vlsm_machine : VLSMMachine X :=
{|
  initial_state_prop := @initial_state_prop _ _ X;
  initial_message_prop := @initial_message_prop _ _ X;
  s0 := @s0 _ _ X;
  transition := @transition _ _ X;
  valid := fun l som => valid X l som /\ constraint l som;
|}.

Definition constrained_vlsm : VLSM message :=
{|
  vtype := vtype X;
  vmachine := constrained_vlsm_machine;
|}.

End sec_constrained_vlsm.

Lemma VLSM_embedding_constrained_vlsm :
  forall `(X : VLSM message) (constraint : label X -> state X * option message -> Prop),
    VLSM_embedding (constrained_vlsm X constraint) X id id.
Proof.
  intros.
  apply basic_VLSM_strong_embedding; red; cbn; [| done..].
  by itauto.
Qed.

Lemma VLSM_incl_constrained_vlsm :
  forall `(X : VLSM message) (constraint : label X -> state X * option message -> Prop),
    VLSM_incl (constrained_vlsm X constraint) X.
Proof.
  intros message X.
  rewrite <- (mk_vlsm_machine X); cbn.
  intros constraint.
  apply (VLSMInclusion.VLSM_incl_embedding_iff (constrained_vlsm_machine X constraint)).
  by apply (VLSM_embedding_constrained_vlsm {| vtype := X; vmachine := X; |}).
Qed.

Section sec_constrained_vlsm_lemmas.

Context
  {message : Type}
  (X : VLSM message)
  (constraint : label X -> state X * option message -> Prop).

Lemma option_initial_message_prop_constrained_vlsm :
  forall om : option message,
    @option_initial_message_prop _ _ (constrained_vlsm X constraint) om
      <->
    @option_initial_message_prop _ _ X om.
Proof.
  done.
Qed.

Lemma valid_state_message_prop_constrained_vlsm :
  forall
    (s : state _) (om : option message),
      valid_state_message_prop (constrained_vlsm X constraint) s om ->
        valid_state_message_prop X s om.
Proof.
  intros s om H.
  destruct X.
  eapply VLSM_incl_valid_state_message; [.. | by do 2 red | done].
  by apply (VLSM_incl_constrained_vlsm {| vtype := vtype; vmachine := vmachine; |}).
Qed.

Lemma valid_state_prop_constrained_vlsm :
  forall (s : state _),
    valid_state_prop (constrained_vlsm X constraint) s ->
      valid_state_prop X s.
Proof.
  intros s [om Hvsmp].
  exists om.
  by apply valid_state_message_prop_constrained_vlsm.
Qed.

Lemma valid_message_prop_constrained_vlsm :
  forall (m : message),
    valid_message_prop (constrained_vlsm X constraint) m ->
      valid_message_prop X m.
Proof.
  intros m [s Hvsmp].
  exists s.
  by apply valid_state_message_prop_constrained_vlsm.
Qed.

Lemma option_valid_message_prop_constrained_vlsm :
  forall (om : option message),
    option_valid_message_prop (constrained_vlsm X constraint) om ->
      option_valid_message_prop X om.
Proof.
  intros om [s Hvsmp].
  exists s.
  by apply valid_state_message_prop_constrained_vlsm.
Qed.

Lemma input_valid_constrained_vlsm :
  forall (l : label _) (som : state _ * option message),
    input_valid (constrained_vlsm X constraint) l som ->
      input_valid X l som.
Proof.
  intros l [s om] Hiv.
  destruct X.
  apply VLSM_incl_input_valid; [| done].
  by apply (VLSM_incl_constrained_vlsm {| vtype := vtype; vmachine := vmachine; |}).
Qed.

Lemma input_valid_transition_constrained_vlsm :
  forall (l : label _) (som som' : state _ * option message),
    input_valid_transition (constrained_vlsm X constraint) l som som' ->
      input_valid_transition X l som som'.
Proof.
  intros l [s om] [s' om'] Hivt.
  destruct X.
  apply VLSM_incl_input_valid_transition; [| done].
  by apply (VLSM_incl_constrained_vlsm {| vtype := vtype; vmachine := vmachine; |}).
Qed.

Lemma option_can_produce_constrained_vlsm :
  forall (s : state _) (om : option message),
    option_can_produce (constrained_vlsm X constraint) s om ->
      option_can_produce X s om.
Proof.
  intros s om Hocp.
  destruct X.
  eapply VLSM_incl_can_produce; [| done].
  by apply (VLSM_incl_constrained_vlsm {| vtype := vtype; vmachine := vmachine; |}).
Qed.

Lemma can_produce_constrained_vlsm :
  forall (s : state _) (m : message),
    can_produce (constrained_vlsm X constraint) s m ->
      can_produce X s m.
Proof.
  by intros; apply option_can_produce_constrained_vlsm.
Qed.

Lemma can_emit_constrained_vlsm :
  forall (m : message),
    can_emit (constrained_vlsm X constraint) m ->
      can_emit X m.
Proof.
  intros m Hce.
  destruct X.
  eapply VLSM_incl_can_emit; [| done].
  by apply (VLSM_incl_constrained_vlsm {| vtype := vtype; vmachine := vmachine; |}).
Qed.

Lemma finite_valid_trace_from_constrained_vlsm :
  forall (s : state _) (tr : list transition_item),
    finite_valid_trace_from (constrained_vlsm X constraint) s tr ->
      finite_valid_trace_from X s tr.
Proof.
  intros s tr Hfvtf.
  destruct X.
  apply VLSM_incl_finite_valid_trace_from; [| done].
  by apply (VLSM_incl_constrained_vlsm {| vtype := vtype; vmachine := vmachine; |}).
Qed.

Lemma finite_valid_trace_constrained_vlsm :
  forall (s : state _) (tr : list transition_item),
    finite_valid_trace (constrained_vlsm X constraint) s tr ->
      finite_valid_trace X s tr.
Proof.
  intros s tr Hfvt.
  destruct X.
  apply VLSM_incl_finite_valid_trace; [| done].
  by apply (VLSM_incl_constrained_vlsm {| vtype := vtype; vmachine := vmachine; |}).
Qed.

Lemma finite_valid_trace_from_to_constrained_vlsm :
  forall (s1 s2 : state _) (tr : list transition_item),
    finite_valid_trace_from_to (constrained_vlsm X constraint) s1 s2 tr ->
      finite_valid_trace_from_to X s1 s2 tr.
Proof.
  intros s1 s2 tr Hfvtft.
  destruct X.
  apply VLSM_incl_finite_valid_trace_from_to; [| done].
  by apply (VLSM_incl_constrained_vlsm {| vtype := vtype; vmachine := vmachine; |}).
Qed.

Lemma finite_valid_trace_init_to_constrained_vlsm :
  forall (s1 s2 : state _) (tr : list transition_item),
    finite_valid_trace_init_to (constrained_vlsm X constraint) s1 s2 tr ->
      finite_valid_trace_init_to X s1 s2 tr.
Proof.
  intros s1 s2 tr Hfvtit.
  destruct X.
  apply VLSM_incl_finite_valid_trace_init_to; [| done].
  by apply (VLSM_incl_constrained_vlsm {| vtype := vtype; vmachine := vmachine; |}).
Qed.

Lemma finite_valid_trace_init_to_emit_constrained_vlsm :
  forall (s1 s2 : state _) (om : option message) (tr : list transition_item),
    finite_valid_trace_init_to_emit (constrained_vlsm X constraint) s1 s2 om tr ->
      finite_valid_trace_init_to_emit X s1 s2 om tr.
Proof.
  induction 1; cbn; [by constructor |].
  by destruct Hv; econstructor.
Qed.

Lemma empty_initial_message_or_final_output_constrained_vlsm :
  forall (tr : list transition_item) (om : option message),
    empty_initial_message_or_final_output (constrained_vlsm X constraint) tr om ->
      empty_initial_message_or_final_output X tr om.
Proof.
  intros tr om.
  unfold empty_initial_message_or_final_output; cbn.
  by case_match.
Qed.

Lemma infinite_valid_trace_from_constrained_vlsm :
  forall (s : state _) (tr : Stream transition_item),
    infinite_valid_trace_from (constrained_vlsm X constraint) s tr ->
      infinite_valid_trace_from X s tr.
Proof.
  intros s tr Hivtf.
  destruct X.
  apply VLSM_incl_infinite_valid_trace_from; [| done].
  by apply (VLSM_incl_constrained_vlsm {| vtype := vtype; vmachine := vmachine; |}).
Qed.

Lemma infinite_valid_trace_constrained_vlsm :
  forall (s : state _) (tr : Stream transition_item),
    infinite_valid_trace (constrained_vlsm X constraint) s tr ->
      infinite_valid_trace X s tr.
Proof.
  intros s tr Hivt.
  destruct X.
  apply VLSM_incl_infinite_valid_trace; [| done].
  by apply (VLSM_incl_constrained_vlsm {| vtype := vtype; vmachine := vmachine; |}).
Qed.

Lemma valid_trace_from_prop_constrained_vlsm :
  forall (tr : Trace),
    valid_trace_from_prop (constrained_vlsm X constraint) tr ->
      valid_trace_from_prop X tr.
Proof.
  intros [] Hvtfp; cbn.
  - by apply finite_valid_trace_from_constrained_vlsm.
  - by apply infinite_valid_trace_from_constrained_vlsm.
Qed.

Lemma valid_trace_prop_constrained_vlsm :
  forall (tr : Trace),
    valid_trace_prop (constrained_vlsm X constraint) tr ->
      valid_trace_prop X tr.
Proof.
  intros tr Hvtp.
  destruct X.
  apply VLSM_incl_valid_trace; [| done].
  by apply (VLSM_incl_constrained_vlsm {| vtype := vtype; vmachine := vmachine; |}).
Qed.

Lemma in_futures_constrained_vlsm :
  forall (s1 s2 : state _),
    in_futures (constrained_vlsm X constraint) s1 s2 ->
      in_futures X s1 s2.
Proof.
  intros s1 s2 Hif.
  destruct X.
  apply VLSM_incl_in_futures; [| done].
  by apply (VLSM_incl_constrained_vlsm {| vtype := vtype; vmachine := vmachine; |}).
Qed.

End sec_constrained_vlsm_lemmas.

Section sec_constrained_vlsm_commutation_lemmas.

Lemma constrained_preloaded_comm :
  forall `(X : VLSM message) (constraint : label X -> state X * option message -> Prop)
    (initial : message -> Prop),
      VLSM_eq
        (constrained_vlsm (pre_loaded_vlsm X initial) constraint)
        (pre_loaded_vlsm (constrained_vlsm X constraint) initial).
Proof.
  intros message X.
  rewrite <- (mk_vlsm_machine X); cbn.
  intros constraint initial.
  by split; apply (VLSM_incl_embedding_iff (constrained_vlsm_machine
    (pre_loaded_vlsm X initial) constraint)), basic_VLSM_strong_embedding; red; cbn.
Qed.

Lemma VLSM_incl_constrained_preloaded :
  forall `(X : VLSM message) (constraint : label X -> state X * option message -> Prop)
    (initial : message -> Prop),
      VLSM_incl
        (constrained_vlsm (pre_loaded_vlsm X initial) constraint)
        (pre_loaded_vlsm (constrained_vlsm X constraint) initial).
Proof.
  by intros; apply constrained_preloaded_comm.
Qed.

Lemma VLSM_incl_preloaded_constrained :
  forall `(X : VLSM message) (constraint : label X -> state X * option message -> Prop)
    (initial : message -> Prop),
      VLSM_incl
        (pre_loaded_vlsm (constrained_vlsm X constraint) initial)
        (constrained_vlsm (pre_loaded_vlsm X initial) constraint).
Proof.
  by intros; apply constrained_preloaded_comm.
Qed.

End sec_constrained_vlsm_commutation_lemmas.

Section sec_constraint_subsumption.

Context
  `(X : VLSM message)
  (constraint : label X -> state X * option message -> Prop).

Lemma constrained_pre_loaded_vlsm_incl_pre_loaded_with_all_messages :
  forall (P : message -> Prop),
    VLSM_incl
      (pre_loaded_vlsm (constrained_vlsm X constraint) P)
      (pre_loaded_with_all_messages_vlsm X).
Proof.
  by intros; apply basic_VLSM_strong_incl; cbv; [| itauto.. |].
Qed.

Lemma constrained_preloaded_incl :
  VLSM_incl (constrained_vlsm X constraint) (pre_loaded_with_all_messages_vlsm X).
Proof.
  apply (@VLSM_incl_trans _ _ _ X).
  - by cbn; apply VLSM_incl_constrained_vlsm.
  - by apply (vlsm_incl_pre_loaded_with_all_messages_vlsm X).
Qed.

Context
  (constraint1 constraint2 : label X -> state X * option message -> Prop)
  (X1 := constrained_vlsm X constraint1)
  (X2 := constrained_vlsm X constraint2)
  .

(**
  A <<constraint1>> is subsumed by <<constraint2>> if <<constraint1>> is stronger
  than <<constraint2>> for any input.
*)
Definition strong_constraint_subsumption : Prop :=
  forall (l : label X) (som : state X * option message),
    constraint1 l som -> constraint2 l som.

(**
  A weaker version of [strong_constraint_subsumption] requiring [input_valid]ity
  w.r.t. [pre_loaded_with_all_messages_vlsm] as a precondition for the subsumption
  property.

  This definition is useful in proving [VLSM_incl]usions between [VLSM]s
  pre-loaded with all messages (Lemma [preloaded_constraint_subsumption_incl]).

  Although there are currently no explicit cases for its usage, it might be more
  useful than the [strong_constraint_subsumption] property in cases where proving
  constraint subsumption relies on the state being valid and/or the message
  being valid.
*)
Definition preloaded_constraint_subsumption : Prop :=
  forall (l : label X) (som : state _ * option message),
    input_valid (pre_loaded_with_all_messages_vlsm (constrained_vlsm X constraint1)) l som ->
      constraint2 l som.

(**
  A weaker version of [preloaded_constraint_subsumption] requiring [input_valid]ity
  as a precondition for the subsumption property.

  This definition is usually useful in proving [VLSM_incl]usions between regular
  [VLSM]s (Lemma [constraint_subsumption_incl]).

  It is more useful than the [strong_constraint_subsumption] property in cases
  where proving constraint subsumption relies on the state/message being valid
  and/or the message being valid (e.g., Lemma [Fixed_incl_StrongFixed]).
*)
Definition input_valid_constraint_subsumption : Prop :=
  forall (l : label X) (som : state X * option message),
    input_valid (constrained_vlsm X constraint1) l som -> constraint2 l som.

(**
  The weakest form of constraint subsumption also requires that the input
  state and message are valid for the composition under the second constraint.
*)
Definition weak_input_valid_constraint_subsumption : Prop :=
  forall (l : label X) (som : state X * option message),
    input_valid (constrained_vlsm X constraint1) l som ->
    valid_state_prop (constrained_vlsm X constraint2) som.1 ->
    option_valid_message_prop (constrained_vlsm X constraint2) som.2 ->
      constraint2 l som.

(**
  Let <<X1>>, <<X2>> be two constrained VLSMs constraints <<constraint1>>
  and <<constraint2>>, respectively. Further assume that <<constraint1>>
  is subsumed by <<constraint2>>.

  We will show that <<X1>> is trace-included into <<X2>> by applying
  the lemma [basic_VLSM_incl].
*)

Lemma weak_constraint_subsumption_incl
  (Hsubsumption : weak_input_valid_constraint_subsumption)
  : VLSM_incl X1 X2.
Proof.
  apply basic_VLSM_incl.
  - by intros s Hs.
  - by intros _ _ m _ _ Hm; apply initial_message_is_valid.
  - by split; [apply Hv | auto].
  - by intros l s om s' om' Ht; apply Ht.
Qed.

Lemma constraint_subsumption_input_valid
  (Hsubsumption : input_valid_constraint_subsumption)
  (l : label X1)
  (s : state X1)
  (om : option message)
  (Hv : input_valid X1 l (s, om))
  : valid X2 l (s, om).
Proof.
  by split; [apply Hv | apply Hsubsumption].
Qed.

Lemma constraint_subsumption_valid_state_message_preservation
  (Hsubsumption : input_valid_constraint_subsumption)
  (s : state X1)
  (om : option message)
  (Hps : valid_state_message_prop X1 s om)
  : valid_state_message_prop X2 s om.
Proof.
  induction Hps; [by apply valid_initial_state_message |].
  apply (valid_generated_state_message X2) with s _om _s om l; only 1-2, 4: done.
  apply constraint_subsumption_input_valid; [done |].
  by split_and!; [exists _om | exists _s |].
Qed.

Lemma constraint_subsumption_incl
  (Hsubsumption : input_valid_constraint_subsumption)
  : VLSM_incl X1 X2.
Proof.
  apply basic_VLSM_incl; intro; intros.
  - done.
  - by apply initial_message_is_valid.
  - by apply constraint_subsumption_input_valid.
  - by apply H.
Qed.

Lemma preloaded_constraint_subsumption_input_valid
  (Hpre_subsumption : preloaded_constraint_subsumption)
  (l : label X1)
  (s : state X1)
  (om : option message)
  (Hv : input_valid (pre_loaded_with_all_messages_vlsm X1) l (s, om))
  : valid X2 l (s, om).
Proof.
  by split; [apply Hv | apply Hpre_subsumption].
Qed.

Lemma preloaded_constraint_subsumption_incl
  (Hpre_subsumption : preloaded_constraint_subsumption)
  : VLSM_incl (pre_loaded_with_all_messages_vlsm X1) (pre_loaded_with_all_messages_vlsm X2).
Proof.
  apply basic_VLSM_incl; intro; intros; [done | | | apply H].
  - by apply initial_message_is_valid.
  - by apply preloaded_constraint_subsumption_input_valid.
Qed.

Lemma preloaded_constraint_subsumption_incl_free :
  VLSM_incl
    (pre_loaded_with_all_messages_vlsm X1)
    (pre_loaded_with_all_messages_vlsm X).
Proof.
  apply basic_VLSM_incl; intro; intros; [done | ..].
  - by apply initial_message_is_valid.
  - by apply Hv.
  - by apply H.
Qed.

Lemma weak_constraint_subsumption_weakest
  (Hsubsumption : input_valid_constraint_subsumption)
  : weak_input_valid_constraint_subsumption.
Proof.
  by intros l som Hv _ _; auto.
Qed.

Lemma preloaded_constraint_subsumption_stronger
  (Hpre_subsumption : preloaded_constraint_subsumption)
  : input_valid_constraint_subsumption.
Proof.
  intros l som Hv.
  apply Hpre_subsumption.
  destruct som.
  eapply VLSM_incl_input_valid; [| done].
  by apply (vlsm_incl_pre_loaded_with_all_messages_vlsm X1).
Qed.

Lemma strong_constraint_subsumption_strongest
  (Hstrong_subsumption : strong_constraint_subsumption)
  : preloaded_constraint_subsumption.
Proof.
  intros l [s om] (_ & _ & _ & Hc).
  by apply Hstrong_subsumption.
Qed.

Lemma constraint_subsumption_byzantine_message_prop
  (Hpre_subsumption : preloaded_constraint_subsumption)
  (m : message)
  (Hm : byzantine_message_prop X1 m)
  : byzantine_message_prop X2 m.
Proof.
  by apply (VLSM_incl_can_emit (preloaded_constraint_subsumption_incl Hpre_subsumption)).
Qed.

End sec_constraint_subsumption.
