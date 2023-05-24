From VLSM.Lib Require Import Itauto.
From stdpp Require Import prelude.
From Coq Require Import Streams.
From VLSM.Lib Require Import Preamble ListExtras StreamExtras.

(** * VLSM Basics

  This module provides basic VLSM infrastructure.
*)

(** ** VLSM definition *)

(** *** The type of a VLSM

  The type of a VLSM is a triple consisting of the underlying types of
  messages, states, and labels.

  In Coq it is defined as a record taking <<message>> as parameter and having
  [state] and [label] as fields.  <<message>> is a parameter to allow it to be
  easily shared by multiple VLSMs during composition.
*)

Record VLSMType (message : Type) : Type :=
{
  state : Type;
  label : Type;
}.

(*
  We set implicit arguments for [state] in such a way that we can provide the
  argument either explicitly as <<state X>> or we can leave it out, writing
  just <<state>>, allowing Coq to infer it. We do the same for [label].
*)
Arguments state {message v}, {message} v.
Arguments label {message v}, {message} v.

(*
  Unfortunately, with the above implicit argument settings the argument is not
  displayed (e.g. in the context during a proof it's displayed as <<state>>), so
  we force Coq to always display this argument using an "only printing" notation.
*)
Notation "'state' X" := (@state _ X) (at level 10, only printing).
Notation "'label' X" := (@label _ X) (at level 10, only printing).

(** *** VLSM class definition

  [VLSMMachine] is parameterized by a [VLSMType], and contains the
  remaining parameters to define a VLSM over the given types.
  These are the properties for initial states ([initial_state_prop])
  and initial messages ([initial_message_prop]), from which we can
  immediately define the types [initial_state] (as [state]s having
  the [initial_state_prop]erty) and [initial_message] (as <<message>>s
  having the [initial_message_prop]erty), a witness [s0] that the
  [initial_state] is inhabited, and the [transition] function and
  [valid]ity predicate.
*)

Record VLSMMachine {message : Type} (T : VLSMType message) : Type :=
{
  initial_state_prop : state T -> Prop;
  initial_state : Type := {s : state T | initial_state_prop s};
  s0 : Inhabited initial_state;
  initial_message_prop : message -> Prop;
  initial_message : Type := {m : message | initial_message_prop m};
  transition : label T -> state T * option message -> state T * option message;
  valid : label T -> state T * option message -> Prop;
}.

(* The & is a "bidirectionality hint", so that typechecking
   a VLSMMachine record definition will try to use the expected
   result type to determine <<T>> before typechecking the fields.
   Without this, the types of the values given for the fields would
   have to be written so they only mention the state and label type
   in ways that can be matched with [state ?T] and [label ?T].
*)
Arguments Build_VLSMMachine _ _ & _ _ _ _ _.

Arguments initial_state_prop {message T} VLSMMachine _, {message T VLSMMachine} _ : rename.
Arguments initial_state {message T} VLSMMachine : rename.
Arguments initial_message_prop {message T} VLSMMachine _, {message T VLSMMachine} _ : rename.
Arguments initial_message {message T} VLSMMachine : rename.
Arguments transition {message T} VLSMMachine _ _, {message T VLSMMachine} _ _ : rename.
Arguments valid {message T} VLSMMachine _ _, {message T VLSMMachine} _ _ : rename.

Definition option_initial_message_prop
  {message : Type} {T : VLSMType message} (M : VLSMMachine T)
  : option message -> Prop := from_option (@initial_message_prop _ _ M) True.

Definition VLSMMachine_pre_loaded_with_messages
  {message : Type} {T : VLSMType message} (M : VLSMMachine T)
  (initial : message -> Prop)
  : VLSMMachine T
  :=
  {| initial_state_prop := @initial_state_prop _ _ M
  ; initial_message_prop := fun m => @initial_message_prop _ _ M  m \/ initial m
  ; s0 := @s0 _ _ M
  ; transition := @transition _ _ M
  ; valid := @valid _ _ M
  |}.

Definition decidable_initial_messages_prop
  {message : Type} {T : VLSMType message} (M : VLSMMachine T)
  := forall m, Decision (@initial_message_prop _ _ M m).

(** *** VLSM type definition

  For technical reasons, e.g., the need to easily talk about VLSMs over
  the same set of messages and about VLSMs of the same type (over the same
  set of messages, labels and states), the VLSM definition is split into
  two parts, [VLSMType] and [VLSMMachine], which are packaged together by
  the following definition.
*)

Record VLSM (message : Type) : Type := mk_vlsm
{
  vtype :> VLSMType message;
  vmachine :> VLSMMachine vtype;
}.

Arguments vtype [message] v.
Arguments vmachine [message] v.
Arguments mk_vlsm [message] [vtype] vmachine.

Definition pre_loaded_vlsm
  {message : Type}
  (X : VLSM message)
  (initial : message -> Prop)
  : VLSM message
  :=
  {| vmachine := VLSMMachine_pre_loaded_with_messages X initial |}.

Section sec_traces.

Context
  {message : Type}
  {T : VLSMType message}
  .

(** ** Traces

  We introduce the concept of a trace to formalize an execution of the protocol.
  It is abstracted as a pair <<(start, steps)>> where <<start>> is a state
  and <<steps>> is a tuple of objects which fully describe the transitions
  underwent during execution. Notably, <<steps>> might be infinite.

  In Coq, we can define these objects (which we name [transition_item]s) as consisting of:
  - the [label] [l]
  - the (optional) [input] <<message>>
  - the [destination] [state] of the transition
  - the (optional) [output] <<message>> generated by the transition
*)

Record transition_item : Type :=
{
  l : label T;
  input : option message;
  destination : state T;
  output : option message;
}.

Definition field_selector
           (field : transition_item -> option message) :
  (message -> transition_item -> Prop) :=
  fun m item => field item = Some m.

Definition item_sends_or_receives :
  message -> transition_item -> Prop :=
  fun m item => input item = Some m \/ output item = Some m.

Definition trace_has_message
  (message_selector : message -> transition_item -> Prop)
  (msg : message)
  (tr : list transition_item)
  : Prop
  := List.Exists (message_selector msg) tr.

Lemma trace_has_message_prefix
  (message_selector : message -> transition_item -> Prop)
  (msg : message)
  (prefix suffix : list transition_item)
  : trace_has_message message_selector msg prefix ->
    trace_has_message message_selector msg (prefix ++ suffix).
Proof.
  by intro Hprefix; apply Exists_app; left.
Qed.

Lemma trace_has_message_observed_iff m tr
  (Hobserved : trace_has_message item_sends_or_receives m tr)
  : trace_has_message (field_selector input) m tr \/ trace_has_message (field_selector output) m tr.
Proof.
  by unfold trace_has_message in *; rewrite !Exists_exists in *; firstorder.
Qed.

(** Defines a message received but not sent by within the trace. *)
Definition trace_received_not_sent_before_or_after
  (tr : list transition_item)
  (m : message)
  : Prop
  := trace_has_message (field_selector input) m tr /\
     ~ trace_has_message (field_selector output) m tr.

(** States that a property holds for all messages received but not sent by a trace. *)
Definition trace_received_not_sent_before_or_after_invariant
  (tr : list transition_item)
  (P : message -> Prop)
  : Prop
  := forall m, trace_received_not_sent_before_or_after tr m -> P m.

Inductive Trace : Type :=
| Finite : state T -> list transition_item -> Trace
| Infinite : state T -> Stream transition_item -> Trace.

Definition trace_first (tr : Trace) : state T :=
  match tr with
  | Finite s _ => s
  | Infinite s _ => s
  end.

Definition finite_trace_last
  (si : state T) (tr : list transition_item) : state T :=
  List.last (List.map destination tr) si.

Definition finite_trace_last_output
  (tr : list transition_item) : option message :=
  List.last (List.map output tr) None.

Definition finite_trace_nth
  (si : state T) (tr : list transition_item)
  : nat -> option (state T) :=
  nth_error (si :: List.map destination tr).

Definition trace_last (tr : Trace) : option (state T)
  :=
    match tr with
    | Finite s ls => Some (finite_trace_last s ls)
    | Infinite _ _ => None
    end.

(**
  This function extracts the nth state of a trace, where the sequence of
  states of a trace is obtained by appending the all destination
  states in the transition list/stream to the initial state of the trace.
*)
Definition trace_nth (tr : Trace)
  : nat -> option (state T) :=
  fun (n : nat) =>
    match tr with
    | Finite s ls => finite_trace_nth s ls n
    | Infinite s st => Some (Str_nth n (Cons s (Streams.map destination st)))
    end.

End sec_traces.

Arguments Trace {message T}, {message} T.
Arguments transition_item {message} {T} , {message} T.
Arguments Build_transition_item {message T}, {message} T.
Arguments field_selector {_} {T} _ msg item /.
Arguments item_sends_or_receives {_} {_} msg item /.

Section sec_trace_lemmas.

Context
  [message : Type]
  [T : VLSMType message]
  .

Lemma last_error_destination_last
  (tr : list transition_item)
  (s : state T)
  (Hlast : option_map destination (last_error tr) = Some s)
  (default : state T)
  : finite_trace_last default tr  = s.
Proof.
  unfold option_map in Hlast.
  destruct (last_error tr) eqn: eq; [| done].
  inversion Hlast.
  unfold last_error in eq.
  destruct tr; [done |].
  inversion eq.
  unfold finite_trace_last.
  by rewrite last_map.
Qed.

Lemma finite_trace_last_cons
  (s : state T) (x : transition_item T) (tl : list (transition_item T)) :
  finite_trace_last s (x :: tl) = finite_trace_last (destination x) tl.
Proof.
  by unfold finite_trace_last; rewrite map_cons, unroll_last.
Qed.

Lemma finite_trace_last_nil
  (s : state T) :
  finite_trace_last s [] = s.
Proof. done. Qed.

Lemma finite_trace_last_app
  (s : state T) (t1 t2 : list (transition_item T)) :
  finite_trace_last s (t1 ++ t2) = finite_trace_last (finite_trace_last s t1) t2.
Proof.
  by unfold finite_trace_last; rewrite map_app, last_app.
Qed.

Lemma finite_trace_last_is_last
  (s : state T) (x : transition_item T) (tl : list (transition_item T)) :
  finite_trace_last s (tl++[x]) = destination x.
Proof.
  by unfold finite_trace_last; rewrite map_app; cbn; rewrite last_is_last.
Qed.

Lemma finite_trace_last_output_is_last
  (x : transition_item T) (tl : list (transition_item T)) :
  finite_trace_last_output (tl++[x]) = output x.
Proof.
  by unfold finite_trace_last_output; rewrite map_app; cbn; rewrite last_is_last.
Qed.

Lemma finite_trace_nth_first
  (si : state T) (tr : list transition_item) :
  finite_trace_nth si tr 0 = Some si.
Proof. done. Qed.

Lemma finite_trace_nth_last
  (si : state T) (tr : list transition_item) :
  finite_trace_nth si tr (length tr) = Some (finite_trace_last si tr).
Proof.
  unfold finite_trace_nth, finite_trace_last.
  destruct tr; [done |].
  cbn [nth_error length].
  apply nth_error_last.
  by rewrite map_length.
Qed.

Lemma finite_trace_nth_app1
  (si : state T) (t1 t2 : list transition_item) n :
  n <= length t1 ->
  finite_trace_nth si (t1++t2) n = finite_trace_nth si t1 n.
Proof.
  intro H.
  unfold finite_trace_nth.
  rewrite map_app, app_comm_cons.
  apply nth_error_app1.
  simpl. rewrite map_length.
  auto with arith.
Qed.

Lemma finite_trace_nth_app2
  (si : state T) (t1 t2 : list transition_item) n :
  length t1 <= n ->
  finite_trace_nth si (t1++t2) n = finite_trace_nth (finite_trace_last si t1) t2 (n - length t1).
Proof.
  intro H.
  apply Compare_dec.le_lt_eq_dec in H.
  destruct H as [H | <-].
  - unfold finite_trace_nth.
    rewrite map_app, app_comm_cons.
    rewrite nth_error_app2; simpl length; rewrite map_length; [| by auto with arith].
    destruct n; [by exfalso; lia |].
    by rewrite (Nat.sub_succ_l (length t1) n); [| lia].
  - by rewrite finite_trace_nth_app1, finite_trace_nth_last,
      Nat.sub_diag, finite_trace_nth_first.
Qed.

Lemma finite_trace_nth_length
  (si : state T) (tr : list transition_item) n s :
  finite_trace_nth si tr n = Some s ->
  n <= length tr.
Proof.
  intros H.
  apply nth_error_length in H.
  simpl in H.
  by rewrite map_length in H; lia.
Qed.

Lemma finite_trace_last_prefix
  (s : state T) (tr : list transition_item) n nth :
  finite_trace_nth s tr n = Some nth ->
  finite_trace_last s (list_prefix tr n) = nth.
Proof.
  unfold finite_trace_nth, finite_trace_last.
  rewrite list_prefix_map.
  generalize (List.map destination tr); intro l; clear tr.
  destruct n.
  - by simpl; intros [= <-]; destruct l.
  - by cbn; intros H; symmetry; apply list_prefix_nth_last.
Qed.

Lemma finite_trace_last_suffix
  (s : state T) (tr : list transition_item) n :
  n < length tr ->
  finite_trace_last s (list_suffix tr n) = finite_trace_last s tr.
Proof.
  intros H.
  unfold finite_trace_last.
  rewrite list_suffix_map.
  apply list_suffix_last.
  by rewrite map_length.
Qed.

Lemma unlock_finite_trace_last (s : state T) (tr : list (transition_item T)) :
  finite_trace_last s tr = List.last (List.map destination tr) s.
Proof. done. Qed.

End sec_trace_lemmas.

Section sec_vlsm_projections.

Context
  {message : Type}
  (vlsm : VLSM message)
  .

Definition vs0 := @inhabitant _ (@s0 _ _ vlsm).

End sec_vlsm_projections.

Lemma mk_vlsm_machine
  {message : Type}
  (X : VLSM message)
  : mk_vlsm (vmachine X) = X.
Proof.
  by destruct X.
Qed.

Section sec_VLSM.

(** In this section we assume a fixed [VLSM]. *)

Context
  {message : Type}
  (X : VLSM message)
  .

(** *** Valid states and messages

  We further characterize certain objects as being _valid_, which means they can
  be witnessed or experienced during executions of the protocol. For example,
  a message is a [valid_message] if there exists an execution of the protocol
  in which it is produced.

  We choose here to define valid states and messages together as the
  [valid_state_message_prop]erty, inductively defined over the
  [state * option message] product type,
  as this definition avoids the need of using a mutually recursive definition.

  The inductive definition has three cases:
  - if <<s>> is a [state] with the [initial_state_prop]erty, then <<(s, None)>>
    has the [valid_state_message_prop]erty;
  - if <<m>> is a <<message>> with the [initial_message_prop]erty,
    then <<(>>[s0, Some]<< m)>> has the [valid_state_message_prop]erty;
  - for all [state]s <<s>>, [option]al <<message>> <<om>>, and [label] <<l>>:
    - if there is an (optional) <<message>> <<_om>> such that <<(s, _om)>>
      has the [valid_state_message_prop]erty;
    - and if there is a [state] <<_s>> such that <<(_s, om)>> has the
      [valid_state_message_prop]erty;
    - and if <<l>> [valid] <<(s, om)>>,
    - then [transition] <<l (s, om)>> has the [valid_state_message_prop]erty.
*)

Inductive valid_state_message_prop : state X -> option message -> Prop :=
| valid_initial_state_message
    (s : state X)
    (Hs : initial_state_prop X s)
    (om : option message)
    (Hom : option_initial_message_prop X om)
  : valid_state_message_prop s om
| valid_generated_state_message
    (s : state X)
    (_om : option message)
    (Hps : valid_state_message_prop s _om)
    (_s : state X)
    (om : option message)
    (Hpm : valid_state_message_prop _s om)
    (l : label X)
    (Hv : valid X l (s, om))
    s' om'
    (Ht : transition X l (s, om) = (s', om'))
  : valid_state_message_prop s' om'.

Definition valid_initial_state
  [s : state X] (Hs : initial_state_prop s)
  : valid_state_message_prop s None
  := valid_initial_state_message s Hs None I.

(**
  The [valid_state_prop]erty and the [valid_message_prop]erty are now
  definable as simple projections of the above definition.

  Moreover, we use these derived properties to define the corresponding
  dependent types [valid_state] and [valid_message].
*)

Definition valid_state_prop (s : state X) :=
  exists om : option message, valid_state_message_prop s om.

Definition valid_message_prop (m : message) :=
  exists s : state X, valid_state_message_prop s (Some m).

Definition valid_state : Type :=
  {s : state X | valid_state_prop s}.

Definition valid_message : Type :=
  {m : message | valid_message_prop m}.

Lemma initial_state_is_valid
  (s : state X)
  (Hinitial : initial_state_prop X s) :
  valid_state_prop s.
Proof.
  exists None.
  by apply valid_initial_state_message.
Qed.

Lemma initial_message_is_valid
  (m : message)
  (Hinitial : initial_message_prop X m) :
  valid_message_prop m.
Proof.
  exists (proj1_sig (vs0 X)).
  by apply valid_initial_state_message; [apply proj2_sig |].
Qed.

(**
  As often times we work with optional valid messages, it is convenient
  to define a valid message property for optional messages.
*)

Definition option_valid_message_prop (om : option message) :=
  exists s : state X, valid_state_message_prop s om.

Lemma option_valid_message_None
  : option_valid_message_prop None.
Proof.
  exists (proj1_sig (vs0 X)).
  by apply valid_initial_state_message; [apply proj2_sig |].
Qed.

Lemma option_valid_message_Some
  (m : message)
  (Hpm : valid_message_prop m)
  : option_valid_message_prop (Some m).
Proof.
  by destruct Hpm as [s Hpm]; exists s.
Qed.

Lemma option_initial_message_is_valid
  (om : option message)
  (Hinitial : option_initial_message_prop X om) :
  option_valid_message_prop om.
Proof.
  destruct om.
  - by apply option_valid_message_Some, initial_message_is_valid.
  - by apply option_valid_message_None.
Qed.

(** *** Input validity and input valid transitions

  To specify that a particular (input of a) transition can actually be
  encountered as part of a protocol execution, we define the notions of
  [input_valid]ity and [input_valid_transition].

  Input validity requires that the [valid] predicate holds for the
  given inputs and that they have a [valid_state] and a [valid_message].
*)
Definition input_valid
           (l : label X)
           (som : state X * option message)
  : Prop
  :=
  let (s, om) := som in
     valid_state_prop s
  /\ option_valid_message_prop om
  /\ valid X l (s, om).

(** Input valid transitions are transitions with [input_valid] inputs. *)
Definition input_valid_transition
  (l : label X)
  (som : state X * option message)
  (som' : state X * option message)
  :=
  input_valid l som
  /\ transition X l som = som'.

Definition input_valid_transition_item
  (s : state X)
  (item : transition_item)
  :=
  input_valid_transition (l item) (s, input item) (destination item, output item).

Definition input_valid_transition_preserving
  (R : state X -> state X -> Prop)
  : Prop
  :=
  forall
    (s1 s2 : state X)
    (l : label X)
    (om1 om2 : option message)
    (Hvalid_transition : input_valid_transition l (s1, om1) (s2, om2)),
    R s1 s2.

(** Next three lemmas show the two definitions above are strongly related. *)

Lemma input_valid_transition_valid
  (l : label X)
  (som : state X * option message)
  (som' : state X * option message)
  (Ht : input_valid_transition l som som')
  : input_valid l som.
Proof.
  by destruct Ht.
Qed.

Lemma input_valid_can_transition
  (l : label X)
  (som : state X * option message)
  (Hv : input_valid l som)
  : forall som', transition X l som = som' ->
    input_valid_transition l som som'.
Proof. done. Qed.

Lemma input_valid_transition_iff
  (l : label X)
  (som : state X * option message)
  : input_valid l som
  <-> exists (som' : state X * option message),
        input_valid_transition l som som'.
Proof.
  split.
  - by eexists; apply input_valid_can_transition.
  - intros [som' Hivt].
    by apply input_valid_transition_valid with som'.
Qed.

(**
  The next couple of lemmas relate the two definitions above with
  pre-existing concepts.
*)
Lemma input_valid_transition_origin
      {l : label X}
      {s s' : state X}
      {om om' : option message}
      (Ht : input_valid_transition l (s, om) (s', om'))
  : valid_state_prop s.
Proof.
  by destruct Ht as [[[_om Hp] _] _]; exists _om.
Qed.

Lemma input_valid_transition_destination
      {l : label X}
      {s s' : state X}
      {om om' : option message}
      (Ht : input_valid_transition l (s, om) (s', om'))
  : valid_state_prop s'.
Proof.
  exists om'.
  destruct Ht as [[[_om Hs] [[_s Hom] Hv]] Ht].
  by apply valid_generated_state_message with s _om _s om l.
Qed.

Lemma input_valid_transition_in
      {l : label X}
      {s s' : state X}
      {om om' : option message}
      (Ht : input_valid_transition l (s, om) (s', om'))
  : option_valid_message_prop om.
Proof.
  destruct Ht as [[_ [[_s Hom] _]] _].
  by exists _s.
Qed.

Lemma input_valid_transition_outputs_valid_state_message
      {l : label X}
      {s s' : state X}
      {om om' : option message}
      (Ht : input_valid_transition l (s, om) (s', om'))
    : valid_state_message_prop s' om'.
Proof.
  destruct Ht as [[[_om Hps] [[_s Hpm] Hv]] Ht].
  by apply valid_generated_state_message with s _om _s om l.
Qed.

Lemma input_valid_transition_out
      {l : label X}
      {s s' : state X}
      {om om' : option message}
      (Ht : input_valid_transition l (s, om) (s', om'))
  : option_valid_message_prop om'.
Proof.
  apply input_valid_transition_outputs_valid_state_message in Ht.
  by exists s'.
Qed.

Lemma input_valid_transition_is_valid
      {l : label X}
      {s s' : state X}
      {om om' : option message}
      (Ht : input_valid_transition l (s, om) (s', om'))
  : valid X l (s, om).
Proof.
  by destruct Ht as [[_ [_ Hv]] _].
Qed.

Lemma input_valid_transition_transition
      {l : label X}
      {s s' : state X}
      {om om' : option message}
      (Ht : input_valid_transition l (s, om) (s', om'))
    : transition X l (s, om) = (s', om').
Proof.
  by destruct Ht as [_ Ht].
Qed.

Lemma input_valid_state_message_outputs
  (l : label X)
  (s : state X)
  (om : option message)
  (Hv : input_valid l (s, om))
  s' om'
  (Ht : transition X l (s, om) = (s', om'))
  : valid_state_message_prop s' om'.
Proof.
  destruct Hv as [[_om Hs] [[_s Hom] Hv]].
  by apply valid_generated_state_message with s _om _s om l.
Qed.

(**
  [transition]s are deterministic, i.e. the final state and output message
  are determined by the label, initial state and input message of the
  transition. This is because [transition] is a function.

  Because of the above, [input_valid_transition]s are also deterministic. 
*)

Lemma input_valid_transition_deterministic :
  forall {lbl : label X} {s s1 s2 : state X} {iom oom1 oom2 : option message},
    input_valid_transition lbl (s, iom) (s1, oom1) ->
    input_valid_transition lbl (s, iom) (s2, oom2) ->
      s1 = s2 /\ oom1 = oom2.
Proof.
  by do 2 inversion 1; itauto congruence.
Qed.

(**
  For VLSMs initialized with many initial messages such as
  the [composite_vlsm_induced_projection] or the [pre_loaded_with_all_messages_vlsm],
  the question of whether a [VLSM] [can_emit] a message <<m>> becomes more
  useful than that whether <<m>> is a [valid_message].
*)

Definition option_can_produce
  (s : state X)
  (om : option message)
  :=
  exists
  (som : state X * option message)
  (l : label X),
  input_valid_transition l som (s, om).

Definition can_produce
  (s : state X)
  (m : message)
  := option_can_produce s (Some m).

(** Of course, if a VLSM [can_emit] <<(s, m)>>, then <<(s, m)>> is valid. *)

Lemma option_can_produce_valid
  (s : state X)
  (om : option message)
  (Hm : option_can_produce s om)
  : valid_state_message_prop s om .
Proof.
  destruct Hm as [(s0, om0) [l [[[_om0 Hs0] [[_s0 Hom0] Hv]] Ht]]].
  by apply valid_generated_state_message with s0 _om0 _s0 om0 l.
Qed.

Definition can_produce_valid
  (s : state X)
  (m : message)
  (Hm : can_produce s m)
  : valid_state_message_prop s (Some m)
  := option_can_produce_valid s (Some m) Hm.

Lemma option_can_produce_valid_iff
  (s : state X)
  (om : option message)
  : valid_state_message_prop s om <->
    option_can_produce s om \/ initial_state_prop X s /\ option_initial_message_prop X om.
Proof.
  split.
  - intros Hm; inversion Hm; subst.
    + by right.
    + by left; exists (s1, om0), l0; firstorder.
  - intros [Hem | Him].
    + by apply option_can_produce_valid.
    + by constructor; apply Him.
Qed.

Definition can_produce_valid_iff
  (s : state X)
  (m : message)
  : valid_state_message_prop s (Some m) <->
    can_produce s m \/ initial_state_prop s /\ initial_message_prop m
  := option_can_produce_valid_iff s (Some m).

Definition can_emit
  (m : message)
  :=
  exists
  (som : state X * option message)
  (l : label X)
  (s : state X),
  input_valid_transition l som (s, Some m).

Lemma can_emit_iff
  (m : message)
  : can_emit m <-> exists s, can_produce s m.
Proof.
  split.
  - by intros [som [l [s Ht]]]; exists s, som, l.
  - by intros [s [som [l Ht]]]; exists som, l, s.
Qed.

(** If a VLSM [can_emit] a message <<m>>, then <<m>> is valid. *)
Lemma emitted_messages_are_valid
  (m : message)
  (Hm : can_emit m)
  : valid_message_prop m .
Proof.
  apply can_emit_iff in Hm.
  destruct Hm as [s Hm].
  apply can_produce_valid in Hm.
  by exists s.
Qed.

(** A characterization of valid messages in terms of [can_emit]. *)

Lemma emitted_messages_are_valid_iff
  (m : message)
  : valid_message_prop m <-> initial_message_prop X m \/ can_emit m.
Proof.
  split.
  - intros [s Hm].
    apply can_produce_valid_iff in Hm as [Hgen | [_ Him]].
    + by right; apply can_emit_iff; exists s.
    + by left.
  - intros [Him | Hm].
    + by apply initial_message_is_valid.
    + by apply emitted_messages_are_valid.
Qed.

(** *** Valid state and valid message characterization

  The definition and results below show that the mutually-recursive definitions
  for [valid_state]s and [valid_message]s can be derived from the
  prior definitions.

  The results below offers equivalent characterizations for [valid_state]s
  and [valid_message]s, similar to their recursive definition.
*)

Lemma valid_state_prop_iff :
  forall s' : state X,
    valid_state_prop s'
    <-> (exists is : initial_state X, s' = proj1_sig is)
      \/ exists (l : label X) (som : state X * option message) (om' : option message),
        input_valid_transition l som (s', om').
Proof.
  intros; split.
  - intro Hps'. destruct Hps' as [om' Hs].
    inversion Hs; subst.
    + by left; exists (exist _ _ Hs0).
    + by right; exists l0, (s, om), om'; firstorder.
  - intros [[[s His] Heq] | [l [[s om] [om' [[[_om Hps] [[_s Hpm] Hv]] Ht]]]]]; subst.
    + by exists None; apply valid_initial_state_message.
    + by exists om'; apply valid_generated_state_message with s _om _s om l.
Qed.

(**
  A specialized induction principle for [valid_state_prop].

  Compared to opening the existential and using [valid_state_message_prop_ind],
  this expresses the inductive assumptions simply in terms of
  [input_valid_transition], rather than than having everything exploded
  as [valid_state_message_prop] assumptions over witnesses <<_s>>
  and <<_om>>, and a spurious inductive assumption <<P _s>>.
*)
Lemma valid_state_prop_ind
  (P : state X -> Prop)
  (IHinit : forall (s : state X) (Hs : initial_state_prop X s), P s)
  (IHgen :
    forall (s' : state X) (l : label X) (om om' : option message) (s : state X)
      (Ht : input_valid_transition l (s, om) (s', om')) (Hs : P s),
      P s')
  : forall (s : state X) (Hs : valid_state_prop s), P s.
Proof.
  intros.
  destruct Hs as [om Hs].
  induction Hs.
  - by apply IHinit.
  - by apply (IHgen s' l0 om om' s); firstorder.
Qed.

(** Valid message characterization. *)
Lemma valid_message_prop_iff :
  forall m' : message,
    valid_message_prop m'
    <-> (exists im : initial_message X, m' = proj1_sig im)
      \/ exists (l : label X) (som : state X * option message) (s' : state X),
        input_valid_transition l som (s', Some m').
Proof.
  intros; split.
  - intros [s' Hpm'].
    inversion Hpm'; subst.
    + by left; exists (exist _ m' Hom).
    + by right; exists l0, (s, om), s'; firstorder.
  - intros [[[s His] Heq] | [l [[s om] [s' [[[_om Hps] [[_s Hpm] Hv]] Ht]]]]]; subst.
    + by apply initial_message_is_valid.
    + by exists s'; apply valid_generated_state_message with s _om _s om l.
Qed.

(** ** Trace Properties

  Note that it is unnecessary to specify the source state of the transition,
  as it is implied by the preceding [transition_item] (or by the <<start>> state,
  if such an item doesn't exist).

  We will now split our groundwork for defining traces into the finite case and
  the infinite case.
*)

(** *** Finite valid traces

  A [finite_valid_trace_from] a [state] <<start>> is a pair <<(start, steps)>> where <<steps>>
  is a list of [transition_item]s, and is inductively defined by:
  - <<(s, [])>> is a [finite_valid_trace_from] <<s>> if <<s>> is valid
  - if there is an [input_valid_transition] <<l (s', iom) (s, oom)>>

    and if <<(s, steps)>> is a [valid_trace_from] <<s>>

    then <<(s', ({| l := l; input := iom; destination := s; output := oom |} :: steps)>>
    is a [finite_valid_trace_from] <<s'>>.

  Note that the definition is given such that it extends an existing trace by
  adding a transition to its front.
  The reason for this choice is to have this definition be similar to the one
  for infinite traces, which can only be extended at the front.
*)

Inductive finite_valid_trace_from : state X -> list transition_item -> Prop :=
| finite_valid_trace_from_empty : forall (s : state X)
    (Hs : valid_state_prop s),
    finite_valid_trace_from s []
| finite_valid_trace_from_extend : forall  (s : state X) (tl : list transition_item)
    (Htl : finite_valid_trace_from s tl)
    (s' : state X) (iom oom : option message) (l : label X)
    (Ht : input_valid_transition l (s', iom) (s, oom)),
    finite_valid_trace_from  s' ({| l := l; input := iom; destination := s; output := oom |} :: tl).

Definition finite_valid_trace_singleton :
  forall {l : label X} {s s' : state X} {iom oom : option message},
    input_valid_transition l (s, iom) (s', oom) ->
    finite_valid_trace_from  s ({| l := l; input := iom; destination := s'; output := oom |} :: [])
  := fun l s s' iom oom Hptrans =>
       finite_valid_trace_from_extend s' []
           (finite_valid_trace_from_empty s' (input_valid_transition_destination Hptrans))
           _ _ _ _ Hptrans.

(**
  To complete our definition of a finite valid trace, we must also guarantee
  that <<start>> is an initial state according to the protocol.
*)
Definition finite_valid_trace (s : state X) (ls : list (transition_item X)) : Prop :=
  finite_valid_trace_from s ls /\ initial_state_prop X s.

(**
  In the remainder of the section we provide various results allowing us to
  prove or decompose the above properties in proofs.
*)

(**
  [finite_valid_trace_empty] is a bit more useful than the small proof suggests,
  because applying it always leaves just one subgoal.

  The tactical <<by split; [constructor; apply initial_state_is_valid |]>>
  only works if the premise is available in the context, which may
  require an <<assert>> and writing out the full VLSM and state expressions
  as part of the proof script.
*)
Lemma finite_valid_trace_empty (s : state X) :
  initial_state_prop X s ->
  finite_valid_trace s [].
Proof.
  by split; [constructor; apply initial_state_is_valid |].
Qed.

Lemma finite_valid_trace_first_valid_transition
      (s : state X)
      (tr : list transition_item)
      (te : transition_item)
      (Htr : finite_valid_trace_from s (te :: tr))
  : input_valid_transition (l te) (s, input te) (destination te, output te).
Proof. by inversion Htr. Qed.

Lemma finite_valid_trace_first_pstate
  (s : state X)
  (tr : list transition_item)
  (Htr : finite_valid_trace_from s tr)
  : valid_state_prop s.
Proof.
  by inversion Htr; subst; [| apply Ht].
Qed.

Lemma finite_valid_trace_tail
      (s : state X)
      (tr : list transition_item)
      (te : transition_item)
      (Htr : finite_valid_trace_from s (te :: tr))
  : finite_valid_trace_from (destination te) tr.
Proof. by inversion Htr. Qed.

Lemma finite_valid_trace_last_pstate
  (s : state X)
  (tr : list transition_item)
  (Htr : finite_valid_trace_from s tr)
  : valid_state_prop (finite_trace_last s tr).
Proof.
  generalize dependent s.
  induction tr; intros.
  - by apply finite_valid_trace_first_pstate with [].
  - apply finite_valid_trace_tail in Htr.
    apply IHtr in Htr.
    replace
      (finite_trace_last s (a :: tr))
      with (finite_trace_last (destination a) tr)
    ; [done |].
    unfold finite_trace_last.
    by rewrite map_cons, unroll_last.
Qed.

Lemma input_valid_transition_to
      (s : state X)
      (tr : list transition_item)
      (tr1 tr2 : list transition_item)
      (te : transition_item)
      (Htr : finite_valid_trace_from s tr)
      (Heq : tr = tr1 ++ [te] ++ tr2)
      (lst1 := finite_trace_last s tr1)
  : input_valid_transition (l te) (lst1, input te) (destination te, output te).
Proof.
  generalize dependent s. generalize dependent tr.
  induction tr1.
  - by intros tr [= ->] s; inversion 1.
  - specialize (IHtr1 (tr1 ++ [te] ++ tr2) eq_refl).
    intros tr Heq is Htr; subst. inversion Htr; subst.
    rewrite finite_trace_last_cons.
    by apply IHtr1.
Qed.

Lemma finite_valid_trace_consecutive_valid_transition
      (s : state X)
      (tr : list transition_item)
      (tr1 tr2 : list transition_item)
      (te1 te2 : transition_item)
      (Htr : finite_valid_trace_from s tr)
      (Heq : tr = tr1 ++ [te1; te2] ++ tr2)
  : input_valid_transition (l te2) (destination te1, input te2) (destination te2, output te2).
Proof.
  change ([te1; te2] ++ tr2) with ([te1] ++ [te2] ++ tr2) in Heq.
  rewrite app_assoc in Heq.
  specialize (input_valid_transition_to s tr (tr1 ++ [te1]) tr2 te2 Htr Heq)
    as Ht.
  by rewrite finite_trace_last_is_last in Ht.
Qed.

Lemma valid_trace_output_is_valid
  (is : state X)
  (tr : list transition_item)
  (Htr : finite_valid_trace_from is tr)
  (m : message)
  (Houtput : trace_has_message (field_selector output) m tr)
  : valid_message_prop m.
Proof.
  revert is Htr.
  induction Houtput as [item tr' Hm | item tr']; intros; inversion Htr; subst.
  - simpl in Hm.
    subst.
    by apply input_valid_transition_out in Ht.
  - by apply (IHHoutput s).
Qed.

Lemma valid_trace_input_is_valid
  (is : state X)
  (tr : list transition_item)
  (Htr : finite_valid_trace_from is tr)
  (m : message)
  (Hinput : trace_has_message (field_selector input) m tr)
  : valid_message_prop m.
Proof.
  revert is Htr.
  induction Hinput as [item tr' Hm | item tr']; intros
  ; inversion Htr as [| s _tr'  Htr' _is iom oom l Ht]; subst.
  - simpl in Hm.
    subst.
    by apply input_valid_transition_in in Ht.
  - by apply (IHHinput s).
Qed.

Lemma valid_trace_observed_is_valid
  (is : state X)
  (tr : list transition_item)
  (Htr : finite_valid_trace_from is tr)
  (m : message)
  (Hobserved : trace_has_message item_sends_or_receives m tr)
  : valid_message_prop m.
Proof.
  by apply trace_has_message_observed_iff in Hobserved as [Hm | Hm]
  ; revert Htr m Hm; [apply valid_trace_input_is_valid | apply valid_trace_output_is_valid].
Qed.

Lemma first_transition_valid
  (s : state X)
  (te : transition_item)
  : finite_valid_trace_from s [te] <->
    input_valid_transition (l te) (s, input te) (destination te, output te).

Proof.
  split; [by inversion 1 |].
  destruct te. simpl. intro Ht.
  apply input_valid_transition_destination in Ht as Hdestination0.
  by constructor; [constructor |].
Qed.

Lemma extend_right_finite_trace_from
  (s1 : state X)
  (ts : list transition_item)
  (Ht12 : finite_valid_trace_from s1 ts)
  (l3 : label X)
  (s2 := finite_trace_last s1 ts)
  (iom3 : option message)
  (s3 : state X)
  (oom3 : option message)
  (Hv23 : input_valid_transition l3 (s2, iom3) (s3, oom3))
  : finite_valid_trace_from s1
      (ts ++ [{| l := l3; destination := s3; input := iom3; output := oom3 |}]).
Proof.
  induction Ht12.
  - by apply finite_valid_trace_singleton.
  - rewrite <- app_comm_cons.
    apply finite_valid_trace_from_extend; [| done].
    simpl in IHHt12. apply IHHt12.
    unfold s2 in *; clear s2.
    by rewrite finite_trace_last_cons in Hv23.
Qed.

(**
  We can now prove several general properties of [finite_valid_trace]s. For example,
  the following lemma states that given two such traces, such that the latter's starting state
  is equal to the former's last state, it is possible to _concatenate_ them into a single
  [finite_valid_trace].
*)

Lemma finite_valid_trace_from_app_iff
  (s : state X) (ls ls' : list transition_item) (s' := finite_trace_last s ls)
  : finite_valid_trace_from s ls /\ finite_valid_trace_from s' ls'
    <->
    finite_valid_trace_from s (ls ++ ls').
Proof.
  subst s'.
  revert s.
  induction ls; intro s.
  - rewrite finite_trace_last_nil. simpl.
    by itauto (eauto using finite_valid_trace_first_pstate, finite_valid_trace_from_empty).
  - rewrite finite_trace_last_cons. simpl.
    specialize (IHls (destination a)).
    split.
    + intros [Hal Hl'].
      inversion Hal; subst; simpl in *.
      by constructor; [apply IHls |].
    + inversion 1; subst; simpl in *.
      apply IHls in Htl as [Hl Hl'].
      by split; [constructor |].
Qed.

Lemma finite_valid_trace_from_rev_ind
  (P : state X -> list transition_item -> Prop)
  (Hempty : forall s,
    valid_state_prop s -> P s nil)
  (Hextend : forall s tr,
    finite_valid_trace_from s tr ->
    P s tr ->
    forall sf iom oom l
    (Hx : input_valid_transition l (finite_trace_last s tr, iom) (sf, oom)),
    let x := {| l := l; input := iom; destination := sf; output := oom |} in
    P s (tr++[x])) :
  forall s tr,
    finite_valid_trace_from s tr ->
    P s tr.
Proof.
  induction tr using rev_ind; intro Htr.
  - by inversion Htr; apply Hempty; congruence.
  - apply finite_valid_trace_from_app_iff in Htr.
    destruct Htr as [Htr Hx].
    destruct x; apply (Hextend _ _ Htr (IHtr Htr)).
    by inversion Hx; congruence.
Qed.

Lemma finite_valid_trace_rev_ind
  (P : state X -> list (transition_item X) -> Prop)
  (Hempty : forall si,
    initial_state_prop X si -> P si nil)
  (Hextend : forall si tr,
    finite_valid_trace si tr ->
    P si tr ->
    forall sf iom oom l
    (Hx : input_valid_transition l (finite_trace_last si tr, iom) (sf, oom)),
    let x := {| l := l; input := iom; destination := sf; output := oom |} in
    P si (tr++[x])) :
  forall si tr,
    finite_valid_trace si tr ->
    P si tr.
Proof.
  intros si tr [Htr Hinit].
  induction Htr using finite_valid_trace_from_rev_ind.
  - by apply Hempty.
  - by apply Hextend; auto.
Qed.

(**
  Several other lemmas in this vein are necessary for proving results regarding
  traces.
*)

Lemma finite_valid_trace_from_prefix
  (s : state X)
  (ls : list transition_item)
  (Htr : finite_valid_trace_from s ls)
  (n : nat)
  : finite_valid_trace_from s (list_prefix ls n).
Proof.
  specialize (list_prefix_suffix ls n); intro Hdecompose.
  rewrite <- Hdecompose in Htr.
  by apply finite_valid_trace_from_app_iff in Htr as [Hpr _].
Qed.

Lemma finite_valid_trace_from_suffix
  (s : state X)
  (ls : list transition_item)
  (Htr : finite_valid_trace_from s ls)
  (n : nat)
  (nth : state X)
  (Hnth : finite_trace_nth s ls n = Some nth)
  : finite_valid_trace_from nth (list_suffix ls n).
Proof.
  rewrite <- (list_prefix_suffix ls n) in Htr.
  apply finite_valid_trace_from_app_iff in Htr.
  destruct Htr as [_ Htr].
  replace (finite_trace_last s (list_prefix ls n)) with nth in Htr; [done |].
  destruct n.
  - rewrite finite_trace_nth_first in Hnth.
    by destruct ls; cbn; congruence.
  - unfold finite_trace_last.
    rewrite list_prefix_map.
    by apply list_prefix_nth_last.
Qed.

Lemma finite_valid_trace_from_segment
  (s : state X)
  (ls : list transition_item)
  (Htr : finite_valid_trace_from s ls)
  (n1 n2 : nat)
  (Hle : n1 <= n2)
  (n1th : state X)
  (Hnth : finite_trace_nth s ls n1 = Some n1th)
  : finite_valid_trace_from n1th (list_segment ls n1 n2).
Proof.
  apply finite_valid_trace_from_suffix with s.
  - by apply finite_valid_trace_from_prefix.
  - destruct n1; [done |].
    unfold finite_trace_nth in Hnth |- *.
    simpl in Hnth |- *.
    by rewrite list_prefix_map, list_prefix_nth.
Qed.

Lemma can_produce_from_valid_trace si tr
  (Htr : finite_valid_trace_from si tr)
  : forall item, item ∈ tr ->
    option_can_produce (destination item) (output item).
Proof.
  intros item Hitem.
  apply elem_of_list_split in Hitem as (l1 & l2 & Heq).
  eexists _, _.
  by eapply input_valid_transition_to; cbn.
Qed.

Lemma can_emit_from_valid_trace
  (si : state X)
  (m : message)
  (tr : list transition_item)
  (Htr : finite_valid_trace si tr)
  (Hm : trace_has_message (field_selector output) m tr) :
  can_emit m.
Proof.
  apply can_emit_iff.
  setoid_rewrite Exists_exists in Hm.
  destruct Hm as (item & Hitem & Houtput).
  exists (destination item).
  unfold can_produce; rewrite <- Houtput.
  by eapply can_produce_from_valid_trace; [apply Htr |].
Qed.

(** ** Finite [valid_trace]s with a final state

  It is often necessary to refer to know ending state of a [finite_valid_trace_from].
  This is either the [destination] of the [last] [transition_item] in the trace, or
  the starting state.

  To avoid repeating reasoning about [last], we define variants of
  [finite_valid_trace_from] and [finite_valid_trace]
  that include the final state, and give appropriate induction principles.

  The final state of a finite portion of a valid trace.
  This is defined over [finite_valid_trace_from] because
  an initial state is necessary in case <<tr>> is empty,
  and this allows the definition to have only one non-implicit
  parameter.
*)

Inductive finite_valid_trace_from_to : state X -> state X -> list transition_item -> Prop :=
| finite_valid_trace_from_to_empty : forall (s : state X)
    (Hs : valid_state_prop s),
    finite_valid_trace_from_to s s []
| finite_valid_trace_from_to_extend : forall  (s f : state X) (tl : list transition_item)
    (Htl : finite_valid_trace_from_to s f tl)
    (s' : state X) (iom oom : option message) (l : label X)
    (Ht : input_valid_transition l (s', iom) (s, oom)),
    finite_valid_trace_from_to s' f
      ({| l := l; input := iom; destination := s; output := oom |} :: tl).

Lemma finite_valid_trace_from_to_singleton s s' iom oom l
    : input_valid_transition l (s, iom) (s', oom) ->
      finite_valid_trace_from_to s s' [{| l := l; input := iom; destination := s'; output := oom |}].
Proof.
  intro Ht.
  constructor; [| done].
  constructor.
  by apply input_valid_transition_destination in Ht.
Qed.

Lemma finite_valid_trace_from_to_forget_last
      s f tr : finite_valid_trace_from_to s f tr -> finite_valid_trace_from s tr.
Proof.
  by induction 1; constructor; auto.
Qed.

Lemma finite_valid_trace_from_to_last
      s f tr : finite_valid_trace_from_to s f tr -> finite_trace_last s tr = f.
Proof.
  induction 1.
  - by apply finite_trace_last_nil.
  - by rewrite finite_trace_last_cons.
Qed.

Lemma finite_valid_trace_from_add_last
      s f tr :
  finite_valid_trace_from s tr ->
  finite_trace_last s tr = f ->
  finite_valid_trace_from_to s f tr.
Proof.
  intro Hfrom.
  induction Hfrom.
  - by rewrite finite_trace_last_nil; intros <-; constructor; auto.
  - by rewrite finite_trace_last_cons; intros <-; constructor; auto.
Qed.

Lemma finite_valid_trace_from_to_first_pstate
      s f tr : finite_valid_trace_from_to s f tr -> valid_state_prop s.
Proof.
  intro Htr.
  by apply finite_valid_trace_from_to_forget_last,
           finite_valid_trace_first_pstate in Htr.
Qed.

Lemma finite_valid_trace_from_to_last_pstate
      s f tr : finite_valid_trace_from_to s f tr -> valid_state_prop f.
Proof.
  intro Htr.
  rewrite <- (finite_valid_trace_from_to_last _ _ _ Htr).
  apply finite_valid_trace_last_pstate.
  by apply finite_valid_trace_from_to_forget_last in Htr.
Qed.

Lemma finite_valid_trace_from_to_app
  (m s f : state X) (ls ls' : list transition_item)
  : finite_valid_trace_from_to s m ls
    -> finite_valid_trace_from_to m f ls'
    -> finite_valid_trace_from_to s f (ls ++ ls').
Proof.
  by intros Hl Hl'; induction Hl; [| constructor; auto].
Qed.

Lemma finite_valid_trace_from_to_app_split
  (s f : state X) (ls ls' : list transition_item)
  : finite_valid_trace_from_to s f (ls ++ ls') ->
    let m := finite_trace_last s ls in
    finite_valid_trace_from_to s m ls
    /\ finite_valid_trace_from_to m f ls'.
Proof.
  revert s; induction ls; intros s; simpl.
  - rewrite finite_trace_last_nil.
    intro Htr. split; [| done].
    apply finite_valid_trace_from_to_first_pstate in Htr.
    by constructor.
  - rewrite finite_trace_last_cons.
    inversion 1; subst; simpl in *.
    apply IHls in Htl as [].
    by auto using finite_valid_trace_from_to_extend.
Qed.

Definition finite_valid_trace_init_to si sf tr : Prop
  := finite_valid_trace_from_to si sf tr
      /\ initial_state_prop X si.

Lemma finite_valid_trace_init_add_last si sf tr :
  finite_valid_trace si tr ->
  finite_trace_last si tr = sf ->
  finite_valid_trace_init_to si sf tr.
Proof.
  intros [Htr Hinit] Hf.
  split; eauto using finite_valid_trace_from_add_last.
Qed.

Lemma finite_valid_trace_init_to_forget_last si sf tr :
  finite_valid_trace_init_to si sf tr ->
  finite_valid_trace si tr.
Proof.
  intros [Hinit Htr].
  split; eauto using finite_valid_trace_from_to_forget_last.
Qed.

Lemma finite_valid_trace_init_to_last si sf tr :
  finite_valid_trace_init_to si sf tr ->
  finite_trace_last si tr = sf.
Proof.
  intros [Htr _].
  eauto using finite_valid_trace_from_to_last.
Qed.

Lemma extend_right_finite_trace_from_to
  (s1 s2 : state X)
  (ts : list transition_item)
  (Ht12 : finite_valid_trace_from_to s1 s2 ts)
  (l3 : label X)
  (iom3 : option message)
  (s3 : state X)
  (oom3 : option message)
  (Hv23 : input_valid_transition l3 (s2, iom3) (s3, oom3))
  : finite_valid_trace_from_to s1 s3
      (ts ++ [{| l := l3; destination := s3; input := iom3; output := oom3 |}]).
Proof.
  induction Ht12.
  - by apply finite_valid_trace_from_to_singleton.
  - rewrite <- app_comm_cons.
    by apply finite_valid_trace_from_to_extend; auto.
Qed.

Lemma finite_valid_trace_from_to_rev_ind
  (P : state X -> state X -> list transition_item -> Prop)
  (Hempty : forall si
    (Hsi : valid_state_prop si),
    P si si nil)
  (Hextend : forall si s tr
    (IHtr : P si s tr)
    (Htr : finite_valid_trace_from_to si s tr)
    sf iom oom l
    (Ht : input_valid_transition l (s, iom) (sf, oom)),
    P si sf (tr++[{| l := l; input := iom; destination := sf; output := oom |}])) :
  forall si sf tr,
    finite_valid_trace_from_to si sf tr ->
    P si sf tr.
Proof.
  intros si sf tr Htr.
  revert sf Htr.
  induction tr using rev_ind;
  intros sf Htr.
  - by inversion Htr; subst; apply Hempty.
  - apply finite_valid_trace_from_to_app_split in Htr.
    destruct Htr as [Htr Hstep].
    inversion Hstep; subst.
    inversion Htl; subst.
    revert Ht.
    apply Hextend; [| done].
    by apply IHtr.
Qed.

Lemma finite_valid_trace_init_to_rev_ind
  (P : state X -> state X -> list (transition_item X) -> Prop)
  (Hempty : forall si
    (Hsi : initial_state_prop X si),
    P si si nil)
  (Hextend : forall si s tr
    (IHtr : P si s tr)
    (Htr : finite_valid_trace_init_to si s tr)
    sf iom oom l
    (Ht : input_valid_transition l (s, iom) (sf, oom)),
    P si sf (tr++[{| l := l; input := iom; destination := sf; output := oom |}])) :
  forall si sf tr,
    finite_valid_trace_init_to si sf tr ->
    P si sf tr.
Proof.
  intros si sf tr Htr.
  destruct Htr as [Htr Hinit].
  induction Htr using finite_valid_trace_from_to_rev_ind.
  - by apply Hempty.
  - by apply Hextend with s; auto.
Qed.

(**
  An inductive valid trace property which also identifies the final message.

  As shown by the [finite_valid_trace_init_to_emit_valid_state_message]  and
  [finite_valid_trace_init_to_emit_valid_state_message_rev] lemmas below, this definition
  is the trace-equivalent of the [valid_state_message_prop]erty.

  This inductive property is reflecting that fact that a that <<valid_state_message_prop (s, om)>>
  holds only if <<s>> and <<om>> are the final state and output of an initial valid
  trace, or a pair of an initial state and option-initial message.
  It follows the inductive structure of <<valid_state_message_prop>>, but augments every node of
  the tree with such an exhibiting trace.

  Its main benefit is that when performing induction over it, one can also use the
  induction hypothesis for the (trace generating the) message being received.

  Although this definition could be used directly, we prefer to use it to derive
  a stronger induction principle ([finite_valid_trace_init_to_rev_strong_ind])
  over [finite_valid_trace_init_to] traces.
*)
Inductive finite_valid_trace_init_to_emit
  : state X -> state X -> option message -> list (transition_item X) -> Prop :=
| finite_valid_trace_init_to_emit_empty : forall (is : state X) (om : option message)
    (His : initial_state_prop X is)
    (Him : option_initial_message_prop X om),
    finite_valid_trace_init_to_emit is is om []
| finite_valid_trace_init_to_emit_extend
    : forall
      (is s : state X) (_om : option message) (tl : list (transition_item X))
      (Hs : finite_valid_trace_init_to_emit is s _om tl)
      (iom_is iom_s : state X) (iom : option message) (iom_tl : list (transition_item X))
      (Hiom : finite_valid_trace_init_to_emit iom_is iom_s iom iom_tl)
      (l : label X)
      (Hv : valid X l (s, iom))
      (s' : state X) (oom : option message)
      (Ht : transition X l (s, iom) = (s', oom)),
      finite_valid_trace_init_to_emit is s' oom
        (tl ++ [{| l := l; input := iom; destination := s'; output := oom |}]).

Lemma finite_valid_trace_init_to_emit_initial_state
  (is f : state X) (om : option message) (tl : list (transition_item X))
  (Htl : finite_valid_trace_init_to_emit is f om tl)
  : initial_state_prop X is.
Proof. by induction Htl. Qed.

(**
  A property characterizing the "emit" message of [finite_valid_trace_init_to_emit].

  There are two cases: (1) either the trace is empty, and then we require
  the message to be initial; or (2) the trace is not empty, and the message
  is the output of the last transition.
*)
Definition empty_initial_message_or_final_output
  (tl : list (transition_item X)) (om : option message) : Prop.
Proof.
  destruct (has_last_or_null tl) as [[_ [item _]] | _].
  - exact (output item  = om).
  - exact (option_initial_message_prop X om).
Defined.

Lemma finite_valid_trace_init_to_emit_output
  (s f : state X) (om : option message) (tl : list transition_item)
  (Htl : finite_valid_trace_init_to_emit s f om tl)
  : empty_initial_message_or_final_output tl om.
Proof.
  unfold empty_initial_message_or_final_output.
  destruct_list_last tl tl' item Heqtl.
  - inversion Htl; [done |].
    by destruct tl0; simpl in *; congruence.
  - rewrite <- Heqtl in Htl.
    inversion Htl; [by destruct tl'; simpl in *; congruence |].
    revert Heqtl; subst; intro Heqtl.
    by apply app_inj_tail, proj2 in Heqtl; subst.
Qed.

Lemma finite_valid_trace_init_to_emit_valid_state_message
  (s f : state X) (om : option message) (tl : list transition_item)
  (Htl : finite_valid_trace_init_to_emit s f om tl)
  : valid_state_message_prop f om.
Proof.
  induction Htl.
  - by apply valid_initial_state_message.
  - by apply valid_generated_state_message with s _om iom_s iom l0.
Qed.

Lemma finite_valid_trace_init_to_emit_valid_state_message_rev
  f om
  (Hp : valid_state_message_prop f om)
  : exists (s : state X) (tl : list transition_item),
    finite_valid_trace_init_to_emit s f om tl.
Proof.
  induction Hp.
  - by exists s, []; constructor.
  - destruct IHHp1 as [is [tl Hs]].
    destruct IHHp2 as [om_is [om_tl Hom]].
    eexists; eexists.
    by apply (finite_valid_trace_init_to_emit_extend _ _ _ _ Hs _ _ _ _ Hom _ Hv _ _ Ht).
Qed.

Lemma finite_valid_trace_init_to_emit_forget_emit
  (s f : state X) (_om : option message) (tl : list transition_item)
  (Htl : finite_valid_trace_init_to_emit s f _om tl)
  : finite_valid_trace_init_to s f tl.
Proof.
  apply finite_valid_trace_init_to_emit_initial_state in Htl as Hinit.
  split; [| done].
  clear Hinit.
  induction Htl.
  - by constructor; apply initial_state_is_valid.
  - apply finite_valid_trace_from_to_app with s; [done |].
    apply finite_valid_trace_from_to_singleton.
    apply finite_valid_trace_init_to_emit_valid_state_message in Htl1.
    apply finite_valid_trace_init_to_emit_valid_state_message in Htl2.
    by firstorder.
Qed.

Lemma finite_valid_trace_init_to_add_emit
  (s f : state X) (tl : list transition_item)
  (Htl : finite_valid_trace_init_to s f tl)
  : finite_valid_trace_init_to_emit s f (finite_trace_last_output tl) tl.
Proof.
  induction Htl using finite_valid_trace_init_to_rev_ind; [by constructor |].
  rewrite finite_trace_last_output_is_last. simpl.
  destruct Ht as [[_ [[_s Hiom] Hv]] Ht].
  destruct (finite_valid_trace_init_to_emit_valid_state_message_rev _ _ Hiom)
    as [iom_s [iom_tr Hiom_tr]].
  by apply (finite_valid_trace_init_to_emit_extend _ _ _ _ IHHtl _ _ _ _ Hiom_tr _ Hv _ _ Ht).
Qed.

(**
  Inspired by [finite_valid_trace_init_to_add_emit], we can derive
  an induction principle for [finite_valid_trace_init_to] stronger than
  [finite_valid_trace_init_to_rev_ind], which allows the induction hypothesis
  to be used for the trace generating the message received in the last transition.
*)
Lemma finite_valid_trace_init_to_rev_strong_ind
  (P : state X -> state X -> list (transition_item X) -> Prop)
  (Hempty : forall is
    (His : initial_state_prop X is),
    P is is nil)
  (Hextend : forall is s tr
    (IHs : P is s tr)
    (Hs : finite_valid_trace_init_to is s tr)
    iom iom_si iom_s iom_tr
    (Heqiom : empty_initial_message_or_final_output iom_tr iom)
    (IHiom : P iom_si iom_s iom_tr)
    (Hiom : finite_valid_trace_init_to iom_si iom_s iom_tr)
    sf oom l
    (Ht : input_valid_transition l (s, iom) (sf, oom)),
    P is sf (tr++[{| l := l; input := iom; destination := sf; output := oom |}]))
  : forall si sf tr,
    finite_valid_trace_init_to si sf tr ->
    P si sf tr.
Proof.
  intros is sf tr Htr.
  apply finite_valid_trace_init_to_add_emit in Htr.
  remember (finite_trace_last_output tr) as om. clear Heqom.
  induction Htr.
  - by apply Hempty.
  - assert (Hivt : input_valid_transition l0 (s, iom) (s', oom)).
    {
      apply finite_valid_trace_init_to_emit_valid_state_message in Htr1.
      apply finite_valid_trace_init_to_emit_valid_state_message in Htr2.
      by firstorder.
    }
    apply finite_valid_trace_init_to_emit_output in Htr2 as Houtput.
    apply finite_valid_trace_init_to_emit_forget_emit in Htr1.
    apply finite_valid_trace_init_to_emit_forget_emit in Htr2.
    by apply (Hextend _ _ _ IHHtr1 Htr1 _ _ _ _ Houtput IHHtr2 Htr2 _ _ _ Hivt).
Qed.

(** *** Infinite protocol traces

  We now define [infinite_valid_trace]s. The definitions
  resemble their finite counterparts, adapted to the technical
  necessities of defining infinite objects. Notably, <<steps>> is
  stored as a stream, as opposed to a list.
*)

CoInductive infinite_valid_trace_from :
  state X -> Stream transition_item -> Prop :=
| infinite_valid_trace_from_extend : forall  (s : state X) (tl : Stream transition_item)
    (Htl : infinite_valid_trace_from s tl)
    (s' : state X) (iom oom : option message) (l : label X)
    (Ht : input_valid_transition l (s', iom) (s, oom)),
    infinite_valid_trace_from  s'
      (Cons {| l := l; input := iom; destination := s; output := oom |}  tl).

Definition infinite_valid_trace (s : state X) (st : Stream (transition_item X))
  := infinite_valid_trace_from s st /\ initial_state_prop X s.

(**
  As for the finite case, the following lemmas help decompose teh above
  definitions, mostly reducing them to properties about their finite segments.
*)
Lemma infinite_valid_trace_consecutive_valid_transition
      (is : state X)
      (tr tr2 : Stream transition_item)
      (tr1 : list transition_item)
      (te1 te2 : transition_item)
      (Htr : infinite_valid_trace_from is tr)
      (Heq : tr = stream_app (tr1 ++ [te1; te2]) tr2)
  : input_valid_transition (l te2) (destination te1, input te2) (destination te2, output te2).
Proof.
  generalize dependent is. generalize dependent tr.
  induction tr1.
  - by cbn; intros tr -> is Htr; inversion Htr; inversion Htl; subst.
  - specialize (IHtr1 (stream_app (tr1 ++ [te1; te2]) tr2) eq_refl).
    intros tr Heq is Htr; subst; inversion Htr; subst.
    by apply (IHtr1 s Htl).
Qed.

Lemma infinite_valid_trace_from_app_iff
  (s : state X)
  (ls : list transition_item)
  (ls' : Stream transition_item)
  (s' := finite_trace_last s ls)
  : finite_valid_trace_from s ls /\ infinite_valid_trace_from s' ls'
    <->
    infinite_valid_trace_from s (stream_app ls ls').
Proof.
  intros. generalize dependent ls'. generalize dependent s.
  induction ls; intros; split.
  - by destruct 1.
  - simpl; intros Hls'; split; [| done].
    constructor; inversion Hls'.
    by apply (input_valid_transition_origin Ht).
  - simpl. intros [Htr Htr'].
    destruct a. apply infinite_valid_trace_from_extend.
    + apply IHls. inversion Htr. split; [by apply Htl |].
      unfold s' in Htr'.
      by rewrite finite_trace_last_cons in Htr'.
    + by inversion Htr; apply Ht.
  - inversion 1; subst.
    apply (IHls s1 ls') in Htl as []; split.
    + by constructor.
    + by unfold s'; rewrite finite_trace_last_cons.
Qed.

Lemma infinite_valid_trace_from_prefix
  (s : state X)
  (ls : Stream transition_item)
  (Htr : infinite_valid_trace_from s ls)
  (n : nat)
  : finite_valid_trace_from s (stream_prefix ls n).
Proof.
  specialize (stream_prefix_suffix ls n); intro Hdecompose.
  rewrite <- Hdecompose in Htr.
  by apply infinite_valid_trace_from_app_iff in Htr as [Hpr _].
Qed.

Lemma infinite_valid_trace_from_prefix_rev
  (s : state X)
  (ls : Stream transition_item)
  (Hpref : forall n : nat, finite_valid_trace_from s (stream_prefix ls n))
  : infinite_valid_trace_from s ls.
Proof.
  revert s ls Hpref.
  cofix Hls.
  intros s (a, ls) Hpref.
  assert (Hpref0 := Hpref 1).
  inversion Hpref0; subst.
  constructor; [| done].
  apply Hls.
  intro n.
  specialize (Hpref (S n)).
  by inversion Hpref; subst.
Qed.

Lemma infinite_valid_trace_from_EqSt :
  forall s tl1 tl2,
    EqSt tl1 tl2 -> infinite_valid_trace_from s tl1 -> infinite_valid_trace_from s tl2.
Proof.
  intros s tl1 tl2 Heq Htl1.
  apply infinite_valid_trace_from_prefix_rev.
  intro n.
  rewrite <- (stream_prefix_EqSt _ _ Heq n).
  by apply infinite_valid_trace_from_prefix.
Qed.

Lemma infinite_valid_trace_from_segment
  (s : state X)
  (ls : Stream transition_item)
  (Htr : infinite_valid_trace_from s ls)
  (n1 n2 : nat)
  (Hle : n1 <= n2)
  (n1th := Str_nth n1 (Cons s (Streams.map destination ls)))
  : finite_valid_trace_from n1th (stream_segment ls n1 n2).
Proof.
  apply finite_valid_trace_from_suffix with s.
  - by apply infinite_valid_trace_from_prefix.
  - destruct n1; [done |].
    subst n1th; unfold finite_trace_nth; cbn.
    by rewrite stream_prefix_map, stream_prefix_nth.
Qed.

(** *** Valid traces

  Finally, we define [Trace] as a sum-type of its finite/infinite variants.
  It inherits some previously introduced definitions, culminating with the
  [valid_trace].
*)

Definition valid_trace_from_prop (tr : Trace) : Prop :=
  match tr with
  | Finite s ls => finite_valid_trace_from s ls
  | Infinite s sm => infinite_valid_trace_from s sm
  end.

Definition valid_trace_prop (tr : Trace) : Prop :=
  match tr with
  | Finite s ls => finite_valid_trace s ls
  | Infinite s sm => infinite_valid_trace s sm
  end.

Definition valid_trace : Type :=
  { tr : Trace | valid_trace_prop tr}.

Lemma valid_trace_from
  (tr : Trace)
  (Htr : valid_trace_prop tr)
  : valid_trace_from_prop tr.
Proof. by destruct tr, Htr. Qed.

Lemma valid_trace_initial
  (tr : Trace)
  (Htr : valid_trace_prop tr)
  : initial_state_prop X (trace_first tr).
Proof. by destruct tr, Htr. Qed.

Lemma valid_trace_from_iff
  (tr : Trace)
  : valid_trace_prop tr
  <-> valid_trace_from_prop tr /\ initial_state_prop X (trace_first tr).
Proof.
  split.
  - intro Htr; split.
    + by apply valid_trace_from.
    + by apply valid_trace_initial.
  - by destruct tr; cbn; intros [Htr Hinit].
Qed.

(**
  Having defined [valid_trace]s, we now connect them to valid states
  and messages, in the following sense: for each state-message pair (<<s>>, <<m>>)
  that has the [valid_state_message_prop]erty, there exists a [valid_trace] which ends
  in <<s>> by outputting <<m>>
*)

Lemma valid_state_message_has_trace
      (s : state X)
      (om : option message)
      (Hp : valid_state_message_prop s om)
  : initial_state_prop X s /\ option_initial_message_prop X om
  \/ exists (is : state X) (tr : list transition_item),
        finite_valid_trace_init_to is s tr
        /\ finite_trace_last_output tr = om.
Proof.
  apply finite_valid_trace_init_to_emit_valid_state_message_rev in Hp as [is [tr Htr]].
  apply finite_valid_trace_init_to_emit_output in Htr as Houtput.
  unfold empty_initial_message_or_final_output in Houtput.
  destruct_list_last tr tr' item Heqtr.
  - left; split; [| done].
    inversion Htr; [done |].
    by destruct tl; simpl in *; congruence.
  - apply finite_valid_trace_init_to_emit_forget_emit in Htr.
    by right; eexists _, _; rewrite finite_trace_last_output_is_last.
Qed.

(**
  Giving a trace for [valid_state_prop] can be stated more
  simply than [valid_state_message_has_trace], because we don't need a
  disjunction because we are not making claims about [output]
  messages.
*)
Lemma valid_state_has_trace
      (s : state X)
      (Hp : valid_state_prop s) :
  exists (is : state X) (tr : list transition_item),
    finite_valid_trace_init_to is s tr.
Proof using.
  destruct Hp as [_om Hp].
  apply valid_state_message_has_trace in Hp.
  destruct Hp as [[Hinit _] | Htrace].
  - exists s, [].
    split; [| done].
    constructor.
    by apply initial_state_is_valid.
  - by destruct Htrace as [is [tr [Htr _]]]; eauto.
Qed.

(** For any input valid transition there exists a valid trace ending in it. *)
Lemma exists_right_finite_trace_from
  l s1 iom s2 oom
  (Ht : input_valid_transition l (s1, iom) (s2, oom))
  : exists s0 ts, finite_valid_trace_init_to s0 s2
      (ts ++ [{| l := l; destination := s2; input := iom; output := oom |}])
    /\ finite_trace_last s0 ts = s1.
Proof.
  apply input_valid_transition_origin in Ht as Hs1.
  apply valid_state_has_trace in Hs1.
  destruct Hs1 as [s0 [ts Hts]].
  exists s0, ts.
  destruct Hts as [Hts Hinit].
  repeat split; [| done | by revert Hts; apply finite_valid_trace_from_to_last].
  revert Ht.
  by apply extend_right_finite_trace_from_to.
Qed.

Lemma can_emit_has_trace m :
  can_emit m ->
  exists is tr item,
  finite_valid_trace is (tr ++ [item]) /\
  output item = Some m.
Proof.
  intros [(s, im) [l [s' Hm]]].
  apply exists_right_finite_trace_from in Hm as [is [tr [Htr _]]].
  apply finite_valid_trace_init_to_forget_last in Htr.
  by eexists is, tr, _.
Qed.

(**
  Any trace with the [finite_valid_trace_from] property can be completed
  (to the left) to start in an initial state.
*)
Lemma finite_valid_trace_from_complete_left
  (s : state X)
  (tr : list transition_item)
  (Htr : finite_valid_trace_from s tr)
  : exists (is : state X) (trs : list transition_item),
    finite_valid_trace is (trs ++ tr) /\
    finite_trace_last is trs = s.
Proof.
  apply finite_valid_trace_first_pstate in Htr as Hs.
  apply valid_state_has_trace in Hs.
  destruct Hs as [is [trs [Htrs His]]].
  exists is, trs.
  apply finite_valid_trace_from_to_last in Htrs as Hlast.
  rewrite <- Hlast in Htr.
  apply finite_valid_trace_from_to_forget_last in Htrs.
  by firstorder using finite_valid_trace_from_app_iff.
Qed.

(**
  Any trace with the [finite_valid_trace_from_to] property can be completed
  (to the left) to start in an initial state.
*)
Lemma finite_valid_trace_from_to_complete_left
  (s f : state X)
  (tr : list transition_item)
  (Htr : finite_valid_trace_from_to s f tr)
  : exists (is : state X) (trs : list transition_item),
    finite_valid_trace_init_to is f (trs ++ tr) /\
    finite_trace_last is trs = s.
Proof.
  assert (valid_state_prop s) as Hs
    by (apply finite_valid_trace_from_to_forget_last,
        finite_valid_trace_first_pstate in Htr; done).
  apply valid_state_has_trace in Hs.
  destruct Hs as [is [trs [Htrs His]]].
  exists is, trs.
  split.
  - split; [| done].
    by apply finite_valid_trace_from_to_app with s.
  - by apply finite_valid_trace_from_to_last in Htrs.
Qed.

(**
  Another benefit of defining traces is that we can succinctly
  describe indirect transitions between arbitrary pairs of states.

  We say that state <<second>> is in state <<first>>'s futures if
  there exists a finite (possibly empty) valid trace that begins
  with <<first>> and ends in <<second>>.

  This relation is often used in stating safety and liveness properties.
*)

Definition in_futures
  (first second : state X)
  : Prop :=
  exists (tr : list transition_item),
    finite_valid_trace_from_to first second tr.

Lemma in_futures_preserving
  (R : state X -> state X -> Prop)
  (Hpre : PreOrder R)
  (Ht : input_valid_transition_preserving R)
  (s1 s2 : state X)
  (Hin : in_futures s1 s2)
  : R s1 s2.
Proof.
  unfold in_futures in Hin.
  destruct Hin as [tr Htr].
  induction Htr; [done |].
  by apply Ht in Ht0; transitivity s.
Qed.

#[export] Instance eq_equiv : @Equivalence (state X) eq := _.

Lemma in_futures_strict_preserving
  (R : state X -> state X -> Prop)
  (Hpre : StrictOrder R)
  (Ht : input_valid_transition_preserving R)
  (s1 s2 : state X)
  (Hin : in_futures s1 s2)
  (Hneq : s1 <> s2)
  : R s1 s2.
Proof.
  apply (StrictOrder_PreOrder eq_equiv) in Hpre.
  - specialize (in_futures_preserving (relation_disjunction R eq) Hpre) as Hpreserve.
    spec Hpreserve.
    + by intro; intros; left; eapply Ht.
    + by destruct (Hpreserve s1 s2).
  - by intros x1 x2 -> y1 y2 ->.
Qed.

Lemma in_futures_valid_fst
  (first second : state X)
  (Hfuture : in_futures first second)
  : valid_state_prop first.
Proof.
  destruct Hfuture as [tr Htr].
  by apply finite_valid_trace_from_to_forget_last,
     finite_valid_trace_first_pstate in Htr.
Qed.

Lemma in_futures_refl
  (first : state X)
  (Hps : valid_state_prop first)
  : in_futures first first.
Proof.
  by exists []; constructor.
Qed.

#[export] Instance in_futures_trans : Transitive in_futures.
Proof.
  intros s1 s2 s3 [tr12 Htr12] [tr23 Htr23].
  by eexists; eapply finite_valid_trace_from_to_app.
Qed.

Lemma input_valid_transition_in_futures {l s im s' om}
  (Ht : input_valid_transition l (s, im) (s', om))
  : in_futures s s'.
Proof.
  apply finite_valid_trace_singleton in Ht.
  by apply finite_valid_trace_from_add_last with (f := s') in Ht; [eexists |].
Qed.

Lemma elem_of_trace_in_futures_left is s tr
  (Htr : finite_valid_trace_from_to is s tr)
  : forall item, item ∈ tr -> in_futures (destination item) s.
Proof.
  intros item Hitem.
  apply elem_of_list_split in Hitem as (pre & suf & Heqtr).
  exists suf.
  erewrite <- finite_trace_last_is_last.
  eapply finite_valid_trace_from_to_app_split.
  by rewrite <- app_assoc; cbn; rewrite <- Heqtr.
Qed.

Lemma elem_of_trace_in_futures_right is s tr
  (Htr : finite_valid_trace_from_to is s tr)
  : forall item, item ∈ tr -> in_futures is (destination item).
Proof.
  intros item Hitem.
  apply elem_of_list_split in Hitem as (pre & suf & Heqtr).
  exists (pre ++ [item]).
  erewrite <- finite_trace_last_is_last.
  eapply finite_valid_trace_from_to_app_split.
  by rewrite <- app_assoc; cbn; rewrite <- Heqtr.
Qed.

Lemma in_futures_witness
  (first second : state X)
  (Hfutures : in_futures first second)
  : exists (tr : valid_trace) (n1 n2 : nat),
    n1 <= n2
    /\ trace_nth (proj1_sig tr) n1 = Some first
    /\ trace_nth (proj1_sig tr) n2 = Some second.
Proof.
  specialize (in_futures_valid_fst first second Hfutures); intro Hps.
  apply valid_state_has_trace in Hps.
  destruct Hps as [prefix_start [prefix_tr [Hprefix_tr Hinit]]].
  destruct Hfutures as [suffix_tr Hsuffix_tr].
  specialize (finite_valid_trace_from_to_app _ _ _ _ _ Hprefix_tr Hsuffix_tr) as Happ.
  apply finite_valid_trace_from_to_forget_last in Happ.
  assert (Htr : valid_trace_prop (Finite prefix_start (prefix_tr ++ suffix_tr))) by done.
  exists (exist _ _ Htr).
  simpl.
  exists (length prefix_tr), (length prefix_tr + length suffix_tr).
  split; [lia |].
  apply finite_valid_trace_from_to_last in Hprefix_tr.
  apply finite_valid_trace_from_to_last in Hsuffix_tr.
  split.
  - rewrite finite_trace_nth_app1; [| lia].
    by rewrite finite_trace_nth_last; congruence.
  - rewrite finite_trace_nth_app2; [| lia].
    by rewrite Nat.add_comm, Nat.add_sub, finite_trace_nth_last; congruence.
Qed.

Definition trace_segment
  (tr : Trace)
  (n1 n2 : nat)
  : list (transition_item X)
  := match tr with
  | Finite s l => list_segment l n1 n2
  | Infinite s l => stream_segment l n1 n2
  end.

Lemma valid_trace_segment
  (tr : Trace)
  (Htr : valid_trace_prop tr)
  (n1 n2 : nat)
  (Hle : n1 <= n2)
  (first : state X)
  (Hfirst : trace_nth tr n1 = Some first)
  : finite_valid_trace_from first (trace_segment tr n1 n2).
Proof.
  destruct tr as [s tr | s tr]; simpl in *; destruct Htr as [Htr Hinit].
  - by apply finite_valid_trace_from_segment with s.
  - inversion Hfirst; subst; clear Hfirst.
    by apply (infinite_valid_trace_from_segment s tr Htr n1 n2 Hle).
Qed.

Inductive Trace_messages : Type :=
| Finite_messages : list (option message) -> Trace_messages
| Infinite_messages : Stream (option message) -> Trace_messages.

Definition protocol_output_messages_trace (tr : valid_trace) : Trace_messages :=
  match proj1_sig tr with
  | Finite _ ls => Finite_messages (List.map output ls)
  | Infinite _ st => Infinite_messages (map output st) end.

Definition protocol_input_messages_trace (tr : valid_trace) : Trace_messages :=
  match proj1_sig tr with
  | Finite _ ls => Finite_messages (List.map input ls)
  | Infinite _ st => Infinite_messages (map input st) end.

Definition trace_prefix
           (tr : Trace)
           (last : transition_item X)
           (prefix : list (transition_item X))
  :=
    match tr with
    | Finite s ls => exists suffix, ls = prefix ++ (last :: suffix)
    | Infinite s st => exists suffix, st = stream_app prefix (Cons last suffix)
    end.

Definition trace_prefix_fn
  (tr : Trace)
  (n : nat)
  : Trace X
  :=
  match tr with
  | Finite s ls => Finite s (list_prefix ls n)
  | Infinite s st => Finite s (stream_prefix st n)
  end.

Lemma trace_prefix_valid
      (tr : valid_trace)
      (last : transition_item)
      (prefix : list transition_item)
      (Hprefix : trace_prefix (proj1_sig tr) last prefix)
  : valid_trace_prop (Finite (trace_first (proj1_sig tr)) (prefix ++ [last])).
Proof.
  destruct tr as [tr Htr]. simpl in *.
  generalize dependent tr. generalize dependent last.
  apply (rev_ind (fun prefix => forall (last : transition_item) (tr : Trace),
    valid_trace_prop tr -> trace_prefix tr last prefix ->
      finite_valid_trace (trace_first tr) (prefix ++ [last]))).
  - by intros last tr Htr Hprefix; destruct tr; unfold trace_prefix in Hprefix; simpl in Hprefix
    ; destruct Hprefix as [suffix Heq]; subst; destruct Htr as [Htr Hinit]
    ; unfold trace_first; simpl; constructor; try done
    ; inversion Htr; subst; clear Htr
    ; apply finite_valid_trace_singleton.
  - intros last_p p Hind last tr Htr Hprefix.
    specialize (Hind last_p tr Htr).
    destruct tr as [|]; unfold trace_prefix in Hprefix;   simpl in Hprefix
    ; destruct Hprefix as [suffix Heq]; subst; destruct Htr as [Htr Hinit]; simpl; simpl in Hind
    ; split; try done.
    + assert
        (Hex : exists suffix0 : list transition_item,
            (p ++ [last_p]) ++ last :: suffix = p ++ last_p :: suffix0)
          by (exists (last :: suffix); rewrite <- app_assoc; done)
      ; specialize (Hind Hex); clear Hex
      ; destruct Hind as [Hptr _]
      ; destruct last
      ; apply extend_right_finite_trace_from
      ; try done.
      rewrite <- (app_cons {| l := l0; input := input0; destination := destination0;
        output := output0 |} suffix), app_assoc, <- !(app_assoc p _ _) in Htr; cbn in Htr.
      specialize
        (finite_valid_trace_consecutive_valid_transition _ _ _ _ _ _ Htr eq_refl).
      simpl.
      by rewrite finite_trace_last_is_last.
    + assert
        (Hex : exists suffix0 : Stream transition_item,
            stream_app (p ++ [last_p])  (Cons last suffix) = stream_app p (Cons last_p suffix0))
          by (exists (Cons last suffix); rewrite <- stream_app_assoc; done)
      ; specialize (Hind Hex); clear Hex
      ; destruct Hind as [Hptr _]
      ; destruct last
      ; apply extend_right_finite_trace_from
      ; try done.
      rewrite <- stream_app_cons in Htr.
      rewrite stream_app_assoc in Htr.
      rewrite <- (app_assoc p _ _) in Htr. simpl in Htr.
      specialize
        (infinite_valid_trace_consecutive_valid_transition
           s
           (stream_app (p ++ [last_p; {| l := l0; input := input0; destination := destination0;
            output := output0 |}]) suffix)
           suffix
           p
           last_p
           {| l := l0; input := input0; destination := destination0; output := output0 |}
           Htr
           eq_refl).
      simpl.
      by rewrite finite_trace_last_is_last.
Qed.

Definition build_trace_prefix_valid
      {tr : valid_trace}
      {last : transition_item}
      {prefix : list transition_item}
      (Hprefix : trace_prefix (proj1_sig tr) last prefix)
      : valid_trace
  := exist _ (Finite (trace_first (proj1_sig tr)) (prefix ++ [last]))
           (trace_prefix_valid tr last prefix Hprefix).

Lemma trace_prefix_fn_valid
      (tr : Trace)
      (Htr : valid_trace_prop tr)
      (n : nat)
  : valid_trace_prop (trace_prefix_fn tr n).
Proof.
  specialize (trace_prefix_valid (exist _ tr Htr)); simpl; intro Hpref.
  remember (trace_prefix_fn tr n) as pref_tr.
  destruct pref_tr as [s l | s l]; cycle 1.
  - by destruct tr as [s' l' | s' l']; inversion Heqpref_tr.
  - destruct l as [| item l].
    + by destruct tr as [s' l' | s' l']
      ; destruct Htr as [Htr Hinit]
      ; inversion Heqpref_tr; subst
      ; (split; [| done])
      ; constructor
      ; apply initial_state_is_valid.
    + assert (Hnnil : item :: l <> [])
        by (intro Hnil; inversion Hnil).
      specialize (exists_last Hnnil); intros [prefix [last Heq]].
      rewrite Heq in *; clear Hnnil Heq l item.
      replace s with (trace_first (proj1_sig (exist _ tr Htr)))
      ; try (by destruct tr; inversion Heqpref_tr; subst).
      apply trace_prefix_valid.
      remember (prefix ++ [last]) as prefix_last. revert Heqprefix_last.
      destruct tr as [s' l' | s' l']
      ; inversion Heqpref_tr
      ; subst
      ; clear Heqpref_tr
      ; simpl
      ; intro Heqprefix.
      * specialize (list_prefix_suffix l' n); intro Hl'.
        rewrite <- Hl'. rewrite Heqprefix.
        exists (list_suffix l' n).
        by rewrite <- app_assoc.
      * specialize (stream_prefix_suffix l' n); intro Hl'.
        rewrite <- Hl'. rewrite Heqprefix.
        exists (stream_suffix l' n).
        by rewrite <- stream_app_assoc.
Qed.

Lemma valid_trace_nth
  (tr : Trace)
  (Htr : valid_trace_prop tr)
  (n : nat)
  (s : state X)
  (Hnth : trace_nth tr n = Some s)
  : valid_state_prop s.
Proof.
  destruct tr as [s0 l | s0 l]; destruct Htr as [Htr Hinit].
  - specialize (finite_valid_trace_from_suffix s0 l Htr n s Hnth).
    intro Hsuf.
    by apply finite_valid_trace_first_pstate in Hsuf.
  - assert (Hle : n <= n) by lia.
    specialize (infinite_valid_trace_from_segment s0 l Htr n n Hle)
    ; simpl; intros Hseg.
    inversion Hnth.
    by apply finite_valid_trace_first_pstate in Hseg.
Qed.

Lemma in_futures_valid_snd
  (first second : state X)
  (Hfutures : in_futures first second)
  : valid_state_prop second.
Proof.
  specialize (in_futures_witness first second Hfutures)
  ; intros [tr [n1 [n2 [Hle [Hn1 Hn2]]]]].
  destruct tr as [tr Htr]; simpl in Hn2.
  by apply valid_trace_nth with tr n2.
Qed.

Lemma in_futures_witness_reverse
  (first second : state X)
  (tr : valid_trace)
  (n1 n2 : nat)
  (Hle : n1 <= n2)
  (Hs1 : trace_nth (proj1_sig tr) n1 = Some first)
  (Hs2 : trace_nth (proj1_sig tr) n2 = Some second)
  : in_futures first second.
Proof.
  destruct tr as [tr Htr].
  simpl in *.
  inversion Hle; subst; clear Hle.
  - rewrite Hs1 in Hs2. inversion Hs2; subst; clear Hs2.
    by exists []; constructor; apply valid_trace_nth with tr n2.
  - exists (trace_segment tr n1 (S m)).
    apply finite_valid_trace_from_add_last; [by apply valid_trace_segment; [| lia |] |].
    destruct tr as [s tr | s tr]; simpl.
    + simpl in Hs1, Hs2.
      unfold list_segment.
      rewrite finite_trace_last_suffix.
      * by apply finite_trace_last_prefix.
      * apply finite_trace_nth_length in Hs2.
        by rewrite list_prefix_length; lia.
    + unfold stream_segment.
      rewrite unlock_finite_trace_last.
      rewrite list_suffix_map, stream_prefix_map.
      simpl in Hs2.
      rewrite list_suffix_last.
      * symmetry. rewrite stream_prefix_nth_last.
        unfold Str_nth in Hs2. simpl in Hs2.
        by inversion Hs2; subst.
      * specialize (stream_prefix_length (Streams.map destination tr) (S m)); intro Hpref_len.
        by rewrite Hpref_len; lia.
Qed.

(**
  Stating liveness properties will require quantifying over complete
  executions of the protocol. To make this possible, we will now define
  _complete_ [valid_trace]s.

  A [valid_trace] is _terminating_ if there's no other [valid_trace]
  that contains it as a prefix.
*)

Definition terminating_trace_prop (tr : Trace) : Prop
   :=
     match tr with
     | Finite s ls =>
         (exists (tr : valid_trace)
         (last : transition_item),
         trace_prefix (proj1_sig tr) last ls) -> False
     | Infinite s ls => False
     end.

(** A [valid_trace] is _complete_, if it is either _terminating_ or infinite. *)

Definition complete_trace_prop (tr : Trace) : Prop
   := valid_trace_prop tr
      /\
      match tr with
      | Finite _ _ => terminating_trace_prop tr
      | Infinite _ _ => True
      end.

(*
  Implicitly, the state itself must be in the trace, and minimally the last
  element of the trace. Also implicitly, the trace leading up to the state
  is finite.

  Defining equivocation on these trace definitions

  Section 7:
  A message m received by a valid state s with a transition label l in a
  valid execution trace is called "an equivocation" if it wasn't produced
  in that trace
*)

(* 6.2.2 Equivocation-free as a composition constraint *)
Definition composition_constraint : Type :=
  label X -> state X * option message -> Prop.

(* Decidable VLSMs *)

Class VLSM_vdecidable : Type :=
{
  valid_decidable :
    forall (l : label X) (som : state X * option message),
      {valid X l som} + {~ valid X l som}
}.

End sec_VLSM.

(**
  Make all arguments of [valid_state_prop_ind] explicit
  so it will work with the <<induction using>> tactic
  (closing the section added <<{message}>> as an implicit argument).
*)
Arguments valid_state_message_prop_ind : clear implicits.
Arguments valid_state_prop_ind : clear implicits.
Arguments finite_valid_trace_from_to_ind : clear implicits.

Arguments finite_valid_trace_rev_ind : clear implicits.
Arguments finite_valid_trace_from_rev_ind : clear implicits.
Arguments finite_valid_trace_from_to_rev_ind : clear implicits.
Arguments finite_valid_trace_init_to_rev_ind : clear implicits.
Arguments finite_valid_trace_init_to_rev_strong_ind : clear implicits.

Arguments extend_right_finite_trace_from [message] (X) [s1 ts] (Ht12) [l3 iom3 s3 oom3] (Hv23).
Arguments extend_right_finite_trace_from_to [message] (X) [s1 s2 ts] (Ht12) [l3 iom3 s3 oom3] (Hv23).

Class TraceWithLast
  (base_prop : forall {message} (X : VLSM message),
    state X -> list transition_item -> Prop)
  (trace_prop : forall {message} (X : VLSM message),
    state X -> state X -> list transition_item -> Prop)
  : Prop :=
{
  valid_trace_add_last : forall [msg] [X : VLSM msg] [s f tr],
    base_prop X s tr -> finite_trace_last s tr = f -> trace_prop X s f tr;
  valid_trace_get_last : forall [msg] [X : VLSM msg] [s f tr],
    trace_prop X s f tr -> finite_trace_last s tr = f;
  valid_trace_last_pstate : forall [msg] [X : VLSM msg] [s f tr],
    trace_prop X s f tr -> valid_state_prop X f;
  valid_trace_forget_last : forall [msg] [X : VLSM msg] [s f tr],
    trace_prop X s f tr -> base_prop X s tr;
}.

#[global] Hint Mode TraceWithLast - ! : typeclass_instances.
#[global] Hint Mode TraceWithLast ! - : typeclass_instances.

Definition valid_trace_add_default_last
  `{TraceWithLast base_prop trace_prop}
  [msg] [X : VLSM msg] [s tr] (Htr : base_prop msg X s tr) :
    trace_prop msg X s (finite_trace_last s tr) tr.
Proof.
  by apply valid_trace_add_last.
Defined.

#[export] Instance trace_with_last_valid_trace_from :
  TraceWithLast (@finite_valid_trace_from) (@finite_valid_trace_from_to)
  := {valid_trace_add_last := @finite_valid_trace_from_add_last;
      valid_trace_get_last := @finite_valid_trace_from_to_last;
      valid_trace_last_pstate := @finite_valid_trace_from_to_last_pstate;
      valid_trace_forget_last := @finite_valid_trace_from_to_forget_last;
     }.

#[export] Instance trace_with_last_valid_trace_init :
  TraceWithLast (@finite_valid_trace) (@finite_valid_trace_init_to)
  := {valid_trace_add_last := @finite_valid_trace_init_add_last;
      valid_trace_get_last := @finite_valid_trace_init_to_last;
      valid_trace_last_pstate _ _ _ _ _ H := valid_trace_last_pstate (proj1 H);
      valid_trace_forget_last := @finite_valid_trace_init_to_forget_last;
     }.

Class TraceWithStart
  {message} {X : VLSM message}
  (start : state X)
  (trace_prop : list (transition_item X) -> Prop)
  : Prop :=
{
  valid_trace_first_pstate :
    forall [tr], trace_prop tr -> valid_state_prop X start
}.

#[global] Hint Mode TraceWithStart - - - ! : typeclass_instances.

#[export] Instance trace_with_start_valid_trace_from message (X : VLSM message) s :
  TraceWithStart s (finite_valid_trace_from X s)
  := {valid_trace_first_pstate := finite_valid_trace_first_pstate X s}.
#[export] Instance trace_with_start_valid_trace message (X : VLSM message) s :
  TraceWithStart s (finite_valid_trace X s)
  := {valid_trace_first_pstate tr H := valid_trace_first_pstate (proj1 H)}.
#[export] Instance trace_with_start_valid_trace_from_to message (X : VLSM message) s f :
  TraceWithStart s (finite_valid_trace_from_to X s f)
  := {valid_trace_first_pstate tr H := valid_trace_first_pstate (valid_trace_forget_last H)}.
#[export] Instance trace_with_start_valid_trace_init_to message (X : VLSM message) s f :
  TraceWithStart s (finite_valid_trace_init_to X s f)
  := {valid_trace_first_pstate tr H := valid_trace_first_pstate (valid_trace_forget_last H)}.

(** *** Pre-loaded VLSMs

  Given a VLSM <<X>>, we introduce the _pre-loaded_ version of it,
  which is identical to <<X>>, except that it is endowed with the
  whole message universe as its initial messages. The high degree
  of freedom allowed to the _pre-loaded_ version lets it experience
  everything experienced by <<X>> but also other types of behavior,
  including _Byzantine_ behavior, which makes it a useful concept in
  Byzantine fault tolerance analysis.
*)

Section sec_pre_loaded_with_all_messages_vlsm.

Context
  {message : Type}
  (X : VLSM message)
  .

Definition pre_loaded_with_all_messages_vlsm_machine
  : VLSMMachine X
  :=
  {| initial_state_prop := @initial_state_prop _ _ X
   ; initial_message_prop := fun message => True
   ; s0 := @s0 _ _ X
   ; transition := @transition _ _ X
   ; valid := @valid _ _ X
  |}.

Definition pre_loaded_with_all_messages_vlsm
  : VLSM message
  := mk_vlsm pre_loaded_with_all_messages_vlsm_machine.

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
  by apply valid_initial_state_message; [apply proj2_sig | destruct om].
Qed.

Lemma pre_loaded_with_all_messages_valid_state_message_preservation
  (s : state X)
  (om : option message)
  (Hps : valid_state_message_prop X s om)
  : valid_state_message_prop pre_loaded_with_all_messages_vlsm s om.
Proof.
  induction Hps.
  - by apply (valid_initial_state_message pre_loaded_with_all_messages_vlsm); [| destruct om].
  - by apply (valid_generated_state_message pre_loaded_with_all_messages_vlsm) with s _om _s om l0.
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
    (Hs : initial_state_prop (VLSMMachine := pre_loaded_with_all_messages_vlsm_machine) s) :
       preloaded_valid_state_prop s
| preloaded_protocol_generated
    (l : label X)
    (s : state X)
    (Hps : preloaded_valid_state_prop s)
    (om : option message)
    (Hv : valid (VLSMMachine := pre_loaded_with_all_messages_vlsm_machine) l (s, om))
    s' om'
    (Ht : transition (VLSMMachine := pre_loaded_with_all_messages_vlsm_machine) l (s, om) = (s', om'))
  : preloaded_valid_state_prop s'.

Lemma preloaded_valid_state_prop_iff (s : state X) :
  valid_state_prop pre_loaded_with_all_messages_vlsm s
  <-> preloaded_valid_state_prop s.
Proof.
  split.
  - intros [om Hvalid].
    induction Hvalid.
    + by apply preloaded_valid_initial_state.
    + by apply preloaded_protocol_generated with l0 s om om'.
  - induction 1.
    + by exists None; apply valid_initial_state_message.
    + exists om'. destruct IHpreloaded_valid_state_prop as [_om Hs].
      specialize (any_message_is_valid_in_preloaded om) as [_s Hom].
      by apply (valid_generated_state_message pre_loaded_with_all_messages_vlsm) with s _om _s om l0.
Qed.

Lemma preloaded_weaken_valid_state_message_prop s om :
  valid_state_message_prop X s om ->
  valid_state_message_prop pre_loaded_with_all_messages_vlsm s om.
Proof.
  induction 1.
  - refine (valid_initial_state_message pre_loaded_with_all_messages_vlsm s Hs om _).
    by destruct om.
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

Lemma non_empty_valid_trace_from_can_produce
  `(X : VLSM message)
  (s : state X)
  (m : message)
  : can_produce X s m
  <-> exists (is : state X) (tr : list transition_item) (item : transition_item),
    finite_valid_trace X is tr /\
    last_error tr = Some item /\
    destination item = s /\ output item = Some m.
Proof.
  split.
  - intros [(s', om') [l Hsm]].
    destruct (id Hsm) as [[Hp _] _].
    pose proof (finite_valid_trace_singleton _ Hsm) as Htr.
    apply finite_valid_trace_from_complete_left in Htr.
    destruct  Htr as [is [trs [Htrs _]]].
    exists is.
    match type of Htrs with
    | context [_ ++ [?item]] => remember item as lstitem
    end.
    exists (trs ++ [lstitem]). exists lstitem.
    by rewrite last_error_is_last; subst.
  - intros [is [tr [item [Htr [Hitem [Hs Hm]]]]]].
    destruct_list_last tr tr' item' Heq; [by inversion Hitem |].
    clear Heq.
    rewrite last_error_is_last in Hitem. inversion Hitem. clear Hitem. subst item'.
    destruct Htr as [Htr _].
    apply finite_valid_trace_from_app_iff in Htr.
    destruct Htr as [_ Htr].
    inversion Htr. clear Htr. subst. simpl in Hm. subst.
    by eexists _, l0; apply Ht.
Qed.

(** *** Properties of provably-equal VLSMs

  If we know that two VLSMs are provably equal, we could try rewriting by them.
  However, that gets usually quite technical. To go around that, we will prove
  that there is a [VLSMProjections.VLSM_embedding] between them which will
  allow trace-based results to be easily moved between the two VLSMs.

  Below are some preliminary results; the actual projection is given in
  [VLSMProjections.same_VLSM_embedding].
*)
Section sec_same_VLSM.

Context
  {message : Type}
  .

Section sec_definitions.

Context
  [X1 X2 : VLSM message]
  (Heq : X1 = X2)
  .

Definition same_VLSM_label_rew (l1 : label X1) : label X2 :=
  eq_rect X1 (@label _) l1 _ Heq.

Definition same_VLSM_state_rew (s1 : state X1) : state X2 :=
  eq_rect X1 (@state _) s1 _ Heq.

End sec_definitions.

Context
  (X1 X2 : VLSM message)
  (Heq : X1 = X2)
  .

Lemma same_VLSM_valid_preservation l1 s1 om
  : valid X1 l1 (s1, om) ->
    valid X2 (same_VLSM_label_rew Heq l1) (same_VLSM_state_rew Heq s1, om).
Proof. by subst. Qed.

Lemma same_VLSM_transition_preservation l1 s1 om s1' om'
  : transition X1 l1 (s1, om) = (s1', om') ->
    transition X2 (same_VLSM_label_rew Heq l1) (same_VLSM_state_rew Heq s1, om) =
      (same_VLSM_state_rew Heq s1', om').
Proof. by subst. Qed.

Lemma same_VLSM_initial_state_preservation s1
  : initial_state_prop X1 s1 -> initial_state_prop X2 (same_VLSM_state_rew Heq s1).
Proof. by subst. Qed.

Lemma same_VLSM_initial_message_preservation m
  : initial_message_prop X1 m -> initial_message_prop X2 m.
Proof. by subst. Qed.

End sec_same_VLSM.

Record ValidTransition `(X : VLSM message) l s1 iom s2 oom : Prop :=
{
  vt_valid : valid X l (s1, iom);
  vt_transition : transition X l (s1, iom) = (s2, oom);
}.

Inductive ValidTransitionNext `(X : VLSM message) (s1 s2 : state X) : Prop :=
| transition_next :
    forall l iom oom (Ht : ValidTransition X l s1 iom s2 oom),
      ValidTransitionNext X s1 s2.

Section sec_valid_transition_props.

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

Lemma valid_transition_next :
  forall l s1 iom s2 oom,
    ValidTransition X l s1 iom s2 oom -> ValidTransitionNext X s1 s2.
Proof. by intros * [Hv Ht]; econstructor. Qed.

Lemma input_valid_transition_forget_input :
  forall l s1 iom s2 oom,
    input_valid_transition X l (s1, iom) (s2, oom) ->
    ValidTransition X l s1 iom s2 oom.
Proof. by firstorder. Qed.

End sec_valid_transition_props.

Class HistoryVLSM `(X : VLSM message) : Prop :=
{
  not_ValidTransitionNext_initial :
    forall s2, initial_state_prop X s2 ->
    forall s1, ~ ValidTransitionNext X s1 s2;
  unique_transition_to_state :
    forall [s : state X],
    forall [l1 s1 iom1 oom1], ValidTransition X l1 s1 iom1 s oom1 ->
    forall [l2 s2 iom2 oom2], ValidTransition X l2 s2 iom2 s oom2 ->
    l1 = l2 /\ s1 = s2 /\ iom1 = iom2 /\ oom1 = oom2;
}.

#[global] Hint Mode HistoryVLSM - ! : typeclass_instances.

#[export] Instance preloaded_history_vlsm
  `{HistoryVLSM message X} : HistoryVLSM (pre_loaded_with_all_messages_vlsm X).
Proof.
  split; intros.
  - rewrite <- ValidTransitionNext_preloaded_iff.
    by apply not_ValidTransitionNext_initial.
  - by eapply (@unique_transition_to_state _ X);
      [| apply ValidTransition_preloaded_iff..].
Qed.

Section sec_history_vlsm.

Context
  `{HistoryVLSM message X}
  (R := pre_loaded_with_all_messages_vlsm X)
  .

Lemma history_unique_trace_to_reachable :
  forall is s tr, finite_valid_trace_init_to R is s tr ->
  forall is' tr', finite_valid_trace_init_to R is' s tr' ->
    is' = is /\ tr' = tr.
Proof.
  intros is s tr Htr; induction Htr using finite_valid_trace_init_to_rev_ind;
    intros is' tr' [Htr' His'].
  - destruct_list_last tr' tr'' item Heqtr'; [by inversion Htr' | subst].
    apply finite_valid_trace_from_to_app_split in Htr' as [_ Hitem].
    inversion Hitem; inversion Htl; subst.
    destruct Ht as [(_ & _ & Hv) Ht].
    exfalso; clear His'; eapply @not_ValidTransitionNext_initial;
      [| done | by esplit].
    by typeclasses eauto.
  - destruct_list_last tr' tr'' item Heqtr'; subst tr'.
    + inversion Htr'; subst; clear Htr'.
      destruct Ht as [(_ & _ & Hv) Ht].
      exfalso; eapply @not_ValidTransitionNext_initial; [| done | by esplit].
      by typeclasses eauto.
    + apply finite_valid_trace_from_to_app_split in Htr' as [Htr' Hitem].
      inversion Hitem; inversion Htl; subst; clear Hitem Htl.
      apply input_valid_transition_forget_input in Ht, Ht0.
      specialize (unique_transition_to_state Ht Ht0) as Heqs.
      destruct_and! Heqs; subst.
      specialize (IHHtr _ _  (conj Htr' His')).
      by destruct_and! IHHtr; subst.
Qed.

End sec_history_vlsm.
