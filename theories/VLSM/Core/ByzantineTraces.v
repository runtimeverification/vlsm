From stdpp Require Import prelude.
From Coq Require Import FinFun.
From VLSM Require Import Lib.Preamble Core.VLSM Core.VLSMProjections Core.Composition Core.ProjectionTraces Core.Validating.

(** * VLSM Byzantine Traces

In this section, we introduce two definitions of Byzantine traces,
then show them equivalent (Lemma [byzantine_alt_byzantine_iff]),
and equivalent with traces on the corresponding pre-loaded VLSM
(Lemmas [byzantine_pre_loaded_with_all_messages] and [pre_loaded_with_all_messages_alt_eq]).

Note that, contrary to what one might think, the [byzantine_trace_prop]erty
does not only capture traces exhibiting byzantine behavior, but also all
[protocol_trace]s (consequence of Lemma [vlsm_incl_pre_loaded_with_all_messages_vlsm]).
Therefore to avoid confusion we will call _proper byzantine traces_,
or _traces exhibiting byzantine behavior_ the collection of traces with
the [byzantine_trace_prop]erty but without the [protocol_trace_prop]erty.

In the remainder of this section, we fix a (regular) VLSM <<M>> with
signature <<S>> and of type <<T>>.
*)

(** ** Definition and basic properties *)

Section ByzantineTraces.
Context
    {message : Type}
    (M : VLSM message)
    .

(**

The first definition says that a trace has the [byzantine_trace_prop]erty
if it is the projection of
a trace which can be obtained by freely composing <<M>> with an arbitrary
VLSM <<M'>> (of a signatulre <<S'>> and type <<T'>> over the same set of <<message>>s).

Below, [binary_free_composition_fst] represents the projection of
the free composition between <<M>> and <<M'>> to the component corresponding
to <<M>>.
*)

Definition byzantine_trace_prop
    (tr : vTrace M) :=
    exists (M' : VLSM message)
        (Proj := binary_free_composition_fst M M'),
        protocol_trace_prop Proj tr.

(**

The first result says that all traces with the [byzantine_trace_prop]erty
for a VLSM <<M>> are traces of the [pre_loaded_with_all_messages_vlsm] associated to <<M>>:
*)

Lemma byzantine_pre_loaded_with_all_messages
    (PreLoaded := pre_loaded_with_all_messages_vlsm M)
    (tr : vTrace M)
    (Hbyz : byzantine_trace_prop tr)
    : protocol_trace_prop PreLoaded tr.
Proof.
    destruct Hbyz as [M' Htr].
    simpl in Htr.
    apply
        (proj_pre_loaded_with_all_messages_incl
            (binary_IM M M')
            (free_constraint _)
            first
            tr
            Htr
        ).
Qed.

(** ** An alternative definition

The [alternate_byzantine_trace_prop]erty relies on the composition
of the VLSM with a special VLSM which can produce all messages.

We will define its type ([all_messages_type]),
signature ([all_messages_sig]) and the VLSM itself ([emit_any_message_vlsm]) below.

The type of the [emit_any_message_vlsm] sets the [label] set to consist of all
<<message>>s and the [state] to consist of a single state (here [tt]).
*)

Definition all_messages_type : VLSMType message :=
    {| label := message
     ; state := unit
    |}.

(**

The [emit_any_message_vlsm] signature further says that the (single) state is
initial and no messages are initial.
It takes as parameter a <<message>> to ensure that the sets of labels and
messages are both non-empty.
*)

Definition all_messages_s0 := exist (fun s: @state _ all_messages_type => True) tt I.

Instance all_messages_state_inh : Inhabited (sig  (fun s: @state _ all_messages_type => True)) :=
  {| inhabitant := all_messages_s0 |}.

Definition all_messages_sig
    : VLSMSign all_messages_type
    :=
    {| initial_state_prop := fun s => True
     ; initial_message_prop := fun m => False
    |}.

(**

The [transition] function of the [emit_any_message_vlsm] generates the
message given as a label:
*)

Definition all_messages_transition
    (l : @label _ all_messages_type)
    (som : @state _ all_messages_type * option message)
    : @state _ all_messages_type * option message
    := (tt, Some l).


(**

The [valid]ity predicate specifies that all transitions are valid

*)
Definition all_messages_valid
    (l : @label _ all_messages_type)
    (som : @state _ all_messages_type * option message)
    : Prop
    := True.

Definition emit_any_message_vlsm_machine
    : VLSMClass all_messages_sig
    :=
    {| transition := all_messages_transition
     ; valid := all_messages_valid
    |}.

Definition emit_any_message_vlsm
    := mk_vlsm emit_any_message_vlsm_machine.

(**

Using the VLSM defined above, we can define the [alternate_byzantine_trace_prop]erty
of a trace <<tr>> for the VLSM <<M>> as being a trace in the projection
of the free composition between <<M>> and the [emit_any_message_vlsm],
to the component corresponding to <<M>>:

*)

Definition alternate_byzantine_trace_prop
    (tr : vTrace M)
    (Proj := binary_free_composition_fst M emit_any_message_vlsm)
    :=
    protocol_trace_prop Proj tr.

(**

Since the [byzantine_trace_prop]erty was referring to the free composition
to any other VLSM, we can instantiate that definition to the
[emit_any_message_vlsm] to derive that a trace with the
[alternate_byzantine_trace_prop]erty also has the [byzantine_trace_prop]erty.

*)

Lemma byzantine_alt_byzantine
    (tr : vTrace M)
    (Halt : alternate_byzantine_trace_prop tr)
    : byzantine_trace_prop tr.
Proof.
    exists emit_any_message_vlsm.
    assumption.
Qed.

(** ** Equivalence between the two Byzantine trace definitions

In this section we prove that the [alternate_byzantine_trace_prop]erty is
equivalent to the [byzantine_trace_prop]erty.

Since we have already proven that the [alternate_byzantine_trace_prop]erty
implies the [byzantine_trace_prop]erty (Lemma [byzantine_alt_byzantine]),
and since we know that the traces with the [byzantine_trace_prop]erty
are [protocol_trace]s for the [pre_loaded_with_all_messages_vlsm], to prove the
equivalence it is enough to close the circle by proving the
[VLSM_incl]usion between the [pre_loaded_with_all_messages_vlsm] and the projection VLSM used
in the definition of the [alternate_byzantine_trace_prop]erty.

*)

Section pre_loaded_with_all_messages_byzantine_alt.

Context
    (PreLoaded := pre_loaded_with_all_messages_vlsm M)
    (Alt1 := binary_free_composition_fst M emit_any_message_vlsm)
    (Alt := binary_free_composition M emit_any_message_vlsm)
    .

(**
Let <<PreLoaded>> denote the [pre_loaded_with_all_messages_vlsm] of <<M>>, <<Alt>> denote
the free composition of <<M>> with the [emit_any_message_vlsm],
and <<Alt1>> denote the projection of <<Alt>> to the component of <<M>>.

First, note that using the results above it is easy to prove the inclusion
of <<Alt1>> into <<Preloaded>>
*)

    Lemma alt_pre_loaded_with_all_messages_incl
        : VLSM_incl Alt1 PreLoaded.
    Proof.
        intros t Hpt.
        apply byzantine_pre_loaded_with_all_messages.
        apply byzantine_alt_byzantine.
        assumption.
    Qed.

(**
To prove the reverse inclusion (between <<PreLoaded>> and <<Alt1>>) we will use the
[basic_VLSM_incl] meta-result about proving inclusions bewteen
VLSMs which states that
- if all [valid] messages in the first are [protocol_message]s in the second, and
- if all [protocol_state]s in the first are also [protocol_state]s in the second,
- and if all [protocol_transition]s in the first are also [protocol_transition]s
in the second,
- then the first VLSM is included in the second.

We will tackle each of these properties in the sequel.

First note that _all_ messages are [protocol_message]s for <<Alt>>, as
[emit_any_message_vlsm] can generate any message without changing state.
*)

    Lemma alt_option_protocol_message
        (om : option message)
        : option_protocol_message_prop Alt om.
    Proof.
        destruct om as [m|];[|apply option_protocol_message_None].
        pose (s :=proj1_sig (vs0 Alt): vstate Alt).
        unfold vstate in s.
        exists s.
        assert (protocol_prop Alt s None) as Hs
          by (apply protocol_initial_state;apply proj2_sig).
        eapply (protocol_generated Alt) with s None s None (existT second _)
        ;[assumption|assumption|split; exact I|].
        simpl. f_equal.
        rewrite state_update_id; reflexivity.
    Qed.

(**
Using the above, it is straight-forward to show that:
*)

    Lemma alt_proj_option_protocol_message
        (m : option message)
        : option_protocol_message_prop Alt1 m.
    Proof.
        apply protocol_message_projection.
        apply alt_option_protocol_message.
    Qed.

(**
Next we define the "lifing" of a [state] <<s>> from <<M>> to <<Alt>>,
by simply setting to <<s>> the  corresponding component of the initial
(composed) state [s0] of <<Alt>>.
*)
    Definition lifted_alt_state
        (s : vstate M)
        : vstate Alt
        := lift_to_composite_state
             (binary_IM M emit_any_message_vlsm) first s.

(**
Lifting a [protocol_state] of <<PreLoaded>> we obtain a [protocol_state] of <<Alt>>.
*)
    Lemma preloaded_alt_protocol_state
        (sj : state)
        (om : option message)
        (Hp : protocol_prop PreLoaded sj om)
        : protocol_state_prop Alt (lifted_alt_state sj).
    Proof.
      assert (protocol_state_prop PreLoaded sj) as Hsj
        by (exists om;assumption);clear Hp.
      induction Hsj using protocol_state_prop_ind.
      - apply initial_is_protocol.
        intros [];[exact Hs|exact I].
      - exists om'.
        assert (option_protocol_message_prop Alt om0) as Hom0
          by apply alt_option_protocol_message.
        cut (protocol_transition Alt (existT first l) (lifted_alt_state s,om0) (lifted_alt_state s', om'))
          ;[apply protocol_prop_transition_out|].
        split.
        * split;[assumption|].
          split;[assumption|].
          split;[|exact I].
          simpl. apply Ht.
        * simpl.
          replace (lifted_alt_state s first) with s
            by (unfold lifted_alt_state,lift_to_composite_state
               ;rewrite state_update_eq;reflexivity).
          apply proj2 in Ht.
          change (vtransition M l (s: vstate M,om0) = (s',om')) in Ht.
          rewrite Ht.
          f_equal.
          apply state_update_twice.
    Qed.

(**
Finally, we can use [basic_VLSM_incl] together with the
results above to show that <<Preloaded>> is included in <<Alt1>>.
*)

    Lemma pre_loaded_with_all_messages_alt_incl
        : VLSM_incl PreLoaded Alt1.
    Proof.
        apply (basic_VLSM_incl (machine PreLoaded) (machine Alt1))
        ; intro; intros; [assumption| | |apply H].
        - apply alt_proj_option_protocol_message.
        - exists (lifted_alt_state s).
          split; [reflexivity|].
          destruct Hv as [[_om Hps] [Hpm Hv]].
          repeat split.
          + apply preloaded_alt_protocol_state with _om; assumption.
          + apply alt_option_protocol_message.
          + assumption.
    Qed.

(**
Hence, <<Preloaded>> and <<Alt1>> are actually trace-equal:
*)
    Lemma pre_loaded_with_all_messages_alt_eq
        : VLSM_eq PreLoaded Alt1
        .
    Proof.
        split.
        - apply pre_loaded_with_all_messages_alt_incl.
        - apply alt_pre_loaded_with_all_messages_incl.
    Qed.

End pre_loaded_with_all_messages_byzantine_alt.

(**
Finally, we can conclude that the two definitions for byzantine traces are
equivalent:
*)

Lemma byzantine_alt_byzantine_iff
    (tr : vTrace M)
    : alternate_byzantine_trace_prop tr <-> byzantine_trace_prop tr.
Proof.
    split; intros.
    - apply byzantine_alt_byzantine; assumption.
    - apply pre_loaded_with_all_messages_alt_incl.
      apply byzantine_pre_loaded_with_all_messages.
      assumption.
Qed.

End ByzantineTraces.

(** ** Byzantine fault tolerance for a single validator

Given that projections of validating VLSMs are equal to their corresponding
pre-loaded with all messages VLSM ([pre_loaded_with_all_messages_validating_proj_eq]),
we can derive that for validating VLSMs, all their byzantine traces are
included in the [protocol_trace]s of their projection from the composition.
*)
Lemma validating_component_byzantine_fault_tolerance
    message `{EqDecision index}
    (IM : index -> VLSM message)
    (constraint : composite_label IM -> composite_state IM  * option message -> Prop)
    (i : index)
    (Hvalidating: validating_projection_prop IM constraint i)
    : forall tr, byzantine_trace_prop (IM i) tr ->
        protocol_trace_prop (composite_vlsm_constrained_projection IM constraint i) tr.
Proof.
    intros tr Htr.
    apply
        (VLSM_incl_protocol_trace
            (pre_loaded_with_all_messages_validating_proj_incl _ _ _ Hvalidating)).
    revert Htr.
    apply byzantine_pre_loaded_with_all_messages.
Qed.


(** ** Byzantine fault tolerance for a composition of validators

In this section we show that if all components of a composite VLSM <<X>> have
the [validating_projection_prop]erty, then its byzantine traces (that is,
traces obtained upon placing this composition in any, possibly adversarial,
context) are [protocol_traces] of <<X>>.
*)
Section composite_validating_byzantine_traces.

    Context {message : Type}
            {index : Type}
            {IndEqDec : EqDecision index}
            (IM : index -> VLSM message)
            (constraint : composite_label IM -> composite_state IM  * option message -> Prop)
            (X := composite_vlsm IM constraint)
            (PreLoadedX := pre_loaded_with_all_messages_vlsm X)
            (FreeX := free_composite_vlsm IM)
            (Hvalidating: forall i : index, validating_projection_prop IM constraint i)
            .

(**
Let us fix an indexed set of VLSMs <<IM>> and their composition <<X>>
using <<constraint>>, and let <<PreloadedX>> be the
[pre_loaded_with_all_messages_vlsm] associated to <<X>>.

Since we know that <<PreloadedX>> contains precisely the byzantine traces
of <<X>>, we just need to show that <<PreLoadedX>> is
included in <<X>> to prove our main result.

*)
    Lemma validating_pre_loaded_with_all_messages_incl
        : VLSM_incl PreLoadedX X.
    Proof.
        apply VLSM_incl_finite_traces_characterization.
        intros.
        split; [|apply H].
        destruct H as [Htr Hs].
        induction Htr using finite_protocol_trace_from_rev_ind.
        - apply (finite_ptrace_empty X).
          apply initial_is_protocol; assumption.
        - specialize (IHHtr Hs) as IHtr; clear IHHtr.
          apply (extend_right_finite_trace_from X).
          assumption.
          destruct Hx as [Hvx Htx].
          split; [|assumption].
          apply finite_ptrace_last_pstate in IHtr.
          simpl in *.
          match type of IHtr with
          | protocol_state_prop _ ?s => remember s as lst
          end.
          split; [assumption|].
          repeat split; [|apply Hvx|apply Hvx].
          destruct Hvx as [Hlst [_ [Hv _]]].
          destruct l as (i, li). simpl in *.
          specialize (protocol_state_project_preloaded_to_preloaded _ IM constraint lst i Hlst)
            as Hlsti.
          assert (Hpv : protocol_valid (pre_loaded_with_all_messages_vlsm (IM i)) li (lst i, iom)).
          { split; [assumption|]. split; [|assumption].
            eexists _. apply (pre_loaded_with_all_messages_message_protocol_prop (IM i)).
          }
          apply Hvalidating in Hpv.
          clear -Hpv.
          destruct Hpv as [_ [_ [_ [Hinput _]]]].
          destruct Hinput as [s Hinput].
          exists s.
          revert Hinput.
          apply (constraint_subsumption_protocol_prop IM constraint).
          intro. intros. destruct som. apply H.
    Qed.

(**
Finally, we can conclude that a composition of validating components can
resist any kind of external influence:
*)
    Lemma composite_validating_byzantine_traces_are_not_byzantine
        (tr : vTrace X)
        (Hbyz : byzantine_trace_prop X tr)
        : protocol_trace_prop X tr.
    Proof.
        apply validating_pre_loaded_with_all_messages_incl.
        apply alt_pre_loaded_with_all_messages_incl.
        apply byzantine_alt_byzantine_iff.
        assumption.
    Qed.
End composite_validating_byzantine_traces.
