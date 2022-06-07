From Cdcl Require Import Itauto. Local Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From Coq Require Import Vectors.Fin FunctionalExtensionality Arith.Compare_dec Lia Program.Equality.
From VLSM Require Import Lib.Preamble Lib.ListExtras Lib.StdppListSet.
From VLSM Require Import Lib.ListSetExtras Lib.FinExtras.
From VLSM Require Import Core.VLSM Core.Equivocation.
From VLSM Require Import Core.Equivocators.Common Core.Equivocators.Projections.

(** * VLSM Message Properties *)

Section equivocator_vlsm_message_properties.

(** ** Lifting properties about sent messages to the equivocators

In this section we first prove some general properties about sent messages
being preserved and reflected by the [equivocator_vlsm], and then we show
that the [HasBeenSentCapability] and the [ComputableSentMessages]
can be lifted (each separately) from the original machine to the
[equivocator_vlsm].
*)


Context
  {message : Type}
  (X : VLSM message)
  (equivocator_vlsm := equivocator_vlsm X)
  (MachineDescriptor := MachineDescriptor X)
  .

(**
If a projection of an [equivocator_vlsm] trace [output]s a message, then
the original trace must do so too.
*)
Lemma equivocator_vlsm_trace_project_output_reflecting
  (tr: list (vtransition_item equivocator_vlsm))
  (trX: list (vtransition_item X))
  (j i : MachineDescriptor)
  (HtrX: equivocator_vlsm_trace_project _ tr j = Some (trX, i))
  (m : message)
  (Hjbs: Exists (field_selector output m) trX)
  : Exists (field_selector output m) tr.
Proof.
  revert trX i HtrX Hjbs.
  induction tr; intros.
  - inversion HtrX. subst. inversion Hjbs.
  - simpl in HtrX.
    destruct (equivocator_vlsm_trace_project _ tr j) as [(trX', i')|]
      eqn:Htr; [|congruence].
    specialize (IHtr trX').
    destruct (equivocator_vlsm_transition_item_project _ a i') as [[[item'|] i'']|]
      eqn:Hitem'
    ; inversion HtrX; subst; clear HtrX.
    + apply equivocator_transition_item_project_inv_messages in Hitem'.
      destruct Hitem' as [_ [_ [_ [_ Ha]]]].
      inversion Hjbs; subst.
      * by left; cbn in *; rewrite Ha.
      * by right; eapply IHtr.
    + by right; eapply IHtr.
Qed.

Lemma preloaded_equivocator_vlsm_trace_project_valid_item_new_machine
  (bs : vstate equivocator_vlsm)
  (btr : list (vtransition_item equivocator_vlsm))
  (Hbtr : finite_valid_trace_from (pre_loaded_with_all_messages_vlsm equivocator_vlsm) bs btr)
  (bitem : vtransition_item equivocator_vlsm)
  (Hitem : bitem ∈ btr)
  (sn : state)
  (Hnew : l bitem = Spawn sn)
  : input bitem = None /\ output bitem = None /\
    exists
      (d : MachineDescriptor),
      equivocator_vlsm_transition_item_project _ bitem d = Some (None, NewMachine sn).
Proof.
  apply elem_of_list_split in Hitem.
  destruct Hitem as [bprefix [bsuffix Heq]].
  subst btr.
  apply (finite_valid_trace_from_app_iff (pre_loaded_with_all_messages_vlsm equivocator_vlsm)) in Hbtr.
  destruct Hbtr as [Hbprefix Hbsuffix].
  remember (finite_trace_last _ _) as lst.
  inversion Hbsuffix. subst s' tl bitem.
  destruct Ht as [[_ [_ Hv]] Ht].
  simpl.
  specialize
    (equivocator_valid_transition_project_inv5_new_machine
      _ l s lst iom oom Ht)
    as Hpitem.
  unfold VLSM.l in *.
  subst l.
  specialize (Hpitem _ eq_refl) as [i [lst_i [Hi Hpitem]]].
  by inversion Ht; destruct Hv as [Hsndl Hiom]; subst; eauto.
Qed.

(**
For any [transition_item] in a valid trace segment of an
[equivocator_vlsm] there exists a projection of that trace containing
the projection of the item.
*)
Lemma preloaded_equivocator_vlsm_trace_project_valid_item
  (bs bf : vstate equivocator_vlsm)
  (btr : list (vtransition_item equivocator_vlsm))
  (Hbtr : finite_valid_trace_from_to (pre_loaded_with_all_messages_vlsm equivocator_vlsm) bs bf btr)
  (bitem : vtransition_item equivocator_vlsm)
  (Hitem : bitem ∈ btr)
  (idl : nat)
  (Hlbitem : equivocator_label_descriptor (l bitem) = Existing idl)
  : exists (item : vtransition_item X),
      (exists (d : MachineDescriptor),
        equivocator_vlsm_transition_item_project _ bitem d = Some (Some item, Existing idl))
      /\ exists (tr : list (vtransition_item X)),
        item ∈ tr /\
        exists (dfinal dfirst : MachineDescriptor),
          proper_descriptor X dfirst bs /\
          existing_descriptor X dfinal (finite_trace_last bs btr) /\
          equivocator_vlsm_trace_project _ btr dfinal = Some (tr, dfirst).
Proof.
  specialize (preloaded_equivocator_vlsm_valid_trace_project_inv2 X bs bf btr) as Hinv2.
  spec Hinv2. { intro contra. subst. inversion Hitem. }
  spec Hinv2 Hbtr.
  apply elem_of_list_split in Hitem.
  destruct Hitem as [bprefix [bsuffix Heq]].
  subst btr.
  apply (finite_valid_trace_from_to_app_split (pre_loaded_with_all_messages_vlsm equivocator_vlsm)) in Hbtr.
  destruct Hbtr as [Hbprefix Hbsuffix].
  remember (finite_trace_last _ _) as lst.
  inversion Hbsuffix; subst s' f bitem tl.
  destruct Ht as [[_ [_ Hv]] Ht].
  specialize
    (equivocator_valid_transition_project_inv5 _ l s lst iom oom Hv Ht) as Hpitem.
  unfold VLSM.l in *.
  destruct (Hpitem _ Hlbitem) as [i [si [Hi [itemx Hitemx]]]].

  apply valid_trace_forget_last in Htl.
  destruct
    (preloaded_equivocator_vlsm_trace_project_valid_inv _ _ _ Htl _ _ Hi)
    as [suffix Hsuffix].
  exists itemx. split; [eexists; apply Hitemx|].
  remember (Existing i) as dsuffix.
  remember {| input := iom |} as bitem.
  specialize
    (equivocator_vlsm_trace_project_app_inv _ [bitem] bsuffix (Existing i) (Existing idl) dsuffix [itemx] suffix)
    as Hsuffix'.
  spec Hsuffix'.  { by simpl; rewrite Hitemx. }
  subst dsuffix.
  spec Hsuffix' Hsuffix.
  subst bitem.
  destruct
    (equivocator_valid_transition_project_inv2 _ l lst s iom oom Hv Ht _ _ _ Hitemx)
    as [_i [_Hdsuffix [s_i [_Hi Hd']]]].
  inversion _Hdsuffix. subst _i. clear _Hdsuffix.
  destruct Hd' as [_i' [_Heq [lst_i' [id [Hex [_Hitemx [Hvs' Hts']]]]]]].
  inversion _Heq. subst _i'. clear _Heq.
  subst lst.
  destruct
    (preloaded_equivocator_vlsm_trace_project_valid _ _ _ _ Hbprefix idl _ id)
    as [prefix [dfirst [Hprefix _]]].
  specialize
    (equivocator_vlsm_trace_project_app_inv _ _ _ _ _ _ _ _ Hprefix Hsuffix')
    as Htr.
  simpl in Htr.
  exists (prefix ++ itemx :: suffix).
  specialize (Hinv2 _ _ _ Htr) as [bfi [Hdfinal Hdinitial]].
  split.
  - apply elem_of_app. right. left.
  - eexists _. eexists _. repeat split; [..|apply Htr].
    + clear -Hdinitial.
      destruct dfirst as [sn | j].
      * by destruct Hdinitial.
      * destruct Hdinitial as [bsj [Hdinitial _]]. by exists bsj.
    + remember (bprefix ++ _) as btr.
      specialize (equivocator_vlsm_trace_project_inv X btr) as Hinv.
      spec Hinv. { by destruct bprefix; subst. }
      spec Hinv i.
      spec Hinv; [by subst; eexists |].
      specialize (Hinv bs) as [lst_i Hlst_i].
      by eexists.
Qed.

(**
If an [equivocator_vlsm]'s valid trace segment [output]s a message, then
one of its projections must do so too.
*)
Lemma equivocator_vlsm_trace_project_output_reflecting_inv
  (is: vstate equivocator_vlsm)
  (tr: list (vtransition_item equivocator_vlsm))
  (Htr: finite_valid_trace_from (pre_loaded_with_all_messages_vlsm equivocator_vlsm) is tr)
  (m : message)
  (Hbbs : Exists (field_selector output m) tr)
  : exists
    (j i : MachineDescriptor)
    (Hi : proper_descriptor X i is)
    (Hj : existing_descriptor X j (finite_trace_last is tr))
    (trX: list (vtransition_item X))
    (HtrX: equivocator_vlsm_trace_project _ tr j = Some (trX, i))
    ,
    Exists (field_selector output m) trX.
Proof.
  apply Exists_exists in Hbbs.
  destruct Hbbs as [item [Hin Houtput]].
  destruct (equivocator_label_descriptor (l item)) as [sn | i] eqn:Hsndl.
  - destruct item. destruct l; inversion Hsndl.
    subst. simpl in *.
    specialize
      (preloaded_equivocator_vlsm_trace_project_valid_item_new_machine
         _ _ Htr _ Hin _ eq_refl)
      as Hitem.
    simpl in Hitem.
    destruct Hitem as [_ [Hcontra _]]. congruence.
  - apply valid_trace_add_default_last in Htr.
    specialize
    (preloaded_equivocator_vlsm_trace_project_valid_item
       _ _ _ Htr _ Hin _ Hsndl)
      as [itemx [[d Hitemx] [trx [Hinx [ifinal [ifirst [Hifirst [Hifinal Htrx]]]]]]]].
  exists ifinal. exists ifirst. split; [done |].
  split; [done |].
  exists trx. exists Htrx.
  apply Exists_exists. exists itemx. split; [done |].
  apply equivocator_transition_item_project_inv_messages in Hitemx.
  destruct Hitemx as [_ [_ [_ [_ Hitemx]]]].
  simpl in *.
  congruence.
Qed.

Section oracle_lifting.

Context
  selector
  (Hselector_io : forall l1 l2 s1 s2 im om m, selector m  {| l:= l1; input := im; destination := s1; output := om |} <-> selector m  {| l:= l2; input := im; destination := s2; output := om |})
  oracle
  (Hdec : RelDecision oracle)
  (Hstepwise : oracle_stepwise_props (vlsm := X) selector oracle).

Definition equivocator_selector
  (m : message)
  (item : vtransition_item equivocator_vlsm)
  : Prop
  :=
  match (l item) with
  | Spawn _ => False
  | ContinueWith _ l | ForkWith _ l =>
    selector m
      {| l := l
       ; input := input item
       ; destination := equivocator_state_zero (destination item)
       ; output := output item
      |}
  end.

(** We define [equivocator_oracle] for the [equivocator_vlsm] as being the oracle for any
of the internal machines.
*)
Definition equivocator_oracle
  (s : vstate equivocator_vlsm)
  (m : message)
  : Prop
  :=
  exists i si, equivocator_state_project s i = Some si /\
    oracle si m.

Lemma equivocator_oracle_dec
  : RelDecision equivocator_oracle.
Proof.
  intros s m.
  eapply
    (Decision_iff
      (P := Exists
        (fun i =>
          from_option (fun si => oracle si m) False
            (equivocator_state_project s i)) _)).
  - split; unfold equivocator_oracle; rewrite Exists_exists; cycle 1.
    + intros (i & si & Hsi & Hi); exists i.
      split; [| by rewrite Hsi].
      by eapply up_to_n_full, equivocator_state_project_Some_rev.
    + intros (i & _ & Hi); exists i.
      by destruct (equivocator_state_project s i); [eexists |].
  - apply Exists_dec; intro i.
    destruct (equivocator_state_project s i); [apply Hdec | typeclasses eauto]. 
Qed.

Lemma equivocator_oracle_stepwise_props
  : oracle_stepwise_props (vlsm := equivocator_vlsm) equivocator_selector equivocator_oracle.
Proof.
  destruct Hstepwise.
  split; intros.
  - destruct H as [Hn His]. unfold is_singleton_state in Hn.
    intros [j [sj [Hsj Hmbrj]]].
    apply equivocator_state_project_Some_rev in Hsj as Hltj.
    assert (j = 0) by lia. subst.
    rewrite equivocator_state_project_zero in Hsj.
    inversion Hsj. subst.
    by elim (oracle_no_inits  _ His m).
  - unfold equivocator_oracle.
    destruct H as [[Hs [_ Hv]] Ht].
    destruct l as [sdesc | idesc l | idesc l].
    + inversion Ht. subst. clear Ht.
      destruct Hv as [Hisdesc Him]. simpl in Him. subst im.
      split.
      * intros [ins [sins [Hsins Hir]]]. right.
        destruct_equivocator_state_extend_project s sdesc ins Hins
        ; [by exists ins, sins | | done].
        inversion Hsins. subst.
        by elim (oracle_no_inits _ Hisdesc msg).
      * intros [H | [ins [sins [Hsins Hir]]]]; [done |].
        exists ins, sins. split; [| done].
        rewrite equivocator_state_extend_project_1; [done |].
        by apply equivocator_state_project_Some_rev in Hsins.
    + cbn in Hv.
      destruct (equivocator_state_project s idesc) as [sidesc|] eqn:Hidesc; [| done].
      destruct (vtransition X l (sidesc, im)) as (sidesc', om') eqn:Htx.
      specialize
        (oracle_step_update l sidesc im sidesc' om').
      spec oracle_step_update.
      { repeat split
        ; [..| eexists _; apply (pre_loaded_with_all_messages_message_valid_initial_state_message X) | done | done].
        apply (preloaded_equivocator_state_project_valid_state X _ Hs _ _ Hidesc).
      }
     specialize (existing_false_label_equivocator_state_project_not_same X Ht _ Hidesc)
       as Hnot_same.
     specialize (existing_false_label_equivocator_state_project_same X Ht _ Hidesc _ _ Htx)
       as [Hom Hsame].
     subst om'.
     specialize (existing_false_label_equivocator_transition_size X Ht _ Hidesc) as Ht_size.
     spec oracle_step_update msg.
     split.
      * intros [i [s'i [Hs'i Hbri]]].
        apply equivocator_state_project_Some_rev in Hs'i as Hlti.
        destruct (decide (idesc = i)).
        --  subst i. simpl in Hsame. rewrite Hs'i in Hsame.
          simpl in Hsame. subst s'i.
          apply oracle_step_update in Hbri.
          destruct Hbri as [H | Hbri]; [| by right; eexists _,_].
          left. revert H. apply Hselector_io.
        -- right. exists i, s'i. split; [| done].
          spec Hnot_same i.
          spec Hnot_same; [lia|]. spec Hnot_same n.
          simpl in Hnot_same. rewrite Hs'i in Hnot_same.
          destruct_equivocator_state_project s i si Hlti'; [|lia].
          simpl in Hnot_same. congruence.
      * apply proj2 in oracle_step_update.
        apply equivocator_state_project_Some_rev in Hidesc as Hltidesc.
        intros [Heq_im | [ins [sins [Hsins Hbri]]]].
        -- unfold equivocator_selector in Heq_im. simpl in Heq_im.
          rewrite Hselector_io with (l2 := l) (s2 := sidesc') in Heq_im.
          specialize (oracle_step_update (or_introl Heq_im)).
          exists idesc, sidesc'.
          simpl in Hsame.
          destruct_equivocator_state_project  s' idesc _sidesc' Hlst; [|lia].
          simpl in Hsame.
          by subst.
        -- apply equivocator_state_project_Some_rev in Hsins as Hltins.
          simpl in Hsame.
          destruct (decide (idesc = ins)). subst idesc.
          ++ rewrite Hsins in Hidesc. inversion Hidesc. subst sidesc.
            specialize (oracle_step_update (or_intror Hbri)).
            exists ins, sidesc'. split; [| done].
            simpl in Hsame.
            destruct_equivocator_state_project s' ins _sidesc' Hins; [|lia].
            by subst.
          ++ exists ins, sins. split; [| done].
            spec Hnot_same ins. spec Hnot_same; [lia|]. spec Hnot_same n.
            simpl in Hnot_same. rewrite Hsins in Hnot_same.
            destruct_equivocator_state_project s' ins _sins Hins; [|lia].
            simpl in Hnot_same. congruence.
    + cbn in Hv.
      destruct (equivocator_state_project s idesc) as [sidesc|] eqn:Hidesc; [| done].
      destruct (vtransition X l (sidesc, im)) as (sidesc', om') eqn:Htx.
      specialize
        (oracle_step_update l sidesc im sidesc' om').
      spec oracle_step_update.
      { repeat split
        ; [..| eexists _; apply (pre_loaded_with_all_messages_message_valid_initial_state_message X) | done | done].
        apply (preloaded_equivocator_state_project_valid_state X _ Hs _ _ Hidesc).
      }
      specialize (existing_true_label_equivocator_state_project_not_last X Ht _ Hidesc)
        as Hnot_last.
       specialize (existing_true_label_equivocator_state_project_last X Ht _ Hidesc _ _ Htx)
        as [Hom Hlast].
      subst om'.
      specialize (existing_true_label_equivocator_transition_size X Ht _ Hidesc) as Ht_size.
      spec oracle_step_update msg.
      split.
      * intros [i [s'i [Hs'i Hbri]]].
        apply equivocator_state_project_Some_rev in Hs'i as Hlti.
        destruct (decide (i = equivocator_state_n s)).
        --  subst i. simpl in Hlast. rewrite Hs'i in Hlast.
          simpl in Hlast. subst s'i.
          apply oracle_step_update in Hbri.
          destruct Hbri as [H | Hbri]; [| by right; eexists _,_].
          left. revert H. apply Hselector_io.
        -- right. exists i, s'i. split; [| done].
          spec Hnot_last i.
          spec Hnot_last; [lia|].
          simpl in Hnot_last. rewrite Hs'i in Hnot_last.
          destruct_equivocator_state_project s i si Hlti'; [|lia].
          simpl in Hnot_last.
          congruence.
      * apply proj2 in oracle_step_update.
        intros [Heq_im | [ins [sins [Hsins Hbri]]]].
        -- unfold equivocator_selector in Heq_im. simpl in Heq_im.
          rewrite Hselector_io with (l2 := l) (s2 := sidesc') in Heq_im.
          specialize (oracle_step_update (or_introl Heq_im)).
          exists (equivocator_state_n s), sidesc'.
          simpl in Hlast.
          destruct_equivocator_state_project  s' (equivocator_state_n s) _sidesc' Hlst; [|lia].
          by subst.
        -- apply equivocator_state_project_Some_rev in Hsins as Hltins.
            spec Hnot_last ins. spec Hnot_last; [lia|].
            simpl in Hnot_last. rewrite Hsins in Hnot_last.
            exists ins, sins. split; [| done].
            destruct_equivocator_state_project s' ins _sins Hltins'; [|lia].
            simpl in Hnot_last. congruence.
Qed.

End oracle_lifting.

Section has_been_received_lifting.

(** ** Lifting the [HasBeenReceivedCapability] *)

Context
  `{HasBeenReceivedCapability message X}
  .

(** We define [has_been_received] for the [equivocator_vlsm] as being received by any
of the internal machines.
*)
Definition equivocator_has_been_received  := equivocator_oracle (has_been_received X).

Global Instance equivocator_has_been_received_dec
  : RelDecision equivocator_has_been_received
  := equivocator_oracle_dec (has_been_received X) _.

Lemma equivocator_has_been_received_stepwise_props
  : has_been_received_stepwise_props (vlsm := equivocator_vlsm) equivocator_has_been_received.
Proof.
  eapply oracle_stepwise_props_change_selector.
  - apply equivocator_oracle_stepwise_props
    ; [|apply has_been_received_stepwise_from_trace].
    cbv; itauto.
  - intros s item; destruct item, l; cbn.
    2,3:itauto.
    intros [(_ & _ & _ & Him) _]; simpl in Him; subst.
    itauto congruence.
Qed.

(** Finally we define the [HasBeenReceivedCapability] for the [equivocator_vlsm].
*)
Global Instance equivocator_HasBeenReceivedCapability
  : HasBeenReceivedCapability equivocator_vlsm
  := HasBeenReceivedCapability_from_stepwise (vlsm := equivocator_vlsm)
    equivocator_has_been_received_dec
    equivocator_has_been_received_stepwise_props.

End has_been_received_lifting.

Section has_been_sent_lifting.

(** ** Lifting the [HasBeenSentCapability] *)

Context
  `{HasBeenSentCapability message X}
  .

(** We define [has_been_sent] for the [equivocator_vlsm] as being sent by any
of the internal machines.
*)
Definition equivocator_has_been_sent  := equivocator_oracle (has_been_sent X).

Global Instance equivocator_has_been_sent_dec
  : RelDecision equivocator_has_been_sent
  := equivocator_oracle_dec (has_been_sent X) _.

Lemma equivocator_has_been_sent_stepwise_props
  : has_been_sent_stepwise_props (vlsm := equivocator_vlsm) equivocator_has_been_sent.
Proof.
  eapply oracle_stepwise_props_change_selector.
  - apply equivocator_oracle_stepwise_props
    ; [|apply has_been_sent_stepwise_from_trace].
    cbv; itauto.
  - intros s item; destruct item, l; cbn.
    2,3:itauto.
    intros [_ Ht]; inversion_clear Ht.
    itauto congruence.
Qed.

(** Finally we define the [HasBeenSentCapability] for the [equivocator_vlsm].
*)
Global Instance equivocator_HasBeenSentCapability
  : HasBeenSentCapability equivocator_vlsm
  := HasBeenSentCapability_from_stepwise (vlsm := equivocator_vlsm)
    equivocator_has_been_sent_dec
    equivocator_has_been_sent_stepwise_props.

End has_been_sent_lifting.

Section ComputableSentMessages_lifting.

(** ** Lifting the [ComputableSentMessages] property *)

Context
  {Hsent_messages : ComputableSentMessages X}
  `(EqDecision message)
  (Hbeen_sent_X := @ComputableSentMessages_HasBeenSentCapability message X Hsent_messages)
  .

Existing Instance Hbeen_sent_X.

(** We define the [sent_messages_fn] for the [equivocator_vlsm] as the
union of all [sent_messages_fn] for its internal machines.
*)
Definition equivocator_sent_messages_fn
  (s : vstate equivocator_vlsm)
  : set message
  :=
  fold_right set_union []
    (map
      (fun i =>
        match equivocator_state_project s i with
        | None => []
        | Some si => sent_messages_fn X si
        end)
      (up_to_n_listing (equivocator_state_n s))).

(** [equivocator_sent_messages_fn] captures all [sent_messages] for that state.
*)
Lemma equivocator_sent_messages_full
  (s : vstate equivocator_vlsm)
  (Hs : valid_state_prop (pre_loaded_with_all_messages_vlsm equivocator_vlsm) s)
  (m : message)
  : m ∈ (equivocator_sent_messages_fn s)
  <-> exists (sm : sent_messages equivocator_vlsm s), proj1_sig sm = m.
Proof.
  specialize (preloaded_equivocator_state_project_valid_state _ _ Hs) as HpsX.
  split.
  - intro Hin. apply set_union_in_iterated in Hin.
    apply Exists_exists in Hin as [msgsi [Hmsgsi Hin]].
    apply elem_of_list_fmap in Hmsgsi.
    destruct Hmsgsi as [i [Heq _]]. subst.
    destruct (equivocator_state_project s i) as [si|] eqn:Hsi; [|inversion Hin].
    specialize (HpsX _ _ Hsi).
    apply (sent_messages_full X) in Hin; [| done].
    destruct Hin as [[m' Hm] Heq]. simpl in Heq. subst m'.
    apply (sent_messages_consistency X) in Hm; [| done].
    destruct Hs as [om Hs].
    apply (valid_state_message_has_trace (pre_loaded_with_all_messages_vlsm equivocator_vlsm)) in Hs.
    destruct Hs as [[Hs _] | [is [tr [Htr _]]]].
    + specialize (Hm si []).
      spec Hm.
      { split.
        - by constructor.
        - revert Hsi Hs. apply (equivocator_vlsm_initial_state_preservation_rev X).
      }
      inversion Hm.
    + apply valid_trace_get_last in Htr as Hlst.
      assert (Hbm : selected_message_exists_in_some_preloaded_traces equivocator_vlsm (field_selector output) s m)
      ; [| by exists (exist _ m Hbm)].
      exists is. exists tr. exists Htr.
      subst s.
      destruct
        (preloaded_equivocator_vlsm_trace_project_valid _ _ _ _ (proj1 Htr) _ _ Hsi)
        as [trX [di [Hproject Hdi]]].
      destruct di as [sn | id].
      * apply equivocator_vlsm_trace_project_output_reflecting with trX (Existing i) (NewMachine sn)
        ; [done |].
        apply (Hm sn trX). split; apply Hdi.
      * destruct Hdi as [isid [Hi' HtrX]].
        apply equivocator_vlsm_trace_project_output_reflecting with trX (Existing i) (Existing id)
        ; [done |].
        apply (Hm isid trX). split; [done |].
        apply (equivocator_vlsm_initial_state_preservation_rev X _ _ _ Hi'). apply Htr.
  - intros [[m' Hm] Heq]. simpl in Heq. subst m'.
    destruct Hm as [is [tr [Htr Hexists]]].
    destruct
      (equivocator_vlsm_trace_project_output_reflecting_inv _ _ (proj1 (valid_trace_forget_last Htr)) _ Hexists)
      as [ifinal [istart [_ [_ [trX [Hproject HexistsX]]]]]].
    assert (Hntr : tr <> []) by (intro contra; subst; inversion Hexists).
    destruct ifinal as [sfinal | i]
    ; [
      rewrite equivocator_vlsm_trace_project_on_new_machine in Hproject
      ; inversion Hproject; subst; inversion HexistsX
      |].
    specialize
      (preloaded_equivocator_vlsm_valid_trace_project_inv2 _ _ _ _ Hntr (proj1 Htr) _ _ _ Hproject)
      as [si [Hi Histart]].
    apply set_union_in_iterated. apply Exists_exists.
    exists (sent_messages_fn X si).
    split.
    + rewrite elem_of_list_fmap.
      exists i. rewrite Hi.
      split; [done |]. apply up_to_n_full.
      by apply equivocator_state_project_Some_rev in Hi.
    + specialize (HpsX _ _ Hi). apply (sent_messages_full X); [apply HpsX|].
      assert (Hm : selected_message_exists_in_some_preloaded_traces X (field_selector output) si m)
      ; [| by exists (exist _ m Hm)].
      destruct istart as [sstart | istart].
      * by exists sstart, trX, Histart.
      * destruct Histart as [isi [Histart [HtrX HinitX]]].
        by exists isi, trX, (conj HtrX (HinitX (proj2 Htr))).
Qed.

(** Finally, we define the [ComputableSentMessages] instance for the
[equivocator_vlsm].
Note that we can reuse the consistency property proved above since
[ComputableSentMessages] for <<X>> implies [HasBeenSentCapability].
*)
Program Definition equivocator_ComputableSentMessages
  : ComputableSentMessages equivocator_vlsm
  :=
  {|
    sent_messages_fn := equivocator_sent_messages_fn;
    sent_messages_full := equivocator_sent_messages_full;
  |}.
Next Obligation.
  by intros; apply has_been_sent_consistency;
   [eapply equivocator_HasBeenSentCapability|].
Qed.

End ComputableSentMessages_lifting.

End equivocator_vlsm_message_properties.
