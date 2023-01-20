From stdpp Require Import prelude.
From VLSM.Lib Require Import Preamble ListExtras.
From VLSM.Core Require Import VLSM VLSMProjections Equivocators.Equivocators.

(** * VLSM Projecting Equivocator Traces *)

Section sec_equivocator_vlsm_projections.

(**
  Given an [equivocator_vlsm] trace ending in a state <<s>>, we can obtain a
  trace in the original vlsm leading to the <<si>>, the  <<i>>th internal
  state in <<s>>, by extracting a path leading to <<si>>.

  This section is devoting to formalizing this projects studying its
  properties. In particular, we show that given a [valid_trace] for
  the [equivocator_vlsm], we can always extract such a trace for any valid
  index, and, furthermore, that the trace extracted is valid for the
  original machine.
*)

Context
  {message : Type}
  (X : VLSM message)
  (equivocator_vlsm := equivocator_vlsm X)
  (MachineDescriptor := MachineDescriptor X)
  .

(**
  Given a [transition_item] <<item>> for the [equivocator_vlsm] and a
  [MachineDescriptor] referring to a position in the [destination] of <<item>>,
  it returns a transition item for the original machine (if the descriptor
  matches the copy affected by this transition) and a new machine descriptor
  referring to a position in the state prior to the transition.
*)
Definition equivocator_vlsm_transition_item_project
  (item : vtransition_item equivocator_vlsm)
  (descriptor : MachineDescriptor)
  : option (option (vtransition_item X) * MachineDescriptor)
  :=
  match descriptor with
  | NewMachine _ => Some (None, descriptor)
  | Existing j =>
    match item with {| l := el; input := im; output := om; destination := s |} =>
      match equivocator_state_project s j with
      | None => None
      | Some sj =>
        match el with
        | Spawn sn =>
          if (decide (j = equivocator_state_last s)) then (* this is the first state *)
            Some (None, NewMachine sn)
          else Some (None, Existing j)
        | ForkWith i lx =>
            if (decide (j = equivocator_state_last s)) then (* this is the copy *)
              Some (Some {| l := lx; input := im; output := om; destination := sj |}, Existing i)
            else Some (None, Existing j)
        | ContinueWith i lx =>
          if decide (i = j) then
              Some ( Some {| l := lx; input := im; output := om; destination := sj |}, Existing i)
            else Some (None, Existing j)
        end
      end
    end
  end.

(**
  Since equivocators always have machine 0, We can always project a [valid]
  equivocator [transition item] to component 0.
*)
Lemma equivocators_vlsm_transition_item_project_zero_descriptor
  (item : vtransition_item equivocator_vlsm)
  s
  (Ht : vtransition equivocator_vlsm (l item) (s, input item) = (destination item, output item))
  (Hv : vvalid equivocator_vlsm (l item) (s, input item))
  : exists oitem, equivocator_vlsm_transition_item_project item (Existing 0) =
      Some (oitem, Existing 0).
Proof.
  destruct item.
  destruct l; cbn in Hv, Ht |- *.
  - inversion_clear Ht. destruct Hv as [Hv Hinput]. subst input.
    rewrite equivocator_state_extend_lst.
    rewrite decide_False by (cbv; lia).
    by eexists.
  - by destruct (decide _); subst; eexists.
  - destruct (equivocator_state_project s n) as [si |]; [| done].
    destruct (vtransition _ _ _) as (si', om').
    inversion_clear Ht.
    rewrite equivocator_state_extend_lst.
    by eexists.
Qed.

(** An injectivity result for [equivocator_vlsm_transition_item_project]. *)
Lemma equivocator_vlsm_transition_item_project_some_inj
  {item : vtransition_item equivocator_vlsm}
  {itemX itemX' : vtransition_item X}
  {i i' : nat}
  (idescriptor := Existing i)
  (idescriptor' := Existing i')
  {odescriptor odescriptor' : MachineDescriptor}
  (HitemX : equivocator_vlsm_transition_item_project item idescriptor =
    Some (Some itemX, odescriptor))
  (HitemX' : equivocator_vlsm_transition_item_project item idescriptor' =
    Some (Some itemX', odescriptor'))
  : i = i' /\ itemX = itemX' /\ odescriptor = odescriptor'.
Proof.
  destruct item.
  destruct l as [sn | j ls | j l2]; cbn in HitemX, HitemX'
  ; destruct (equivocator_state_project _ i) as [si |] eqn:Hsi; [| done | | done | | done]
  ; destruct (equivocator_state_project _ i') as [si' |] eqn:Hsi'; [| done | | done | | done]
  ; case_decide; [done | done | | done | | done]; subst
  ; case_decide; [| done | | done]; subst.
  - assert (si = si') by congruence; subst si'.
    inversion_clear HitemX.
    inversion_clear HitemX'.
    by repeat split.
  - assert (si = si') by congruence; subst si'.
    subst.
    inversion_clear HitemX.
    inversion_clear HitemX'.
    by repeat split.
Qed.

(**
  [equivocator_vlsm_transition_item_project] only fails for an out-of-range
  descriptor.
*)
Lemma equivocator_transition_item_project_inv_none
  (item : vtransition_item equivocator_vlsm)
  (descriptor : MachineDescriptor)
  (Hitem: equivocator_vlsm_transition_item_project item descriptor = None)
  : exists (i : nat),
    descriptor = Existing i /\
    equivocator_state_project (destination item) i = None.
Proof.
  destruct item.
  destruct descriptor as [s | i]; cbn in *; [by congruence |].
  exists i. split; [done |].
  destruct_equivocator_state_project destination i si Hi; [| done].
  by destruct l; case_decide.
Qed.

Lemma equivocator_transition_item_project_proper
  (item : vtransition_item equivocator_vlsm)
  (descriptor : MachineDescriptor)
  (Hproper : proper_descriptor X descriptor (destination item))
  : is_Some (equivocator_vlsm_transition_item_project item descriptor).
Proof.
  destruct (equivocator_vlsm_transition_item_project _ _) as [x |] eqn:contra
  ; [by eexists |].
  apply equivocator_transition_item_project_inv_none in contra.
  destruct contra as [id [Heqd Hd]].
  subst. simpl in *. destruct Hproper as [x Hproper].
  by congruence.
Qed.

(**
  If [equivocator_vlsm_transition_item_project] produces a transition item,
  then that item has the same [input] and [output] as the argument item.
*)
Lemma equivocator_transition_item_project_inv_messages
  (item : vtransition_item equivocator_vlsm)
  (itemX : vtransition_item X)
  (idescriptor odescriptor : MachineDescriptor)
  (Hitem : equivocator_vlsm_transition_item_project item idescriptor = Some (Some itemX, odescriptor))
  : exists
    (i : nat),
    idescriptor = Existing i /\
    proper_descriptor X idescriptor (destination item) /\
    input item = input itemX /\ output item = output itemX.
Proof.
  destruct idescriptor as [s | j]; cbn in Hitem; [by congruence |].
  exists j. split; [done |].
  destruct item.
  simpl in Hitem |- *.
  destruct (equivocator_state_project _ _); [| done].
  split; [by eexists |].
  by destruct l as [s | i' | i']; case_decide; inversion Hitem.
Qed.

(**
  If the [destination] of a [valid] equivocator [transition_item] is singleton,
  then by projecting the item to component 0 we actually obtain a
  [transition_item] for the original machine.
*)
Lemma no_equivocating_equivocator_transition_item_project
  (item : vtransition_item equivocator_vlsm)
  (Hno_equiv_item : is_singleton_state X (destination item))
  (s : vstate equivocator_vlsm)
  (Hv : vvalid equivocator_vlsm (l item) (s, input item))
  (Ht : vtransition equivocator_vlsm (l item) (s, input item) = (destination item, output item))
  : exists (Hex : existing_equivocator_label _ (l item)),
    equivocator_vlsm_transition_item_project item (Existing 0) =
      Some (Some
        {| l := existing_equivocator_label_extract _ (l item) Hex;
           input := input item; output := output item;
           destination := equivocator_state_descriptor_project (destination item) (Existing 0)
        |}, Existing 0).
Proof.
  destruct item.
  unfold VLSM.l, VLSM.input, VLSM.output, VLSM.destination in *.
  specialize
    (equivocator_transition_no_equivocation_zero_descriptor X _ _ _ _ _ Hv Ht Hno_equiv_item)
    as [li Heq_eqvi].
  subst. simpl. repeat split.
Qed.

(**
  For every valid transition there exists a (non-equivocating)
  [MachineDescriptor] for its destination such that by projecting
  the transition item through that descriptor we obtain the transition
  item corresponding to the input transition.
*)
Lemma exists_equivocator_transition_item_project
  (item : vtransition_item equivocator_vlsm)
  (s : vstate equivocator_vlsm)
  (Hs : proper_existing_equivocator_label X (l item) s)
  (Hv : vvalid equivocator_vlsm (l item) (s, input item))
  (Ht : vtransition equivocator_vlsm (l item) (s, input item) = (destination item, output item))
  : proper_equivocator_label X (l item) s /\
    exists dest_eqv,
      existing_descriptor X dest_eqv (destination item) /\
        equivocator_vlsm_transition_item_project item dest_eqv = Some
          (Some
            {| l := existing_equivocator_label_extract _ (l item)
                (existing_equivocator_label_forget_proper _ Hs);
               input := input item;
               output := output item;
               destination := equivocator_state_descriptor_project (destination item) dest_eqv
            |}, equivocator_label_descriptor (l item)).
Proof.
  destruct item. simpl in *.
  destruct l as [sn | i l | i l]
  ; [by inversion Hs | ..]
  ; cbn in Hv, Ht
  ; destruct (equivocator_state_project _ _) as [si |] eqn:Hpr; [| done | | done]
  ; split; [done | | done |]
  ; destruct (vtransition _ _ _) as (si', om'); inversion_clear Ht.
  - exists (Existing i).
    simpl.
    apply equivocator_state_project_Some_rev in Hpr.
    by rewrite equivocator_state_update_project_eq, decide_True.
  - exists (Existing (equivocator_state_n s)); cbn.
    destruct_equivocator_state_extend_project s si' (equivocator_state_n s) Hn
    ; [lia | | lia]; cbn.
    by rewrite (equivocator_state_last_n _ s), decide_True.
Qed.

(**
  This property attempts to characterize the descriptor obtained after
  applying an equivocator projection (trace, transition_item) function in
  terms of the input descriptor and the resulting state.

  It is assumed that the original_descriptor is a proper descriptor
  w.r.t. the final state of the trace/transition on which
  [equivocator_vlsm_transition_item_project] or [equivocator_vlsm_trace_project]
  was applied. In particular this makes s_descriptor a proper descriptor for
  the state s (see the lemmas above and below).

  What this property adds is the fact that it constrains more the output
  descriptor of a projection operation in terms of the input descriptor
  (if the input is Newmachine, the output must be Newmachine, if both
  are Existing, then the output index must be less than the input), while also
  guaranteeing that the output state of such a projection has a size less than
  the index of the input descriptor in case that output descriptor becomes
  NewMachine (signaling that the projection is complete).

  This property is crucial for establishing an invariant on known equivocators
  (see [full_node_limited_equivocation_constraint_known_equivocators]).
*)
Definition previous_state_descriptor_prop
  (original_descriptor : MachineDescriptor)
  (s : vstate equivocator_vlsm)
  (s_descriptor : MachineDescriptor)
  : Prop :=
    match original_descriptor with
    | NewMachine sd => s_descriptor = original_descriptor
    | Existing id =>
      match s_descriptor with
      | NewMachine _ => equivocator_state_n s <= id
      | Existing id' => id' <= id
      end
    end.

Lemma equivocator_transition_item_project_proper_characterization
  (item : vtransition_item equivocator_vlsm)
  (descriptor : MachineDescriptor)
  (Hproper : proper_descriptor X descriptor (destination item))
  : exists oitem descriptor',
    equivocator_vlsm_transition_item_project item descriptor = Some (oitem, descriptor')
    /\ match oitem with
      | Some itemx =>
        (exists (Hex : existing_equivocator_label _ (l item)),
          l itemx = existing_equivocator_label_extract _ (l item) Hex) /\
        input item = input itemx /\ output item = output itemx /\
        (equivocator_state_descriptor_project (destination item) descriptor = destination itemx)
        /\ descriptor' = equivocator_label_descriptor (l item)
      | None => True
      end
    /\ forall
      (s : vstate equivocator_vlsm)
      (Hv : vvalid equivocator_vlsm (l item) (s, input item))
      (Ht : vtransition equivocator_vlsm (l item) (s, input item) = (destination item, output item)),
      proper_descriptor X descriptor' s /\
      previous_state_descriptor_prop descriptor s descriptor' /\
      match oitem with
      | Some itemx =>
        forall (sx : vstate X)
          (Hsx : sx = equivocator_state_descriptor_project s descriptor'),
          vvalid X (l itemx) (sx, input itemx) /\
          vtransition X (l itemx) (sx, input itemx) = (destination itemx, output itemx)
      | None =>
        equivocator_state_descriptor_project (destination item) descriptor =
        equivocator_state_descriptor_project s descriptor'
      end.
Proof.
  destruct item. simpl. simpl in Hproper.
  destruct descriptor eqn:Heqvi; cbn.
  - by eexists None, _.
  - destruct l as [nsi | ieqvi li | ieqvi li]
    ; destruct Hproper as [destn Hpr]; rewrite Hpr
    ; case_decide; subst
    ; eexists _, _; split; try done.
    + split; [done |].
      intros.
      split; [by apply Hv |].
      specialize (new_machine_label_equivocator_transition_size X Ht) as Ht_size.
      specialize (equivocator_state_last_n X destination) as Hlst_size.
      split; [lia |].
      rewrite <-
        (new_machine_label_equivocator_state_project_last X Ht).
      simpl.
      replace (equivocator_state_n s) with (equivocator_state_last destination) by lia.
      by rewrite Hpr.
    + split; [done |].
      intros.
      specialize (new_machine_label_equivocator_transition_size X Ht) as Ht_size.
      cut (proper_descriptor X (Existing n) s).
      { intros [_sn Hpr']. split_and!; [by eexists _sn | lia |].
        apply equivocator_state_project_Some_rev in Hpr'.
        rewrite <- (new_machine_label_equivocator_state_project_not_last X Ht) by done.
        by simpl; rewrite Hpr.
      }
      simpl.
      apply equivocator_state_project_Some_rev in Hpr as Hn.
      specialize (equivocator_state_last_n X destination) as Hlst_size.
      by destruct_equivocator_state_project s n _sn Hn'; [eexists | lia].
    + simpl.
      split; [repeat split |].
      intros.
      cbn in Hv.
      destruct (equivocator_state_project s n) as [sn |] eqn:Hpri
      ; [| done].
      split; [by eexists |].
      split; [lia |].
      intros. subst sx. simpl.
      split; [done |].
      destruct (vtransition _ _ _) as (si', _output).
      inversion Ht. subst.
      rewrite equivocator_state_update_project_eq in Hpr
      ; [by inversion Hpr | | done].
      by apply equivocator_state_project_Some_rev in Hpri.
    + split; [done |].
      intros.
      cbn in Hv.
      destruct (equivocator_state_project s ieqvi) as [sieqvi |] eqn:Hpri
      ; [| done].
      cut (proper_descriptor X (Existing n) s).
      { intro Hproper. split_and!; [done | lia |].
        destruct Hproper as [_sn Hprn].
        apply equivocator_state_project_Some_rev in Hprn.
        rewrite <- (existing_false_label_equivocator_state_project_not_same X Ht _ Hpri _ Hprn H).
        by simpl; rewrite Hpr.
      }
      simpl.
      specialize (existing_false_label_equivocator_transition_size X Ht _ Hpri) as Ht_size.
      specialize (equivocator_state_last_n X destination) as Hlst_size.
      destruct_equivocator_state_project s n _sn Hn; [by eexists |].
      by apply equivocator_state_project_Some_rev in Hpr; lia.
    + split; [by simpl; repeat split |].
      intros.
      cbn in Hv.
      simpl.
      destruct (equivocator_state_project s ieqvi) as [sieqvi |] eqn:Hpri
      ; [| done].
      split; [by eexists |].
      specialize (existing_true_label_equivocator_transition_size X Ht _ Hpri) as Ht_size.
      specialize (equivocator_state_last_n X destination) as Hlst_size.
      specialize (existing_true_label_equivocator_state_project_last X Ht _ Hpri) as Ht_pr.
      apply equivocator_state_project_Some_rev in Hpri as Hlt.
      split; [lia |].
      simpl in *.
      intros. subst  sx.
      rewrite Hpri in *.
      split; [done |].
      destruct (vtransition _ _ _).
      specialize (Ht_pr _ _ eq_refl) as [Heqo Heqs0].
      subst.
      replace (equivocator_state_n s) with (equivocator_state_last destination) by lia.
      by rewrite Hpr.
    + split; [done |].
      intros.
      cbn in Hv.
      destruct (equivocator_state_project s ieqvi) as [sieqvi |] eqn:Hpri
      ; [| done].
      cut (proper_descriptor X (Existing n) s).
      { intro Hproper. split_and!; [done | lia |].
        destruct Hproper as [_sn Hprn].
        apply equivocator_state_project_Some_rev in Hprn.
        rewrite <-
          (existing_true_label_equivocator_state_project_not_last X Ht _ Hpri _ Hprn).
        by cbn; rewrite Hpr.
      }
      simpl.
      specialize (existing_true_label_equivocator_transition_size X Ht _ Hpri) as Ht_size.
      specialize (equivocator_state_last_n X destination) as Hlst_size.
      destruct_equivocator_state_project s n _sn Hn; [by eexists |].
      by apply equivocator_state_project_Some_rev in Hpr; lia.
Qed.

Lemma equivocator_transition_item_project_preserves_equivocating_indices
  (item : vtransition_item equivocator_vlsm)
  (descriptor : MachineDescriptor)
  (Hproper : proper_descriptor X descriptor (destination item))
  oitem idescriptor
  (Hproject : equivocator_vlsm_transition_item_project item descriptor = Some (oitem, idescriptor))
  (s : vstate equivocator_vlsm)
  (Hv : vvalid equivocator_vlsm (l item) (s, input item))
  (Ht : vtransition equivocator_vlsm (l item) (s, input item) = (destination item, output item))
  : is_equivocating_state X s \/ is_newmachine_descriptor X idescriptor ->
    is_equivocating_state X (destination item) \/ is_newmachine_descriptor X descriptor.
Proof.
  specialize
    (equivocator_transition_item_project_proper_characterization item _ Hproper)
    as Hchar.
  destruct item. simpl in *.
  destruct Hchar as [_oitemx [_deqv' [_Hpr [Hchar1 Hchar2]]] ].
  rewrite Hproject in _Hpr. inversion _Hpr. subst _oitemx _deqv'. clear _Hpr.
  specialize (Hchar2 _ Hv Ht).
  destruct Hchar2 as [Hdeqv' Hchar2].
  destruct l as [sn | j l | j l]; simpl in *
  ; [left; inversion_clear Ht;  cbv; lia | ..]
  ; (destruct oitem as [itemx |]
    ; [intros Heqv; left; destruct itemx; destruct Hchar1
        as [[_ Hl] [Hinput [Houtput [Hdest Heq_deqv']]]]
      ; subst; apply (equivocator_transition_preserves_equivocating_state X _ _ _ _ _ Ht)
      ; destruct Heqv as [Heqv | Heqv]; done
      |])
  ; cbn in Hv
  ; (destruct (equivocator_state_project s j) as [sj |] eqn:Hsj; [| done]).
  - specialize (existing_false_label_equivocator_transition_size X Ht _ Hsj) as Ht_size.
    intros [Heqv | Heqv]; [clear -Ht_size Heqv; cbv in *; lia |].
    right.
    unfold equivocator_vlsm_transition_item_project in Hproject.
    destruct descriptor as [| deqvi]; [done |].
    destruct (equivocator_state_project destination deqvi); [| done].
    case_decide; [by congruence |].
    by inversion Hproject; subst; inversion Heqv.
  - specialize (existing_true_label_equivocator_transition_size X Ht _ Hsj) as Ht_size.
    left. unfold is_equivocating_state, is_singleton_state. rewrite Ht_size.
    by cbv; lia.
Qed.

Lemma equivocator_transition_item_project_inv_characterization
  (item : vtransition_item equivocator_vlsm)
  (itemx : vtransition_item X)
  (descriptor descriptor' : MachineDescriptor)
  (Hitem : equivocator_vlsm_transition_item_project item descriptor = Some (Some itemx, descriptor'))
  : (exists (Hex : existing_equivocator_label _ (l item)), l itemx =
      existing_equivocator_label_extract _ (l item) Hex) /\
    input item = input itemx /\ output item = output itemx /\
    (equivocator_state_descriptor_project (destination item) descriptor = destination itemx)
    /\ descriptor' = equivocator_label_descriptor (l item)
    .
Proof.
  apply equivocator_transition_item_project_inv_messages in Hitem as Hitem'.
  destruct Hitem' as [_ [_ [Hproper _]]].
  apply equivocator_transition_item_project_proper_characterization in Hproper.
  destruct Hproper as [oitem [odescriptor [Hpr' H]]].
  rewrite Hpr' in Hitem.
  inversion Hitem. subst.
  by apply H.
Qed.

(**
  The projection of an [equivocator_vlsm] trace is obtained by traversing the
  trace from right to left guided by the descriptors produced by
  [equivocator_vlsm_transition_item_project] and gathering all non-empty
  [transition_item]s it produces.
*)
Definition equivocator_vlsm_trace_project
  (tr : list (vtransition_item equivocator_vlsm))
  (descriptor : MachineDescriptor)
  : option (list (vtransition_item X) * MachineDescriptor)
  :=
  fold_right
    (fun item result =>
      match result with
      | None => None
      | Some (r, idescriptor) =>
        match equivocator_vlsm_transition_item_project item idescriptor with
        | None => None
        | Some (None, odescriptor) => Some (r, odescriptor)
        | Some (Some item', odescriptor) => Some (item' :: r, odescriptor)
        end
      end
    )
    (Some ([], descriptor))
    tr.

(**
  Projecting on a [NewMachine] descriptor yields an empty trace and the same
  descriptor.
*)
Lemma equivocator_vlsm_trace_project_on_new_machine
  (tr : list (vtransition_item equivocator_vlsm))
  (s : vstate X)
  : equivocator_vlsm_trace_project tr (NewMachine s) = Some ([], NewMachine s).
Proof.
  by induction tr; simpl; rewrite ?IHtr.
Qed.

(**
  [equivocator_vlsm_trace_project] acts like a morphism w.r.t. concatenation
  (single element in left operand case).
*)
Lemma equivocator_vlsm_trace_project_cons
  (bprefix : vtransition_item equivocator_vlsm)
  (bsuffix : list (vtransition_item equivocator_vlsm))
  (dstart dlast : MachineDescriptor)
  (tr : list (vtransition_item X))
  (Hproject : equivocator_vlsm_trace_project ([bprefix] ++ bsuffix) dlast = Some (tr, dstart))
  : exists
    (dmiddle : MachineDescriptor)
    (prefix suffix : list (vtransition_item X))
    (Hprefix : equivocator_vlsm_trace_project [bprefix] dmiddle = Some (prefix, dstart))
    (Hsuffix : equivocator_vlsm_trace_project bsuffix dlast = Some (suffix, dmiddle)),
    tr = prefix ++ suffix.
Proof.
  simpl in Hproject.
  destruct (equivocator_vlsm_trace_project bsuffix dlast) as [(suffix, dmiddle) |]
    eqn:Hsuffix
  ; [| by congruence].
  exists dmiddle.
  destruct (equivocator_vlsm_transition_item_project bprefix dmiddle) as [[[prefix |] i] |]
    eqn:Hprefix
  ; inversion Hproject; subst; clear Hproject.
  - by exists [prefix], suffix; cbn; rewrite Hprefix.
  - by exists []; exists tr; cbn; rewrite Hprefix.
Qed.

(** [equivocator_vlsm_trace_project] acts like a morphism w.r.t. concatenation. *)
Lemma equivocator_vlsm_trace_project_app
  (bprefix bsuffix : list (vtransition_item equivocator_vlsm))
  (dlast dstart : MachineDescriptor)
  (tr : list (vtransition_item X))
  (Hproject : equivocator_vlsm_trace_project (bprefix ++ bsuffix) dlast = Some (tr, dstart))
  : exists
    (dmiddle : MachineDescriptor)
    (prefix suffix : list (vtransition_item X))
    (Hprefix : equivocator_vlsm_trace_project bprefix dmiddle = Some (prefix, dstart))
    (Hsuffix : equivocator_vlsm_trace_project bsuffix dlast = Some (suffix, dmiddle)),
    tr = prefix ++ suffix.
Proof.
  generalize dependent dstart. generalize dependent tr.
  induction bprefix; intros.
  - by exists dstart, [], tr, eq_refl, Hproject.
  - rewrite <- app_comm_cons in Hproject.
    apply equivocator_vlsm_trace_project_cons in Hproject.
    destruct Hproject as [da [prefixa [tr' [Ha [Hproject Heq]]]]].
    specialize (IHbprefix tr' da Hproject).
    destruct IHbprefix as [dmiddle [prefix' [suffix [Hprefix [Hsuffix Htr']]]]].
    exists dmiddle.
    exists (prefixa ++ prefix'). exists suffix.
    repeat split; [| done |].
    + simpl. rewrite Hprefix.
      simpl in Ha.
      destruct (equivocator_vlsm_transition_item_project a da)
        as [(oitem', i) |]
      ; [| by congruence].
      by destruct oitem' as [item' |]; inversion Ha; subst.
    + by subst; rewrite app_assoc.
Qed.

(**
  [equivocator_vlsm_trace_project] acts like a morphism w.r.t. concatenation
  (converse).
*)
Lemma equivocator_vlsm_trace_project_app_inv
  (bprefix bsuffix : list (vtransition_item equivocator_vlsm))
  (dlast dstart dmiddle : MachineDescriptor)
  (prefix suffix : list (vtransition_item X))
  (Hprefix : equivocator_vlsm_trace_project bprefix dmiddle = Some (prefix, dstart))
  (Hsuffix : equivocator_vlsm_trace_project bsuffix dlast = Some (suffix, dmiddle))
  : equivocator_vlsm_trace_project (bprefix ++ bsuffix) dlast = Some (prefix ++ suffix, dstart).
Proof.
  generalize dependent dstart. generalize dependent prefix.
  induction bprefix; intros.
  - by inversion Hprefix; subst.
  - simpl in Hprefix.
    destruct (equivocator_vlsm_trace_project bprefix dmiddle) as [(prefix', dstart') |]
      eqn:Hprefix'
    ; [| by congruence].
    specialize (IHbprefix prefix' dstart' eq_refl).
    simpl. rewrite IHbprefix.
    by destruct (equivocator_vlsm_transition_item_project a dstart') as [[[item' |] i] |]
    ; inversion Hprefix; subst.
Qed.

(** Next we prove some inversion properties for [equivocator_vlsm_transition_item_project]. *)
Lemma equivocator_valid_transition_project_inv2
  (l : vlabel equivocator_vlsm)
  (s' s: vstate equivocator_vlsm)
  (iom oom : option message)
  (Hv: vvalid equivocator_vlsm l (s', iom))
  (Ht: vtransition equivocator_vlsm l (s', iom) = (s, oom))
  (item := {| l := l; input := iom; destination := s; output := oom |})
  (di di' : MachineDescriptor)
  (item' : vtransition_item X)
  (Hitem: equivocator_vlsm_transition_item_project item di = Some (Some item', di'))
  : exists (i : nat), di = Existing i /\
    exists sx, equivocator_state_project s i = Some sx /\
    exists (i' : nat), di' = Existing i' /\
    exists s'x, equivocator_state_project s' i' = Some s'x /\
    exists (Hex : existing_equivocator_label _ l) (lx := existing_equivocator_label_extract _ l Hex),
    item' = {| l := lx; input := iom; destination := sx; output := oom |} /\
    vvalid X lx (s'x, iom) /\ vtransition X lx (s'x, iom) = (sx, oom).
Proof.
  destruct di as [sn | i]; [by simpl in Hitem; congruence |].
  eexists _; split; [done |].
  simpl in Hitem.
  destruct (equivocator_state_project s i) as [si |] eqn:Heqsi; [| done].
  eexists; split; [done |].
  destruct l as [sn | j lx | j lx]; [by destruct (decide _) | ..]
  ; cbn in Hv
  ; (destruct (equivocator_state_project s' j) as [s'j |] eqn:Heqs'j; [| done])
  ; (destruct (decide _); [| done])
  ; inversion Hitem; subst; simpl; repeat split; eexists _; repeat split; exists s'j
  ; (repeat split; [done.. |])
  ; destruct (vtransition X _ _) as (s'j', _oom) eqn:Hti.
  - specialize (existing_false_label_equivocator_state_project_same X Ht _ Heqs'j _ _ Hti)
      as [Heq_oom Heqs'j'].
    by subst; simpl; rewrite Heqsi.
  - specialize (existing_true_label_equivocator_state_project_last X Ht _ Heqs'j _ _ Hti)
      as [Heq_oom Heqs'j'].
    subst. simpl.
    replace (equivocator_state_n s') with  (equivocator_state_last s)
    ; [by rewrite Heqsi |].
    specialize (existing_true_label_equivocator_transition_size X Ht _ Heqs'j) as Ht_size.
    by specialize (equivocator_state_last_n X s) as Hs_lst; lia.
Qed.

Lemma equivocator_valid_transition_project_inv3
  (l : vlabel equivocator_vlsm)
  (s s' : vstate equivocator_vlsm)
  (iom oom : option message)
  (Hv: vvalid equivocator_vlsm l (s', iom))
  (Ht: vtransition equivocator_vlsm l (s', iom) = (s, oom))
  (item := {| l := l; input := iom; destination := s; output := oom |})
  (di di' : MachineDescriptor)
  (Hitem: equivocator_vlsm_transition_item_project item di = Some (None, di'))
  : match di with
    | NewMachine sn => di' = di
    | Existing i =>
      match di' with
      | Existing i' =>
        exists si,
          equivocator_state_project s i = Some si /\
          equivocator_state_project s' i' = Some si
      | NewMachine sn' =>
          l = Spawn sn' /\ i = equivocator_state_last s /\ iom = None /\ oom = None /\
          equivocator_state_project s i = Some sn' /\ vinitial_state_prop X sn'
      end
    end.
Proof.
  destruct di as [si | i]; [by inversion Hitem |].
  subst item. simpl in Hitem.
  destruct (equivocator_state_project s i) as [si |] eqn:Heqsi; [| done].
  destruct l as [sn | id lx | id lx]; destruct (decide _); inversion Hitem; subst.
  - inversion Ht; subst.
    split_and!; [done | done | apply Hv | done | | apply Hv].
    by rewrite equivocator_state_extend_lst, equivocator_state_extend_project_2 in Heqsi.
  - eexists; split; [done |].
    specialize (new_machine_label_equivocator_state_project_not_last X Ht i) as Hn.
    simpl in Hn. rewrite Heqsi in Hn.
    specialize (new_machine_label_equivocator_transition_size X Ht) as Ht_size.
    specialize (equivocator_state_last_n X s) as Hs_lst.
    apply equivocator_state_project_Some_rev in Heqsi.
    spec Hn; [lia |].
    simpl in Hn.
    by destruct_equivocator_state_project s' i s'i Hi; [subst | lia].
  - eexists; split; [done |].
    cbn in Hv.
    destruct (equivocator_state_project s' id) as [s'id |] eqn:Hpr; [| done].
    specialize (existing_false_label_equivocator_state_project_not_same X Ht _ Hpr i) as Hn.
    simpl in Hn. rewrite Heqsi in Hn.
    specialize (existing_false_label_equivocator_transition_size X Ht _ Hpr) as Ht_size.
    specialize (equivocator_state_last_n X s) as Hs_lst.
    apply equivocator_state_project_Some_rev in Heqsi.
    spec Hn; [lia |].
    specialize (Hn n).
    destruct_equivocator_state_project s' i s'i Hi; [| lia].
    by simpl in Hn; subst.
  - eexists; split; [done |].
    cbn in Hv.
    destruct (equivocator_state_project s' id) as [s'id |] eqn:Hpr; [| done].
    specialize (existing_true_label_equivocator_state_project_not_last X Ht _ Hpr i) as Hn.
    simpl in Hn. rewrite Heqsi in Hn.
    specialize (existing_true_label_equivocator_transition_size X Ht _ Hpr) as Ht_size.
    specialize (equivocator_state_last_n X s) as Hs_lst.
    apply equivocator_state_project_Some_rev in Heqsi.
    spec Hn; [lia |].
    destruct_equivocator_state_project s' i s'i Hi; [| lia].
    by simpl in Hn; subst.
Qed.

Lemma equivocator_valid_transition_project_inv4
  (l : vlabel equivocator_vlsm)
  (s s' : vstate equivocator_vlsm)
  (iom oom : option message)
  (Hv: vvalid equivocator_vlsm l (s', iom))
  (Ht: vtransition equivocator_vlsm l (s', iom) = (s, oom))
  (i' : nat)
  si'
  (Hi' : equivocator_state_project s' i' = Some si')
  : exists si, equivocator_state_project s i' = Some si /\
    exists (oitem : option (vtransition_item X)),
    equivocator_vlsm_transition_item_project
      {| l := l; input := iom; destination := s; output := oom |}
      (Existing i') = Some (oitem, Existing i').
Proof.
  unfold equivocator_vlsm_transition_item_project.
  destruct l as [sn | j lx | j lx].
  - inversion Ht. subst. clear Ht.
    apply equivocator_state_project_Some_rev in Hi' as Hlti'.
    rewrite equivocator_state_extend_project_1 by done.
    eexists; split; [done |].
    rewrite Hi'.
    exists None.
    rewrite decide_False ; [done |].
    by rewrite equivocator_state_extend_lst; lia.
  - cbn in Hv. destruct (equivocator_state_project s' j) as [s'j |] eqn:Heqs'j
    ; [| done].
    specialize (existing_false_label_equivocator_transition_size X Ht _ Heqs'j) as Ht_size.
    apply equivocator_state_project_Some_rev in Hi' as Hlti'.
    destruct_equivocator_state_project s i' si Hlti; [| lia].
    eexists; split; [done |].
    by destruct (decide _); subst; eexists _.
  - cbn in Hv. destruct (equivocator_state_project s' j) as [s'j |] eqn:Heqs'j
    ; [| done].
    specialize (existing_true_label_equivocator_transition_size X Ht _ Heqs'j) as Ht_size.
    apply equivocator_state_project_Some_rev in Hi' as Hlti'.
    destruct_equivocator_state_project s i' si Hlti; [| lia].
    eexists; split; [done |].
    rewrite decide_False; [by eexists _ |].
    by specialize (equivocator_state_last_n X s); lia.
Qed.

Lemma equivocator_valid_transition_project_inv5_new_machine
  (l : vlabel equivocator_vlsm)
  (s s' : vstate equivocator_vlsm)
  (iom oom : option message)
  (Ht: vtransition equivocator_vlsm l (s', iom) = (s, oom))
  (item := {| l := l; input := iom; destination := s; output := oom |})
  (sn : state)
  (Hnew : l = Spawn sn)
  : exists (i : nat) si,
    equivocator_state_project s i = si /\
    equivocator_vlsm_transition_item_project item (Existing i) = Some (None, NewMachine sn).
Proof.
  subst l.
  simpl.
  inversion Ht. subst. clear Ht.
  exists (equivocator_state_n s').
  by rewrite equivocator_state_extend_lst, equivocator_state_extend_project_2, decide_True
  ; eauto.
Qed.

Lemma equivocator_valid_transition_project_inv5
  (l : vlabel equivocator_vlsm)
  (s s' : vstate equivocator_vlsm)
  (iom oom : option message)
  (Hv: vvalid equivocator_vlsm l (s', iom))
  (Ht: vtransition equivocator_vlsm l (s', iom) = (s, oom))
  (item := {| l := l; input := iom; destination := s; output := oom |})
  (_i : nat)
  (Hsndl : equivocator_label_descriptor l = Existing _i)
  : exists (i : nat) si, equivocator_state_project s i = Some si /\
    exists (itemx : vtransition_item X),
    equivocator_vlsm_transition_item_project item (Existing i) = Some (Some itemx, Existing _i).
Proof.
  destruct l as [sn | _i' lx | _i' lx]; simpl in Hsndl; inversion Hsndl; subst
  ; cbn in Hv
  ; (destruct (equivocator_state_project s' _i) as [s'i |] eqn:Heqs'i; [| done]).
  - specialize (existing_false_label_equivocator_transition_size X Ht _ Heqs'i) as Ht_size.
    specialize (existing_false_label_equivocator_state_project_same X Ht _ Heqs'i) as Ht_pr.
    simpl in Ht_pr.
    destruct (vtransition X _ _) as (si', _oom) eqn:Hti.
    specialize (Ht_pr _ _ eq_refl) as [Heq_oom Heqsi'].
    exists _i.
    simpl.
    apply equivocator_state_project_Some_rev in Heqs'i as Hlti.
    destruct_equivocator_state_project s _i si Hi; [| lia].
    simpl in Heqsi'. subst si.
    by rewrite decide_True; eauto.
  - specialize (existing_true_label_equivocator_transition_size X Ht _ Heqs'i) as Ht_size.
    specialize (existing_true_label_equivocator_state_project_last X Ht _ Heqs'i) as Ht_pr.
    cbn in Ht. rewrite Heqs'i in Ht.
    simpl in Ht_pr.
    destruct (vtransition X _ _) as (si', _oom) eqn:Hti.
    specialize (Ht_pr _ _ eq_refl) as [Heq_oom Heqsi'].
    exists (equivocator_state_n s').
    simpl.
    destruct_equivocator_state_project s (equivocator_state_n s') s_lst Hlst; [| lia].
    simpl in Heqsi'. subst s_lst. eexists; split; [done |].
    specialize (equivocator_state_last_n X s) as Hs_lst.
    rewrite decide_True by lia.
    by eexists.
Qed.

(**
  The projection of a segment of an [equivocator_vlsm] valid trace
  is defined and a valid trace segment in the original VLSM.
*)
Lemma preloaded_with_equivocator_vlsm_trace_project_valid
  (seed : message -> Prop)
  (bs be : vstate equivocator_vlsm)
  (btr : list (vtransition_item equivocator_vlsm))
  (Hbtr : finite_valid_trace_from_to (pre_loaded_vlsm equivocator_vlsm seed) bs be btr)
  (j : nat)
  ej
  (Hj : equivocator_state_project be j = Some ej)
  : exists
    (tr : list (vtransition_item X))
    (di : MachineDescriptor),
    equivocator_vlsm_trace_project btr (Existing j) = Some (tr, di) /\
    match di with
    | NewMachine sn =>
      vinitial_state_prop X sn
      /\ finite_valid_trace_from_to (pre_loaded_vlsm X seed) sn ej tr
    | Existing i =>
      exists s, equivocator_state_project bs i = Some s /\
      finite_valid_trace_from_to (pre_loaded_vlsm X seed) s ej tr
    end.
Proof.
  induction Hbtr; intros.
  - exists [].
    eexists; split; [done |].
    eexists; split; [done |].
    constructor. revert Hj.
    by apply preloaded_with_equivocator_state_project_valid_state.
  - remember {| l := l; input := iom; |} as item.
    destruct Ht as [[Hs' [Hiom Hv]] Ht].
    specialize (IHHbtr Hj) as [tlX [di' [Htl_pr Hdi]]].
    change (item :: tl) with ([item] ++ tl).
    unfold equivocator_vlsm_trace_project.
    rewrite foldr_app. replace (foldr _ _ tl) with (Some (tlX, di')).
    simpl.
    destruct di' as [sn | i]; [by eexists _, _ |].
    destruct Hdi as [si [Heqsi HltX]].
    specialize (equivocator_transition_item_project_proper_characterization item (Existing i))
      as Hchar.
    spec Hchar; [by subst item; cbn; rewrite Heqsi; eexists |].
    destruct Hchar as [oitem [descriptor' [Hitem_pr [Hchar1 Hchar2]]]].
    rewrite Hitem_pr.
    subst item.
    specialize (Hchar2 _ Hv Ht) as [Hproper' [Hprevious Hchar2]].
    destruct oitem as [itemX |]; eexists _, _; split; [done | | done |].
    2: { simpl in *. rewrite Heqsi in Hchar2.
         destruct descriptor' as [sn | i']; simpl in Hchar2.
         - by subst si.
         - destruct Hproper' as [s'i' Hproper'].
            rewrite Hproper' in Hchar2.
            simpl in Hchar2. subst s'i'. by exists si.
    }
    simpl in Hchar1. rewrite Heqsi in Hchar1.
    destruct Hchar1 as [[Hex Hl] [Heqiom [Hoom [Hsi Hdl]]]]. subst.
    destruct (equivocator_label_descriptor l) as [sn | i'] eqn:Hd; simpl in Hchar2.
    + specialize (Hchar2 _ eq_refl) as [HvX HtX].
      split; [apply Hproper' |].
      destruct itemX. simpl in *.
      rewrite Heqsi in Hitem_pr. subst.
      apply (finite_valid_trace_from_to_extend (pre_loaded_vlsm X seed)); [done |].
      repeat split; [.. | done | done].
      * by apply initial_state_is_valid.
      * by apply preloaded_with_equivocator_state_project_valid_message.
    + destruct Hproper' as [s'i' Heqs'i']; rewrite Heqs'i' in *.
      simpl in Hchar2.
      specialize (Hchar2 _ eq_refl) as [HvX HtX].
      eexists _; split; [done |].
      destruct itemX. simpl in *.
      subst.
      apply (finite_valid_trace_from_to_extend (pre_loaded_vlsm X seed)); [done |].
      repeat split; [.. | done | done].
      * by eapply preloaded_with_equivocator_state_project_valid_state.
      * by apply preloaded_with_equivocator_state_project_valid_message.
Qed.

Lemma equivocator_vlsm_trace_project_valid
  (bs be : vstate equivocator_vlsm)
  (btr : list (vtransition_item equivocator_vlsm))
  (Hbtr : finite_valid_trace_from_to equivocator_vlsm bs be btr)
  (j : nat)
  ej
  (Hj : equivocator_state_project be j = Some ej)
  : exists
    (tr : list (vtransition_item X))
    (di : MachineDescriptor),
    equivocator_vlsm_trace_project btr (Existing j) = Some (tr, di) /\
    match di with
    | NewMachine sn =>
      vinitial_state_prop X sn
      /\ finite_valid_trace_from_to X sn ej tr
    | Existing i =>
      exists s, equivocator_state_project bs i = Some s /\
      finite_valid_trace_from_to X s ej tr
    end.
Proof.
  apply (VLSM_incl_finite_valid_trace_from_to
    (VLSM_eq_proj1 (vlsm_is_pre_loaded_with_False equivocator_vlsm))) in Hbtr.
  specialize (preloaded_with_equivocator_vlsm_trace_project_valid _ _ _ _ Hbtr _ _ Hj)
    as [tr [di [Hbtr_pr Hdi]]].
  eexists _, _; split; [done |].
  destruct di as [sn | i].
  - destruct Hdi as [Hsn Htr].
    split; [done |].
    apply (VLSM_incl_finite_valid_trace_from_to (VLSM_eq_proj2
      (vlsm_is_pre_loaded_with_False X))) in Htr.
    by clear -Htr; destruct X.
  - destruct Hdi as [s [Hpr_bs_i Htr]].
    eexists; split; [done |].
    apply (VLSM_incl_finite_valid_trace_from_to (VLSM_eq_proj2 (vlsm_is_pre_loaded_with_False X)))
      in Htr.
    by clear -Htr; destruct X.
Qed.

(**
  The projection of a segment of a valid trace from the [pre_loaded_with_all_messages_vlsm]
  corresponding to the [equivocator_vlsm] is defined and it is a valid
  trace segment in the [pre_loaded_with_all_messages_vlsm] corresponding to the original vlsm.
*)
Lemma preloaded_equivocator_vlsm_trace_project_valid
  (bs be : vstate equivocator_vlsm)
  (btr : list (vtransition_item equivocator_vlsm))
  (Hbtr : finite_valid_trace_from_to (pre_loaded_with_all_messages_vlsm equivocator_vlsm) bs be btr)
  (j : nat)
  ej
  (Hj : equivocator_state_project be j = Some ej)
  : exists
    (tr : list (vtransition_item X))
    (di : MachineDescriptor),
    equivocator_vlsm_trace_project btr (Existing j) = Some (tr, di) /\
    match di with
    | NewMachine sn =>
      vinitial_state_prop X sn
      /\ finite_valid_trace_from_to (pre_loaded_with_all_messages_vlsm X) sn ej tr
    | Existing i =>
      exists s, equivocator_state_project bs i = Some s /\
      finite_valid_trace_from_to (pre_loaded_with_all_messages_vlsm X) s ej tr
    end.
Proof.
  apply (VLSM_incl_finite_valid_trace_from_to (VLSM_eq_proj1
    (pre_loaded_with_all_messages_vlsm_is_pre_loaded_with_True equivocator_vlsm))) in Hbtr.
  specialize (preloaded_with_equivocator_vlsm_trace_project_valid _ _ _ _ Hbtr _ _ Hj)
    as [tr [di [Hbtr_pr Hdi]]].
  eexists _, _; split; [done |].
  destruct di as [sn | i].
  - destruct Hdi as [Hsn Htr].
    split; [done |].
    apply (VLSM_incl_finite_valid_trace_from_to (VLSM_eq_proj2
      (pre_loaded_with_all_messages_vlsm_is_pre_loaded_with_True X))) in Htr.
    by clear -Htr; destruct X.
  - destruct Hdi as [s [Hpr_bs_i Htr]].
    eexists; split; [done |].
    apply (VLSM_incl_finite_valid_trace_from_to (VLSM_eq_proj2
      (pre_loaded_with_all_messages_vlsm_is_pre_loaded_with_True X))) in Htr.
    by clear -Htr; destruct X.
Qed.

(**
  If [equivocator_vlsm_trace_project] does not fail, then the index of the
  machine descriptor is valid for the last state of the trace argument.
*)
Lemma equivocator_vlsm_trace_project_inv
  (tr: list transition_item)
  (Hntr : tr <> [])
  (j: nat)
  (HtrX: is_Some (equivocator_vlsm_trace_project tr (Existing j)))
  (is: state)
  : exists sj, equivocator_state_project (finite_trace_last is tr) j = Some sj.
Proof.
  apply exists_last in Hntr.
  destruct Hntr as [suffix [x Heq]]. subst tr.
  destruct HtrX as [p Htr].
  destruct p as (trX, d).
  apply equivocator_vlsm_trace_project_app in Htr.
  destruct Htr as [dmiddle [_ [lx [_ [Hx _]]]]].
  rewrite finite_trace_last_is_last.
  remember (Existing j) as dj.
  simpl in *.
  destruct (equivocator_vlsm_transition_item_project x dj)
    as [(_x, _dmiddle) |]
    eqn:Hx'
  ; [| by congruence].
  destruct _x as [itemx |]; inversion Hx; subst lx _dmiddle; clear Hx.
  - subst. destruct x. unfold equivocator_vlsm_transition_item_project in Hx'.
    simpl.
    destruct (equivocator_state_project destination j); [| congruence].
    by eexists.
  - subst. destruct x. simpl in *.
    destruct (equivocator_state_project destination j); [| congruence].
    by eexists.
Qed.

(**
  Projecting a valid trace segment on an index which is valid for the
  first state of the trace does not fail and yields the same index.
*)
Lemma preloaded_equivocator_vlsm_trace_project_valid_inv
  (bs : vstate equivocator_vlsm)
  (btr : list (vtransition_item equivocator_vlsm))
  (Hbtr : finite_valid_trace_from (pre_loaded_with_all_messages_vlsm equivocator_vlsm) bs btr)
  (i : nat)
  si
  (Hi : equivocator_state_project bs i = Some si)
  : exists
    (tr : list (vtransition_item X)),
    equivocator_vlsm_trace_project btr (Existing i) = Some (tr, Existing i).
Proof.
  revert i si Hi.
  induction Hbtr; intros.
  - by exists [].
  - remember {| l := l; input := iom; destination := s; output := oom |} as item.
    simpl.
    destruct Ht as [[_ [_ Hv]] Ht].
    specialize
      (equivocator_valid_transition_project_inv4 l s s' iom oom Hv Ht i)
      as Hitem.
    replace
      {| input := iom |}
      with item in Hitem.
    specialize (Hitem _ Hi) as [si' [Hsi' Hitem]].
    specialize (IHHbtr i si' Hsi') as [tr Htr].
    rewrite Htr.
    destruct Hitem as [oitem Hoitem].
    rewrite Hoitem.
    destruct oitem as [itemx |].
    + by exists (itemx :: tr).
    + by exists tr.
Qed.

(** An inversion lemma about projections of a valid trace. *)
Lemma preloaded_equivocator_vlsm_valid_trace_project_inv2
  (is fs: state)
  (tr: list transition_item)
  (Hntr : tr <> [])
  (Htr: finite_valid_trace_from_to (pre_loaded_with_all_messages_vlsm equivocator_vlsm) is fs tr)
  (j : nat)
  (di : MachineDescriptor)
  (trX: list (vtransition_item X))
  (HtrX: equivocator_vlsm_trace_project tr (Existing j) = Some (trX, di))
  : exists fsj, equivocator_state_project fs j = Some fsj /\
    match di with
    | NewMachine sn =>
      finite_valid_trace_init_to (pre_loaded_with_all_messages_vlsm X)
        sn fsj trX
    | Existing i =>
      exists isi, equivocator_state_project is i = Some isi /\
      finite_valid_trace_from_to (pre_loaded_with_all_messages_vlsm X) isi fsj trX /\
      (vinitial_state_prop (pre_loaded_with_all_messages_vlsm equivocator_vlsm) is ->
        vinitial_state_prop (pre_loaded_with_all_messages_vlsm X) isi)
    end.
Proof.
  specialize (equivocator_vlsm_trace_project_inv _ Hntr j) as Hj.
  spec Hj; [done |].
  specialize (Hj is) as [fsj Hfsj].
  replace (finite_trace_last _ _) with fs in Hfsj
    by (symmetry; apply (valid_trace_get_last Htr)).
  exists fsj. split; [done |].
  specialize
    (preloaded_equivocator_vlsm_trace_project_valid _ _ _ Htr _ _ Hfsj)
    as [trX' [di' [HtrX' Hdi]]].
  rewrite HtrX in HtrX'.
  inversion HtrX'. subst di' trX'.  clear HtrX'.
  destruct di as [sn | n]; repeat split; [by apply Hdi.. |].
  destruct Hdi as [isi [Hisi HtrX']].
  exists isi. repeat split; [done.. |].
  by apply (equivocator_vlsm_initial_state_preservation_rev X _ _ _ Hisi).
Qed.

Definition equivocator_label_zero_project (l : equivocator_label X) : option (vlabel X) :=
  match l with
  | ContinueWith 0 li => Some li
  | _ => None
  end.

Lemma equivocator_zero_projection
  : VLSM_projection equivocator_vlsm X
    equivocator_label_zero_project equivocator_state_zero.
Proof.
  apply basic_VLSM_strong_projection; intro; intros.
  - by destruct lX as [sn | [| i] lX | [| i] lX]; inversion H; subst.
  - destruct lX as [sn | [| i] lX | [| i] lX]; inversion H; subst.
    cbn in H0.
    rewrite equivocator_state_project_zero in H0.
    by destruct (vtransition _ _ _); inversion_clear H0.
  - unfold equivocator_label_zero_project in H.
    destruct lX as [sn | [| i] lX | [| i] lX]; inversion H; subst; cbn in H0.
    + by inversion H0.
    + by destruct (equivocator_state_project _ _); [destruct (vtransition _ _ _) |]; inversion H0.
    + rewrite equivocator_state_project_zero in H0.
      by destruct (vtransition _ _ _); inversion_clear H0.
    + by destruct (equivocator_state_project _ _); [destruct (vtransition _ _ _) |];
        inversion_clear H0.
  - by apply H.
  - by apply equivocator_state_project_valid_message.
Qed.

Lemma preloaded_equivocator_zero_projection :
  VLSM_projection
    (pre_loaded_with_all_messages_vlsm equivocator_vlsm) (pre_loaded_with_all_messages_vlsm X)
    equivocator_label_zero_project equivocator_state_zero.
Proof.
  apply basic_VLSM_projection_preloaded; intro; intros.
  - by destruct lX as [sn | [| i] lX | [| i] lX]; inversion H; subst.
  - destruct lX as [sn | [| i] lX | [| i] lX]; inversion H; subst.
    cbn in H0. rewrite equivocator_state_project_zero in H0.
    by destruct (vtransition _ _ _); inversion_clear H0.
  - unfold equivocator_label_zero_project in H.
    destruct lX as [sn | [| i] lX | [| i] lX]; inversion H; subst; cbn in H0.
    + by inversion H0.
    + by destruct (equivocator_state_project _ _); [destruct (vtransition _ _ _) |];
        inversion_clear H0.
    + by rewrite equivocator_state_project_zero in H0; destruct (vtransition _ _ _);
        inversion_clear H0.
    + by destruct (equivocator_state_project _ _); [destruct (vtransition _ _ _) |];
        inversion_clear H0.
  - apply H.
Qed.

End sec_equivocator_vlsm_projections.
