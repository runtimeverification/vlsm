From stdpp Require Import prelude.
From Coq Require Import Reals Lra.
From VLSM.Lib Require Import RealsExtras Measurable ListExtras StdppListSet.

Class ReachableThreshold V Cv `{Hm : Measurable V} `{FinSet V Cv} : Set :=
{
  threshold : {r | (r >= 0)%R};
  reachable_threshold : exists (vs : Cv), (sum_weights vs > proj1_sig threshold)%R;
}.

#[global] Hint Mode ReachableThreshold - - ! ! ! ! ! ! ! ! ! ! : typeclass_instances.

Section sec_reachable_threshold_props.

Context
  `{EqDecision V}
  `{Hrt : ReachableThreshold V Cv}.

Lemma pivotal_validator_extension_list
  : forall vsfix vss,
  NoDup vsfix ->
  (* and whose added weight does not pass the threshold *)
  (sum_weights_list vsfix <= proj1_sig threshold)%R ->
  NoDup (vss ++ vsfix) ->
  (sum_weights_list (vss ++ vsfix) > proj1_sig threshold)%R ->
  exists (vs : list V),
  NoDup vs /\
  vs ⊆ vss /\
  (sum_weights_list (vs ++ vsfix) > proj1_sig threshold)%R /\
  exists v,
    v ∈ vs /\
    (sum_weights_list ((StdppListSet.set_remove v vs) ++ vsfix) <= proj1_sig threshold)%R.
Proof.
  destruct threshold as [t about_t]; simpl in *.
  intro.  induction vss; intros Hnd_vsfix Hvsfix Hnd_all Hall.
  - simpl in Hall. exfalso.
    by apply (Rge_gt_trans t) in Hall; [eapply Rgt_not_eq | apply Rle_ge].
  - simpl in Hall. destruct (Rtotal_le_gt (sum_weights_list (vss ++ vsfix)) t) as [| Hgt].
    + exists (a :: vss). repeat split; [| done | done |].
      * by apply nodup_append_left in Hnd_all.
      * exists a. split; [left |]. cbn. by rewrite decide_True.
    + simpl in Hnd_all.
      apply NoDup_cons in Hnd_all as [Hnin Hvss].
      apply IHvss in Hgt as [vs [Hvs [Hincl Hex]]]; [| done..].
      exists vs. repeat (split; try done).
      by right; apply Hincl.
Qed.

Lemma pivotal_validator_extension
  : forall (vsfix vss : Cv),
  (* and whose added weight does not pass the threshold *)
  (sum_weights vsfix <= proj1_sig threshold)%R ->
  vss ## vsfix ->
  (sum_weights (vss ∪ vsfix) > proj1_sig threshold)%R ->
  exists (vs : Cv),
  vs ⊆ vss /\
  (sum_weights (vs ∪ vsfix) > proj1_sig threshold)%R /\
  exists v,
    v ∈ vs /\
    (sum_weights (vs ∖ {[v]} ∪ vsfix) <= proj1_sig threshold)%R.
Proof.
  intros vsfix vss Hvsfix Hdisj Hall.
  destruct (pivotal_validator_extension_list (elements vsfix) (elements vss))
    as (vs & Hnd_vs & Hincl & Hvs & v & Hv & Hvs_v);
      [by apply NoDup_elements | done | .. | exists (list_to_set vs); split_and!].
  - apply NoDup_app; split_and!; [apply NoDup_elements | | apply NoDup_elements].
    by intro; rewrite !elem_of_elements; intros ? ?; eapply Hdisj.
  - rewrite sum_weights_app_list.
    by rewrite sum_weights_disj_union in Hall.
  - by intros a Ha; apply elem_of_list_to_set, Hincl, elem_of_elements in Ha.
  - rewrite sum_weights_app_list in Hvs.
    rewrite sum_weights_disj_union.
    + replace (sum_weights (list_to_set vs)) with (sum_weights_list vs); [done |].
      apply sum_weights_list_permutation_proper.
      by rewrite elements_list_to_set.
    + intros x; rewrite elem_of_list_to_set.
      intros Hx_vs Hx_vsfix; eapply Hdisj; [| done].
      by eapply elem_of_elements, Hincl.
  - exists v; split; [by apply elem_of_list_to_set |].
    replace (sum_weights _)
      with (sum_weights_list (StdppListSet.set_remove v vs ++ elements vsfix)); [done |].
    apply sum_weights_list_permutation_proper.
    rewrite elements_disj_union.
    + apply Permutation_app_tail.
      etransitivity; [by symmetry; apply elements_list_to_set, set_remove_nodup |].
      apply elements_proper.
      by intro x; rewrite elem_of_difference, !elem_of_list_to_set, set_remove_iff, elem_of_singleton.
    + intros x; rewrite elem_of_difference, elem_of_list_to_set, elem_of_singleton.
      by intros [] ?; eapply Hdisj; [apply elem_of_elements, Hincl |].
Qed.

Lemma validators_pivotal_ind
  : forall (vss : Cv),
  (sum_weights vss > proj1_sig threshold)%R ->
  exists vs,
  vs ⊆ vss /\
  (sum_weights vs > proj1_sig threshold)%R /\
  exists v,
    v ∈ vs /\
    (sum_weights (vs ∖ {[v]}) <= proj1_sig threshold)%R.
Proof.
  intros vss Hvss.
  destruct (pivotal_validator_extension ∅ vss)
    as (vs & Hincl & Hvs & v & Hv & Hvs').
  - by rewrite sum_weights_empty; [destruct threshold; apply Rge_le |].
  - by apply disjoint_empty_r.
  - by rewrite sum_weights_union_empty.
  - rewrite sum_weights_union_empty in Hvs, Hvs'.
    by repeat esplit.
Qed.

Lemma sufficient_validators_pivotal
  : exists (vs : Cv),
    (sum_weights vs > proj1_sig threshold)%R /\
    exists v,
      v ∈ vs /\
      (sum_weights (vs ∖ {[v]}) <= proj1_sig threshold)%R.
Proof.
  destruct reachable_threshold as [vs Hweight].
  apply (validators_pivotal_ind vs) in Hweight as (vs' & Hincl & Hvs').
  by exists vs'.
Qed.

Definition potentially_pivotal
  (v : V) : Prop
  :=
  exists (vs : Cv),
      v ∉ vs /\
      (sum_weights vs <= proj1_sig threshold)%R /\
      (sum_weights vs > proj1_sig threshold - (proj1_sig (weight v)))%R.

Lemma exists_pivotal_validator
  : exists v, potentially_pivotal v.
Proof.
  destruct sufficient_validators_pivotal as [vs [Hgt [v [Hin Hlte]]]].
  exists v, (vs ∖ {[v]}); split_and!.
  - by rewrite elem_of_difference, elem_of_singleton; intros [].
  - done.
  - rewrite (sum_weights_in v) in Hgt by done.
    by clear Hlte; cbv in *; lra.
Qed.

End sec_reachable_threshold_props.
