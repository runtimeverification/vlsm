From stdpp Require Import prelude.
From Coq Require Import Reals Lra.
From VLSM.Lib Require Import RealsExtras Measurable ListExtras StdppListSet.

(**
  Given a set of validators and a [threshold] (a positive real number), we say
  that the threshold is reachable ([rt_reachable]) when there exists a
  set of validators whose combined weight passes the threshold.

  In this module we prove that there exist a [potentially_pivotal] validator,
  i.e., a validator which added to a set of validators tips over the threshold.
*)

Class ReachableThreshold V Cv (threshold : R) `{Hm : Measurable V} `{FinSet V Cv} : Prop :=
{
  rt_positive : (0 <= threshold)%R;
  rt_reachable : exists (vs : Cv), (sum_weights vs > threshold)%R;
}.

#[global] Hint Mode ReachableThreshold - - - ! ! ! ! ! ! ! ! ! ! : typeclass_instances.

Section sec_reachable_threshold_props.

Context
  (threshold : R)
  `{Hrt : ReachableThreshold V Cv threshold}.

(**
  Given a list with no duplicates and whose added weight does not pass the
  threshold, we can iteratively add elements into it until it passes the
  threshold.  Hence, the last element added will tip over the threshold.
*)
Lemma pivotal_validator_extension_list
  : forall vsfix vss,
  NoDup vsfix ->
  (sum_weights_list vsfix <= threshold)%R ->
  NoDup (vss ++ vsfix) ->
  (sum_weights_list (vss ++ vsfix) > threshold)%R ->
  exists (vs : list V),
  NoDup vs /\
  vs ⊆ vss /\
  (sum_weights_list (vs ++ vsfix) > threshold)%R /\
  exists v,
    v ∈ vs /\
    (sum_weights_list (set_remove v vs ++ vsfix) <= threshold)%R.
Proof.
  induction vss; intros Hnd_vsfix Hvsfix Hnd_all Hall; simpl in Hall; [by lra |].
  destruct (Rtotal_le_gt (sum_weights_list (vss ++ vsfix)) threshold) as [| Hgt].
  - exists (a :: vss).
    repeat split; [| done | done |].
    + by apply nodup_append_left in Hnd_all.
    + exists a.
      split; [by left |].
      by cbn; rewrite decide_True.
  - apply NoDup_cons in Hnd_all as [Hnin Hvss].
    apply IHvss in Hgt as (vs & Hvs & Hincl & Hex); [| done..].
    exists vs.
    repeat (split; try done).
    by right; apply Hincl.
Qed.

(**
  The [FinSet] version of the [pivotal_validator_extension_list] result.
*)
Lemma pivotal_validator_extension
  : forall (vsfix vss : Cv),
  (sum_weights vsfix <= threshold)%R ->
  vss ## vsfix ->
  (sum_weights (vss ∪ vsfix) > threshold)%R ->
  exists (vs : Cv),
  vs ⊆ vss /\
  (sum_weights (vs ∪ vsfix) > threshold)%R /\
  exists v,
    v ∈ vs /\
    (sum_weights (vs ∖ {[ v ]} ∪ vsfix) <= threshold)%R.
Proof.
  intros vsfix vss Hvsfix Hdisj Hall.
  destruct (pivotal_validator_extension_list (elements vsfix) (elements vss))
    as (vs & Hnd_vs & Hincl & Hvs & v & Hv & Hvs_v);
      [by apply NoDup_elements | done | ..].
  - apply NoDup_app; split_and!; [by apply NoDup_elements | | by apply NoDup_elements].
    by intro; rewrite !elem_of_elements; intros ? ?; eapply Hdisj.
  - rewrite sum_weights_app_list.
    by rewrite sum_weights_disj_union in Hall.
  - exists (list_to_set vs); split_and!.
    + by intros a Ha; apply elem_of_list_to_set, Hincl, elem_of_elements in Ha.
    + rewrite sum_weights_app_list in Hvs.
      rewrite sum_weights_disj_union.
      * replace (sum_weights (list_to_set vs)) with (sum_weights_list vs); [done |].
        apply sum_weights_list_permutation_proper.
        by rewrite elements_list_to_set.
      * intros x; rewrite elem_of_list_to_set.
        intros Hx_vs Hx_vsfix; eapply Hdisj; [| done].
        by eapply elem_of_elements, Hincl.
    + exists v; split; [by apply elem_of_list_to_set |].
      replace (sum_weights _)
        with (sum_weights_list (StdppListSet.set_remove v vs ++ elements vsfix)); [done |].
      apply sum_weights_list_permutation_proper.
      rewrite elements_disj_union.
      * apply Permutation_app_tail.
        etransitivity.
        -- symmetry.
           by apply (elements_list_to_set (H6 := H6)), set_remove_nodup.
        -- apply elements_proper.
           intro x.
           rewrite elem_of_difference, !elem_of_list_to_set.
           by rewrite set_remove_iff, elem_of_singleton.
      * intros x; rewrite elem_of_difference, elem_of_list_to_set, elem_of_singleton.
        by intros [] ?; eapply Hdisj; [apply elem_of_elements, Hincl |].
Qed.

(**
  Given a set of validators whose combined weight passes the threshold, we can
  iteratively remove elements until the combined weight decreases below the
  threshold. The last element removed tips over the threshold.
*)
Lemma validators_pivotal_ind
  : forall (vss : Cv),
  (sum_weights vss > threshold)%R ->
  exists vs,
  vs ⊆ vss /\
  (sum_weights vs > threshold)%R /\
  exists v,
    v ∈ vs /\
    (sum_weights (vs ∖ {[ v ]}) <= threshold)%R.
Proof.
  intros vss Hvss.
  destruct (pivotal_validator_extension ∅ vss)
    as (vs & Hincl & Hvs & v & Hv & Hvs').
  - rewrite sum_weights_empty; [| done].
    by apply (rt_positive (H6 := H6)).
  - by apply disjoint_empty_r.
  - by rewrite sum_weights_union_empty.
  - rewrite sum_weights_union_empty in Hvs, Hvs'.
    by repeat esplit.
Qed.

(**
  There exists a set whose combined weight passes the threshold and containing
  an element such that, if the element is removed, the combined weight decreases
  below the threshold.
*)
Lemma sufficient_validators_pivotal
  : exists (vs : Cv),
    (sum_weights vs > threshold)%R /\
    exists v,
      v ∈ vs /\
      (sum_weights (vs ∖ {[ v ]}) <= threshold)%R.
Proof.
  destruct (rt_reachable (1 := Hrt)) as [vs Hweight].
  apply (validators_pivotal_ind vs) in Hweight as (vs' & Hincl & Hvs').
  by exists vs'.
Qed.

(**
  A validator <<v>> is called potentially pivotal if there exists a set of
  validators whose combined weight is below the threshold such that, if
  adding <<v>> to the set, the combine weight would pass over the threshold.
*)
Definition potentially_pivotal (v : V) : Prop :=
  exists (vs : Cv),
      v ∉ vs /\
      (sum_weights vs <= threshold)%R /\
      (sum_weights vs > threshold - weight v)%R.

(**
  The main result of this section proves the existence of a [potentially_pivotal]
  validator.
*)
Lemma exists_pivotal_validator :
  exists v, potentially_pivotal v.
Proof.
  destruct sufficient_validators_pivotal as (vs & Hgt & v & Hin & Hlte).
  exists v, (vs ∖ {[ v ]}); split_and!.
  - by rewrite elem_of_difference, elem_of_singleton; intros [].
  - done.
  - rewrite (sum_weights_in v) in Hgt by done.
    by clear Hlte; cbv in *; lra.
Qed.

End sec_reachable_threshold_props.
