From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From VLSM.Lib Require Import Preamble ListExtras StdppExtras StdppListSet.

(** * List set utility definitions and lemmas *)

Definition set_eq {A} (s1 s2 : set A) : Prop :=
  s1 ⊆ s2 /\ s2 ⊆ s1.

#[export] Instance set_eq_dec `{EqDecision A} : RelDecision (@set_eq A).
Proof.
  by intros s1 s2; typeclasses eauto.
Qed.

Lemma set_eq_extract_forall
  {A : Type}
  (l1 l2 : set A)
  : set_eq l1 l2 <-> forall a, (a ∈ l1 <-> a ∈ l2).
Proof.
  unfold set_eq. firstorder.
Qed.

Lemma set_eq_proj1 {A} : forall (s1 s2 : set A),
  set_eq s1 s2 ->
  s1 ⊆ s2.
Proof.
  by intros s1 s2 [].
Qed.

Lemma set_eq_proj2 {A} : forall (s1 s2 : set A),
  set_eq s1 s2 ->
  s2 ⊆ s1.
Proof.
  by intros s1 s2 [].
Qed.

Lemma set_eq_refl {A} : forall (s : list A), set_eq s s.
Proof.
  by induction s.
Qed.

Lemma set_eq_comm {A} : forall s1 s2 : set A,
  set_eq s1 s2 <-> set_eq s2 s1.
Proof.
  firstorder.
Qed.

Lemma set_eq_tran {A} : forall s1 s2 s3 : set A,
  set_eq s1 s2 ->
  set_eq s2 s3 ->
  set_eq s1 s3.
Proof.
  intros.
  split; apply PreOrder_Transitive with s2; apply H || apply H0.
Qed.

Lemma set_eq_empty_iff
  {A}
  : forall (l : list A),
    set_eq l [] <-> l = [].
Proof.
  split; intros; [|subst; apply set_eq_refl].
  destruct l as [| hd tl]; [done |].
  destruct H.
  spec H hd (elem_of_list_here hd tl).
  by inversion H.
Qed.

Lemma set_eq_cons {A} : forall (a : A) (s1 s2 : set A),
  set_eq s1 s2 ->
  set_eq (a :: s1) (a :: s2).
Proof.
  intros a s1 s2 Heq.
  rewrite !set_eq_extract_forall in *.
  setoid_rewrite elem_of_cons.
  firstorder.
Qed.

Lemma set_eq_Forall
  {A : Type}
  (s1 s2 : set A)
  (H12 : set_eq s1 s2)
  (P : A -> Prop)
  : Forall P s1 <-> Forall P s2.
Proof.
  rewrite !Forall_forall. firstorder.
Qed.

Lemma set_union_comm `{EqDecision A}  : forall (s1 s2 : list A),
  set_eq (set_union s1 s2) (set_union s2 s1).
Proof.
  intros s1 s2; split; intro x; rewrite !set_union_iff; itauto.
Qed.

Lemma set_union_empty `{EqDecision A}  : forall (s1 s2 : list A),
  set_union s1 s2 = [] ->
  s1 = [] /\ s2 = [].
Proof.
  intros.
  destruct s2; [done |].
  by cbn in H; apply set_add_not_empty in H.
Qed.

Lemma set_union_nodup_left `{EqDecision A} (l l' : set A)
  : NoDup l -> NoDup (set_union l l').
Proof.
  intro Hl.
  induction l' as [| x' l' IH]; [done |].
  by apply set_add_nodup.
Qed.

Lemma set_union_subseteq_left `{EqDecision A}  : forall (s1 s2 : list A),
  s1 ⊆ (set_union s1 s2).
Proof.
  by intros; intros x H; apply set_union_intro; left.
Qed.

Lemma set_union_subseteq_right `{EqDecision A}  : forall (s1 s2 : list A),
  s2 ⊆ (set_union s1 s2).
Proof.
  by intros; intros x H; apply set_union_intro; right.
Qed.

Lemma set_union_subseteq_iff `{EqDecision A}  : forall (s1 s2 s : list A),
  set_union s1 s2 ⊆ s <-> s1 ⊆ s /\ s2 ⊆ s.
Proof.
  intros.
  unfold subseteq, list_subseteq.
  setoid_rewrite set_union_iff.
  split; itauto.
Qed.

Lemma set_union_iterated_nodup `{EqDecision A}
  (ss : list (list A))
  (H : forall s, s ∈ ss -> NoDup s) :
  NoDup (fold_right set_union [] ss).
Proof.
  intros.
  generalize dependent ss.
  induction ss.
  - by intros; apply NoDup_nil.
  - intros.
    simpl.
    apply set_union_nodup.
    + apply H; left.
    + apply IHss. by intros; apply H; right.
Qed.

Lemma set_union_in_iterated
  `{EqDecision A}
  (ss : list (set A))
  (a : A)
  : a ∈ (fold_right set_union [] ss) <-> Exists (fun s => a ∈ s) ss.
Proof.
  rewrite Exists_exists.
  induction ss; split; simpl.
  - intro H; inversion H.
  - intros [x [Hin _]]; inversion Hin.
  - intro Hin. apply set_union_iff in Hin.
    destruct Hin as [Hina0 | Hinss].
    + exists a0. rewrite elem_of_cons. by split; [left |].
    + apply IHss in Hinss. destruct Hinss as [x [Hinss Hinx]].
      setoid_rewrite elem_of_cons. eauto.
  - rewrite set_union_iff.
    intros [x [Hx Ha]].
    apply elem_of_cons in Hx.
    destruct Hx; subst.
    + by left.
    + right. apply IHss. by exists x.
Qed.

Lemma set_union_iterated_subseteq
  `{EqDecision A}
  (ss ss': list (set A))
  (Hincl : ss ⊆ ss') :
  (fold_right set_union [] ss) ⊆
  (fold_right set_union [] ss').
Proof.
  intros a H.
  apply set_union_in_iterated in H.
  apply set_union_in_iterated.
  rewrite Exists_exists in *.
  destruct H as [x [Hx Ha]].
  exists x.
  unfold incl in Hincl.
  split; [| done].
  by apply Hincl.
Qed.

Lemma set_union_empty_left `{EqDecision A}  : forall (s : list A),
  NoDup s -> set_eq (set_union [] s) s.
Proof.
  intros. split; intros x Hin.
  - apply set_union_elim in Hin. destruct Hin.
    + inversion H0.
    + done.
  - by apply set_union_intro; right.
Qed.

Lemma map_list_subseteq {A B} : forall (f : B -> A) (s s' : list B),
  s ⊆ s' -> (map f s) ⊆ (map f s').
Proof.
intro f; induction s; intros; simpl.
- apply list_subseteq_nil.
- assert (s ⊆ s') as Hs. {
    intros b Hs.
    by apply H; right.
  }
  spec IHs s' Hs.
  intros b Hs'.
  apply elem_of_cons in Hs'.
  destruct Hs'.
  * subst.
    apply elem_of_list_fmap_1.
    apply H.
    left.
  * by apply IHs.
Qed.

Lemma map_set_eq {A B} (f : B -> A) : forall s s',
  set_eq s s' ->
  set_eq (map f s) (map f s').
Proof.
  split; apply map_list_subseteq; apply H.
Qed.

Lemma set_map_nodup {A B} `{EqDecision A} (f : B -> A) : forall (s : set B),
  NoDup (set_map f s).
Proof.
  induction s; simpl; try constructor.
  by apply set_add_nodup.
Qed.

Lemma set_map_elem_of {A B} `{EqDecision A} (f : B -> A) : forall x s,
  x ∈ s ->
  (f x) ∈ (set_map f s).
Proof.
  induction s; intros; inversion H; subst; clear H; simpl.
  - by apply set_add_intro2.
  - by apply set_add_intro1, IHs.
Qed.

Lemma set_map_exists {A B} `{EqDecision A} (f : B -> A) : forall y s,
  y ∈ (set_map f s) <->
  exists x, x ∈ s /\ f x = y.
Proof.
  intros.
  induction s; split; intros; simpl in H.
  - inversion H.
  - destruct H as [x [Hx Hf]].
    inversion Hx.
  - apply set_add_iff in H. destruct H as [Heq | Hin]; subst.
    + exists a. by split; [left |].
    + apply IHs in Hin. destruct Hin as [x [Hin Heq]]; subst.
      exists x. by split; [right |].
  - simpl. destruct H as [x [Hx Hf]]; subst; simpl; apply set_add_iff.
    apply elem_of_cons in Hx.
    destruct Hx.
    + by subst; left.
    + by right; apply IHs; exists x.
Qed.

Lemma set_map_subseteq {A B} `{EqDecision A} (f : B -> A) : forall s s',
  s ⊆ s' ->
  (set_map f s) ⊆ (set_map f s').
Proof.
  induction s; intros; intro msg; intros.
  - inversion H0.
  - simpl in H0. apply set_add_elim in H0. destruct H0.
    + subst. apply set_map_elem_of. apply H. left.
    + apply IHs; [| done]. by intros x Hel; apply H; right.
Qed.

Lemma set_map_eq {A B} `{EqDecision A} (f : B -> A) : forall s s',
  set_eq s s' ->
  set_eq (set_map f s) (set_map f s').
Proof.
  by split; destruct H; apply set_map_subseteq.
Qed.

Lemma set_map_singleton {A B} `{EqDecision A} (f : B -> A) : forall s a,
  set_map f s = [a] ->
  forall b, b ∈ s -> f b = a.
Proof.
  intros. apply (set_map_elem_of f) in H0. rewrite H in H0. apply elem_of_cons in H0.
  destruct H0; [done | inversion H0].
Qed.

Lemma filter_set_add `{StrictlyComparable X} P
  `{∀ (x:X), Decision (P x)} :
  forall (l:list X) x, ~ P x ->
  filter P l = filter P (set_add x l).
Proof.
  induction l as [|hd tl IHl]; intros x H_false; cbn.
  - by rewrite decide_False.
  - destruct (decide (x = hd)); cbn; [done |].
    by destruct (decide (P hd)); rewrite <- IHl.
Qed.

Lemma set_add_ignore `{StrictlyComparable X} :
  forall (l : list X) (x : X),
    x ∈ l ->
    set_add x l = l.
Proof.
  induction l as [|hd tl IHl]; inversion 1; subst; cbn.
  - by rewrite decide_True.
  - by case_decide; [| rewrite IHl].
Qed.

Lemma set_add_new `{EqDecision A}:
  forall (x:A) l, ~x ∈ l -> set_add x l = l++[x].
Proof.
  induction l; cbn; [done |]; intros H_not_in.
  rewrite decide_False; cycle 1.
  - by intros ->; apply H_not_in; left.
  - rewrite elem_of_cons in H_not_in. rewrite IHl; itauto.
Qed.

Lemma set_remove_not_elem_of `{EqDecision A} : forall x (s : list A),
  ~ x ∈ s ->
  set_remove x s = s.
Proof.
  induction s; cbn; intros; [done |].
  rewrite decide_False; cycle 1.
  + by intros ->; contradict H; left.
  + rewrite IHs; [done |]. rewrite elem_of_cons in H. itauto.
Qed.

Lemma set_remove_elim `{EqDecision A} : forall x (s : list A),
  NoDup s -> ~ x ∈ (set_remove x s).
Proof.
  intros x s HND Hnelem. apply set_remove_iff in Hnelem; itauto.
Qed.

Lemma set_remove_first `{EqDecision A} : forall x y (s : list A),
  x = y -> set_remove x (y::s) = s.
Proof.
  by intros x y s ->; cbn; rewrite decide_True.
Qed.

Lemma set_remove_nodup_1 `{EqDecision A} : forall x (s : list A),
  NoDup (set_remove x s) ->
  ~ x ∈ (set_remove x s) ->
  NoDup s.
Proof.
  induction s; intros.
  - constructor.
  - simpl in H0 . destruct (decide (x = a)).
    + cbn in H; subst. constructor; [done |]. by rewrite decide_True in H.
    + rewrite elem_of_cons in H0.
      simpl in H.
      rewrite decide_False in H; auto.
      inversion H; subst.
      constructor.
      * intro Ha; apply (set_remove_3 _ x) in Ha; auto.
      * apply IHs; [done |].
        intro Hx.
        by contradict H0; right.
Qed.

Lemma set_remove_elem_of_iff `{EqDecision A} :  forall x y (s : list A),
  NoDup s ->
  y ∈ s ->
  x ∈ s <-> x = y \/ x ∈ (set_remove y s).
Proof.
  intros. split; intros.
  - destruct (decide (x = y)).
    + by left.
    + by right; apply set_remove_3.
  - destruct H1 as [Heq | Hin].
    + by subst.
    + by apply set_remove_1 in Hin.
Qed.

Lemma set_add_length
  `{EqDecision A}
  (x : A)
  (s : set A)
  (Hx : x ∉ s)
  : S (length s) = length (set_add x s).
Proof.
  revert x Hx.
  induction s; intros; [done |].
  simpl.
  destruct (decide (x = a)); [subst; elim Hx; left|].
  simpl. f_equal. apply IHs.
  by intro Hs; elim Hx; right.
Qed.

Lemma set_remove_length
  `{EqDecision A}
  (x : A)
  (s : set A)
  (Hx : x ∈ s)
  : length s = S (length (set_remove x s)).
Proof.
  generalize dependent x. induction s; intros; inversion Hx; subst.
  - by rewrite set_remove_first.
  - cbn. destruct (decide (x = a)); firstorder.
Qed.

Lemma set_eq_remove `{EqDecision A} : forall x (s1 s2 : list A),
  NoDup s1 ->
  NoDup s2 ->
  set_eq s1 s2 ->
  set_eq (set_remove x s1) (set_remove x s2).
Proof.
  intros x s1 s2 HND1 HND2 [].
  split; intros a Hin; rewrite set_remove_iff in *; itauto.
Qed.

Lemma subseteq_remove_union `{EqDecision A} : forall x (s1 s2 : list A),
  NoDup s1 ->
  NoDup s2 ->
  (set_remove x (set_union s1 s2)) ⊆
  (set_union s1 (set_remove x s2)).
Proof.
  intros. intros y Hin. apply set_remove_iff in Hin.
  - apply set_union_intro. destruct Hin. apply set_union_elim in H1.
    rewrite set_remove_iff; itauto.
  - by apply set_union_nodup.
Qed.

Lemma set_eq_remove_union_elem_of  `{EqDecision A} : forall x (s1 s2 : list A),
  NoDup s1 ->
  NoDup s2 ->
  x ∈ s1 ->
  set_eq (set_union s1 (set_remove x s2)) (set_union s1 s2).
Proof.
  split; intros msg Hin; apply set_union_iff; apply set_union_iff in Hin
  ; destruct Hin; try by left.
  - apply set_remove_iff in H2; itauto.
  - destruct (decide (msg = x)); subst.
    + by left.
    + by right; apply set_remove_iff.
Qed.

Lemma set_eq_remove_union_not_elem_of  `{EqDecision A} : forall x (s1 s2 : list A),
  NoDup s1 ->
  NoDup s2 ->
  ~ x ∈ s1 ->
  set_eq (set_union s1 (set_remove x s2)) (set_remove x (set_union s1 s2)).
Proof.
  intros.
  assert (HnodupUs1s2 := H0).
  apply (set_union_nodup _ _ H) in HnodupUs1s2.
  split; intros msg Hin.
  - apply set_remove_iff; [done |].
    apply set_union_iff in Hin as []; split.
    + by apply set_union_iff; left.
    + by intro; subst; apply H1.
    + apply set_remove_iff in H2 as []; [| done].
      by apply set_union_iff; right.
    + intro; subst.
      apply set_remove_iff in H2; itauto.
  - apply set_union_iff.
    apply set_remove_iff in Hin as []; [| done].
    apply set_union_iff in H2 as []; [by left |].
    by right; apply set_remove_iff.
Qed.

(** An improved version of the [set_diff_nodup] Lemma not requiring [NoDup]
for the second argument.
*)
(* TODO(palmskog): consider submitting a PR to Coq's stdlib. *)
Lemma set_diff_nodup' `{EqDecision A} (l l' : list A)
  : NoDup l -> NoDup (set_diff l l').
Proof.
induction 1 as [|x l H H' IH]; simpl.
- constructor.
- case_decide.
  + by apply IH.
  + by apply set_add_nodup, IH.
Qed.

Lemma diff_app_nodup `{EqDecision A} : forall (s1 s2 : list A),
  NoDup s1 ->
  NoDup s2 ->
  NoDup ((set_diff s1 s2) ++ s2).
Proof.
  intros.
  apply nodup_append; [| done | |].
  - by apply set_diff_nodup.
  - by intros; apply (set_diff_elim2 a s1).
  - setoid_rewrite set_diff_iff. itauto.
Qed.

Lemma add_remove_inverse `{EqDecision X}:
  forall (lv : list X) (v : X),
    ~ v ∈ lv ->
    set_remove v (set_add v lv) = lv.
Proof.
  induction lv as [| hd tl IHlv]; cbn; intros.
  - by rewrite decide_True.
  - rewrite elem_of_cons in H.
    destruct (decide (v = hd)) eqn: Heq; subst; cbn; [itauto |].
    rewrite Heq, IHlv; itauto.
Qed.

Lemma set_union_iterated_empty `{EqDecision A} :
  forall ss : list (set A),
    (forall s : list A, s ∈ ss -> s = []) -> fold_right set_union [] ss = [].
Proof.
  induction ss; [done |]; cbn; intros H.
  rewrite IHss; cycle 1.
  - by intros s Hel; apply H; right.
  - by cbn; apply H; left.
Qed.

(** For each element X of l1, exactly one occurrence of X is removed
   from l2. If no such occurrence exists, nothing happens. *)

Definition set_remove_list `{EqDecision A} (l1 l2 : list A) : list A :=
  fold_right set_remove l2 l1.

Example set_remove_list1 : set_remove_list [3;1;3] [1;1;2;3;3;3;3] = [1;2;3;3].
Proof. done. Qed.

Example set_remove_list2 : set_remove_list [4] [1;2;3] = [1;2;3].
Proof. done. Qed.

Lemma set_remove_list_1
  `{EqDecision A}
  (a : A)
  (l1 l2 : list A)
  (Hin : a ∈ (set_remove_list l1 l2)) :
  a ∈ l2.
Proof.
  unfold set_remove_list in Hin.
  induction l1.
  - simpl in Hin; itauto.
  - simpl in Hin.
    by apply set_remove_1, IHl1 in Hin.
Qed.

Lemma set_prod_nodup `(s1: set A) `(s2: set B):
  NoDup s1 ->
  NoDup s2 ->
  NoDup (set_prod s1 s2).
Proof.
  intros Hs1 HS2.
  induction Hs1.
  + constructor.
  + simpl.
    apply nodup_append.
    * apply NoDup_fmap; [congruence | done].
    * done.
    * intros [a b].
      rewrite elem_of_list_fmap, elem_of_list_prod.
      intros [_ [[= <- _] _]]. itauto.
    * intros [a b].
      rewrite elem_of_list_prod, elem_of_list_fmap.
      intros [Ha _] [_ [[= Hax _] _]]. congruence.
Qed.

(** An alternative to [set_diff].
    Unlike [set_diff], the result may contain
    duplicates if the first argument list <<l>> does.

    This definition exists to make proving
    [len_set_diff_decrease] more convenient,
    because <<length>> of <<filter>> can be simplified
    step by step while doing induction over <<l>>.
 *)
Definition set_diff_filter `{EqDecision A} (l r : list A) :=
  filter (.∉ r) l.

(**
   The characteristic membership property, parallel to
   [set_diff_iff].
 *)
Lemma set_diff_filter_iff `{EqDecision A} (a:A) l r:
  a ∈ (set_diff_filter l r) <-> (a ∈ l /\ ~a ∈ r).
Proof.
  induction l;simpl.
  - cbn. split; intros; [|itauto].
    inversion H.
  - unfold set_diff_filter in *.
    rewrite filter_cons.
    destruct (decide (~ a0 ∈ r)).
    * rewrite 2 elem_of_cons, IHl.
      split; itauto congruence.
    * rewrite elem_of_cons.
      split;itauto congruence.
Qed.

Lemma set_diff_filter_nodup `{EqDecision A} (l r:list A):
  NoDup l -> NoDup (set_diff_filter l r).
Proof.
  intros H.
  by apply NoDup_filter.
Qed.

(**
   Prove that subtracting a superset cannot produce
   a smaller result.
   This lemma is used to prove [len_set_diff_decrease].
 *)
Lemma len_set_diff_incl_le `{EqDecision A} (l a b: list A)
      (H_subseteq: forall x, x ∈ b -> x ∈ a):
  length (set_diff_filter l a) <= length (set_diff_filter l b).
Proof.
  induction l; [done |].
  unfold set_diff_filter.
  rewrite 2 filter_cons.
  destruct (decide (~ a0 ∈ a)); destruct (decide (~ a0 ∈ b)).
  - simpl. unfold set_diff_filter in IHl. lia.
  - itauto.
  - simpl.
    apply le_S.
    apply IHl.
  - apply IHl.
Qed.

(**
   Prove that strictly increasing the set to be subtracted,
   by adding an element actually found in <<l>> will decrease
   the size of the result.
 *)
Lemma len_set_diff_decrease `{EqDecision A} (new:A) (l a b: list A)
      (H_subseteq: forall x, x ∈ b -> x ∈ a)
      (H_new_is_new: new ∈ a /\ ~new ∈ b)
      (H_new_is_relevant: new ∈ l):
  length (set_diff_filter l a) < length (set_diff_filter l b).
Proof.
  induction l; [inversion H_new_is_relevant|];
    apply elem_of_cons in H_new_is_relevant; destruct H_new_is_relevant.
  - subst a0.
    unfold set_diff_filter.
    rewrite 2 filter_cons.
    destruct (decide (~ new ∈ a)); [tauto|].
    destruct (decide (~ new ∈ b));[|contradict n0; itauto].
    simpl.
    by apply le_n_S, len_set_diff_incl_le.
  - specialize (IHl H);clear H.
    unfold set_diff_filter.
    rewrite 2 filter_cons.
    destruct (decide (~ a0 ∈ a)); destruct (decide (~ a0 ∈ b)).
    + simpl.
      rewrite <- Nat.succ_lt_mono.
      apply IHl.
    + contradict n.
      apply H_subseteq.
      by destruct (decide (a0 ∈ b)).
    + simpl.
      apply Nat.lt_lt_succ_r.
      apply IHl.
    + apply IHl.
Qed.

Lemma len_set_diff_map_set_add `{EqDecision B} (new:B) `{EqDecision A} (f: B -> A)
      (a: list B) (l: list A)
      (H_new_is_new: ~(f new) ∈ (map f a))
      (H_new_is_relevant: (f new) ∈ l):
  length (set_diff_filter l (map f (set_add new a))) <
    length (set_diff_filter l (map f a)).
Proof.
  apply len_set_diff_decrease with (f new).
  - intro x. rewrite 2 elem_of_list_fmap.
    intros [x0 [Hx0 Hin]]. exists x0.
    rewrite set_add_iff. itauto.
  - split; [| done].
    apply elem_of_list_fmap_1.
    by apply set_add_iff; left.
  - done.
Qed.

Add Parametric Relation A : (set A) (@set_eq A)
 reflexivity proved by (@set_eq_refl A)
 transitivity proved by (@set_eq_tran A) as set_eq_rel.

Add Parametric Morphism A : (@elem_of_list A)
  with signature @eq A ==> @set_eq A ==> iff as set_eq_elem_of.
Proof.
  intros a l1 l2 H.
  split;apply H.
Qed.

Add Parametric Morphism A : (@elem_of_list A)
  with signature @eq A ==> @list_subseteq A ==> Basics.impl as set_elem_of_subseteq.
Proof. firstorder. Qed.

Lemma set_union_iterated_preserves_prop
  `{EqDecision A}
  (ss : list (set A))
  (P : A -> Prop)
  (Hp : forall (s : set A), forall (a : A), (s ∈ ss /\ a ∈ s) -> P a) :
  forall (a : A), a ∈ (fold_right set_union [] ss) -> P a.
Proof.
  intros.
  apply set_union_in_iterated in H. rewrite Exists_exists in H.
  destruct H as [s [Hins Hina]].
  apply Hp with (s := s).
  itauto.
Qed.

Lemma filter_set_eq {X} P Q
 `{∀ (x:X), Decision (P x)} `{∀ (x:X), Decision (Q x)}
   (l : list X)
   (resf := filter P l)
   (resg := filter Q l) :
   set_eq resf resg -> resf = resg.
Proof.
  intros.
  unfold resf, resg in *.
  apply filter_ext_elem_of. intros.
  unfold set_eq in H1.
  destruct H1 as [H1 H1'].
  unfold incl in *.
  specialize (H1 a). specialize (H1' a).
  split; intros.
  - by eapply elem_of_list_filter, H1, elem_of_list_filter.
  - by eapply elem_of_list_filter, H1', elem_of_list_filter.
Qed.

Lemma subseteq_appr : forall A (l m n : list A), l ⊆ n -> l ⊆ (m ++ n).
Proof.
  intros A l m n x y yinl.
  apply x in yinl.
  by apply elem_of_app; right.
Qed.

Lemma elem_of_union_fold
  `{EqDecision A}
  (haystack : list (list A))
  (a : A) :
  a ∈ (fold_right set_union [] haystack)
  <->
  exists (needle : list A), (a ∈ needle) /\ (needle ∈ haystack).
Proof.
  split.
  - generalize dependent a.
    generalize dependent haystack.
    induction haystack.
    + intros.
      simpl in H.
      inversion H.
    + intros.
      unfold fold_right in H.
      rewrite set_union_iff in H.
      destruct H.
      * setoid_rewrite elem_of_cons. eauto.
      * destruct (IHhaystack a0 H) as (needle & Hin1 & Hin2).
        setoid_rewrite elem_of_cons. eauto.
   - generalize dependent a.
     generalize dependent haystack.
     induction haystack.
     + intros.
       simpl in *.
       destruct H.
       destruct H as [Ha Hx].
       inversion Hx.
     + intros.
       destruct H as [needle [Hin Hin2]].
       rewrite elem_of_cons in Hin2.
       destruct Hin2.
       * cbn. rewrite set_union_iff, <- H; auto.
       * simpl.
         rewrite set_union_iff.
         right.
         apply IHhaystack.
         by exists needle.
Qed.

Lemma subseteq_Forall (A:Type) (P : A -> Prop) (l1 l2 : list A) :
 l2 ⊆ l1 -> Forall P l1 -> Forall P l2.
Proof.
  intros Hsub Hfor.
  apply Forall_forall.
  rewrite Forall_forall in Hfor.
  intros.
  by apply Hfor, Hsub.
Qed.
