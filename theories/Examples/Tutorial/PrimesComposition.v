From VLSM.Lib Require Import Itauto.
From Coq Require Import FunctionalExtensionality.
From Coq Require Import ZArith.Znumtheory.
From stdpp Require Import prelude.
From VLSM.Lib Require Import Preamble StdppExtras FinSuppFn NatExtras ListExtras.
From VLSM.Core Require Import VLSM PreloadedVLSM ConstrainedVLSM Composition.
From VLSM.Core Require Import VLSMProjections ProjectionTraces.
From VLSM.Examples Require Import Parity.

(** * Primes Composition of VLSMs

  This module demonstrates advanced concepts of the VLSM framework.
  We generalize the multiplying VLSMs defined in module [Parity] as a radix VLSM
  parameterized on a multiplier and study the composition of a family of
  such VLSMs.
  We then construct the composition consisting of a component for each prime
  number, characterize the valid messages, and show that any component in
  the composition is a validator.
*)

#[local] Open Scope Z_scope.

Section sec_radix_vlsm.

(**
  We parameterize a radix VLSM on an integer multiplier
  greater than one.
*)
Context
 (multiplier : Z)
 (multiplier_gt_1 : multiplier > 1)
 .

(** ** Definition of the Radix VLSM

  The Radix VLSM will share the type and transition validity predicate of the
  multiplying VLSM and differ only by the fact that the only initial message
  is the <<multiplier>> parameter, and that it outputs its input multiplied by
  the <<multiplier>>.
*)

Definition radix_transition
  (l : multiplying_label) (st : multiplying_state) (om : option multiplying_message)
  : multiplying_state * option multiplying_message :=
  match om with
  | Some j  => (st - j, Some (multiplier * j))
  | None    => (st, None)
  end.

(**
  We must also provide a proof that the intial state type
  is inhabited as the set of initial states is non-empty.
*)

(**
  An intermediate representation for the VLSM is required.
  It uses the previously defined specifications.
*)

Definition radix_machine : VLSMMachine multiplying_type :=
{|
  initial_state_prop := multiplying_initial_state_prop;
  initial_message_prop := fun (ms : multiplying_message) => ms = multiplier;
  s0 := multiplying_initial_state_type_inhabited;
  transition := fun l '(st, om) => radix_transition l st om;
  valid := fun l '(st, om) => multiplying_valid l st om;
|}.

(** The definition of the Radix VLSM. *)

Definition radix_vlsm : VLSM multiplying_message :=
{|
  vtype := multiplying_type;
  vmachine := radix_machine;
|}.

(**
  To improve readability, we explicitly define [radix_label] as the value of
  the unit type.
*)

Definition radix_label : label multiplying_type := ().

(** ** Parity VLSM Properties *)

(** *** Constrained messages are positives divisible by <<multiplier>> *)

Lemma radix_constrained_messages_left :
  forall (m : multiplying_message),
    constrained_message_prop radix_vlsm m ->
    exists (j : Z), m = multiplier * j /\ j > 1.
Proof.
  intros m ([s []] & [] & s' & (_ & _ & []) & Ht).
  inversion Ht; subst.
  by eexists; split; [done | lia].
Qed.

Lemma radix_constrained_messages_right :
  forall (m : multiplying_message),
    (exists (j : Z), m = multiplier * j) -> m > multiplier ->
    constrained_message_prop radix_vlsm m.
Proof.
  intros m (j & Hj) Hmgt0.
  unfold constrained_message_prop_direct, can_emit.
  exists (j, Some j), radix_label, 0.
  repeat split.
  - by apply initial_state_is_valid; cbn; red; nia.
  - by apply any_message_is_valid_in_preloaded.
  - by lia.
  - by nia.
  - by cbn; do 2 f_equal; lia.
Qed.

Lemma radix_constrained_messages :
  forall (m : multiplying_message),
    constrained_message_prop radix_vlsm m <-> (exists (j : Z), m = multiplier * j /\ j > 1).
Proof.
  split.
  - by apply radix_constrained_messages_left.
  - by intros [? []]; apply radix_constrained_messages_right; [exists x | nia].
Qed.

(** *** Constrained states property *)

Lemma radix_constrained_states_right :
  forall (st : multiplying_state),
    constrained_state_prop radix_vlsm st -> st >= 0.
Proof.
  induction 1 using valid_state_prop_ind.
  - by cbn in Hs; red in Hs; lia.
  - destruct l, om, Ht as [(Hs & _ & []) Ht].
    by inversion Ht; subst; cbn in *; lia.
Qed.

Lemma radix_constrained_states_left :
  forall (st : multiplying_state),
    st >= 0 -> constrained_state_prop radix_vlsm st.
Proof.
  intros st Hst.
  apply input_valid_transition_destination
    with (l := radix_label) (s := st + 2) (om := Some 2) (om' := Some (2 * multiplier)).
  repeat split; [| | by lia.. | by cbn; do 2 f_equal; lia].
  - by apply initial_state_is_valid; cbn; red; lia.
  - by apply any_message_is_valid_in_preloaded.
Qed.

Lemma radix_constrained_states :
  forall (st : multiplying_state),
    constrained_state_prop radix_vlsm st <-> st >= 0.
Proof.
  split.
  - by apply radix_constrained_states_right.
  - by apply radix_constrained_states_left.
Qed.

(** *** Positive powers of the multiplier are valid messages *)

Lemma radix_valid_messages_powers_of_mult_right :
  forall (m : multiplying_message),
    valid_message_prop radix_vlsm m ->
    exists p : Z, p >= 1 /\ m = multiplier ^ p.
Proof.
  intros m [s Hvsm].
  assert (Hom : is_Some (Some m)) by (eexists; done).
  replace m with (is_Some_proj Hom) by done.
  revert Hvsm Hom; generalize (Some m) as om; intros.
  clear m; induction Hvsm using valid_state_message_prop_ind.
  - unfold option_initial_message_prop, from_option in Hom; cbn in Hom.
    destruct Hom as [m ->]; cbn in *.
    by exists 1; split; [lia | f_equal; lia].
  - destruct om as [m |]; [| done].
    unshelve edestruct IHHvsm2 as [x Hx]; [done |].
    inversion Ht; subst; clear Ht.
    cbn in Hx |- *; destruct Hx as [Hgeq1 ->].
    exists (x + 1).
    split; [by lia |].
    by rewrite <- Z.pow_succ_r; [| lia].
Qed.

Lemma radix_valid_messages_powers_of_mult_left :
  forall (p : Z),
    p >= 1 -> valid_message_prop radix_vlsm (multiplier ^ p).
Proof.
  intros p Hp.
  assert (Hle : 0 <= p - 1) by lia.
  replace p with (p - 1 + 1) by lia.
  remember (p - 1) as x.
  clear p Hp Heqx.
  revert x Hle.
  apply natlike_ind; [by apply initial_message_is_valid; cbn; lia |].
  intros x Hxgt0 Hindh.
  pose (msgin := multiplier ^ (x + 1)).
  apply emitted_messages_are_valid.
  exists (msgin, Some (multiplier ^ (x + 1))), radix_label, 0.
  repeat split.
  - by apply initial_state_is_valid; cbn; red; lia.
  - by apply Hindh.
  - by lia.
  - replace (x + 1) with (Z.succ x) by lia.
    by rewrite Z.pow_succ_r; lia.
  - by cbn; rewrite <- Z.pow_succ_r, Z.add_succ_l; [do 2 f_equal; lia | lia].
Qed.

Lemma radix_valid_messages_powers_of_mult :
  forall (m : multiplying_message),
    valid_message_prop radix_vlsm m
      <->
    exists p : Z, p >= 1 /\ m = multiplier ^ p.
Proof.
  split.
  - by intros; apply radix_valid_messages_powers_of_mult_right.
  - by intros (p & Hpgt0 & [= ->]); apply radix_valid_messages_powers_of_mult_left.
Qed.

End sec_radix_vlsm.

Section sec_composition.

Context
  {index : Type}
  (multipliers : index -> Z)
  (Hmultipliers : forall (i : index), multipliers i <> 0)
  `{FinSet index indexSet}
  .

Definition indexed_radix_vlsms (i : index) : VLSM multiplying_message :=
  radix_vlsm (multipliers i).

Context
  (radix_constraint : composite_label indexed_radix_vlsms ->
    composite_state indexed_radix_vlsms * option multiplying_message -> Prop)
  .

Definition radix_composite_vlsm : VLSM multiplying_message :=
  composite_vlsm indexed_radix_vlsms radix_constraint.

Lemma composite_state_pos
  (s : composite_state indexed_radix_vlsms)
  (Hs : valid_state_prop radix_composite_vlsm s) :
    forall (i : index), s i >= 0.
Proof.
  intros i.
  apply radix_constrained_states_right with (multipliers i).
  by apply (valid_state_project_preloaded multiplying_message indexed_radix_vlsms radix_constraint).
Qed.

(**
  Any valid message can be expressed as a non-empty product of powers
  of the multipliers associated to the components.
*)
Lemma composition_valid_messages_powers_of_mults_right (m : multiplying_message) :
  valid_message_prop radix_composite_vlsm m ->
  exists (f : fsfun index 0%nat),
    fin_supp f <> [] /\ m = fsfun_prod multipliers f.
Proof.
  intros [s Hvsm].
  remember (Some m) as om.
  revert m Heqom.
  induction Hvsm using valid_state_message_prop_ind; intros; subst.
  - destruct Hom as (n & (mielem & mi) & Hmi); cbn in mi, Hmi.
    exists (delta_nat_fsfun n).
    split; [by eapply elem_of_not_nil, elem_of_delta_nat_fsfun |].
    by rewrite <- Hmi, mi, prod_powers_delta.
  - destruct l as (k & lk).
    destruct om; [| done].
    destruct (IHHvsm2 _ eq_refl) as (f & Hdomf & ->).
    inversion Ht.
    exists (succ_fsfun f k).
    split; [| by rewrite fsfun_prod_succ].
    apply not_null_element in Hdomf; destruct_dec_sig Hdomf i Hi Heq.
    by eapply elem_of_not_nil, elem_of_succ_fsfun; right.
Qed.

End sec_composition.

Section sec_free_composition.

Context
  `{EqDecision index}
  (multipliers : index -> Z)
  `{Inhabited index}
  .

Definition free_radix_composite_vlsm : VLSM multiplying_message :=
  free_composite_vlsm (indexed_radix_vlsms multipliers).

#[local] Lemma free_radix_composite_vlsm_emits_multiplier :
  forall (m : multiplying_message),
    valid_message_prop free_radix_composite_vlsm m ->
    m >= 2 ->
  forall (n : index),
  input_valid_transition free_radix_composite_vlsm (existT n radix_label)
(update (const 1) n (m + 1), Some m)
(const 1, Some (multipliers n * m)).
Proof.
  repeat split.
  - apply initial_state_is_valid.
    intros j; cbn; red.
    by destruct (decide (n = j)) as [-> |];
      [rewrite update_eq; lia | rewrite update_neq].
  - done.
  - by rewrite update_eq; lia.
  - by lia.
  - cbn; f_equal; rewrite update_eq.
    extensionality j; cbn.
    destruct (decide (n =j)) as [-> |]; state_update_simpl; [by lia |].
    by rewrite update_neq.
Qed.

Lemma composition_valid_messages_powers_of_mults_left
  (Hmpos : forall (i : index), multipliers i > 1) (m : multiplying_message)
  (f : fsfun index 0%nat) :
    fin_supp f <> [] /\ m = fsfun_prod multipliers f ->
    valid_message_prop free_radix_composite_vlsm m.
Proof.
  intros [Hpowgeq1 Hm]; revert f Hpowgeq1 m Hm.
  apply (nat_fsfun_ind (fun (f : fsfun index 0%nat) => fin_supp f <> [] ->
    forall m : multiplying_message, m = fsfun_prod multipliers f ->
    valid_message_prop free_radix_composite_vlsm m)); [| done |].
  - intros f1 f2 Heq Hall Hi m Hm.
    eapply Hall; [| by rewrite Heq].
    contradict Hi.
    apply Permutation_nil.
    by rewrite <- Hi, Heq.
  - intros n f0 IHf0 Hi m Hm.
    destruct (nat_fsfun_inv f0) as [Heq | (n' & f0' & Heq)].
    + rewrite fsfun_prod_succ, Heq, fsfun_prod_zero in Hm.
      apply initial_message_is_valid. exists n.
      by unshelve eexists (exist _ m _); cbn; lia.
    + assert (Hmvalid : valid_message_prop free_radix_composite_vlsm (fsfun_prod multipliers f0)).
      {
        apply IHf0; [| done].
        assert (Hinh : fin_supp (succ_fsfun f0' n') <> []).
        {
          by eapply elem_of_not_nil, elem_of_succ_fsfun; left.
        }
        contradict Hinh; apply Permutation_nil.
        by rewrite <- Hinh, Heq.
      }
      subst m; rewrite fsfun_prod_succ.
      assert (Hpos : fsfun_prod multipliers f0 >= multipliers n').
      {
        rewrite Heq, fsfun_prod_succ.
        cut (fsfun_prod multipliers f0' > 0); [by specialize (Hmpos n'); nia |].
        destruct (decide (fin_supp f0' = [])) as [Hz |].
        - eapply empty_fsfun_supp_inv in Hz as ->.
          by setoid_rewrite fsfun_prod_zero; lia.
        - apply prod_powers_gt; [by lia | | done].
          by intro i; specialize (Hmpos i); lia.
      }
      specialize (Hmpos n').
      by eapply input_valid_transition_out,
        free_radix_composite_vlsm_emits_multiplier; [| lia].
Qed.

Lemma composition_valid_messages_powers_of_mults
  (Hmpos : forall (i : index), multipliers i > 1) (m : multiplying_message) :
    valid_message_prop free_radix_composite_vlsm m <->
  exists (f : fsfun index 0%nat),
    fin_supp f <> [] /\ m = fsfun_prod multipliers f.
Proof.
  split.
  - intros Hvm.
    eapply VLSM_incl_valid_message in Hvm; cycle 1.
    + by apply free_composite_vlsm_spec.
    + by do 2 red.
    + by cbn in Hvm; eapply composition_valid_messages_powers_of_mults_right.
  - by intros [? []]; eapply composition_valid_messages_powers_of_mults_left.
Qed.

Lemma composition_valid_message_ge_2
  (Hmpos : forall (i : index), multipliers i > 1) (m : multiplying_message) :
  valid_message_prop free_radix_composite_vlsm m -> m >= 2.
Proof.
  intro Hv.
  apply composition_valid_messages_powers_of_mults in Hv
    as (i & Hsupp & ->); [| done].
  cut (fsfun_prod multipliers i > 1); [by lia |].
  by apply prod_powers_gt; [lia | ..].
Qed.

End sec_free_composition.

(** ** A VLSM composition for all primes

  In the following section we give an example of a composition with an infinite
  number of [radix_vlsm] components, one for each prime number.

  Then we characterize the valid messages for this composition to be precisely
  all natural numbers larger than 1.

  Finally, we show that in this composition any component is a validator.
*)

Section sec_primes_vlsm_composition.

Definition primes_vlsm_composition : VLSM Z :=
  free_radix_composite_vlsm (fun p : primes => `p).

Lemma primes_vlsm_composition_valid_message_char :
  forall (m : Z),
    valid_message_prop primes_vlsm_composition m <-> (m > 1)%Z.
Proof.
  assert (Hprime_pos : forall i : primes, `i > 1).
  {
    intro i.
    destruct_dec_sig i n Hn Heq; subst; cbn.
    by destruct Hn; lia.
  }
  intros m; unfold primes_vlsm_composition.
  rewrite composition_valid_messages_powers_of_mults;
    [| by intro i; specialize (Hprime_pos i); lia..].
  split.
  - intros (fp & Hdom_fp & ->).
    by apply prod_powers_gt.
  - by apply primes_factorization.
Qed.

(**
  For any prime number, its corresponding component in the [primes_vlsm_composition]
  is a validator for that composition, i.e., all of its constrained transitions
  can be lifted to valid transitions for the composition.
*)
Theorem component_projection_validator_prop_primes :
  forall (p : primes),
    component_projection_validator_prop
      (indexed_radix_vlsms (fun p : primes => ` p))
      (fun _ _ => True) p.
Proof.
  intros p lp sp [m|] (Hsp & _ & []).
  exists (lift_to_composite_state' (indexed_radix_vlsms (fun p : primes => `p)) p sp).
  repeat split; [by state_update_simpl | | | by state_update_simpl | done].
  - apply initial_state_is_valid.
    intros p'; cbn; red.
    by destruct (decide (p = p')); subst; state_update_simpl; cbn; [lia |].
  - eapply VLSM_incl_valid_message; [by apply free_composite_vlsm_spec | ..].
    + by do 2 red.
    + by apply primes_vlsm_composition_valid_message_char; lia.
Qed.

(** *** A (slightly) constrained composition of primes *)

(**
  To show how a composition constraint affects validation, we here add a very
  simple constraint, that the received message must be even, to the composition.
*)
Inductive EvenConstraint :
  label primes_vlsm_composition -> state primes_vlsm_composition * option Z -> Prop :=
| even_constraint : forall l s m, Z.Even m -> EvenConstraint l (s, Some m).

Definition even_constrained_primes_composition : VLSM Z :=
  constrained_vlsm primes_vlsm_composition EvenConstraint.

#[local] Lemma even_constrained_primes_composition_emits_multiplier :
  forall (m : multiplying_message),
    valid_message_prop even_constrained_primes_composition m ->
    m >= 2 ->
    Z.Even m ->
  forall (n : primes),
  input_valid_transition even_constrained_primes_composition (existT n radix_label)
  (update (const 1) n (m + 1), Some m)
  (const 1, Some (` n * m)).
Proof.
  repeat split.
  - apply initial_state_is_valid.
    intros j; cbn; red.
    by destruct (decide (n = j)) as [-> |];
      [rewrite update_eq; lia | rewrite update_neq].
  - done.
  - by rewrite update_eq; lia.
  - by lia.
  - done.
  - cbn; f_equal; extensionality j; cbn.
    destruct (decide (n = j)); subst; state_update_simpl.
    + by rewrite update_eq; lia.
    + by rewrite update_neq.
Qed.

Lemma even_constrained_primes_composition_valid_messages_left (m : Z) :
  m > 1 -> Z.Even m -> valid_message_prop even_constrained_primes_composition m.
Proof.
  intros Hm1 Hmeven.
  assert (Hinit : composite_initial_message_prop (indexed_radix_vlsms (fun p : primes => `p)) 2)
    by (unshelve eexists (dexist 2 prime_2), (exist _ 2 _); done).
  destruct (decide (m = 2)) as [-> | Hm2]; [by apply initial_message_is_valid |].
  destruct Hmeven as [n ->].
  assert (Hn : 2 <= n) by lia.
  pose (P := fun n => valid_message_prop even_constrained_primes_composition (2 * n)).
  cut (P n); [done |].
  clear -Hn Hinit; revert n Hn; apply Zlt_lower_bound_ind; subst P; cbn; intros n Hind Hn.
  destruct (decide (prime n)) as [Hp | Hnp].
  - replace (2 * n) with (` (dexist n Hp) * 2) by (cbn; lia).
    eapply input_valid_transition_out,
      even_constrained_primes_composition_emits_multiplier;
        [| done | by exists 1].
    by apply initial_message_is_valid.
  - apply not_prime_divide_prime in Hnp as (m & Hp & q & Hq & ->); [| by lia].
    replace (2 * (q * m)) with (` (dexist m Hp) * (2 * q)) by (cbn; lia).
    eapply input_valid_transition_out,
      even_constrained_primes_composition_emits_multiplier;
      [| by lia | by eexists].
    by apply Hind.
Qed.

(**
  The valid messages of the [even_constrained_primes_composition] are precisely
  all positive even numbers.
*)
Lemma even_constrained_primes_composition_valid_message_char (m : Z) :
  valid_message_prop even_constrained_primes_composition m
    <->
  (m > 1)%Z /\ Z.Even m \/ prime m.
Proof.
  split.
  - intros Hm.
    cut ((m > 1)%Z /\ (Z.Even m \/ prime m)).
    {
      by destruct (decide (prime m)); [right | left; itauto].
    }
    split.
    + apply primes_vlsm_composition_valid_message_char.
      eapply VLSM_incl_valid_message; [..| done].
      * by apply (VLSM_incl_constrained_vlsm primes_vlsm_composition).
      * by do 2 red.
    + apply emitted_messages_are_valid_iff in Hm
        as [([p Hp] & [i Hi] & <-) | ([s [im |]] & [i li] & s' & (_ & _ & _ & Hc) & Ht)];
        cbn in *; [by subst; right; apply bool_decide_spec in Hp | | done].
      inversion Hc; subst; clear Hc.
      inversion Ht; subst; clear Ht.
      by left; apply Zeven_equiv, Zeven_mult_Zeven_r, Zeven_equiv.
  - intros [[] | Hprime].
    + by apply even_constrained_primes_composition_valid_messages_left.
    + apply initial_message_is_valid.
      by unshelve eexists (dexist m Hprime), (exist _ m _).
Qed.

(** No component is validating for the [even_constrained_primes_composition]. *)
Lemma even_constrained_primes_composition_no_validator :
  forall (p : primes),
    ~ component_projection_validator_prop
        (indexed_radix_vlsms (fun p : primes => ` p))
        EvenConstraint p.
Proof.
  intros p Hnv.
  cut (input_valid
    (pre_loaded_with_all_messages_vlsm
      (indexed_radix_vlsms (λ p0 : primes, `p0) p)) () (3, Some 3)).
  {
    intro Hiv.
    apply Hnv in Hiv as (s & _ & _ & _ & _ & Hc).
    by inversion Hc as [? ? ? []]; lia.
  }
  repeat split; [| by apply any_message_is_valid_in_preloaded | by lia..].
  apply initial_state_is_valid; cbn.
  by red; lia.
Qed.

(**
  Now we show that if we constrain each component with a local condition
  equivalent to the global constraint we can recover validation.
*)
Inductive LocalEvenConstraint (mult : Z) :
  label (radix_vlsm mult) -> state (radix_vlsm mult) * option Z -> Prop :=
| local_even_constraint : forall l s m, Z.Even m ->
    LocalEvenConstraint mult l (s, Some m).

Definition even_prime_vlsms (p : primes) : VLSM multiplying_message :=
  constrained_vlsm (radix_vlsm (`p)) (LocalEvenConstraint (`p)).

(**
  Adding the local constraint to each component does not change the behavior
  of the composition.
*)
Lemma even_constrained_primes_composition_incl_left :
  VLSM_incl
    even_constrained_primes_composition
    (composite_vlsm even_prime_vlsms EvenConstraint).
Proof.
  apply basic_VLSM_strong_incl; cycle 3; [by intros ? **.. |].
  intros [p []] s [m |] [Hv Hc]; [| by inversion Hc]; cbn.
  split; [| done].
  split; [| by inversion Hc].
  by destruct Hv.
Qed.

(**
  The validation result is recovered for the new constrained components and composition.
*)
Theorem even_constrained_primes_composition_all_validators :
  forall (p : primes),
    component_projection_validator_prop even_prime_vlsms EvenConstraint p.
Proof.
  intros p lp sp [m |] (Hsp & _ & [[] Hc]).
  inversion Hc as [? ? ? Heven]; subst.
  exists (lift_to_composite_state' (indexed_radix_vlsms (fun p : primes => `p)) p sp).
  repeat split; [by state_update_simpl | | | by state_update_simpl | done..].
  - apply initial_state_is_valid.
    intro p'; cbn; red.
    by destruct (decide (p = p')); subst; state_update_simpl; cbn; [lia |].
  - apply option_valid_message_Some.
    eapply VLSM_incl_valid_message;
      [by apply even_constrained_primes_composition_incl_left | ..].
    + by do 2 red.
    + apply even_constrained_primes_composition_valid_message_char.
      by left; split; [lia |].
Qed.

End sec_primes_vlsm_composition.
