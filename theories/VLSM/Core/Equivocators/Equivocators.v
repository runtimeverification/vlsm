From VLSM.Lib Require Import Itauto.
From stdpp Require Import prelude.
From Coq Require Import Eqdep Fin FunctionalExtensionality.
From VLSM.Lib Require Import Preamble.
From VLSM.Core Require Import VLSM PreloadedVLSM VLSMProjections Composition.

(** * VLSM Equivocation

  An [equivocator_vlsm] for a given [VLSM] <<X>> is a VLSM which starts as a
  regular machine X, and then, at any moment:
  - can spawn a new machine in a (potentially) different initial state.
  - can perform [valid] [transition]s on any of its internal machines
  - can fork any of its internal machines by duplicating its state and then using
    the given label and message to [transition] on the new fork.

    Note that we only allow forking if a transition is then taken on the neq fork.
*)

Section sec_equivocator_vlsm.

Context
  {message : Type}
  (X : VLSM message)
  .

(**
  The state of such a machine will be abstracted using

  1. A natural <<n>>, stating the number of copies of the original machine
  2. A state of <<X>> for each 1..n+1
*)
#[local] Definition bounded_state_copies := {n : nat & Fin.t (S n) -> state X}.

(**
  To preserve determinism we need to enhance the labels to indicate what copy
  of the machine will be used for a transition.
  To achieve this, we'll define the following label variants:

  - [Spawn] <<s>> to extend the state with a new machine initialized with <<s>>
  - [ContinueWith] <<n>> <<l>>, to transition on copy <<n>> using label <<l>>
  - [ForkWith] <<n>> <<l>>, to extend the state with a new machine initialized
    with the current state of machine <<n>> and to transition on that copy
    using label <<l>>.
*)
Inductive EquivocatorLabel : Type :=
| Spawn : state X -> EquivocatorLabel
| ContinueWith : nat -> label X -> EquivocatorLabel
| ForkWith : nat -> label X -> EquivocatorLabel.

Definition equivocator_type : VLSMType message :=
  {| state := bounded_state_copies ;
     label := EquivocatorLabel
  |}.

Definition equivocator_state : Type := state equivocator_type.
Definition equivocator_label : Type := label equivocator_type.

(** The number of machine copies in the given state. *)
Definition equivocator_state_n (es : equivocator_state) := S (projT1 es).
(** The index of the last machine copies in the given state. *)
Definition equivocator_state_last (es : equivocator_state) := projT1 es.
Definition equivocator_state_s (es : equivocator_state) := projT2 es.

Lemma equivocator_state_last_n es : equivocator_state_n es = S (equivocator_state_last es).
Proof. done. Qed.

Definition mk_singleton_state
  (s : state X)
  : equivocator_state
  :=
  existT 0 (fun _ => s).

#[local] Lemma equivocator_state_projection_irrel (s : equivocator_state)
  i (li : i < (equivocator_state_n s))
  j (lj : j < (equivocator_state_n s))
  (Heq : i = j)
  : equivocator_state_s s (nat_to_fin li) = equivocator_state_s s (nat_to_fin lj).
Proof.
  subst i.
  by replace (nat_to_fin li) with (nat_to_fin lj) by apply of_nat_ext.
Qed.

#[local] Lemma equivocator_state_eq s (i1 i2 : fin (equivocator_state_n s))
  : fin_to_nat i1 = fin_to_nat i2 -> equivocator_state_s s i1 = equivocator_state_s s i2.
Proof.
  intro Heq.
  replace i2 with i1; [done |].
  by apply (inj fin_to_nat).
Qed.

Definition is_singleton_state
  (s : equivocator_state)
  : Prop
  := equivocator_state_n s = 1.

Lemma is_singleton_state_dec
  (s : equivocator_state)
  : Decision (is_singleton_state s).
Proof.
  by apply Nat.eq_dec.
Qed.

Definition is_equivocating_state
  (s : equivocator_state)
  : Prop
  := not (is_singleton_state s).

#[export] Instance is_equivocating_state_dec
  (s : equivocator_state)
  : Decision (is_equivocating_state s).
Proof.
  apply not_dec.
  by apply is_singleton_state_dec.
Qed.

(**
  Attempts to obtain the state of the internal machine with index <<i>>
  from an [equivocator_state]. Fails when index <<i>> does not refer to a
  machine.
*)
Definition equivocator_state_project
  (bs : equivocator_state)
  (i : nat)
  : option (state X)
  :=
  match (decide (i < equivocator_state_n bs)) with
  | left lt_in => Some (equivocator_state_s bs (of_nat_lt lt_in))
  | _ =>  None
  end.

#[local] Lemma equivocator_state_project_Some s i (Hi : i < equivocator_state_n s)
  : equivocator_state_project s i = Some (equivocator_state_s s (nat_to_fin Hi)).
Proof.
  unfold equivocator_state_project.
  case_decide; [| lia].
  f_equal. apply equivocator_state_eq.
  by rewrite !fin_to_nat_to_fin.
Qed.

#[local] Lemma equivocator_state_project_None s i (Hi : ~ i < equivocator_state_n s)
  : equivocator_state_project s i = None.
Proof.
  unfold equivocator_state_project.
  by case_decide; [lia |].
Qed.

Lemma equivocator_state_project_Some_rev s i si
  : equivocator_state_project s i = Some si -> i < equivocator_state_n s.
Proof.
  by unfold equivocator_state_project; case_decide.
Qed.

Lemma equivocator_state_project_None_rev s i
  : equivocator_state_project s i = None -> ~ i < equivocator_state_n s.
Proof.
  unfold equivocator_state_project.
  by case_decide; [congruence | intro; lia].
Qed.

#[local] Ltac destruct_equivocator_state_project' es i si Hi Hpr :=
  destruct (equivocator_state_project es i) as [si |] eqn: Hpr
  ; [specialize (equivocator_state_project_Some_rev _ _ _ Hpr) as Hi
    | specialize (equivocator_state_project_None_rev _ _ Hpr) as Hi].

#[local] Ltac destruct_equivocator_state_project es i si Hi :=
  let Hpr := fresh "Hpr" in
  destruct_equivocator_state_project' es i si Hi Hpr
  ; clear Hpr.

(**
  Extensionality result, reducing the proof of the equality of two
  [equivocator_state]s to the equality of their projections.
*)
Lemma equivocator_state_project_ext es1 es2
  (Hext : forall i, equivocator_state_project es1 i = equivocator_state_project es2 i)
  : es1 = es2.
Proof.
  assert (equivocator_state_last es1 = equivocator_state_last es2).
  { specialize (equivocator_state_last_n es1) as Hlst1.
    specialize (equivocator_state_last_n es2) as Hlst2.
    specialize (Hext (equivocator_state_last es1)) as Hlst_es1.
    specialize (Hext (equivocator_state_last es2)) as Hlst_es2.
    clear Hext.
    symmetry in Hlst_es1.
    destruct_equivocator_state_project es1 (equivocator_state_last es1) lst1 Hi1; [| lia].
    destruct_equivocator_state_project es2 (equivocator_state_last es2) lst2 Hi2; [| lia].
    apply equivocator_state_project_Some_rev in Hlst_es1.
    apply equivocator_state_project_Some_rev in Hlst_es2.
    lia.
  }
  apply eq_sigT_uncurried.
  exists H.
  extensionality x.
  specialize (Hext x).
  specialize (fin_to_nat_lt x) as Hx.
  rewrite (equivocator_state_project_Some es2 x Hx) in Hext.
  rewrite <- !(@nat_to_fin_to_nat _ x Hx).
  destruct es1 as [x1 s1], es2 as [x2 s2]; simpl in *; subst; simpl.
  rewrite (equivocator_state_project_Some (existT x2 s1) x Hx) in Hext.
  by inversion Hext.
Qed.

(** The original state index is present in any equivocator state. *)
Lemma Hzero (s : equivocator_state) : 0 < equivocator_state_n s.
Proof. by pose proof (equivocator_state_last_n s); lia. Qed.

Definition equivocator_state_zero (es : equivocator_state) : state X :=
  equivocator_state_s es (nat_to_fin (Hzero es)).

Lemma equivocator_state_project_zero (es : equivocator_state)
  : equivocator_state_project es 0 = Some (equivocator_state_zero es).
Proof.
  unfold equivocator_state_project, equivocator_state_n.
  by case_decide; [| lia].
Qed.

Definition equivocator_state_update
  (bs : equivocator_state)
  (i : nat)
  (si : state X)
  : equivocator_state
  :=
  @existT nat (fun n => Fin.t (S n) -> state X)
    (equivocator_state_last bs)
	  (fun j => if  decide (i = j) then si else equivocator_state_s bs j).

(** Some basic properties for [equivocator_state_update]. *)

Lemma equivocator_state_update_size bs i si
  : equivocator_state_n (equivocator_state_update bs i si) = equivocator_state_n bs.
Proof. done. Qed.

Lemma equivocator_state_update_lst bs i si
  : equivocator_state_last (equivocator_state_update bs i si) = equivocator_state_last bs.
Proof. done. Qed.

Lemma equivocator_state_update_project_eq bs i si j
  (Hj : j < equivocator_state_n bs)
  (Hij : i = j)
  : equivocator_state_project (equivocator_state_update bs i si) j = Some si.
Proof.
  pose proof (equivocator_state_update_size bs i si) as Heq.
  destruct_equivocator_state_project' (equivocator_state_update bs i si) j sj Hi' Hpr ; [| lia].
  rewrite <- Hpr.
  rewrite (equivocator_state_project_Some _ _ Hi').
  f_equal; subst; clear; simpl.
  rewrite decide_True; [done |].
  by rewrite fin_to_nat_to_fin.
Qed.

Lemma equivocator_state_update_project_neq bs i si j
  (Hij : i <> j)
  : equivocator_state_project (equivocator_state_update bs i si) j = equivocator_state_project bs j.
Proof.
  pose proof (equivocator_state_update_size bs i si) as Heq.
  destruct_equivocator_state_project' (equivocator_state_update bs i si) j sj Hj Hpr.
  - assert (Hj' := Hj).
    rewrite Heq in Hj'.
    rewrite (equivocator_state_project_Some _ _ Hj) in Hpr.
    rewrite (equivocator_state_project_Some _ _ Hj').
    f_equal.
    inversion Hpr.
    rewrite decide_False.
    + apply equivocator_state_eq.
      by rewrite !fin_to_nat_to_fin.
    + intro Hcontra.
      by rewrite !fin_to_nat_to_fin in Hcontra; congruence.
  - rewrite Heq in Hj.
    by rewrite (equivocator_state_project_None _ _ Hj).
Qed.

#[local] Ltac destruct_equivocator_state_update_project' es i s j Hj Hij Hpr :=
  let Hsize := fresh "Hsize" in
  pose proof (equivocator_state_update_size es i s) as Hsize
  ; destruct (decide (j < equivocator_state_n es)) as [Hj | Hj]
  ; [destruct (decide (i = j)) as [Hij | Hij]
    ; [specialize (equivocator_state_update_project_eq es i s j Hj Hij) as Hpr
      | specialize (equivocator_state_update_project_neq es i s j Hij) as Hpr]
    | specialize (equivocator_state_project_None (equivocator_state_update es i s) j Hj) as Hpr]
  ; rewrite Hpr in *
  ; clear Hsize.

#[local] Ltac destruct_equivocator_state_update_project es i s j Hj Hij :=
  let Hpr := fresh "Hpr" in
  destruct_equivocator_state_update_project' es i s j Hj Hij Hpr
  ; clear Hpr.

(** Extends an [equivocator_state] with a new state of the original machine. *)
Program Definition equivocator_state_extend
  (bs : equivocator_state)
  (s : state X)
  : equivocator_state
  :=
  existT (S (equivocator_state_last bs))
    (fun j => if decide (S (equivocator_state_last bs) = j)
              then s else equivocator_state_s bs (@of_nat_lt j (S (equivocator_state_last bs)) _)).
Next Obligation.
Proof.
  by intros; specialize (fin_to_nat_lt j);  lia.
Qed.

Lemma equivocator_state_extend_size bs s
  : equivocator_state_n (equivocator_state_extend bs s) = S (equivocator_state_n bs).
Proof. done. Qed.

Lemma equivocator_state_extend_lst bs s
  : equivocator_state_last (equivocator_state_extend bs s) = equivocator_state_n bs.
Proof. done. Qed.

Lemma equivocator_state_extend_project_1 es s i (Hi : i < equivocator_state_n es)
  : equivocator_state_project (equivocator_state_extend es s) i = equivocator_state_project es i.
Proof.
  rewrite (equivocator_state_project_Some _ _ Hi).
  specialize (equivocator_state_extend_size es s) as Hsize.
  assert (Hi' : i < equivocator_state_n (equivocator_state_extend es s))
    by lia.
  rewrite (equivocator_state_project_Some _ _ Hi').
  f_equal.
  cbn.
  specialize (equivocator_state_last_n es) as Hes_size.
  destruct (decide _).
  - by rewrite fin_to_nat_to_fin in e; lia.
  - apply equivocator_state_eq.
    by rewrite !fin_to_nat_to_fin.
Qed.

Lemma equivocator_state_extend_project_2 es s i (Hi : i = equivocator_state_n es)
  : equivocator_state_project (equivocator_state_extend es s) i = Some s.
Proof.
  specialize (equivocator_state_extend_size es s) as Hsize.
  assert (Hi' : i < equivocator_state_n (equivocator_state_extend es s))
    by lia.
  rewrite (equivocator_state_project_Some _ _ Hi').
  f_equal.
  cbn.
  destruct (decide _); [done |].
  elim n.
  rewrite fin_to_nat_to_fin.
  by specialize (equivocator_state_last_n es) as Hes_size; lia.
Qed.

Lemma equivocator_state_extend_project_3 es s i (Hi : equivocator_state_n es < i)
  : equivocator_state_project (equivocator_state_extend es s) i = None.
Proof.
  remember (equivocator_state_extend _ _) as ex.
  specialize (equivocator_state_extend_size es s) as Hsize.
  by destruct_equivocator_state_project ex i si Hi''; subst; [lia |].
Qed.

#[local] Ltac destruct_equivocator_state_extend_project' es s i Hi Hpr :=
  let Hni := fresh "Hni" in
  let Hni' := fresh "Hni" in
  destruct (decide (i < equivocator_state_n es)) as [Hi | Hni]
  ; [| destruct (decide (i = equivocator_state_n es)) as [Hi | Hni']]
  ; [| | assert (Hi : equivocator_state_n es < i) by lia]
  ; [specialize (equivocator_state_extend_project_1 es s i Hi) as Hpr
    | specialize (equivocator_state_extend_project_2 es s i Hi) as Hpr
    | specialize (equivocator_state_extend_project_3 es s i Hi) as Hpr]
  ; rewrite Hpr in *.

#[local] Ltac destruct_equivocator_state_extend_project es s i Hi :=
  let Hpr := fresh "Hpr" in
  destruct_equivocator_state_extend_project' es s i Hi Hpr
  ; clear Hpr.

Program Definition equivocator_state_append
  (es1 es2 : equivocator_state)
  : equivocator_state
  :=
  existT (equivocator_state_n es1 + equivocator_state_last es2)
    (fun j =>
      let (nj, Hnj) := to_nat j in
      match decide (nj < equivocator_state_n es1) with
      | left lt_in => equivocator_state_s es1 (of_nat_lt lt_in)
      | right ge_in =>
        let (k, Hk) := not_lt_plus_dec ge_in in
        equivocator_state_s es2 (@of_nat_lt k (equivocator_state_n es2) _)
      end).
Next Obligation.
Proof.
  by intros; specialize (equivocator_state_last_n es2) as Hlst_es2; lia.
Qed.

Lemma equivocator_state_append_size es1 es2
  : equivocator_state_n (equivocator_state_append es1 es2) =
    equivocator_state_n es1 + equivocator_state_n es2.
Proof.
  by destruct es1, es2; unfold equivocator_state_n; cbn; lia.
Qed.

Lemma equivocator_state_append_lst es1 es2
  : equivocator_state_last (equivocator_state_append es1 es2) =
    equivocator_state_last es2 + equivocator_state_n es1.
Proof.
  by destruct es1, es2; unfold equivocator_state_n; cbn; lia.
Qed.

Lemma equivocator_state_append_project_1 s s' i (Hi : i < equivocator_state_n s)
  : equivocator_state_project (equivocator_state_append s s') i = equivocator_state_project s i.
Proof.
  specialize (equivocator_state_projection_irrel s) as Hpi.
  rewrite (equivocator_state_project_Some _ _ Hi).
  specialize (equivocator_state_append_size s s') as Hsize.
  assert (Hi' : i < equivocator_state_n (equivocator_state_append s s')) by lia.
  rewrite (equivocator_state_project_Some _ _ Hi').
  f_equal.
  destruct s as (n1, bs1).
  destruct s' as (n2, bs2).
  unfold equivocator_state_n in *.
  simpl in *.
  rewrite to_nat_of_nat.
  unfold equivocator_state_n. simpl.
  by case_decide; [apply Hpi | lia].
Qed.

Lemma equivocator_state_append_project_2 s s' i k (Hi : i = k + equivocator_state_n s)
  : equivocator_state_project (equivocator_state_append s s') i = equivocator_state_project s' k.
Proof.
  specialize (equivocator_state_projection_irrel s') as Hpi.
  specialize (equivocator_state_append_size s s') as Hsize.
  remember (equivocator_state_append s s') as append.
  destruct_equivocator_state_project' s' k s'k Hk Hprs'
  ; destruct_equivocator_state_project' append i appendi Hi' Hprapp
  ; [| lia | lia | done].
  f_equal.
  rewrite (equivocator_state_project_Some _ _ Hi') in Hprapp.
  inversion_clear Hprapp.
  rewrite (equivocator_state_project_Some _ _ Hk) in Hprs'.
  inversion_clear Hprs'.
  subst.
  destruct s, s'. simpl in *. unfold equivocator_state_n in *. simpl in *.
  rewrite to_nat_of_nat.
  by case_decide; [| apply Hpi]; lia.
Qed.

Lemma equivocator_state_append_project_3
  s s' i (Hi : ~ i < equivocator_state_n s + equivocator_state_n s')
  : equivocator_state_project (equivocator_state_append s s') i = None.
Proof.
  apply equivocator_state_project_None.
  unfold equivocator_state_n, equivocator_state_append, equivocator_state_last in *.
  by cbn in *; lia.
Qed.

#[local] Ltac destruct_equivocator_state_append_project' es es' i Hi k Hk Hpr :=
  let Hi' := fresh "Hi" in
  destruct (decide (i < equivocator_state_n es)) as [Hi | Hi']; swap 1 2;
  [destruct (decide (i < equivocator_state_n es + equivocator_state_n es')) as [Hi | Hi];
    swap 1 2;
    [specialize (equivocator_state_append_project_3 es es' i Hi) as Hpr
    | apply not_lt_plus_dec in Hi' as [k Hk];
      specialize (equivocator_state_append_project_2 es es' i k (eq_sym Hk)) as Hpr]
  | specialize (equivocator_state_append_project_1 es es' i Hi) as Hpr]
  ; rewrite Hpr in *
  .

#[local] Ltac destruct_equivocator_state_append_project es es' i Hi k Hk :=
  let Hpr := fresh "Hpr" in
  destruct_equivocator_state_append_project' es es' i Hi k Hk Hpr
  ; clear Hpr.

Lemma equivocator_state_append_singleton_is_extend
  (es1 es2 : equivocator_state)
  (Hsingleton : is_singleton_state es2)
  : equivocator_state_append es1 es2 = equivocator_state_extend es1 (equivocator_state_zero es2).
Proof.
  apply equivocator_state_project_ext.
  intro i.
  symmetry.
  unfold is_singleton_state in Hsingleton.
  destruct_equivocator_state_append_project es1 es2 i Hi k Hk.
  - by apply equivocator_state_extend_project_3; lia.
  - rewrite equivocator_state_extend_project_2 by lia.
    rewrite <- equivocator_state_project_zero.
    by f_equal; lia.
  - by rewrite equivocator_state_extend_project_1 by lia.
Qed.

Lemma equivocator_state_append_extend_commute
  (es1 es2 : equivocator_state)
  (s : state X)
  : equivocator_state_extend (equivocator_state_append es1 es2) s =
    equivocator_state_append es1 (equivocator_state_extend es2 s).
Proof.
  apply equivocator_state_project_ext.
  intro i.
  destruct_equivocator_state_append_project es1 (equivocator_state_extend es2 s) i Hi k Hk.
  - rewrite equivocator_state_extend_size in Hi.
    apply equivocator_state_extend_project_3.
    by rewrite equivocator_state_append_size; lia.
  - subst; rewrite equivocator_state_extend_size in Hi.
    destruct (decide (k = equivocator_state_n es2)).
    + subst.
      rewrite !equivocator_state_extend_project_2
      ; [done | done |].
      by rewrite equivocator_state_append_size; lia.
    + rewrite !equivocator_state_extend_project_1
      ; [rewrite equivocator_state_append_project_2 with (k := k) | lia |]
      ; [done | done |].
      by rewrite equivocator_state_append_size; lia.
  - rewrite equivocator_state_extend_project_1.
    + by rewrite equivocator_state_append_project_1.
    + by rewrite equivocator_state_append_size; lia.
Qed.

Lemma equivocator_state_append_update_commute es1 es2 s n
  : equivocator_state_update (equivocator_state_append es1 es2) (n + equivocator_state_n es1) s =
    equivocator_state_append es1 (equivocator_state_update es2 n s).
Proof.
  apply equivocator_state_project_ext.
  intro i.
  destruct_equivocator_state_append_project es1 (equivocator_state_update es2 n s) i Hi k Hk.
  - apply equivocator_state_project_None.
    by rewrite equivocator_state_update_size, equivocator_state_append_size in *; lia.
  - destruct (decide (n = k)).
    + subst; rewrite equivocator_state_update_size in Hi.
      rewrite equivocator_state_update_project_eq;
      [| rewrite equivocator_state_append_size; lia | done].
      by rewrite equivocator_state_update_project_eq; [| lia |].
    + rewrite !equivocator_state_update_project_neq by lia.
      by apply equivocator_state_append_project_2 with (k := k).
  - by rewrite equivocator_state_update_project_neq,
      equivocator_state_append_project_1 by lia.
Qed.

(*
  An [equivocator_state] has the [initial_state_prop]erty if it only
  contains one state of original machine, and that state is initial.
*)
Definition equivocator_initial_state_prop
  (bs : equivocator_state)
  : Prop
  := is_singleton_state bs /\ initial_state_prop X (equivocator_state_zero bs).

Definition equivocator_initial_state : Type :=
  {bs : equivocator_state | equivocator_initial_state_prop bs}.

Program Definition equivocator_s0 : equivocator_initial_state :=
  exist _ (mk_singleton_state (proj1_sig (vs0 X))) _.
Next Obligation.
Proof.
  unfold mk_singleton_state, equivocator_initial_state_prop; cbn.
  by split; [| destruct (vs0 X)].
Defined.

#[export] Instance equivocator_initial_state_inh : Inhabited equivocator_initial_state :=
  populate equivocator_s0.

Definition equivocator_transition
  (bl : equivocator_label)
  (bsom : equivocator_state * option message)
  : equivocator_state * option message
  :=
  match bl with
  | Spawn sn  => (* creating a new machine with initial state sn*)
    (equivocator_state_extend bsom.1 sn, None)
  | ContinueWith i l =>
    match equivocator_state_project bsom.1 i with
    | None => bsom
    | Some si =>
      let (si', om') := transition X l (si, bsom.2) in
      (equivocator_state_update bsom.1 i si', om')
    end
  | ForkWith i l =>
    match equivocator_state_project bsom.1 i with
    | None => bsom
    | Some si =>
      let (si', om') := transition X l (si, bsom.2) in
      (equivocator_state_extend bsom.1 si', om')
    end
  end.

Definition equivocator_valid
  (bl : equivocator_label)
  (bsom : equivocator_state * option message)
  : Prop
  :=
  match bl with
  | Spawn sn  => (* state is initial *)
    initial_state_prop X sn /\ bsom.2 = None
  | ContinueWith i l | ForkWith i l =>
    match equivocator_state_project bsom.1 i with
    | Some si => valid X l (si, bsom.2)
    | None => False
    end
  end.

Definition equivocator_vlsm_machine
  : VLSMMachine equivocator_type
  :=
  {|  initial_state_prop := equivocator_initial_state_prop
   ;  initial_message_prop := @initial_message_prop _ _ X
   ;  transition := equivocator_transition
   ;  valid := equivocator_valid
  |}.

Definition equivocator_vlsm
  : VLSM message
  :=
  mk_vlsm equivocator_vlsm_machine.

Lemma equivocator_vlsm_initial_message_preservation
  : strong_embedding_initial_message_preservation X equivocator_vlsm.
Proof. by intro. Qed.

Lemma equivocator_vlsm_initial_message_preservation_rev
  : strong_embedding_initial_message_preservation equivocator_vlsm X.
Proof. by intro. Qed.

Lemma equivocator_vlsm_initial_state_preservation_rev is i s
  (Hs : equivocator_state_project is i = Some s)
  : initial_state_prop equivocator_vlsm is -> initial_state_prop X s.
Proof.
  intros [Hzero Hinit].
  apply equivocator_state_project_Some_rev in Hs as Hlt_i.
  replace i with 0 in * by (cbv in *; lia).
  by rewrite equivocator_state_project_zero in Hs; inversion Hs.
Qed.

Lemma mk_singleton_initial_state
  (s : state X)
  : initial_state_prop X s ->
    initial_state_prop equivocator_vlsm (mk_singleton_state s).
Proof. done. Qed.

End sec_equivocator_vlsm.

#[export] Hint Rewrite @equivocator_state_update_size : equivocator_state_update.
#[export] Hint Rewrite @equivocator_state_update_lst : equivocator_state_update.
#[export] Hint Rewrite @equivocator_state_update_project_eq using first [done | lia]
  : equivocator_state_update.
#[export] Hint Rewrite @equivocator_state_update_project_neq using first [done | lia]
  : equivocator_state_update.

#[export] Hint Rewrite @equivocator_state_extend_size using done : equivocator_state_update.
#[export] Hint Rewrite @equivocator_state_extend_lst using done : equivocator_state_update.
#[export] Hint Rewrite @equivocator_state_extend_project_1 using first [done | lia]
  : equivocator_state_update.
#[export] Hint Rewrite @equivocator_state_extend_project_2 using first [done | lia]
  : equivocator_state_update.
#[export] Hint Rewrite @equivocator_state_extend_project_3 using first [done | lia]
  : equivocator_state_update.

#[export] Hint Rewrite @equivocator_state_append_size using done : equivocator_state_update.
#[export] Hint Rewrite @equivocator_state_append_lst using done : equivocator_state_update.
#[export] Hint Rewrite @equivocator_state_append_project_1 using first [done | lia]
  : equivocator_state_update.
#[export] Hint Rewrite @equivocator_state_append_project_2 using first [done | lia]
  : equivocator_state_update.
#[export] Hint Rewrite @equivocator_state_append_project_3 using first [done | lia]
  : equivocator_state_update.

Ltac equivocator_state_update_simpl :=
  autounfold with state_update in *;
  autorewrite with equivocator_state_update state_update in *.

Arguments Spawn {_ _} _ : assert.
Arguments ContinueWith {_ _} _ _ : assert.
Arguments ForkWith {_ _} _ _ : assert.
Arguments equivocator_state_n {_ _} _ : assert.
Arguments equivocator_state_last {_ _} _ : assert.
Arguments equivocator_state_zero {_ _} _ : assert.
Arguments equivocator_state_s {_ _} _ _ : assert.
Arguments equivocator_state_project {_ _} _ _ : assert.
Arguments equivocator_state_update {_ _} _ _ _ : assert.
Arguments equivocator_state_extend {_ _} _ _ : assert.
Arguments equivocator_state_append {_ _} _ _ : assert.

Ltac destruct_equivocator_state_project' es i si Hi Hpr :=
  destruct (equivocator_state_project es i) as [si |] eqn: Hpr
  ; [specialize (equivocator_state_project_Some_rev _ _ _ _ Hpr) as Hi
    | specialize (equivocator_state_project_None_rev _ _ _ Hpr) as Hi].

Ltac destruct_equivocator_state_project es i si Hi :=
  let Hpr := fresh "Hpr" in
  destruct_equivocator_state_project' es i si Hi Hpr
  ; clear Hpr.

Ltac destruct_equivocator_state_update_project' es i s j Hj Hij Hpr :=
  let Hsize := fresh "Hsize" in
  pose proof (equivocator_state_update_size _ es i s) as Hsize
  ; destruct (decide (j < equivocator_state_n es)) as [Hj | Hj]; swap 1 2
  ; [specialize (equivocator_state_project_None _ (equivocator_state_update es i s) j Hj) as Hpr
    | destruct (decide (i = j)) as [Hij | Hij]
    ; [specialize (equivocator_state_update_project_eq _ es i s j Hj Hij) as Hpr
      | specialize (equivocator_state_update_project_neq _ es i s j Hij) as Hpr]]
  ; rewrite Hpr in *
  ; clear Hsize.

Ltac destruct_equivocator_state_update_project es i s j Hj Hij :=
  let Hpr := fresh "Hpr" in
  destruct_equivocator_state_update_project' es i s j Hj Hij Hpr
  ; clear Hpr.

Ltac destruct_equivocator_state_extend_project' es s i Hi Hpr :=
  let Hni := fresh "Hni" in
  let Hni' := fresh "Hni" in
  destruct (decide (i < equivocator_state_n es)) as [Hi | Hni]
  ; [| destruct (decide (i = equivocator_state_n es)) as [Hi | Hni']]
  ; [| | assert (Hi : equivocator_state_n es < i) by lia]
  ; [specialize (equivocator_state_extend_project_1 _ es s i Hi) as Hpr
    | specialize (equivocator_state_extend_project_2 _ es s i Hi) as Hpr
    | specialize (equivocator_state_extend_project_3 _ es s i Hi) as Hpr]
  ; rewrite Hpr in *.

Ltac destruct_equivocator_state_extend_project es s i Hi :=
  let Hpr := fresh "Hpr" in
  destruct_equivocator_state_extend_project' es s i Hi Hpr
  ; clear Hpr.

Section sec_equivocator_vlsm_valid_state_projections.

Context
  {message : Type}
  (X : VLSM message)
  (equivocator_vlsm := equivocator_vlsm X)
  .

(**
  When projecting an equivocator trace on one copy, we start from its final
  state and trace back transitions, making sure to follow [ForkWith] transitions
  back to their original copy and to stop on [Spawn] transitions.

  To do that we need to track the current copy, or whether we already reached
  the initial state.

  - [NewMachine] <<s>> indicates that a [Spawn] <<s>> was already reached for the
    copy being tracked
  - [Existing] <<i>> indicates that we're currently tracking copy <<i>>
*)
Inductive MachineDescriptor : Type :=
| NewMachine : state X -> MachineDescriptor
| Existing : nat -> MachineDescriptor.

(**
  The [MachineDescriptor] associated to an [equivocator_label] tells us
  which copy should we continue with if the current transition is relevant
  for the copy we're tracking.
*)
Definition equivocator_label_descriptor (l : equivocator_label X) : MachineDescriptor :=
  match l with
  | Spawn sn => NewMachine sn
  | ContinueWith i _ | ForkWith i _ => Existing i
  end.

Definition is_newmachine_descriptor (d : MachineDescriptor) : Prop
  := match d with
    | NewMachine _ => True
    | _ => False
  end.

Lemma newmachine_descriptor_dec (d : MachineDescriptor)
  : Decision (is_newmachine_descriptor d).
Proof.
  destruct d.
  - by left.
  - by right; itauto.
Qed.

(** Projecting an [equivocator_state] over a [MachineDescriptor]. *)
Definition equivocator_state_descriptor_project
  (s : equivocator_state X)
  (descriptor : MachineDescriptor)
  : state X
  :=
  match descriptor with
  | NewMachine sn => sn
  | Existing j => default (equivocator_state_zero s) (equivocator_state_project s j)
  end.

(**
  Whether a [MachineDescriptor] can be used to project an
  [equivocator_state] to a regular [state].
  The [NewMachine] descriptor signals that an equivocation has occurred
  starting a new machine, thus we require the argument to be initial.
  For an [Existing] descriptor, the index of the descriptor must
  refer to an existing machine in the current state.
*)
Definition proper_descriptor
  (d : MachineDescriptor)
  (s : state equivocator_vlsm)
  :=
  match d with
  | NewMachine sn => initial_state_prop X sn
  | Existing i => is_Some (equivocator_state_project s i)
  end.

Definition proper_equivocator_label
  (l : equivocator_label X)
  (s : equivocator_state X)
  := proper_descriptor (equivocator_label_descriptor l) s.

(** Existing-only descriptor. *)
Definition existing_descriptor
  (d : MachineDescriptor)
  (s : state equivocator_vlsm)
  :=
  match d with
  | Existing i => is_Some (equivocator_state_project s i)
  | _ => False
  end.

#[local] Instance  existing_descriptor_dec : RelDecision existing_descriptor.
Proof.
  intros d s. destruct d; simpl.
  - by right; itauto.
  - destruct_equivocator_state_project s n _sn Hn.
    + by left.
    + by right; intros [si Hi]; congruence.
Qed.

Definition existing_equivocator_label
  (l : equivocator_label X)
  := match l with Spawn _ => False | _ => True end.

Definition existing_equivocator_label_extract
  (l : equivocator_label X)
  (Hs : existing_equivocator_label l)
  : label X.
Proof.
  by destruct l.
Defined.

Definition proper_existing_equivocator_label
  (l : equivocator_label X)
  (s : equivocator_state X)
  := existing_descriptor (equivocator_label_descriptor l) s.

Lemma existing_equivocator_label_forget_proper
  {l : equivocator_label X}
  {s : equivocator_state X}
  (Hs : proper_existing_equivocator_label l s)
  : existing_equivocator_label l.
Proof.
  by destruct l; [inversion Hs | ..].
Qed.

Lemma existing_descriptor_proper
  (d : MachineDescriptor)
  (s : state equivocator_vlsm)
  (Hned : existing_descriptor d s)
  : proper_descriptor d s.
Proof. by destruct d. Qed.

(*
  TODO: derive some some simpler lemmas about the equivocator operations,
  or a simpler way of defining the equivocator_transition - it's not nice
  to need to pick apart these cases from inside equivocator_transition inside
  of so many proofs.
*)

(**
  If the state obtained after one transition has no equivocation, then
  the descriptor of the label of the transition must be Existing 0 false
*)
Lemma equivocator_transition_no_equivocation_zero_descriptor
  (iom oom : option message)
  (l : label equivocator_vlsm)
  (s s' : state equivocator_vlsm)
  (Hv : valid equivocator_vlsm l (s, iom))
  (Ht : transition equivocator_vlsm l (s, iom) = (s', oom))
  (Hs' : is_singleton_state X s')
  : exists li, l = ContinueWith 0 li.
Proof.
  unfold is_singleton_state in Hs'.
  destruct l as [sn | ei l | ei l]
  ; [inversion Ht; subst; rewrite equivocator_state_extend_size in Hs'; cbv in Hs'; lia | ..]
  ; cbn in Hv, Ht;  destruct_equivocator_state_project s ei sei Hei; [| done | | done]
  ; destruct (transition _ _ _) as (si', om')
  ; inversion Ht; subst; equivocator_state_update_simpl.
  - by exists l; f_equal; lia.
  - by lia.
Qed.

(**
  If the state obtained after one transition has no equivocation, then
  the state prior to the transition has no equivocation as well.
*)
Lemma equivocator_transition_reflects_singleton_state
  (iom oom : option message)
  (l : label equivocator_vlsm)
  (s s' : state equivocator_vlsm)
  (Ht : equivocator_transition X l (s, iom) = (s', oom))
  : is_singleton_state X s' -> is_singleton_state X s.
Proof.
  unfold is_singleton_state.
  by destruct l as [sn | ei l | ei l]; cbn in Ht
  ; [inversion Ht; rewrite equivocator_state_extend_size; cbv; lia | ..]
  ; destruct (equivocator_state_project _ _)
  ; [| by inversion Ht | | by inversion Ht]
  ; destruct (transition _ _ _) as (si', om')
  ; inversion Ht; subst; clear Ht; equivocator_state_update_simpl.
Qed.

Lemma equivocator_transition_cannot_decrease_state_size
  (iom oom : option message)
  (l : label equivocator_vlsm)
  (s s' : state equivocator_vlsm)
  (Ht : equivocator_transition X l (s, iom) = (s', oom))
  : equivocator_state_n s <= equivocator_state_n s'.
Proof.
  specialize (equivocator_state_extend_size X s) as Hex_size.
  destruct l as [sn | ei l | ei l]
  ; [inversion Ht; rewrite Hex_size; lia | ..]
  ; cbn in Ht
  ; destruct (equivocator_state_project _ _)
  ; [| by inversion Ht; lia | | by inversion Ht; lia]
  ; destruct (transition _ _ _) as (si', om')
  ; inversion Ht; subst; clear Ht.
  - by equivocator_state_update_simpl.
  - by rewrite Hex_size; lia.
Qed.

Lemma equivocator_transition_preserves_equivocating_state
  (iom oom : option message)
  (l : label equivocator_vlsm)
  (s s' : state equivocator_vlsm)
  (Ht : equivocator_transition X l (s, iom) = (s', oom))
  : is_equivocating_state X s -> is_equivocating_state X s'.
Proof.
  intros Hs Hs'. elim Hs. clear Hs. revert Ht Hs' .
  by apply equivocator_transition_reflects_singleton_state.
Qed.

Lemma zero_descriptor_transition_reflects_equivocating_state
  (iom oom : option message)
  (l : label equivocator_vlsm)
  (s s' : state equivocator_vlsm)
  (Ht : equivocator_transition X l (s, iom) = (s', oom))
  li
  (Hzero : l = ContinueWith 0 li)
  : is_equivocating_state X s' -> is_equivocating_state X s.
Proof.
  subst.
  cbn in Ht.
  rewrite equivocator_state_project_zero in Ht.
  destruct (transition _ _ _).
  inversion Ht. subst.
  unfold is_equivocating_state, is_singleton_state.
  by equivocator_state_update_simpl.
Qed.

(**
  Valid messages in the [equivocator_vlsm] are also valid in the
  original machine.  All components of a valid state in the
  [equivocator_vlsm] are also valid in the original machine.
*)
Lemma preloaded_equivocator_state_projection_preserves_validity
  (seed : message -> Prop)
  (bs : state equivocator_vlsm)
  (om : option message)
  (Hbs : valid_state_message_prop (pre_loaded_vlsm equivocator_vlsm seed) bs om)
  : option_valid_message_prop (pre_loaded_vlsm X seed) om /\
    forall i si,
      equivocator_state_project bs i = Some si ->
      valid_state_prop (pre_loaded_vlsm X seed) si.
Proof.
  induction Hbs.
  - split; [by apply option_initial_message_is_valid |].
    intros.
    destruct Hs as [Hn0 Hinit].
    apply equivocator_state_project_Some_rev in H as Hi.
    unfold is_singleton_state in Hn0.
    replace i with 0 in * by lia.
    rewrite equivocator_state_project_zero in H; inversion H.
    by apply initial_state_is_valid.
  - specialize (valid_generated_state_message (pre_loaded_vlsm X seed)) as Hgen.
    apply proj2 in IHHbs1. apply proj1 in IHHbs2.

    (*
      destruction tactic for a valid equivocator transition
      transition equivocator_vlsm l (s, om) = (s', om')
    *)
    destruct l as [sn | i l | i l]
    ; [inversion_clear Ht; split; [by apply option_valid_message_None |]
      ; intros
      ; destruct_equivocator_state_extend_project s sn i Hi
      ; [by apply IHHbs1 in H
      | inversion H; subst; apply initial_state_is_valid; apply Hv
      | done]
      | ..]
    ; cbn in Hv, Ht
    ; destruct_equivocator_state_project' s i si Hi Hpr; [| done | | done]
    ; destruct (transition _ _ _) as (si', _om') eqn: Hti
    ; inversion Ht; subst s' _om'; clear Ht

    (* I wish I could solve this goal, then apply the composed tactic for the remaining two goals. *)
    (* common tactic for the last two goals. *)
    ; apply IHHbs1 in Hpr as [_omi Hsi]
      ; destruct IHHbs2 as [_som Hom]
      ; specialize (Hgen _ _ Hsi _ _ Hom _ Hv _ _ Hti)
      ; split; [by eexists | | by eexists |]; intros.
    + destruct_equivocator_state_update_project s i si' i0 Hi0 Hij.
      * done.
      * by inversion H; subst; eexists.
      * by apply IHHbs1 in H.
    + destruct_equivocator_state_extend_project s si' i0 Hi0.
      * by apply IHHbs1 in H.
      * by inversion H; subst; eexists.
      * done.
Qed.

Lemma preloaded_with_equivocator_state_project_valid_state
  (seed : message -> Prop)
  (bs : state equivocator_vlsm)
  (Hbs : valid_state_prop (pre_loaded_vlsm equivocator_vlsm seed) bs)
  : forall i si,
    equivocator_state_project bs i = Some si ->
    valid_state_prop (pre_loaded_vlsm X seed) si.
Proof.
  destruct Hbs as [om  Hbs].
  by apply preloaded_equivocator_state_projection_preserves_validity, proj2 in Hbs.
Qed.

Lemma preloaded_with_equivocator_state_project_valid_message
  (seed : message -> Prop)
  (om : option message)
  (Hom : option_valid_message_prop (pre_loaded_vlsm equivocator_vlsm seed) om)
  :
  option_valid_message_prop (pre_loaded_vlsm X seed) om.
Proof.
  destruct Hom as [s Hm].
  by apply preloaded_equivocator_state_projection_preserves_validity, proj1 in Hm.
Qed.

Lemma equivocator_state_project_valid_state
  (bs : state equivocator_vlsm)
  (Hbs : valid_state_prop equivocator_vlsm bs)
  : forall i si,
    equivocator_state_project bs i = Some si -> valid_state_prop X si.
Proof.
  intros i si Hpr.
  apply (VLSM_eq_valid_state (vlsm_is_pre_loaded_with_False equivocator_vlsm)) in Hbs.
  specialize (preloaded_with_equivocator_state_project_valid_state _ _ Hbs _ _ Hpr) as Hsi.
  apply (VLSM_eq_valid_state (vlsm_is_pre_loaded_with_False X)) in Hsi.
  by destruct X.
Qed.

Lemma equivocator_state_project_valid_message
  (om : option message)
  (Hom : option_valid_message_prop equivocator_vlsm om)
  :
  option_valid_message_prop X om.
Proof.
  destruct om as [m |]; [| by apply option_valid_message_None].
  specialize (vlsm_is_pre_loaded_with_False_initial_message equivocator_vlsm) as Hinit.
  apply (VLSM_incl_valid_message (proj1 (vlsm_is_pre_loaded_with_False equivocator_vlsm)))
    in Hom; [| done].
  apply preloaded_with_equivocator_state_project_valid_message in Hom.
  specialize (vlsm_is_pre_loaded_with_False_initial_message_rev X) as Hinit_rev.
  by apply (VLSM_incl_valid_message (proj2 (vlsm_is_pre_loaded_with_False X))) in Hom
  ; destruct X.
Qed.

(**
  All components of valid states of the [pre_loaded_with_all_messages_vlsm] corresponding
  to an [equivocator_vlsm] are also valid for the [pre_loaded_with_all_messages_vlsm]
  corresponding to the original machine.
*)
Lemma preloaded_equivocator_state_project_valid_state
  (bs : state equivocator_vlsm)
  (Hbs : valid_state_prop (pre_loaded_with_all_messages_vlsm equivocator_vlsm) bs)
  : forall i si,
    equivocator_state_project bs i = Some si ->
      valid_state_prop (pre_loaded_with_all_messages_vlsm X) si.
Proof.
  intros i si Hpr.
  by apply (preloaded_with_equivocator_state_project_valid_state _ _ Hbs _ _ Hpr).
Qed.

(**
  Next couple of lemmas characterize the projections of a [equivocator_state]
  after taking a transition in terms of the preceding state.

  These are simpler version of the results concerning the projection of
  states from the composition of equivocators over [equivocation_descriptors].

  These results are used for characterizing the projection of the [destination]
  of a [transition_item] in an equivocator trace in
  [equivocator_transition_item_project_proper_characterization].
*)

Lemma new_machine_label_equivocator_transition_size
  {sn s oin s' oout}
  (Ht : transition equivocator_vlsm (Spawn sn) (s, oin) = (s', oout))
  : equivocator_state_n s' = S (equivocator_state_n s).
Proof.
  inversion_clear Ht.
  by apply equivocator_state_extend_size.
Qed.

Lemma existing_true_label_equivocator_transition_size
  {ieqvi li s oin s' oout}
  (Ht : transition equivocator_vlsm (ForkWith ieqvi li) (s, oin) = (s', oout))
  si
  (Hv : equivocator_state_project s ieqvi = Some si)
  : equivocator_state_n s' = S (equivocator_state_n s).
Proof.
  cbn in Ht.
  rewrite Hv in Ht.
  destruct (transition _ _ _).
  inversion Ht. subst.
  by apply equivocator_state_extend_size.
Qed.

Lemma existing_false_label_equivocator_transition_size
  {ieqvi li s oin s' oout}
  (Ht : transition equivocator_vlsm (ContinueWith ieqvi li) (s, oin) = (s', oout))
  si
  (Hv : equivocator_state_project s ieqvi = Some si)
  : equivocator_state_n s' = equivocator_state_n s.
Proof.
  cbn in Ht.
  rewrite Hv in Ht.
  destruct (transition _ _ _).
  inversion Ht. subst.
  by equivocator_state_update_simpl.
Qed.

Lemma new_machine_label_equivocator_state_project_last
  {sn s oin s' oout}
  (Ht : transition equivocator_vlsm (Spawn sn) (s, oin) = (s', oout))
  : equivocator_state_descriptor_project s' (Existing (equivocator_state_n s)) =
    equivocator_state_descriptor_project s (NewMachine sn).
Proof.
  inversion_clear Ht. simpl.
  by destruct_equivocator_state_extend_project s sn (equivocator_state_n s) Hi;
    [lia | | lia].
Qed.

Lemma new_machine_label_equivocator_state_project_not_last
  {sn s oin s' oout}
  (Ht : transition equivocator_vlsm (Spawn sn) (s, oin) = (s', oout))
  ni
  (Hni : ni < equivocator_state_n s)
  : equivocator_state_descriptor_project s' (Existing ni) =
    equivocator_state_descriptor_project s (Existing ni).
Proof.
  subst. inversion_clear Ht. simpl.
  by destruct_equivocator_state_extend_project s sn ni Hi; [| lia..].
Qed.

Lemma existing_true_label_equivocator_state_project_not_last
  {ieqvi li s oin s' oout}
  (Ht : transition equivocator_vlsm (ForkWith ieqvi li) (s, oin) = (s', oout))
  si
  (Hsi : equivocator_state_project s ieqvi = Some si)
  ni
  (Hni : ni < equivocator_state_n s)
  : equivocator_state_descriptor_project s' (Existing ni)
  = equivocator_state_descriptor_project s (Existing ni).
Proof.
  cbn in Ht.
  rewrite Hsi in Ht.
  destruct (transition _ _ _) as (si', _om') eqn: Hti.
  inversion Ht; subst s' _om'. clear Ht.
  simpl.
  by destruct_equivocator_state_extend_project s si' ni Hni'; [| lia..].
Qed.

Lemma existing_true_label_equivocator_state_project_last
  {ieqvi li s oin s' oout}
  (Ht : transition equivocator_vlsm (ForkWith ieqvi li) (s, oin) = (s', oout))
  si
  (Hsi : equivocator_state_project s ieqvi = Some si)
  si' _oout
  (Hti : transition X li (si, oin) = (si', _oout))
  : _oout = oout /\
    equivocator_state_descriptor_project s' (Existing (equivocator_state_n s)) = si'.
Proof.
  cbn in Ht.
  rewrite Hsi in Ht.
  simpl in Hti. rewrite Hti in Ht.
  inversion Ht. subst. clear Ht.
  by cbn; rewrite equivocator_state_extend_project_2.
Qed.

Lemma existing_false_label_equivocator_state_project_not_same
  {ieqvi li s oin s' oout}
  (Ht : transition equivocator_vlsm (ContinueWith ieqvi li) (s, oin) = (s', oout))
  si
  (Hsi : equivocator_state_project s ieqvi = Some si)
  ni
  (Hni : ni < equivocator_state_n s)
  (Hnieqvi : ieqvi <> ni)
  : equivocator_state_descriptor_project s' (Existing ni)
  = equivocator_state_descriptor_project s (Existing ni).
Proof.
  cbn in Ht. rewrite Hsi in Ht.
  destruct (transition _ _ _) as (si', _om') eqn: Hti.
  inversion Ht; subst s' _om'. clear Ht.
  simpl.
  destruct_equivocator_state_update_project s ieqvi si' ni Hni' Hini; [lia.. |].
  by destruct_equivocator_state_project s ni sni Hni''; [| lia].
Qed.

Lemma existing_false_label_equivocator_state_project_same
  {ieqvi li s oin s' oout}
  (Ht : transition equivocator_vlsm (ContinueWith ieqvi li) (s, oin) = (s', oout))
  si
  (Hsi : equivocator_state_project s ieqvi = Some si)
  si' _oout
  (Hti : transition X li (si, oin) = (si', _oout))
  : _oout = oout /\
    equivocator_state_descriptor_project s' (Existing ieqvi) = si'.
Proof.
  cbn in Ht. rewrite Hsi in Ht.
  simpl in Hti. rewrite Hti in Ht.
  inversion Ht; subst s' _oout. clear Ht.
  split; [done |].
  simpl.
  rewrite equivocator_state_update_project_eq; [done | | done].
  by apply equivocator_state_project_Some_rev in Hsi.
Qed.

End sec_equivocator_vlsm_valid_state_projections.

Arguments NewMachine {_ _} _ : assert.
Arguments Existing {_ _} _ : assert.
Arguments equivocator_label_descriptor {_ _} _ : assert.
Arguments equivocator_state_descriptor_project {_ _} _ _ : assert.
