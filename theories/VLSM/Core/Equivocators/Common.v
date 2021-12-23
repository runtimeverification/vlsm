From stdpp Require Import prelude.
From Coq Require Import Eqdep Vectors.Fin Program.Equality Lia FunctionalExtensionality.
From VLSM Require Import Lib.Preamble Core.VLSM Core.VLSMProjections.

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

(** The state of such a machine will be abstracted using

1. A [nat]ural <<n>>, stating the number of copies of the original machine
2. A state of <<X>> for each 1..n+1
*)
Local Definition bounded_state_copies := {n : nat & Fin.t (S n) -> vstate X}.

(** To preserve determinism we need to enhance the labels to indicate what copy
of the machine will be used for a transition.
To achieve this, we'll define the following label variants:

- [Spawn] <<s>> to extend the state with a new machine initialized with <<s>>
- [ContinueWith] <<n>> <<l>>, to transition on copy <<n>> using label <<l>>
- [ForkWith] <<n>> <<l>>, to extend the state with a new machine initialized
  with the current state of machine <<n>> and to transition on that copy
  using label <<l>>.
*)
Inductive EquivocatorLabel : Type :=
  | Spawn : vstate X -> EquivocatorLabel
  | ContinueWith : nat -> vlabel X -> EquivocatorLabel
  | ForkWith : nat -> vlabel X -> EquivocatorLabel.

Definition equivocator_type : VLSMType message :=
  {| state := bounded_state_copies ;
     label := EquivocatorLabel
  |}.

Definition equivocator_state : Type := @state message equivocator_type.
Definition equivocator_label : Type := @label message equivocator_type.

(** the number of machine copies in the given state *)
Definition equivocator_state_n (es : equivocator_state) := S (projT1 es).
(** the index of the last machine copies in the given state *)
Definition equivocator_state_last (es : equivocator_state) := projT1 es.
Definition equivocator_state_s (es : equivocator_state) := projT2 es.

Lemma equivocator_state_last_n es : equivocator_state_n es = S (equivocator_state_last es).
Proof. reflexivity. Qed.

Definition mk_singleton_state
  (s : vstate X)
  : equivocator_state
  :=
  existT 0 (fun _ => s).

Local Lemma equivocator_state_projection_irrel (s : equivocator_state)
  i (li : i < (equivocator_state_n s))
  j (lj : j < (equivocator_state_n s))
  (Heq : i = j)
  : equivocator_state_s s (nat_to_fin li) = equivocator_state_s s (nat_to_fin lj).
Proof.
  subst i.
  replace (nat_to_fin li) with (nat_to_fin lj) by apply of_nat_ext.
  reflexivity.
Qed.

Local Lemma equivocator_state_eq s (i1 i2 : fin (equivocator_state_n s))
  : fin_to_nat i1 = fin_to_nat i2 -> equivocator_state_s s i1 = equivocator_state_s s i2.
Proof.
  intro Heq.
  replace i2 with i1; [reflexivity|].
  apply (inj fin_to_nat). assumption.
Qed.

Definition is_singleton_state
  (s : equivocator_state)
  : Prop
  := equivocator_state_n s = 1.

Lemma is_singleton_state_dec
  (s : equivocator_state)
  : Decision (is_singleton_state s).
Proof.
  apply nat_eq_dec.
Qed.

Definition is_equivocating_state
  (s : equivocator_state)
  : Prop
  := not (is_singleton_state s).

Lemma is_equivocating_state_dec
  (s : equivocator_state)
  : Decision (is_equivocating_state s).
Proof.
  apply Decision_not.
  apply is_singleton_state_dec.
Qed.

(**
Attempts to obtain the state of the internal machine with index <<i>>
from an [equivocator_state]. Fails when index <<i>> does not refer to a
machine.
*)
Definition equivocator_state_project
  (bs : equivocator_state)
  (i : nat)
  : option (vstate X)
  :=
  match (decide (i < equivocator_state_n bs)) with
  | left lt_in => Some (equivocator_state_s bs (of_nat_lt lt_in))
  | _ =>  None
  end.

Local Lemma equivocator_state_project_Some s i (Hi : i < equivocator_state_n s)
  : equivocator_state_project s i = Some (equivocator_state_s s (nat_to_fin Hi)).
Proof.
  unfold equivocator_state_project.
  case_decide; [|lia].
  f_equal. apply equivocator_state_eq.
  rewrite !fin_to_nat_to_fin.
  reflexivity.
Qed.

Local Lemma equivocator_state_project_None s i (Hi : ~i < equivocator_state_n s)
  : equivocator_state_project s i = None.
Proof.
  unfold equivocator_state_project.
  case_decide; [lia|].
  reflexivity.
Qed.

Lemma equivocator_state_project_Some_rev s i si
  : equivocator_state_project s i = Some si -> i < equivocator_state_n s.
Proof.
  unfold equivocator_state_project.
  case_decide; [|congruence].
  intro. assumption.
Qed.

Lemma equivocator_state_project_None_rev s i
  : equivocator_state_project s i = None -> ~i < equivocator_state_n s.
Proof.
  unfold equivocator_state_project.
  case_decide; [congruence|].
  intro. lia.
Qed.

Local Ltac destruct_equivocator_state_project' es i si Hi Hpr :=
  destruct (equivocator_state_project es i) as [si|] eqn:Hpr
  ; [ specialize (equivocator_state_project_Some_rev _ _ _ Hpr) as Hi
    | specialize (equivocator_state_project_None_rev _ _ Hpr) as Hi ].

Local Ltac destruct_equivocator_state_project es i si Hi :=
  let Hpr := fresh "Hpr" in
  destruct_equivocator_state_project' es i si Hi Hpr
  ; clear Hpr.

(** Extensionality result, reducing the proof of the equality of two
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
    destruct_equivocator_state_project es1 (equivocator_state_last es1) lst1 Hi1; [|lia].
    destruct_equivocator_state_project es2 (equivocator_state_last es2) lst2 Hi2; [|lia].
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
  destruct es1, es2; simpl in *. subst. simpl.
  rewrite (equivocator_state_project_Some (existT x1 v) x Hx) in Hext.
  inversion Hext.
  assumption.
Qed.

(** The original state index is present in any equivocator state*)
Lemma Hzero (s : equivocator_state) : 0 < equivocator_state_n s.
Proof. pose proof (equivocator_state_last_n s). lia. Qed.

Definition equivocator_state_zero (es : equivocator_state) : state :=
  equivocator_state_s es (nat_to_fin (Hzero es)).

Lemma equivocator_state_project_zero (es : equivocator_state)
  : equivocator_state_project es 0 = Some (equivocator_state_zero es).
Proof.
  unfold equivocator_state_project, equivocator_state_n.
  case_decide; [|lia].
  reflexivity.
Qed.

Definition equivocator_state_update
  (bs : equivocator_state)
  (i : nat)
  (si : vstate X)
  : equivocator_state
  :=
  @existT nat (fun n => Fin.t (S n) -> state)
    (equivocator_state_last bs)
	  (fun j => if  decide (i = j) then si else equivocator_state_s bs j).

(** Some basic properties for 'equivocator_state_update' *)

Lemma equivocator_state_update_size bs i si
  : equivocator_state_n (equivocator_state_update bs i si) = equivocator_state_n bs.
Proof.  reflexivity.  Qed.

Lemma equivocator_state_update_lst bs i si
  : equivocator_state_last (equivocator_state_update bs i si) = equivocator_state_last bs.
Proof. reflexivity. Qed.

Lemma equivocator_state_update_project_eq bs i si j
  (Hj : j < equivocator_state_n bs)
  (Hij : i = j)
  : equivocator_state_project (equivocator_state_update bs i si) j = Some si.
Proof.
  pose proof (equivocator_state_update_size bs i si) as Heq.
  destruct_equivocator_state_project' (equivocator_state_update bs i si) j sj Hi' Hpr ; [|lia].
  rewrite <- Hpr.
  rewrite (equivocator_state_project_Some _ _ Hi').
  f_equal.
  subst.
  clear.
  simpl. rewrite decide_True; [reflexivity|].
  rewrite fin_to_nat_to_fin. reflexivity.
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
    + apply equivocator_state_eq. rewrite !fin_to_nat_to_fin. reflexivity.
    + intro Hcontra.
      rewrite !fin_to_nat_to_fin in Hcontra. congruence.
  - rewrite Heq in Hj.
    rewrite (equivocator_state_project_None _ _ Hj).
    reflexivity.
Qed.

Local Ltac destruct_equivocator_state_update_project' es i s j Hj Hij Hpr :=
  let Hsize := fresh "Hsize" in
  pose proof (equivocator_state_update_size es i s) as Hsize
  ; destruct (decide (j < equivocator_state_n es)) as [Hj | Hj]
  ; [ destruct (decide (i = j)) as [Hij | Hij]
    ; [ specialize (equivocator_state_update_project_eq es i s j Hj Hij) as Hpr
      | specialize (equivocator_state_update_project_neq es i s j Hij) as Hpr
      ]
    | specialize (equivocator_state_project_None (equivocator_state_update es i s) j Hj) as Hpr]
  ; rewrite Hpr in *
  ; clear Hsize.

Local Ltac destruct_equivocator_state_update_project es i s j Hj Hij :=
  let Hpr := fresh "Hpr" in
  destruct_equivocator_state_update_project' es i s j Hj Hij Hpr
  ; clear Hpr.


(**
Extends an [equivocator_state] with a new state of the original machine.
*)
Program Definition equivocator_state_extend
  (bs : equivocator_state)
  (s : vstate X)
  : equivocator_state
  :=
  existT (S (equivocator_state_last bs))
    (fun j =>
      if decide (S (equivocator_state_last bs) = j) then s else equivocator_state_s bs (@of_nat_lt j (S (equivocator_state_last bs)) _)
    ).
Next Obligation.
  intros. specialize (fin_to_nat_lt j).  lia.
Qed.

Lemma equivocator_state_extend_size bs s
  : equivocator_state_n (equivocator_state_extend bs s) = S (equivocator_state_n bs).
Proof. reflexivity. Qed.

Lemma equivocator_state_extend_lst bs s
  : equivocator_state_last (equivocator_state_extend bs s) = equivocator_state_n bs.
Proof. reflexivity. Qed.

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
  - rewrite fin_to_nat_to_fin in e. lia.
  - apply equivocator_state_eq.
    rewrite !fin_to_nat_to_fin. reflexivity.
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
  destruct (decide _); [reflexivity|].
  elim n.
  rewrite fin_to_nat_to_fin.
  specialize (equivocator_state_last_n es) as Hes_size.
  lia.
Qed.

Lemma equivocator_state_extend_project_3 es s i (Hi : equivocator_state_n es < i)
  : equivocator_state_project (equivocator_state_extend es s) i = None.
Proof.
  remember (equivocator_state_extend _ _) as ex.
  specialize (equivocator_state_extend_size es s) as Hsize.
  destruct_equivocator_state_project ex i si Hi''; subst; [lia|].
  reflexivity.
Qed.

Local Ltac destruct_equivocator_state_extend_project' es s i Hi Hpr :=
  let Hni := fresh "Hni" in
  let Hni' := fresh "Hni" in
  destruct (decide (i < equivocator_state_n es)) as [Hi | Hni]
  ; [|destruct (decide (i = equivocator_state_n es)) as [Hi | Hni']]
  ; [| | assert (Hi : equivocator_state_n es < i) by lia]
  ; [ specialize (equivocator_state_extend_project_1 es s i Hi) as Hpr
    | specialize (equivocator_state_extend_project_2 es s i Hi) as Hpr
    | specialize (equivocator_state_extend_project_3 es s i Hi) as Hpr]
  ; rewrite Hpr in *.

Local Ltac destruct_equivocator_state_extend_project es s i Hi :=
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
  intros.
  specialize (equivocator_state_last_n es2) as Hlst_es2.
  lia.
Qed.

Lemma equivocator_state_append_size es1 es2
  : equivocator_state_n (equivocator_state_append es1 es2) =
    equivocator_state_n es1 + equivocator_state_n es2.
Proof.
  destruct es1, es2. unfold equivocator_state_n.
  simpl. lia.
Qed.

Lemma equivocator_state_append_lst es1 es2
  : equivocator_state_last (equivocator_state_append es1 es2) = equivocator_state_last es2 + equivocator_state_n es1.
Proof. destruct es1, es2. cbn. unfold equivocator_state_n. simpl. lia. Qed.

Lemma equivocator_state_append_project_1 s s' i (Hi : i < equivocator_state_n s)
  : equivocator_state_project (equivocator_state_append s s') i = equivocator_state_project s i.
Proof.
  specialize (equivocator_state_projection_irrel s) as Hpi.
  rewrite (equivocator_state_project_Some _ _ Hi).
  specialize (equivocator_state_append_size s s') as Hsize.
  assert (Hi' : i < equivocator_state_n (equivocator_state_append s s'))
    by lia.
  rewrite (equivocator_state_project_Some _ _ Hi').
  f_equal.
  destruct s as (n1, bs1).
  destruct s' as (n2, bs2).
  unfold equivocator_state_n in *.
  simpl in *.
  rewrite to_nat_of_nat.
  unfold equivocator_state_n. simpl.
  case_decide; [|lia].
  apply Hpi.
  reflexivity.
Qed.

Lemma equivocator_state_append_project_2 s s' i k (Hi : i = k + equivocator_state_n s)
  : equivocator_state_project (equivocator_state_append s s') i = equivocator_state_project s' k.
Proof.
  specialize (equivocator_state_projection_irrel s') as Hpi.
  specialize (equivocator_state_append_size s s') as Hsize.
  remember (equivocator_state_append s s') as append.
  destruct_equivocator_state_project' s' k s'k Hk Hprs'
  ; destruct_equivocator_state_project' append i appendi Hi' Hprapp
  ; [|lia|lia|reflexivity].
  f_equal.
  rewrite (equivocator_state_project_Some _ _ Hi') in Hprapp.
  inversion_clear Hprapp.
  rewrite (equivocator_state_project_Some _ _ Hk) in Hprs'.
  inversion_clear Hprs'.
  subst.
  destruct s, s'. simpl in *. unfold equivocator_state_n in *. simpl in *.
  rewrite to_nat_of_nat.
  case_decide; [lia|].
  apply Hpi. lia.
Qed.

Lemma equivocator_state_append_project_3 s s' i (Hi : ~i < equivocator_state_n s + equivocator_state_n s')
  : equivocator_state_project (equivocator_state_append s s') i = None.
Proof.
  apply equivocator_state_project_None.
  unfold equivocator_state_n, equivocator_state_append, equivocator_state_last in *.
  simpl in *.
  lia.
Qed.

Local Ltac destruct_equivocator_state_append_project' es es' i Hi k Hk Hpr :=
  let Hi' := fresh "Hi" in
  destruct (decide (i < equivocator_state_n es)) as [Hi| Hi']; swap 1 2;
  [ destruct (decide (i < equivocator_state_n es + equivocator_state_n es')) as [Hi|Hi];
    swap 1 2;
    [ specialize (equivocator_state_append_project_3 es es' i Hi) as Hpr
    | apply not_lt_plus_dec in Hi' as [k Hk];
      specialize (equivocator_state_append_project_2 es es' i k (eq_sym Hk)) as Hpr
    ]
  | specialize (equivocator_state_append_project_1 es es' i Hi) as Hpr
  ]
  ; rewrite Hpr in *
  .

Local Ltac destruct_equivocator_state_append_project es es' i Hi k Hk :=
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
  - apply equivocator_state_extend_project_3. lia.
  - rewrite equivocator_state_extend_project_2 by lia.
    rewrite <- equivocator_state_project_zero.
    replace k with 0 by lia.
    reflexivity.
  - rewrite equivocator_state_extend_project_1 by lia.
    reflexivity.
Qed.

Lemma equivocator_state_append_extend_commute
  (es1 es2 : equivocator_state)
  (s : vstate X)
  : equivocator_state_extend (equivocator_state_append es1 es2) s =
    equivocator_state_append es1 (equivocator_state_extend es2 s).
Proof.
  apply equivocator_state_project_ext.
  intro i.
  destruct_equivocator_state_append_project es1 (equivocator_state_extend es2 s) i Hi k Hk.
  - apply equivocator_state_extend_project_3.
    rewrite equivocator_state_append_size.
    rewrite equivocator_state_extend_size in Hi.
    lia.
  - subst.
    rewrite equivocator_state_extend_size in Hi.
    destruct (decide (k = equivocator_state_n es2)).
    + subst.
      rewrite !equivocator_state_extend_project_2
      ; [reflexivity|reflexivity|].
      rewrite equivocator_state_append_size.
      lia.
    + rewrite !equivocator_state_extend_project_1
      ; [rewrite equivocator_state_append_project_2 with (k := k)|lia|]
      ; [reflexivity|reflexivity|].
      rewrite equivocator_state_append_size.
      lia.
  - rewrite equivocator_state_extend_project_1.
    + by apply equivocator_state_append_project_1.
    + rewrite equivocator_state_append_size. lia.
Qed.

Lemma equivocator_state_append_update_commute es1 es2 s n
  : equivocator_state_update (equivocator_state_append es1 es2) (n + equivocator_state_n es1) s =
    equivocator_state_append es1 (equivocator_state_update es2 n s).
Proof.
  apply equivocator_state_project_ext.
  intro i.
  destruct_equivocator_state_append_project es1 (equivocator_state_update es2 n s) i Hi k Hk.
  - apply equivocator_state_project_None.
    rewrite equivocator_state_update_size in *.
    rewrite equivocator_state_append_size.
    lia.
  - destruct (decide (n = k)).
    + subst. rewrite equivocator_state_update_size in Hi.
      rewrite equivocator_state_update_project_eq;
      [|rewrite equivocator_state_append_size; lia
      | reflexivity
      ].
      symmetry.
      apply equivocator_state_update_project_eq; lia.
    + rewrite !equivocator_state_update_project_neq by lia.
      by apply equivocator_state_append_project_2 with (k := k).
  - rewrite equivocator_state_update_project_neq by lia.
    rewrite equivocator_state_append_project_1 by lia.
    reflexivity.
Qed.

(* An [equivocator_state] has the [initial_state_prop]erty if it only
contains one state of original machine, and that state is initial.
*)
Definition equivocator_initial_state_prop
  (bs : equivocator_state)
  : Prop
  := is_singleton_state bs /\ vinitial_state_prop X (equivocator_state_zero bs).

Definition equivocator_initial_state
  := sig equivocator_initial_state_prop.

Definition equivocator_s0 : equivocator_initial_state.
Proof.
  exists (mk_singleton_state (proj1_sig (vs0 X))).
  unfold mk_singleton_state.
  unfold equivocator_initial_state_prop.
  split; [reflexivity|].
  simpl. destruct (vs0 X). assumption.
Defined.

Instance equivocator_initial_state_inh : Inhabited equivocator_initial_state :=
  {| inhabitant := equivocator_s0 |}.

Definition equivocator_sig
  : VLSMSign equivocator_type
  :=
    {|   initial_state_prop := equivocator_initial_state_prop
       ; initial_message_prop := vinitial_message_prop X
    |}.

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
      let (si', om') := vtransition X l (si, bsom.2) in
      (equivocator_state_update bsom.1 i si', om')
    end
  | ForkWith i l =>
    match equivocator_state_project bsom.1 i with
    | None => bsom
    | Some si =>
      let (si', om') := vtransition X l (si, bsom.2) in
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
    vinitial_state_prop X sn /\ bsom.2 = None
  | ContinueWith i l | ForkWith i l =>
    match equivocator_state_project bsom.1 i with
    | Some si => vvalid X l (si, bsom.2)
    | None => False
    end
  end.

Definition equivocator_vlsm_machine
  : VLSMClass equivocator_sig
  :=
  {|  transition := equivocator_transition
   ;  valid := equivocator_valid
  |}.

Definition equivocator_vlsm
  : VLSM message
  :=
  mk_vlsm equivocator_vlsm_machine.

Lemma equivocator_vlsm_initial_message_preservation
  : strong_full_projection_initial_message_preservation X equivocator_vlsm.
Proof.
  intro; intros. assumption.
Qed.

Lemma equivocator_vlsm_initial_message_preservation_rev
  : strong_full_projection_initial_message_preservation equivocator_vlsm X.
Proof.
  intro; intros. assumption.
Qed.

Lemma equivocator_vlsm_initial_state_preservation_rev is i s
  (Hs : equivocator_state_project is i = Some s)
  : vinitial_state_prop equivocator_vlsm is -> vinitial_state_prop X s.
Proof.
  intros [Hzero Hinit].
  apply equivocator_state_project_Some_rev in Hs as Hlt_i.
  assert (i = 0) by (cbv in *; lia). subst i.
  rewrite equivocator_state_project_zero in Hs. inversion Hs.
  assumption.
Qed.

Lemma mk_singleton_initial_state
  (s : vstate X)
  : vinitial_state_prop X s ->
    vinitial_state_prop equivocator_vlsm (mk_singleton_state s).
  Proof.
    intro Hs.
    split;[reflexivity|assumption].
  Qed.

End sec_equivocator_vlsm.

Arguments Spawn {_ _} _: assert.
Arguments ContinueWith {_ _} _ _: assert.
Arguments ForkWith {_ _} _ _: assert.
Arguments equivocator_state_n {_ _} _: assert.
Arguments equivocator_state_last {_ _} _: assert.
Arguments equivocator_state_zero {_ _} _: assert.
Arguments equivocator_state_s {_ _} _ _: assert.
Arguments equivocator_state_project {_ _} _ _: assert.
Arguments equivocator_state_update {_ _} _ _ _: assert.
Arguments equivocator_state_extend {_ _} _ _ : assert.
Arguments equivocator_state_append {_ _} _ _ : assert.

Ltac destruct_equivocator_state_project' es i si Hi Hpr :=
  destruct (equivocator_state_project es i) as [si|] eqn:Hpr
  ; [ specialize (equivocator_state_project_Some_rev _ _ _ _ Hpr) as Hi
    | specialize (equivocator_state_project_None_rev _ _ _ Hpr) as Hi ].

Ltac destruct_equivocator_state_project es i si Hi :=
  let Hpr := fresh "Hpr" in
  destruct_equivocator_state_project' es i si Hi Hpr
  ; clear Hpr.

Ltac destruct_equivocator_state_update_project' es i s j Hj Hij Hpr :=
  let Hsize := fresh "Hsize" in
  pose proof (equivocator_state_update_size _ es i s) as Hsize
  ; destruct (decide (j < equivocator_state_n es)) as [Hj | Hj]; swap 1 2
  ; [ specialize (equivocator_state_project_None _ (equivocator_state_update es i s) j Hj) as Hpr
    | destruct (decide (i = j)) as [Hij | Hij]
    ; [ specialize (equivocator_state_update_project_eq _ es i s j Hj Hij) as Hpr
      | specialize (equivocator_state_update_project_neq _ es i s j Hij) as Hpr
      ]]
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
  ; [|destruct (decide (i = equivocator_state_n es)) as [Hi | Hni']]
  ; [| | assert (Hi : equivocator_state_n es < i) by lia]
  ; [ specialize (equivocator_state_extend_project_1 _ es s i Hi) as Hpr
    | specialize (equivocator_state_extend_project_2 _ es s i Hi) as Hpr
    | specialize (equivocator_state_extend_project_3 _ es s i Hi) as Hpr]
  ; rewrite Hpr in *.

Ltac destruct_equivocator_state_extend_project es s i Hi :=
  let Hpr := fresh "Hpr" in
  destruct_equivocator_state_extend_project' es s i Hi Hpr
  ; clear Hpr.

Section equivocator_vlsm_valid_state_projections.

Context
  {message : Type}
  (X : VLSM message)
  (equivocator_vlsm := equivocator_vlsm X)
  .

(** When projecting an equivocator trace on one copy, we start from its final
state and trace back transitions, making sure to follow [ForkWith] transitions
back to their original copy and to stop on [Spawn] transitions.

To do that we need to track the current copy, or whether we already reached
the initial state.

- [NewMachine] <<s>> indicates that a [Spawn] <<s>> was already reached for the
  copy being tracked
- [Existing] <<i>> indicates that we're currently tracking copy <<i>>
*)
Inductive MachineDescriptor : Type
  :=
  | NewMachine : vstate X -> MachineDescriptor
  | Existing : nat -> MachineDescriptor.

(** The [MachineDescriptor] associated to an [equivocator_label] tells us
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
  - left. exact I.
  - right. simpl. intuition.
Qed.

(** Projecting an [equivocator_state] over a [MachineDescriptor].  *)
Definition equivocator_state_descriptor_project
  (s : equivocator_state X)
  (descriptor : MachineDescriptor)
  : vstate X
  :=
  match descriptor with
  | NewMachine sn => sn
  | Existing j => default (equivocator_state_zero s) (equivocator_state_project s j)
  end.

 (** Whether a [MachineDescriptor] can be used to project an
 [equivocator_state] to a regular [state].
 The [NewMachine] descriptor signals that an equivocation has occured
 starting a new machine, thus we require the argument to be initial.
 For an [Existing] descriptor, the index of the descriptor must
 refer to an existing machine in the current state.
 *)
Definition proper_descriptor
  (d : MachineDescriptor)
  (s : vstate equivocator_vlsm)
  :=
  match d with
  | NewMachine sn => vinitial_state_prop X sn
  | Existing i => is_Some (equivocator_state_project s i)
  end.

Definition proper_equivocator_label
  (l : equivocator_label X)
  (s : equivocator_state X)
  := proper_descriptor (equivocator_label_descriptor l) s.

(** Existing-only descriptor. *)
Definition existing_descriptor
  (d : MachineDescriptor)
  (s : vstate equivocator_vlsm)
  :=
  match d with
  | Existing i => is_Some (equivocator_state_project s i)
  | _ => False
  end.

Local Instance  existing_descriptor_dec : RelDecision existing_descriptor.
Proof.
  intros d s. destruct d; simpl.
  - right. intuition.
  - destruct_equivocator_state_project s n _sn Hn.
    + left. eexists; reflexivity.
    + right. intros [si Hi]. congruence.
Qed.

Definition existing_equivocator_label
  (l : equivocator_label X)
  := match l with Spawn _ => False | _ => True end.

Definition existing_equivocator_label_extract
  (l : equivocator_label X)
  (Hs : existing_equivocator_label l)
  : vlabel X.
Proof.
  destruct l.
  - contradiction.
  - exact v.
  - exact v.
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
  destruct l; [|exact I..].
  inversion Hs.
Qed.

Lemma existing_descriptor_proper
  (d : MachineDescriptor)
  (s : vstate equivocator_vlsm)
  (Hned : existing_descriptor d s)
  : proper_descriptor d s.
Proof.
  destruct d; [contradict Hned|].
  assumption.
Qed.

(* TODO: derive some some simpler lemmas about the equivocator operations,
or a simpler way of defining the equivocator_transition
- it's not nice to need to pick apart these cases from inside
equivocator_transition inside of so many proofs.
*)

(** If the state obtained after one transition has no equivocation, then
the descriptor of the label of the transition must be Existing 0 false
*)
Lemma equivocator_transition_no_equivocation_zero_descriptor
  (iom oom: option message)
  (l: vlabel equivocator_vlsm)
  (s s': vstate equivocator_vlsm)
  (Hv: vvalid equivocator_vlsm l (s, iom))
  (Ht: vtransition equivocator_vlsm l (s, iom) = (s', oom))
  (Hs' : is_singleton_state X s')
  : exists li, l = ContinueWith 0 li.
Proof.
  unfold is_singleton_state in Hs'.
  destruct l as [sn | ei l | ei l]
  ; [ inversion Ht; subst; rewrite equivocator_state_extend_size in Hs'; cbv in Hs'; lia|..]
  ; cbn in Hv, Ht;  destruct_equivocator_state_project s ei sei Hei; [|contradiction| |contradiction]
  ; destruct (vtransition _ _ _) as (si', om')
  ; inversion Ht; subst.
  - rewrite equivocator_state_update_size in Hs'. exists l. f_equal. lia.
  - rewrite equivocator_state_extend_size in Hs'. lia.
Qed.

(** If the state obtained after one transition has no equivocation, then
the state prior to the transition has no equivocation as well.
*)
Lemma equivocator_transition_reflects_singleton_state
  (iom oom: option message)
  (l: vlabel equivocator_vlsm)
  (s s': vstate equivocator_vlsm)
  (Ht: vtransition equivocator_vlsm l (s, iom) = (s', oom))
  : is_singleton_state X s' -> is_singleton_state X s.
Proof.
  unfold is_singleton_state.
  destruct l as [sn| ei l| ei l]; cbn in Ht
  ; [inversion Ht; rewrite equivocator_state_extend_size; cbv; lia| ..]
  ; destruct (equivocator_state_project _ _)
  ; [| inversion Ht; exact id| | inversion Ht; exact id]
  ; destruct (vtransition _ _ _) as (si', om')
  ; inversion Ht; subst; clear Ht.
  - rewrite equivocator_state_update_size. exact id.
  - rewrite equivocator_state_extend_size. cbv; lia.
Qed.

Lemma equivocator_transition_cannot_decrease_state_size
  (iom oom: option message)
  (l: vlabel equivocator_vlsm)
  (s s': vstate equivocator_vlsm)
  (Ht: vtransition equivocator_vlsm l (s, iom) = (s', oom))
  : equivocator_state_n s <= equivocator_state_n s'.
Proof.
  specialize (equivocator_state_extend_size X s) as Hex_size.
  destruct l as [sn| ei l| ei l]
  ; [inversion Ht; rewrite Hex_size; lia|..]
  ; cbn in Ht
  ; destruct (equivocator_state_project _ _)
  ; [|inversion Ht; lia| |inversion Ht; lia]
  ; destruct (vtransition _ _ _) as (si', om')
  ; inversion Ht; subst; clear Ht.
  - rewrite equivocator_state_update_size. lia.
  - rewrite Hex_size. lia.
Qed.

Lemma equivocator_transition_preserves_equivocating_state
  (iom oom: option message)
  (l: vlabel equivocator_vlsm)
  (s s': vstate equivocator_vlsm)
  (Ht: vtransition equivocator_vlsm l (s, iom) = (s', oom))
  : is_equivocating_state X s -> is_equivocating_state X s'.
Proof.
  intros Hs Hs'. elim Hs. clear Hs. revert Ht Hs' .
  apply equivocator_transition_reflects_singleton_state.
Qed.

Lemma zero_descriptor_transition_reflects_equivocating_state
  (iom oom: option message)
  (l: vlabel equivocator_vlsm)
  (s s': vstate equivocator_vlsm)
  (Ht: vtransition equivocator_vlsm l (s, iom) = (s', oom))
  li
  (Hzero : l = ContinueWith 0 li)
  : is_equivocating_state X s' -> is_equivocating_state X s.
Proof.
  subst.
  cbn in Ht.
  rewrite equivocator_state_project_zero in Ht.
  destruct (vtransition _ _ _).
  inversion Ht. subst.
  unfold is_equivocating_state, is_singleton_state.
  rewrite equivocator_state_update_size.
  exact id.
Qed.

(**
Valid messages in the [equivocator_vlsm] are also valid in the
original machine.  All components of a valid state in the
[equivocator_vlsm] are also valid in the original machine.
*)
Lemma preloaded_equivocator_state_projection_preserves_validity
  (seed : message -> Prop)
  (bs : vstate equivocator_vlsm)
  (om : option message)
  (Hbs : valid_state_message_prop (pre_loaded_vlsm equivocator_vlsm seed) bs om)
  : option_valid_message_prop (pre_loaded_vlsm X seed) om /\
    forall i si,
      equivocator_state_project bs i = Some si ->
      valid_state_prop (pre_loaded_vlsm X seed) si.
Proof.
  induction Hbs.
  - split; [apply option_initial_message_is_valid;assumption|].
    intros.
    destruct Hs as [Hn0 Hinit].
    apply equivocator_state_project_Some_rev in H as Hi.
    unfold is_singleton_state in Hn0.
    assert (i = 0) by lia. subst.
    rewrite equivocator_state_project_zero in H.
    inversion H. apply initial_state_is_valid. assumption.
  - specialize (valid_generated_state_message (pre_loaded_vlsm X seed)) as Hgen.
    apply proj2 in IHHbs1. apply proj1 in IHHbs2.

    (* destruction tactic for a valid equivocator transition
      vtransition equivocator_vlsm l (s, om) = (s', om')
    *)
    destruct l as [sn|i l|i l]
    ; [ inversion_clear Ht; split; [apply option_valid_message_None|]
      ; intros
      ; destruct_equivocator_state_extend_project s sn i Hi
      ; [ apply IHHbs1 in H; assumption
      | inversion H; subst; apply initial_state_is_valid; apply Hv
      | discriminate]
      |..]
    ; cbn in Hv, Ht
    ; destruct_equivocator_state_project' s i si Hi Hpr; [|contradiction| |contradiction]
    ; destruct (vtransition _ _ _) as (si', _om') eqn:Hti
    ; inversion Ht; subst s' _om'; clear Ht

    (* I wish I could solve this goal, then apply the composed tactic for the remaining two goals. *)
    (* common tactic for the last two goals. *)
    ; apply IHHbs1 in Hpr as [_omi Hsi]
      ; destruct IHHbs2 as [_som Hom]
      ; specialize (Hgen _ _ Hsi _ _ Hom _ Hv _ _ Hti)
      ; split; [eexists; exact Hgen| | eexists; exact Hgen|]; intros.
    + destruct_equivocator_state_update_project s i si' i0 Hi0 Hij.
      * discriminate.
      * inversion H. subst. eexists; exact Hgen.
      * apply IHHbs1 in H. assumption.
    + destruct_equivocator_state_extend_project s si' i0 Hi0.
      * apply IHHbs1 in H. assumption.
      * inversion H. subst. eexists; exact Hgen.
      * discriminate.
Qed.

Lemma preloaded_with_equivocator_state_project_valid_state
  (seed : message -> Prop)
  (bs : vstate equivocator_vlsm)
  (Hbs : valid_state_prop (pre_loaded_vlsm equivocator_vlsm seed) bs)
  : forall i si,
    equivocator_state_project bs i = Some si ->
    valid_state_prop (pre_loaded_vlsm X seed) si.
Proof.
  destruct Hbs as [om  Hbs].
  apply preloaded_equivocator_state_projection_preserves_validity, proj2 in Hbs.
  assumption.
Qed.

Lemma preloaded_with_equivocator_state_project_valid_message
  (seed : message -> Prop)
  (om : option message)
  (Hom : option_valid_message_prop (pre_loaded_vlsm equivocator_vlsm seed) om)
  :
  option_valid_message_prop (pre_loaded_vlsm X seed) om.
Proof.
  destruct Hom as [s Hm].
  apply preloaded_equivocator_state_projection_preserves_validity, proj1 in Hm.
  assumption.
Qed.

Lemma equivocator_state_project_valid_state
  (bs : vstate equivocator_vlsm)
  (Hbs : valid_state_prop equivocator_vlsm bs)
  : forall i si,
    equivocator_state_project bs i = Some si -> valid_state_prop X si.
Proof.
  intros i si Hpr.
  apply (VLSM_eq_valid_state (vlsm_is_pre_loaded_with_False equivocator_vlsm)) in Hbs.
  specialize (preloaded_with_equivocator_state_project_valid_state _ _ Hbs _ _ Hpr) as Hsi.
  apply (VLSM_eq_valid_state (vlsm_is_pre_loaded_with_False X)) in Hsi.
  destruct X as (T, (S, M)).
  assumption.
Qed.

Lemma equivocator_state_project_valid_message
  (om : option message)
  (Hom : option_valid_message_prop equivocator_vlsm om)
  :
  option_valid_message_prop X om.
Proof.
  destruct om as [m|]; [|apply option_valid_message_None].
  specialize (vlsm_is_pre_loaded_with_False_initial_message equivocator_vlsm) as Hinit.
  apply (VLSM_incl_valid_message (VLSM_eq_proj1 (vlsm_is_pre_loaded_with_False equivocator_vlsm))) in Hom
  ; [| assumption].
  apply preloaded_with_equivocator_state_project_valid_message in Hom.
  specialize (vlsm_is_pre_loaded_with_False_initial_message_rev X) as Hinit_rev.
  apply (VLSM_incl_valid_message (VLSM_eq_proj2 (vlsm_is_pre_loaded_with_False X))) in Hom
  ; destruct X as (T, (S, M))
  ; assumption.
Qed.

(**
All components of valid states of the [pre_loaded_with_all_messages_vlsm] corresponding
to an [equivocator_vlsm] are also valid for the [pre_loaded_with_all_messages_vlsm]
corresponding to the original machine.
*)
Lemma preloaded_equivocator_state_project_valid_state
  (bs : vstate equivocator_vlsm)
  (Hbs : valid_state_prop (pre_loaded_with_all_messages_vlsm equivocator_vlsm) bs)
  : forall i si,
    equivocator_state_project bs i = Some si -> valid_state_prop (pre_loaded_with_all_messages_vlsm X) si.
Proof.
  intros i si Hpr.
  apply (VLSM_eq_valid_state (pre_loaded_with_all_messages_vlsm_is_pre_loaded_with_True equivocator_vlsm)) in Hbs.
  specialize (preloaded_with_equivocator_state_project_valid_state _ _ Hbs _ _ Hpr) as Hsi.
  apply (VLSM_eq_valid_state (pre_loaded_with_all_messages_vlsm_is_pre_loaded_with_True X)) in Hsi.
  destruct X as (T, (S, M)).
  assumption.
Qed.

(**
Next couple of lemmas characterize the projections of a [equivocator_state]
after taking a transition in terms of the preceeeding state.

These are simpler version of the results concerning the projection of
states from the composition of equivocators over [equivocation_descriptors].

These results are used for characterizing the projection of the [destination]
of a [transition_item] in an equivocator trace in
[equivocator_transition_item_project_proper_characterization].
*)

Lemma new_machine_label_equivocator_transition_size
  {sn s oin s' oout}
  (Ht : vtransition equivocator_vlsm (Spawn sn) (s, oin) = (s', oout))
  : equivocator_state_n s' = S (equivocator_state_n s).
Proof.
  inversion_clear Ht.
  apply equivocator_state_extend_size.
Qed.

Lemma existing_true_label_equivocator_transition_size
  {ieqvi li s oin s' oout}
  (Ht : vtransition equivocator_vlsm (ForkWith ieqvi li) (s, oin) = (s', oout))
  si
  (Hv : equivocator_state_project s ieqvi = Some si)
  : equivocator_state_n s' = S (equivocator_state_n s).
Proof.
  cbn in Ht.
  rewrite Hv in Ht.
  destruct (vtransition _ _ _).
  inversion Ht. subst.
  apply equivocator_state_extend_size.
Qed.

Lemma existing_false_label_equivocator_transition_size
  {ieqvi li s oin s' oout}
  (Ht : vtransition equivocator_vlsm (ContinueWith ieqvi li) (s, oin) = (s', oout))
  si
  (Hv : equivocator_state_project s ieqvi = Some si)
  : equivocator_state_n s' = equivocator_state_n s.
Proof.
  cbn in Ht.
  rewrite Hv in Ht.
  destruct (vtransition _ _ _).
  inversion Ht. subst.
  apply equivocator_state_update_size.
Qed.

Lemma new_machine_label_equivocator_state_project_last
  {sn s oin s' oout}
  (Ht : vtransition equivocator_vlsm (Spawn sn) (s, oin) = (s', oout))
  : equivocator_state_descriptor_project s' (Existing (equivocator_state_n s)) =
    equivocator_state_descriptor_project s (NewMachine sn).
Proof.
    inversion_clear Ht. simpl.
    destruct_equivocator_state_extend_project s sn (equivocator_state_n s) Hi
    ; [lia|reflexivity|lia].
Qed.

Lemma new_machine_label_equivocator_state_project_not_last
  {sn s oin s' oout}
  (Ht : vtransition equivocator_vlsm (Spawn sn) (s, oin) = (s', oout))
  ni
  (Hni : ni < equivocator_state_n s)
  : equivocator_state_descriptor_project s' (Existing ni) =
    equivocator_state_descriptor_project s (Existing ni).
Proof.
  subst. inversion_clear Ht. simpl.
  destruct_equivocator_state_extend_project s sn ni Hi; [reflexivity|lia..].
Qed.

Lemma existing_true_label_equivocator_state_project_not_last
  {ieqvi li s oin s' oout}
  (Ht : vtransition equivocator_vlsm (ForkWith ieqvi li) (s, oin) = (s', oout))
  si
  (Hsi : equivocator_state_project s ieqvi = Some si)
  ni
  (Hni : ni < equivocator_state_n s)
  : equivocator_state_descriptor_project s' (Existing ni)
  = equivocator_state_descriptor_project s (Existing ni).
Proof.
  cbn in Ht.
  rewrite Hsi in Ht.
  destruct (vtransition _ _ _) as (si', _om') eqn:Hti.
  inversion Ht; subst s' _om'. clear Ht.
  simpl.
  destruct_equivocator_state_extend_project s si' ni Hni'; [reflexivity|lia..].
Qed.

Lemma existing_true_label_equivocator_state_project_last
  {ieqvi li s oin s' oout}
  (Ht : vtransition equivocator_vlsm (ForkWith ieqvi li) (s, oin) = (s', oout))
  si
  (Hsi : equivocator_state_project s ieqvi = Some si)
  si' _oout
  (Hti : vtransition X li (si, oin) = (si', _oout))
  : _oout = oout /\
    equivocator_state_descriptor_project s' (Existing (equivocator_state_n s)) = si'.
Proof.
  cbn in Ht.
  rewrite Hsi in Ht.
  simpl in Hti. rewrite Hti in Ht.
  inversion Ht. subst. clear Ht.
  split; [reflexivity|].
  simpl.
  rewrite equivocator_state_extend_project_2; reflexivity.
Qed.

Lemma existing_false_label_equivocator_state_project_not_same
  {ieqvi li s oin s' oout}
  (Ht : vtransition equivocator_vlsm (ContinueWith ieqvi li) (s, oin) = (s', oout))
  si
  (Hsi : equivocator_state_project s ieqvi = Some si)
  ni
  (Hni : ni < equivocator_state_n s)
  (Hnieqvi : ieqvi <> ni)
  : equivocator_state_descriptor_project s' (Existing ni)
  = equivocator_state_descriptor_project s (Existing ni).
Proof.
  cbn in Ht. rewrite Hsi in Ht.
  destruct (vtransition _ _ _) as (si', _om') eqn:Hti.
  inversion Ht; subst s' _om'. clear Ht.
  simpl.
  destruct_equivocator_state_update_project s ieqvi si' ni Hni' Hini; [lia..|].
  destruct_equivocator_state_project s ni sni Hni''; [|lia].
  reflexivity.
Qed.

Lemma existing_false_label_equivocator_state_project_same
  {ieqvi li s oin s' oout}
  (Ht : vtransition equivocator_vlsm (ContinueWith ieqvi li) (s, oin) = (s', oout))
  si
  (Hsi : equivocator_state_project s ieqvi = Some si)
  si' _oout
  (Hti : vtransition X li (si, oin) = (si', _oout))
  : _oout = oout /\
    equivocator_state_descriptor_project s' (Existing ieqvi) = si'.
Proof.
  cbn in Ht. rewrite Hsi in Ht.
  simpl in Hti. rewrite Hti in Ht.
  inversion Ht; subst s' _oout. clear Ht.
  split; [reflexivity|].
  simpl.
  rewrite equivocator_state_update_project_eq; [reflexivity| |reflexivity].
  apply equivocator_state_project_Some_rev in Hsi. assumption.
Qed.

End equivocator_vlsm_valid_state_projections.

Arguments NewMachine {_ _} _: assert.
Arguments Existing {_ _} _ : assert.
Arguments equivocator_label_descriptor {_ _} _ : assert.
Arguments equivocator_state_descriptor_project {_ _} _ _: assert.
