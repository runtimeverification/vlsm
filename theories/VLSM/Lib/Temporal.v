From VLSM.Lib Require Import Itauto.
From stdpp Require Import prelude.
From Coq Require Import Streams Classical.

(** * Temporal Logic Predicates and Results *)

Lemma Exists_map_conv [A B : Type] (f : A -> B) (P : Stream B -> Prop) : forall s,
  Exists P (Streams.map f s) -> Exists (fun s => P (Streams.map f s)) s.
Proof.
  intros; remember (map f s) as fs; revert s Heqfs.
  induction H; [by intros s0 ->; constructor |].
  intros [a' s'] Heqfs.
  constructor 2.
  apply IHExists.
  by rewrite Heqfs.
Qed.

Definition progress [A : Type] (R : A -> A -> Prop) : Stream A -> Prop :=
  ForAll (fun s => let x := hd s in let a := hd (tl s) in a = x \/ R a x).

Lemma not_Exists [A : Type] (P : Stream A -> Prop) :
  forall s, ~ Exists P s -> ForAll (fun s => ~ P s) s.
Proof.
  cofix not_Exists.
  destruct s.
  constructor.
  - by contradict H; constructor.
  - by apply not_Exists; contradict H; constructor.
Qed.

Lemma ForAll_impl [A : Type] (P Q : Stream A -> Prop) :
  forall s, ForAll (fun s => P s -> Q s) s -> ForAll P s -> ForAll Q s.
Proof.
  cofix ForAll_impl.
  destruct s, 1.
  inversion 1; subst.
  by constructor; auto.
Qed.

Lemma Exists_impl [A : Type] (P Q : Stream A -> Prop) :
  forall s, ForAll (fun s => P s -> Q s) s -> Exists P s -> Exists Q s.
Proof.
  induction 2.
  - by apply Here, H.
  - by apply Further, IHExists; inversion H.
Qed.

Lemma ForAll_tauto [A : Type] (P : Stream A -> Prop) :
  (forall s, P s) -> forall s, ForAll P s.
Proof.
  cofix ForAll_tauto.
  by destruct s; constructor; auto.
Qed.

Lemma use_Exists [A : Type] (P Q : Stream A -> Prop) :
  forall s, Exists P s -> ForAll Q s ->
            exists s', P s' /\ ForAll Q s'.
Proof.
  induction 1.
  - by exists x; itauto.
  - by inversion 1; subst; itauto.
Qed.

Lemma refutation [A : Type] [R : A -> A-> Prop] (HR : well_founded R)
      [s] : ~ ForAll (fun s => Exists (fun x => R (hd x) (hd s)) s) s.
Proof.
  remember (hd s) as x.
  revert s Heqx.
  specialize (HR x).
  induction HR. clear H.
  intros s -> HF.
  destruct (id HF).
  destruct (use_Exists _ _ _ H HF) as [[a' s'] [Ha' H1']].
  simpl in Ha'.
  by eapply H0; eauto.
Qed.

Lemma forall_ForAll : forall [A B : Type] (P : A -> Stream B -> Prop) [s : Stream B],
    (forall (a : A), ForAll (P a) s) -> ForAll (fun s => forall a, P a s) s.
Proof.
  intros A B P.
  cofix forall_ForAll.
  destruct s.
  intro H.
  constructor.
  - by intro a; destruct (H a).
  - apply forall_ForAll.
    by intro a; destruct (H a).
Qed.

Lemma not_ForAll [A : Type] (P : Stream A -> Prop) :
  forall s, ~ ForAll P s -> Exists (fun s => ~ P s) s.
Proof.
  intros s H. apply Classical_Prop.NNPP.
  contradict H.
  apply not_Exists in H.
  revert H; apply ForAll_impl, ForAll_tauto.
  by intro; apply Classical_Prop.NNPP.
Qed.

Lemma stabilization [A : Type] [R : A -> A-> Prop] (HR : well_founded R)
      [s] : progress R s -> exists x, Exists (ForAll (fun s => hd s = x)) s.
Proof.
  intro Hprogress.
  apply Classical_Prop.NNPP.
  intro H.
  assert (forall x, ForAll (Exists (fun s => hd s <> x)) s).
  {
    intro x.
    assert (forall n : A, ~ Exists (ForAll (fun s : Stream A => hd s = n)) s) by firstorder.
    specialize (H0 x).
    apply not_Exists in H0.
    revert H0.
    apply ForAll_impl, ForAll_tauto.
    clear. intros s H.
    by apply not_ForAll in H.
  }
  clear H; rename H0 into H.
  refine (@refutation _ _ HR s _).
  revert s Hprogress H.
  cofix the_lemma.
  constructor.
  - destruct s.
    simpl.
    generalize (eq_refl : hd (Cons a s) = a).
    specialize (H a).
    destruct H as [H _]. revert Hprogress.
    induction H; intro Hprogress.
    + by destruct s; cbn in *; congruence.
    + simpl. intro. subst a.
      apply Further.
      inversion Hprogress.
      simpl in H0, H1.
      specialize (IHExists H1).
      destruct H0.
      * by apply IHExists.
      * by constructor.
  - apply the_lemma.
    + by apply Hprogress.
    + by apply H.
Qed.
