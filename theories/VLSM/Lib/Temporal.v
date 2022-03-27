From Cdcl Require Import Itauto. Local Tactic Notation "itauto" := itauto auto.
From Coq Require Import Streams Classical.

Set Implicit Arguments.

Lemma not_exists [A:Type] (P: A -> Prop):
  (~exists x, P x) -> (forall x, ~P x).
Proof.
  intros H x.
  contradict H.
  exists x;assumption.
Qed.

Inductive Eventually [A:Type] (P: Stream A -> Prop) : Stream A -> Prop :=
  | ehere : forall s, P s -> Eventually P s
  | elater : forall s, Eventually P s -> forall a, Eventually P (Cons a s).


CoInductive Forever [A:Type] (P: Stream A -> Prop) : Stream A -> Prop :=
  fcons : forall s, P s -> Forever P (tl s) -> Forever P s.

Lemma fhere [A:Type] (P: Stream A -> Prop) : forall s, Forever P s -> P s.
Proof.
  destruct 1;assumption.
Qed.

Lemma flater [A:Type] (P: Stream A -> Prop) : forall a s, Forever P (Cons a s) -> Forever P s.
Proof.
  intros a s.
  change s with (tl (Cons a s)) at 2.
  destruct 1;assumption.
Qed.

Lemma Eventually_map [A B:Type] (f: A -> B) (P: Stream B -> Prop): forall s,
  Eventually P (Streams.map f s) <-> Eventually (fun s => P (Streams.map f s)) s.
Proof.
  split.
  - remember (map f s) as fs.
    intro H. revert s Heqfs.
    induction H.
    + intros s0 ->. apply ehere. assumption.
    + intros [a' s'].
      intros. apply elater. apply IHEventually.
      apply (f_equal (@Streams.tl _)) in Heqfs. assumption.
  - induction 1.
    apply ehere. assumption.
    rewrite unfold_Stream.
    apply elater. assumption.
Qed.

Lemma Forever_map [A B:Type] (f: A -> B) (P: Stream B -> Prop): forall s,
  Forever P (Streams.map f s) <-> Forever (fun s => P (Streams.map f s)) s.
Proof.
  split;revert s.
  - cofix lem. destruct s.
    rewrite (unfold_Stream (map f (Cons a s))).
    simpl.
    inversion 1;subst.
    constructor.
    rewrite (unfold_Stream (map f (Cons a s))). assumption.
    apply lem. assumption.
  - cofix lem. destruct s.
    inversion 1;subst.
    constructor.
    assumption.
    simpl.
    apply lem;assumption.
Qed.

Definition progress [A:Type] (R: A -> A -> Prop) : Stream A -> Prop :=
  Forever (fun s => let x := hd s in let a := hd (tl s) in a = x \/ R a x).

Lemma not_eventually [A:Type] (P: Stream A -> Prop):
  forall s, ~Eventually P s -> Forever (fun s => ~ P s) s.
Proof.
  cofix not_eventually.
  destruct s.
  constructor.
  contradict H;apply ehere;assumption.
  apply not_eventually.
  contradict H;apply elater;assumption.
Qed.

Lemma forever_impl [A:Type] (P Q : Stream A -> Prop):
  forall s, Forever (fun s => P s -> Q s) s -> Forever P s -> Forever Q s.
Proof.
  cofix forever_impl.
  destruct s, 1.
  inversion 1. subst.
  constructor;auto.
Qed.

Lemma eventually_impl [A:Type] (P Q : Stream A -> Prop):
  forall s, Forever (fun s => P s -> Q s) s -> Eventually P s -> Eventually Q s.
Proof.
  induction 2.
  - apply ehere. apply fhere in H. auto.
  - apply elater. apply flater in H. auto.
Qed.


Lemma forever_tauto [A:Type] (P: Stream A -> Prop):
  (forall s, P s) -> forall s, Forever P s.
Proof.
  cofix forever_tauto.
  destruct s;constructor;auto.
Qed.

Lemma use_eventually [A:Type] (P Q : Stream A -> Prop):
  forall s, Eventually P s -> Forever Q s ->
            exists s', P s' /\ Forever Q s'.
Proof.
  induction 1.
  exists s;itauto.
  inversion 1. subst.
  itauto.
Qed.

Lemma refutation [A:Type] [R:A -> A-> Prop] (HR: well_founded R)
      [s]: ~ Forever (fun s => Eventually (fun x => R (hd x) (hd s)) s) s.
  remember (hd s) as x.
  revert s Heqx.
  specialize (HR x).
  induction HR. clear H.
  intros s -> HF.
  destruct (id HF).
  pose proof (use_eventually H HF).
  destruct H1 as [[a' s'] [Ha' H1']].
  simpl in Ha'.
  exact (H0 a' Ha' (Cons a' s') (eq_refl a') H1').
Qed.

Lemma forall_forever: forall [A B:Type] (P: A -> Stream B -> Prop) [s: Stream B],
    (forall (a:A), Forever (P a) s) -> Forever (fun s => forall a, P a s) s.
Proof.
  intros A B P.
  cofix forall_forever.
  destruct s.
  intro H.
  constructor.
  - intro a. specialize (H a). revert H.
    generalize (Cons b s). destruct 1. assumption.
  - apply forall_forever.
    change s with (tl (Cons b s)).
    intro a. specialize (H a). revert H.
    generalize (Cons b s). destruct 1. assumption.
Qed.

Lemma not_forever [A:Type] (P: Stream A -> Prop):
  forall s, ~Forever P s -> Eventually (fun s => ~ P s) s.
Proof.
  intros s H. apply Classical_Prop.NNPP.
  contradict H.
  apply not_eventually in H.
  revert H. apply forever_impl,forever_tauto. intro. apply Classical_Prop.NNPP.
Qed.

Lemma stabilization [A:Type] [R:A -> A-> Prop] (HR: well_founded R)
      [s]: progress R s -> exists x, Eventually (Forever (fun s => hd s = x)) s.
Proof.
  intro Hprogress.
  apply Classical_Prop.NNPP.
  intro H.
  pose proof (not_exists _ H);clear H. simpl in H0.
  assert (forall x, Forever (Eventually (fun s => hd s <> x)) s).
  {
    intro x.
    specialize (H0 x).
    apply not_eventually in H0.
    revert H0.
    apply forever_impl, forever_tauto.
    clear. intros s H.
    apply not_forever in H.
    assumption.
  }
  clear H0.
  refine (@refutation _ _ HR s _).
  revert s Hprogress H.
  cofix the_lemma.
  constructor.
  - destruct s.
    simpl.
    generalize (eq_refl : hd (Cons a s) = a).
    specialize (H a).
    destruct H as [x H _]. revert Hprogress.
    clear s.
    induction H;intro Hprogress.
    + destruct s. simpl in H. simpl in H |- *. congruence.
    + simpl. intro. subst a0.
      apply elater.
      inversion Hprogress; subst s0.
      simpl in H0, H1.
      specialize (IHEventually H1).
      destruct H0.
      * apply IHEventually. assumption.
      * apply ehere. assumption.
  - apply the_lemma.
    destruct Hprogress;assumption.
    intro x. specialize (H x).
    destruct H;assumption.
Qed.
