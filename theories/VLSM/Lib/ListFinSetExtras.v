From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From VLSM.Lib Require Import Preamble StdppExtras StdppListFinSet.

Section sec_defs.

Context `{FinSet A C}.

Definition set := C.

Definition empty_set : set := ∅.

Definition set_add (a : A) (x : set) : set := {[a]} ∪ x.

Definition set_remove (a : A) (x : set) : set := x ∖ {[ a ]}.

Definition set_union (x y : set) : set := x ∪ y.

Definition set_diff (x y : set) : set := x ∖ y.

Lemma set_union_subseteq_left :
  forall (s1 s2 : set), s1 ⊆ set_union s1 s2.
Proof. by intros s1 s2 x Hincl; apply set_union_intro; left. Qed.

Lemma set_union_subseteq_iff :
  forall (s1 s2 s : set), set_union s1 s2 ⊆ s <-> s1 ⊆ s /\ s2 ⊆ s.
Proof.
  intros s1 s2 s.
  unfold subseteq, set_subseteq_instance, set_subseteq_instance.
  setoid_rewrite set_union_iff.
  by split; itauto.
Qed.

Lemma elem_of_submseteq' :
  forall (a : A) (s1 s2 : set), a ∈ s1 -> s1 ⊆ s2 -> a ∈ s2.
Proof. by intros a s1 s2 Ha Hincl; apply Hincl. Qed.

Lemma empty_subseteq :
  forall (s : set), ∅ ⊆ s.
Proof. by intros s x Hin; contradict Hin; apply not_elem_of_empty. Qed.

#[export] Instance elem_of_dec : RelDecision (@elem_of A C _) := elem_of_dec_slow.

End sec_defs.
