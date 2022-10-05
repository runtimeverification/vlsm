From stdpp Require Import prelude.
From VLSM.Core Require Import MessageDependencies.

(** * VLSM Full Message Dependencies Using Typeclass-based Finite Sets *)

Class FinSetFullMessageDependencies
  `{HfinSetMessage : FinSet message Cm}
  (message_dependencies : message -> Cm)
  (full_message_dependencies : message -> Cm)
  :=
  { fin_set_full_message_dependencies_happens_before
      : forall dm m, dm ∈ full_message_dependencies m <-> msg_dep_happens_before (elements ∘ message_dependencies) dm m
  ; fin_set_full_message_dependencies_irreflexive
      : forall m, m ∉ full_message_dependencies m
  }.

(** Given the message type, we can usually look up the functions for message dependencies *)
#[global] Hint Mode FinSetFullMessageDependencies ! - - - - - - - - - - - - : typeclass_instances.

#[export] Instance full_message_dependencies_from_fin_set
  `{FinSetFullMessageDependencies message Cm message_dependencies full_message_dependencies}
  : FullMessageDependencies (elements ∘ message_dependencies) (elements ∘ full_message_dependencies).
Proof.
  constructor.
  - setoid_rewrite elem_of_elements; apply fin_set_full_message_dependencies_happens_before.
  - setoid_rewrite elem_of_elements; apply fin_set_full_message_dependencies_irreflexive.
  - intro; apply NoDup_elements.
Qed.

Definition fin_set_msg_dep_happens_before
  `{FinSetFullMessageDependencies message Cm message_dependencies full_message_dependencies}
  : message -> message -> Prop :=
  msg_dep_happens_before (elements ∘ message_dependencies).
