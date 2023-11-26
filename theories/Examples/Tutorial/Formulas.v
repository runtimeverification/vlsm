From Coq Require Import FunctionalExtensionality.
From stdpp Require Import prelude.
From VLSM.Lib Require Import ListExtras.
From VLSM.Core Require Import VLSM Composition ProjectionTraces.

(** * Tutorial: VLSMs that Generate Logical Formulas

  This module shows how VLSMs can be used to generate propositional logic formulas.
  To achieve this, we define a family of VLSMs, one for each formula grammar rule, which
  generates messages according to the given rule. By composition, we obtain that
  the valid messages are precisely the "strings" which can be produced by the
  formula grammar.

  To strengthen the connection between formulas and VLSMs, we also define formulas
  as an inductive type and prove an equivalence between the inductively defined formulas
  and those obtained as valid messages of the composition of VLSMs from above.

  To simplify the presentation, the grammar we consider for formulas is
  unambiguous and uses prefix notation:

  <<f ::= ⊤ | ⊥ | x | ¬ f | ∧ f f | ∨ f f | → f f | ↔ f f>>
*)

Section sec_formula.

Context
  `{EqDecision Var}
  `{base.Infinite Var}
  .

Inductive symbol : Type :=
| Top
| Bot
| PVar (x : Var)
| Neg
| Conj
| Disj
| Impl
| Iff.

#[export] Instance symbol_dec : EqDecision symbol.
Proof.
  unfold EqDecision, Decision; decide equality.
  by destruct (decide (x0 = x1)); [left | right].
Qed.

Definition expression : Type := list symbol.

Inductive Formula : Type :=
| FTop
| FBot
| FVar (x : Var)
| FNeg (f : Formula)
| FConj (f1 f2 : Formula)
| FDisj (f1 f2 : Formula)
| FImpl (f1 f2 : Formula)
| FIff (f1 f2 : Formula).

(**
  We introduce the following notations to allow us to more easily write formulas.
*)
#[local] Notation "⊤" := FTop.
#[local] Notation "⊥" := FBot.
#[local] Notation "x ∨ y" := (FDisj x y) (at level 85, right associativity).
#[local] Notation "x ∧ y" := (FConj x y) (at level 80, right associativity).
#[local] Notation "x → y" := (FImpl x y) (at level 99, y at level 200, right associativity).
#[local] Notation "x ↔ y" := (FIff x y) (at level 95, no associativity).
#[local] Notation "¬ x" := (FNeg x) (at level 75, right associativity).

(**
  Similarly to the notations above, the purpose of this coercion is to allow
  using variables directly as formulas.
*)
Coercion FVar : Var >-> Formula.

(** A [Formula] is flattened to an [expression] using prefix notation. *)
Fixpoint flatten_formula (f : Formula) : expression :=
  match f with
  | FTop => [Top]
  | FBot => [Bot]
  | FVar x => [PVar x]
  | ¬ f => Neg :: flatten_formula f
  | f1 ∧ f2 => Conj :: flatten_formula f1 ++ flatten_formula f2
  | f1 ∨ f2 => Disj :: flatten_formula f1 ++ flatten_formula f2
  | f1 → f2 => Impl :: flatten_formula f1 ++ flatten_formula f2
  | f1 ↔ f2 => Iff :: flatten_formula f1 ++ flatten_formula f2
  end.

Lemma flatten_formula_nzlen :
  forall (f : Formula),
    length (flatten_formula f) > 0.
Proof. by intros []; cbn; lia. Qed.

(** ** Encoding formulas as VLSMs *)

(** *** VLSM for top and bottom rules

  This is a very simple VLSM, with a single state and a single label, accepting
  no input and outputing the expression containing just the symbol parameter.
*)

Section sec_expression_const_vlsm.

Context
  (ct : symbol)
  .

Definition expression_const_vlsm_type : VLSMType expression :=
{|
  state := unit;
  label := unit;
|}.

Definition expression_const_vlsm_machine : VLSMMachine expression_const_vlsm_type :=
{|
  initial_state_prop := const True;
  s0 := populate (exist _ () I);
  initial_message_prop := const False;
  transition := fun _ _ => ((), Some [ct]);
  valid := fun _ som => som.2 = None;
|}.

Definition expression_const_vlsm : VLSM expression :=
  mk_vlsm expression_const_vlsm_machine.

End sec_expression_const_vlsm.

(** *** VLSM for the variable rule

  This VLSM has a single state and its labels are the variables.
  Its behavior is to accept no input and to output the expression containing
  just the variable specified by the label of the transition.
*)

Section sec_expression_var_vlsm.

Definition expression_var_vlsm_type : VLSMType expression :=
{|
  state := unit;
  label := Var;
|}.

Definition expression_var_vlsm_machine : VLSMMachine expression_var_vlsm_type :=
{|
  initial_state_prop := const True;
  s0 := populate (exist _ () I);
  initial_message_prop := const False;
  transition := fun l _ => ((), Some [PVar l]);
  valid := fun _ som => som.2 = None;
|}.

Definition expression_var_vlsm : VLSM expression :=
  mk_vlsm expression_var_vlsm_machine.

End sec_expression_var_vlsm.

(** *** VLSM for the negation rule

  This VLSM has a single state and a single label, accepts as input an expression
  and outputs the expression obtained by prefixing the input with the negation
  symbol.
*)

Section sec_expression_neg_vlsm.

Definition expression_neg_vlsm_type : VLSMType expression :=
{|
  state := unit;
  label := unit;
|}.

Definition expression_neg_vlsm_transition (_ : unit)
  (som : unit * option expression) : unit * option expression :=
  match som.2 with
  | None => som
  | Some m => ((), Some (Neg :: m))
  end.

Definition expression_neg_vlsm_machine : VLSMMachine expression_neg_vlsm_type :=
{|
  initial_state_prop := const True;
  s0 := populate (exist _ () I);
  initial_message_prop := const False;
  transition := expression_neg_vlsm_transition;
  valid := fun _ som => is_Some som.2;
|}.

Definition expression_neg_vlsm : VLSM expression :=
  mk_vlsm expression_neg_vlsm_machine.

End sec_expression_neg_vlsm.

(** *** VLSM for binary connective rules

  This VLSM has a single label and its states are [option expression] with
  [None] being the initial state.
  From the initial state it accepts as input an expression and transitions
  to the state holding that expression.
  From a state holding an expression it accepts as input an expression and
  outputs the connective symbol (parameter) followed by the concatenation of
  the expression in the state and that in the input.
*)

Section sec_expression_binop_vlsm.

Context
  (binop : symbol)
  .

Definition expression_binop_vlsm_type : VLSMType expression :=
{|
  state := option expression;
  label := unit;
|}.

Definition expression_binop_vlsm_transition (_ : unit)
  (som : option expression * option expression) :
  option expression * option expression :=
  match som with
  | (_, None) => som
  | (None, Some f) => (Some f, None)
  | (Some f1, Some f2) => (None, Some (binop :: f1 ++ f2))
  end.

Definition expression_binop_vlsm_machine : VLSMMachine expression_binop_vlsm_type :=
{|
  initial_state_prop := fun o => o = None;
  s0 := populate (exist _ None eq_refl);
  initial_message_prop := const False;
  transition := expression_binop_vlsm_transition;
  valid := fun _ som => is_Some som.2;
|}.

Definition expression_binop_vlsm : VLSM expression :=
  mk_vlsm expression_binop_vlsm_machine.

End sec_expression_binop_vlsm.

(** *** VLSM for expressions *)

Section sec_expression_vlsm.

Inductive index :=
| ITop
| IBot
| IVar
| INeg
| IConj
| IDisj
| IImpl
| IIff.

#[export] Instance index_dec : EqDecision index.
Proof. by intros ? ?; unfold Decision; decide equality. Qed.

Definition symbol_to_index (s : symbol) : index :=
  match s with
  | Top => ITop
  | Bot => IBot
  | PVar _ => IVar
  | Neg => INeg
  | Conj => IConj
  | Disj => IDisj
  | Impl => IImpl
  | Iff => IIff
  end.

Definition expression_components (i : index) : VLSM expression :=
  match i with
  | ITop => expression_const_vlsm Top
  | IBot => expression_const_vlsm Bot
  | IVar => expression_var_vlsm
  | INeg => expression_neg_vlsm
  | IConj => expression_binop_vlsm Conj
  | IDisj => expression_binop_vlsm Disj
  | IImpl => expression_binop_vlsm Impl
  | IIff => expression_binop_vlsm Iff
  end.

Definition default_label (i : index) : label (expression_components i) :=
  match i with
  | IVar => fresh []
  | _ => ()
  end.

Definition default_composite_label
  (i : index) : composite_label expression_components :=
    existT i (default_label i).

Definition expression_vlsm : VLSM expression :=
  free_composite_vlsm expression_components.

End sec_expression_vlsm.

(** ** Characterization of valid messages as formulas *)

Section sec_valid_message_char.

Definition well_formed_expression : expression -> Prop :=
  valid_message_prop expression_vlsm.

(**
  We will show below (lemma [flatten_formula_prefix]) that no (strict) prefix of
  a flattened formula can be the flattening of another formula, which is a key
  result for establishing the injectivity of the [flatten_formula] function.

  To reach this result, we first define this property and prove several results
  about formulas satisfying it.
*)
Definition formula_prefix_is_not_formula_prop (f1 : Formula) : Prop :=
  forall (s : expression), strict prefix s (flatten_formula f1) ->
  forall (f2 : Formula), flatten_formula f2 <> s.

Lemma flatten_formula_formula_prefix_is_not_formula_prop_app :
  forall (fa : Formula), formula_prefix_is_not_formula_prop fa ->
  forall (fb : Formula), formula_prefix_is_not_formula_prop fb ->
  forall (sufa sufb : expression),
    flatten_formula fa ++ sufa = flatten_formula fb ++ sufb ->
    flatten_formula fa = flatten_formula fb /\ sufa = sufb.
Proof.
  intros fa Hfa fb Hfb sufa sufb Heq.
  cut (flatten_formula fa = flatten_formula fb);
    [by inversion 1; simplify_list_eq |].
  destruct (decide (prefix (flatten_formula fa) (flatten_formula fb))) as [Hab | Hab],
    (decide (prefix (flatten_formula fb) (flatten_formula fa))) as [Hba | Hba].
  - apply prefix_length_eq; [done |].
    by destruct Hba as [suf ->]; rewrite app_length; lia.
  - by exfalso; eapply Hfb.
  - by exfalso; eapply Hfa.
  - exfalso; revert sufb Heq.
    induction sufa using rev_ind; intros;
      [by simplify_list_eq; contradict Hba; eexists |].
    destruct_list_last sufb sufb' b Hsufb; simplify_list_eq.
    + by contradict Hab; eexists.
    + by eapply IHsufa.
Qed.

Lemma flatten_formula_formula_prefix_is_not_formula_prop_app_prefix :
  forall (fa1 : Formula), formula_prefix_is_not_formula_prop fa1 ->
  forall (fa2 : Formula), formula_prefix_is_not_formula_prop fa2 ->
  forall (fb1 : Formula), formula_prefix_is_not_formula_prop fb1 ->
  forall (fb2 : Formula), formula_prefix_is_not_formula_prop fb2 ->
    flatten_formula fb1 ++ flatten_formula fb2 `prefix_of`
      flatten_formula fa1 ++ flatten_formula fa2 ->
    flatten_formula fa1 ++ flatten_formula fa2
      =
    flatten_formula fb1 ++ flatten_formula fb2.
Proof.
  intros fa1 Hfa1 fa2 Hfa2 fb1 Hfb1 fb2 Hfb2 [suf Hpre].
  rewrite <- app_assoc, <- (app_nil_r (flatten_formula fa2)) in Hpre.
  apply flatten_formula_formula_prefix_is_not_formula_prop_app in Hpre as [-> Hpre]; [| done..].
  by apply flatten_formula_formula_prefix_is_not_formula_prop_app in Hpre as [-> _].
Qed.

Lemma flatten_formula_prefix_helper
  (f1_1 f1_2 : Formula)
  (IHn : forall (y : nat),
    y < S (length (flatten_formula f1_1 ++ flatten_formula f1_2)) ->
    forall (f1 : Formula), y = length (flatten_formula f1) ->
    formula_prefix_is_not_formula_prop f1)
  (suf : list symbol)
  (f2_1 f2_2 : Formula)
  (Hpre : flatten_formula f1_1 ++ flatten_formula f1_2 =
    flatten_formula f2_1 ++ flatten_formula f2_2 ++ suf)
  (s : symbol) :
    s :: flatten_formula f1_1 ++ flatten_formula f1_2
      `prefix_of`
    s :: flatten_formula f2_1 ++ flatten_formula f2_2.
Proof.
  rewrite app_assoc in Hpre.
  erewrite flatten_formula_formula_prefix_is_not_formula_prop_app_prefix;
    [done | .. | by eexists]; (eapply IHn; [| done]).
  - by rewrite app_length; lia.
  - by rewrite app_length; lia.
  - by rewrite Hpre, !app_length; lia.
  - by rewrite Hpre, !app_length; lia.
Qed.

Lemma flatten_formula_prefix :
  forall (f1 : Formula),
    formula_prefix_is_not_formula_prop f1.
Proof.
  intros f1.
  remember (length (flatten_formula f1)) as n.
  revert f1 Heqn; induction n as [n IHn] using (well_founded_induction lt_wf).
  intros f1 -> s [[suf Hpre] Hproper] f2 <-.
  destruct f1, f2; cbn in *; try congruence; simplify_list_eq;
    [done | done | done | | by contradict Hproper; eapply flatten_formula_prefix_helper..].
  eapply IHn with (f1 := f1) (f2 := f2); cycle 1; [done | | done | by lia].
  split; [by eexists |].
  intros [suf' Hsuf']; contradict Hproper.
  by exists suf'; rewrite Hsuf'.
Qed.

Lemma flatten_formula_common_prefix :
  forall (fa fb : Formula) (sufa sufb : expression),
    flatten_formula fa ++ sufa = flatten_formula fb ++ sufb ->
    flatten_formula fa = flatten_formula fb /\ sufa = sufb.
Proof.
  intros * Hpre.
  by apply flatten_formula_formula_prefix_is_not_formula_prop_app;
    [apply flatten_formula_prefix.. |].
Qed.

#[export] Instance flatten_formula_inj : Inj (=) (=) flatten_formula.
Proof.
  by intros f; induction f; intros []; cbn; inversion 1 as [Heq];
    [| | | by apply IHf in Heq as ->
    | apply flatten_formula_common_prefix in Heq as []; erewrite IHf1, IHf2..].
Qed.

Definition binop_state_cast
  (si : expression) (j : index) : state (expression_components j) :=
  match j with
  | ITop | IBot | IVar | INeg => ()
  | _ => Some si
  end.

Inductive BinOp : symbol -> Prop :=
| bin_op_conj : BinOp Conj
| bin_op_disj : BinOp Disj
| bin_op_impl : BinOp Impl
| bin_op_iff : BinOp Iff.

Lemma well_formed_flatten_formula_helper :
  forall (binop : symbol), BinOp binop ->
  forall (f1 f2 : Formula),
    well_formed_expression (flatten_formula f1) ->
    well_formed_expression (flatten_formula f2) ->
    well_formed_expression (binop :: flatten_formula f1 ++ flatten_formula f2).
Proof.
  intros binop Hbinop f1 f2 Hf1 Hf2.
  pose (i := symbol_to_index binop).
  pose (s0 := ` (composite_s0 expression_components)).
  pose (s1 := state_update expression_components s0 i
    (binop_state_cast (flatten_formula f1) i)).
  assert (Ht1 : input_valid_transition expression_vlsm
    (default_composite_label i) (s0, Some (flatten_formula f1)) (s1, None)).
  {
    repeat split.
    - by apply initial_state_is_valid; destruct composite_s0.
    - done.
    - by inversion Hbinop; subst; eexists.
    - by inversion Hbinop; subst.
  }
  cut (input_valid_transition expression_vlsm
    (default_composite_label i) (s1, Some (flatten_formula f2))
    (s0, Some (binop :: flatten_formula f1 ++ flatten_formula f2)));
    [by eapply input_valid_transition_out |].
  repeat split.
  - by eapply input_valid_transition_destination.
  - done.
  - by inversion Hbinop; subst; eexists.
  - by inversion Hbinop; subst binop i s1; cbn in *;
      rewrite state_update_eq, state_update_twice, state_update_id.
Qed.

(** The flattening of a [Formula] is a [well_formed_expression]. *)
Theorem flatten_formulas_are_well_formed_expressions :
  forall (f : Formula),
    well_formed_expression (flatten_formula f).
Proof.
  induction f; cbn.
  - cut (input_valid_transition expression_vlsm (existT ITop ())
      (` (composite_s0 expression_components), None)
      (` (composite_s0 expression_components), Some ([Top])));
      [by eapply input_valid_transition_out |].
    repeat split.
    + by apply initial_state_is_valid; destruct composite_s0.
    + by apply option_valid_message_None.
    + by cbn; rewrite state_update_id.
  - cut (input_valid_transition expression_vlsm (existT IBot ())
      (` (composite_s0 expression_components), None)
      (` (composite_s0 expression_components), Some ([Bot])));
      [by eapply input_valid_transition_out |].
    repeat split.
    + by apply initial_state_is_valid; destruct composite_s0.
    + by apply option_valid_message_None.
    + by cbn; rewrite state_update_id.
  - cut (input_valid_transition expression_vlsm (existT IVar x)
      (` (composite_s0 expression_components), None)
      (` (composite_s0 expression_components), Some ([PVar x])));
      [by eapply input_valid_transition_out |].
    repeat split.
    + by apply initial_state_is_valid; destruct composite_s0.
    + by apply option_valid_message_None.
    + by cbn; rewrite state_update_id.
  - cut (input_valid_transition expression_vlsm (existT INeg ())
      (` (composite_s0 expression_components), Some (flatten_formula f))
      (` (composite_s0 expression_components), Some (Neg :: flatten_formula f)));
      [by eapply input_valid_transition_out |].
    repeat split.
    + by apply initial_state_is_valid; destruct composite_s0.
    + done.
    + by eexists.
    + by cbn; rewrite state_update_id.
  - by apply well_formed_flatten_formula_helper; [constructor | ..].
  - by apply well_formed_flatten_formula_helper; [constructor | ..].
  - by apply well_formed_flatten_formula_helper; [constructor | ..].
  - by apply well_formed_flatten_formula_helper; [constructor | ..].
Qed.

Definition binop_state_proj
  (s : composite_state expression_components) (i : index) : option expression :=
  match i with
  | ITop | IBot | IVar | INeg => None
  | i => s i
  end.

Lemma well_formed_is_flatten_formula_helper
  (binop : symbol)
  (Hbinop : BinOp binop)
  (i := symbol_to_index binop)
  (e : expression)
  (Hind : forall (y : nat),
    y < length e ->
    forall (e : expression), y = length e -> well_formed_expression e ->
    exists (f : Formula), flatten_formula f = e)
  (s0 : composite_state expression_components)
  (si' : option expression)
  (om : option expression)
  (Hom : option_valid_message_prop expression_vlsm om)
  (Hti : transition (VLSMMachine := expression_binop_vlsm_machine binop) ()
    (binop_state_proj s0 i, om) = (si', Some e))
  (Hs0 : valid_state_prop expression_vlsm s0) :
    exists f : Formula, flatten_formula f = e.
Proof.
  destruct (binop_state_proj s0 i) as [e1 |] eqn: Hs0i;
    [| by destruct om; inversion Hti].
  destruct om as [m |]; [| done].
  inversion Hti; subst; clear Hti.
  apply (free_valid_state_component_initial_or_transition i) in Hs0.
  destruct Hs0 as [Hs0 | (l & si & iom & oom & (_ & Hiom & Hvs0) & Ht)];
    [by inversion Hbinop; subst; cbn in *; congruence |].
  cbn in *; state_update_simpl.
  eapply Hind in Hom as [f2 Hf2]; cycle 2;
    [done | | by rewrite app_length; lia].
  cut (exists f1 : Formula, flatten_formula f1 = e1).
  {
    subst m; intros [f1 <-]; inversion Hbinop.
    - by exists (f1 ∧ f2).
    - by exists (f1 ∨ f2).
    - by exists (f1 → f2).
    - by exists (f1 ↔ f2).
  }
  eapply Hind; cycle 1; [done | | by rewrite app_length; lia].
  destruct (transition l (si, iom)) eqn: Hti; inversion Ht as [Heq]; subst.
  rewrite <- Heq, state_update_twice in Hs0i.
  by inversion Hbinop; subst binop i; destruct Hvs0 as [im Him]; cbn in *;
    state_update_simpl; subst; (destruct si; [done |]);
    inversion Hti; subst.
Qed.

(**
  Any [well_formed_expression] is the flattening of a [Formula].
*)
Theorem well_formed_expression_are_flatten_formulas :
  forall (e : expression), well_formed_expression e ->
    exists (f : Formula), flatten_formula f = e.
Proof.
  intros e.
  remember (length e) as n.
  revert e Heqn; induction n as [n Hind] using (well_founded_ind lt_wf).
  intros e -> [s He].
  inversion He; subst; [by destruct Hom as ([] & [im Him] & Hom) |].
  destruct l as [i li]; cbn in *.
  assert (Hs0 : valid_state_prop expression_vlsm s0) by (eexists; done).
  destruct (transition li (s0 i, om)) as [si' om'] eqn: Hti.
  inversion Ht; subst; clear Ht.
  destruct i.
  - by inversion Hti; exists ⊤.
  - by inversion Hti; exists ⊥.
  - by inversion Hti; exists li.
  - destruct om as [m |]; [| done].
    inversion Hti; subst.
    assert (Hm : well_formed_expression m) by (eexists; done).
    by apply (Hind (length m)) in Hm as [fm <-]; [exists (FNeg fm) | cbn; lia |].
  - by eapply well_formed_is_flatten_formula_helper;
      [constructor | | exists _s | cbn in *; apply Hti | ..].
  - by eapply well_formed_is_flatten_formula_helper;
      [constructor | | exists _s | cbn in *; apply Hti | ..].
  - by eapply well_formed_is_flatten_formula_helper;
      [constructor | | exists _s | cbn in *; apply Hti | ..].
  - by eapply well_formed_is_flatten_formula_helper;
      [constructor | | exists _s | cbn in *; apply Hti | ..].
Qed.

(**
  [well_formed_expression]s, that is, valid messages of the [expression_vlsm]
  coincide with flatten [Formula]s.
*)
Corollary well_formed_expression_flatten_formula_equiv :
  forall (e : expression), well_formed_expression e <->
  exists (f : Formula), flatten_formula f = e.
Proof.
  split.
  - by apply well_formed_expression_are_flatten_formulas.
  - by intros [f <-]; apply flatten_formulas_are_well_formed_expressions.
Qed.

End sec_valid_message_char.

(** ** Interpretation of formulas

  We define a function to interpret formulas as Coq terms in the [Prop] sort,
  given that all atoms are mapped to [Prop] terms.
*)

Section sec_formula_interpretation.

Context
  (formula_var_interp : Var -> Prop).

Fixpoint formula_vars (f : Formula) : listset Var :=
  match f with
  | ⊤ | ⊥ => ∅
  | FVar x => {[x]}
  | ¬ f => formula_vars f
  | f1 ∧ f2 | f1 ∨ f2 | f1 → f2 | f1 ↔ f2 => formula_vars f1 ∪ formula_vars f2
  end.

Fixpoint formula_interp (f : Formula) : Prop :=
  match f with
  | ⊤ => True
  | ⊥ => False
  | FVar x => formula_var_interp x
  | ¬ f => ~ formula_interp f
  | f1 ∧ f2 => formula_interp f1 /\ formula_interp f2
  | f1 ∨ f2 => formula_interp f1 \/ formula_interp f2
  | f1 → f2 => formula_interp f1 -> formula_interp f2
  | f1 ↔ f2 => formula_interp f1 <-> formula_interp f2
  end.

End sec_formula_interpretation.

Definition formula_holds_prop (f : Formula) : Prop :=
  forall (i : Var -> Prop), formula_interp i f.

End sec_formula.

Arguments Formula : clear implicits.

(**
  The formula notations we introduced above were local to this module.
  To allow these notations to be used elsewhere, while also allowing them to
  be enabled and disabled by need, we declare them as part of a scope.
*)
Declare Scope formula_scope.
Bind Scope formula_scope with Formula.

Notation "⊤" := FTop : formula_scope.
Notation "⊥" := FBot : formula_scope.
Notation "x ∨ y" := (FDisj x y) (at level 85, right associativity) : formula_scope.
Notation "x ∧ y" := (FConj x y) (at level 80, right associativity) : formula_scope.
Notation "x → y" := (FImpl x y) (at level 99, y at level 200, right associativity) : formula_scope.
Notation "x ↔ y" := (FIff x y) (at level 95, no associativity): formula_scope.
Notation "¬ x" := (FNeg x) (at level 75, right associativity) : formula_scope.
