# VLSM Coding Conventions

## Line wrapping

Try to keep your lines at most 80 characters long.

## Filenames

- [CamelCase](https://en.wikipedia.org/wiki/Camel_case) for Coq files, example: `StateMachineHandlerMonad.v`
- lowercase with dashes for scripts, example: `proof-linter.sh`
- UPPERCASE with underscores for documentation, example: `CODING_CONVENTIONS.md`

## Coq source files

### Require-Imports 

- general pattern: 
```coq
From VLSM.X Require Import Module_Name1 Module_Name2.
``` 

Example:
```coq
From VLSM.Lib Require Import Preamble ListExtras StdppListSet.
```

- in case of [`Stdlib`](https://coq.inria.fr/distrib/current/stdlib/) imports, the pattern should not include the full logical paths

Example:
```coq
From Coq Require Import FunctionalExtensionality Lia.
```

- exception to the rule regarding `stdlib` imports: Imports from `Program` preserve their entire path.

Example:
```coq
From Coq Require Export Program.Tactics.
```

### Sections

- C-style name

Example:
```coq
Section step_relations.
```

### Type classes

- CamelCase name
- field declaration with C-style naming on separate line

Example:
```coq
Class TotalOrder {A} (R : relation A) : Prop := {
  total_order_partial :> PartialOrder R;
  total_order_trichotomy :> Trichotomy (strict R)
}.
```

### Type class instances

- C-style names
- field declaration with C-style naming on separate line

Example with fully tactic-based definition:
```coq
Instance base_params (p : param) : BaseParams.
```

Example with Program environment:
```coq
Program Instance base_params (p : param) : BaseParams := {
  param_fst := _;
  param_snd := foo_bar x _;
}.
```

### Inductive types

- C-style type name
- CamelCase constructors
- one space indentation for each constructor declaration

Example:
```coq
Inductive lv_event_type : Type :=
 | State
 | Sent
 | Received.
```

### Definitions

- C-style name
- two spaces indentation before definition body
- generally avoid unnecessary type declarations for quantified variables

Example:
```coq
Definition lv_message_observations (s : state) (target : index) : set lv_event :=
  set_union (lv_sent_observations s target) (lv_received_observations s target).
```

### Theorems and lemmas

- C-style name
- generally avoid unnecessary type declarations for quantified variables
- two spaces indentation before lemma type

Example:
```coq
Lemma sync_some (s : vstate X) (from to : index) :
  sync s (get_matching_state s to from) to from <> None.
```

### Records

- C-style name
- CamelCase for constructor name
- field declaration with C-style naming on separate line

Example:
```coq
Record simp_lv_event : Type := SimpObs {
  get_simp_event_type : simp_lv_event_type;
  get_simp_event_subject : index;
  get_simp_event_state : (@state index index_listing);
}.
```

## Coqdoc

For multi-line coqdoc comments, place each of `(**` and `*)` on a separate line.
Use two spaces of indentation for the comment itself.

Not recommended:
```coq
(** Very very long
    Coqdoc comment. *)
```

Recommended:
```coq
(**
  Very very long
  Coqdoc comment.
*)
```

# Proof engineering rules of thumb

Here are some rules that we found useful. Some of them are more strict (like using bullets), others are more like rules of thumb.

## Use bullets and brackets

Bullets make the outline (subgoal structure) of the proof more explicit. The canonical order you should follow is (from top-most to bottom-most): `-`, `+`, `*`. If you run out of these, you can use `--`, `++`, `**`, etc.

Bad:
```coq
tac.
sub1_tac.
sub2_tac.
sub2_1_tac.
sub2_2_tac.
```

Good:
```coq
tac.
- sub1_tac.
- sub2_tac.
  + sub2_1_tac.
  + sub2_2_tac.
```

You should use brackets for `assert`.

Bad:
```coq
assert (H : some_fact).
- tac1.
- tac2.
```

Good:
```coq
assert (H : some_fact). {
  tac1.
}
tac2.
```

## Avoid `try` unless it's really really harmless

Using `try` may make refactoring proofs harder, because the refactoring can cause some goals to no longer be solved by the `try`. Instead, you should use `[tac | ... | tac]` or goal selectors.

Bad:
```coq
tac; try done.
```

Better:
```coq
tac; [| done | ... | done |].
```

Also better:
```coq
tac. 1-3,5,8-9,11: done.
```

## Avoid shelved goals and the `Unshelve` command

Sometimes existential tactics (whose name begin with an "e", for example `eapply`, `econstructor`) will generate a goal which is not immediately visible, but "shelved". It then needs to be unshelved using the `Unshelve` command and then proven.

Try to avoid this situation, as proofs with `Unshelve` can be problematic to maintain and refactor. The typical way to fix the problem is to provide more arguments to `eapply` or make sure that typeclass instance search works properly.

## Use goal finalizers if they fit into a single line

Some tactics which can generate side subgoals, like `assert` or `rewrite`, allow solving these subgoals on the fly with a `by` clause. Use this `by` clause if the subgoal is easy to solve.

Bad:
```coq
assert (H : some_fact X Y). {
  done.
}
```

Good:
```coq
assert (H : some_fact X Y) by done.
```

## Use `done` and `by` as finishers instead of more low-level tactics

Traditionally proofs of many goals end with the use of a low-level finisher tactic, like `assumption`, `reflexivity`, `trivial`, `contradiction` or `discriminate`. You should strongly avoid using these and instead use `done` from the `stdpp` library which subsumes them. `done` can also solve some goals that `congruence` can solve, but not all of them. In case `done` works, you should prefer it over `congruence`.

Bad:
```coq
tac.
- assumption.
- reflexivity.
- trivial.
- contradiction.
- discriminate.
```

Less bad:
```coq
tac; done.
```

You should avoid using `tac; done` and instead use `by tac`, which works exactly the same.

Good:
```coq
by tac.
```

Note that the `by` tactic comes from `stdpp`. There is also a standalone `by` tactic in `ssreflect`, but you should strongly avoid using it (to avoid dependency on `ssreflect`).

Also note that the `by` tactic is not the same thing as the `by` clause that can be used with `assert` or `rewrite`. You should avoid using these two `by`s together to avoid confusion. In these cases you should use `by (tac; done)` instead of `by by tac`.

Bad:
```coq
assert (H : some_fact) by by tac.
```

Good:
```coq
assert (H : some_fact) by (tac; done).
```

## Do not rely on autogenerated names - name your hypotheses explicitly

Autogenerated names are often tricky and change in hard to predict ways when the code is changed. For example, changing the sort of a definition from `Prop` to `Type` changes the autogenerated names from `H, H0, H1...` to `X, X0, X1...`. Therefore, when using tactics like `intros` or `destruct`, you should name the hypotheses explicitly.

Bad:
```coq
intros.
```

Good:
```coq
intros x y p H Heq Hlt.
```

### Exception: `Context`/`Variable`/`Hypothesis` blocks

When declaring typeclass instances as (local) axioms, you should use implicit generalization instead of naming the instance.

Bad:
```coq
Context
  (index : Type)
  (EqDecision_index : EqDecision index).
```

Good:
```coq
Context
  (index : Type)
  `(EqDecision index).
```

Best:
```coq
Context
  `(EqDecision index).
```

## The hierarchy of automation tactics

When you want to finish off a goal using automation tactics, you should use the least powerful tactic that works. At first, try `done`, If it doesn't work, then try one of `auto`, `congruence` and `lia`. If these don't work, try `itauto`, `itauto congruence` or `itauto lia`. If these don't work, you can try combinations like `itauto (auto || congruence)` or similar. Finally, if none of these work, you can try `smt` and `firstorder`.

You should completely avoid using the tactic `intuition` and its variants, like `tauto`, `intuition congruence`, `intuition lia`, and especially you should not use `intuition` to preprocess a goal (destruct hypotheses, etc.).
