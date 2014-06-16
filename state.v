(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** The small step reduction (as defined in the file [smallstep]) is a binary
relation between execution states. In this file we define execution states, of
which we consider five variants:

- Execution of statements,
- Execution of expressions,
- Calling a function,
- Returning from a function, and,
- Undefined behavior.

The above kinds of execution states are adapted from Compcert's Cmedium. Like
CompCert, we capture undefined behavior by an explicit state for undefined
behavior. *)

(** Undefined behavior is different from the reduction semantics getting stuck.
For statically correct programs (i.e. those where all function names have a
corresponding body, labels for gotos exist, etc) the reduction semantics should
not get stuck, but might still end up in a state of undefined behavior. *)
Require Export statements memory.

(** * Definitions *)
(** Execution of statements occurs by traversal through the program context in
one of the following directions: down [↘], up [↗], to the top [⇈], or jump [↷].
When a [return e] statement is executed, and the expression [e] is evaluated to
the value [v], the direction is changed to [⇈ v]. The semantics then performs
a traversal to the top of the statement, and returns from the called function.
When a [goto l] statement is executed, the direction is changed to [↷l], and
the semantics performs a non-deterministic small step traversal through the
zipper until the label [l] is found. *)
Inductive direction (Ti : Set) : Set :=
  Down | Up | Top (v : val Ti) | Jump (l : labelname).
Arguments Down {_}.
Arguments Up {_}.
Arguments Top {_} _.
Arguments Jump {_} _%N.

Notation "↘" := Down : C_scope.
Notation "↗" := Up : C_scope.
Notation "⇈ v" := (Top v) (at level 20) : C_scope.
Notation "↷ l" := (Jump l) (at level 20) : C_scope.

Instance direction_eq_dec {Ti : Set} `{∀ k1 k2 : Ti, Decision (k1 = k2)}
  (d1 d2 : direction Ti) : Decision (d1 = d2).
Proof. solve_decision. Defined.

Definition down {Ti} (d : direction Ti) (s : stmt Ti) : Prop :=
  match d with ↘ => True | ↷ l => l ∈ labels s | _ => False end.
Definition up {Ti} (d : direction Ti) (s : stmt Ti) : Prop :=
  match d with ↗ => True | ⇈ _ => True | ↷ l => l ∉ labels s | _ => False end.

Hint Extern 0 (down _ _) => simpl.
Hint Extern 0 (up _ _) => simpl.
Lemma not_down_up {Ti} d (s : stmt Ti) : ¬down d s → up d s.
Proof. destruct d; intuition. Qed.
Definition down_up_dec {Ti} d (s : stmt Ti) : {down d s} + {up d s} :=
  match d with
  | ↘ => left I | ↗ => right I | ⇈ _ => right I
  | ↷ l => decide_rel (∈) l (labels s)
  end.

Tactic Notation "discriminate_down_up" hyp(H) := repeat
  match type of H with
  | up _ _ => progress simpl in H
  | down _ _ => progress simpl in H
  | True => clear H
  | False => destruct H
(*  | ?l ∉ _ => destruct H; solve_stmt_elem_of *)
  | ?l ∈ _ => solve [decompose_elem_of H]
  end.
Tactic Notation "discriminate_down_up" := repeat
  match goal with
  | H : up _ _ |- _ => discriminate_down_up H
  | H : down _ _ |- _ => discriminate_down_up H
  end.

(** The data type [focus] describes the part of the program that is focused. An
execution state [state] equips a focus with a program context and memory.

- The focus [Stmt] is used for execution of statements, it contains the
  statement to be executed and the direction in which traversal should be
  performed.
- The focus [Expr] is used for expressions and contains the whole expression
  that is being executed. Notice that this constructor does not contain the set
  of locked locations due to sequenced writes, these are contained more
  structurally in the expression itself.
- The focus [Call] is used to call a function, it contains the name of the
  called function and the values of the arguments.
- The focus [Return] is used to return from the called function to the calling
  function, it contains the return value.
- The focus [Undef] is used to capture undefined behavior. It contains the
  expression that got stuck.

These focuses correspond to the five variants of execution states as described
above. *)
Inductive focus (Ti : Set) : Set :=
  | Stmt : direction Ti → stmt Ti → focus Ti
  | Expr : expr Ti → focus Ti
  | Call : funname → list (val Ti) → focus Ti
  | Return : val Ti → focus Ti
  | Undef : expr Ti → focus Ti.
Record state (Ti : Set) : Set :=
  State { SCtx : ctx Ti; SFoc : focus Ti; SMem : mem Ti }.
Add Printing Constructor state.

Arguments Stmt {_} _ _.
Arguments Expr {_} _.
Arguments Call {_} _ _.
Arguments Return {_} _.
Arguments Undef {_} _.
Arguments State {_} _ _ _.
Arguments SCtx {_} _.
Arguments SFoc {_} _.
Arguments SMem {_} _.

Instance focus_eq_dec {Ti : Set} `{∀ k1 k2 : Ti, Decision (k1 = k2)}
  (φ1 φ2 : focus Ti) : Decision (φ1 = φ2).
Proof. solve_decision. Defined.
Instance state_eq_dec {Ti : Set} `{∀ k1 k2 : Ti, Decision (k1 = k2)}
  (S1 S2 : state Ti) : Decision (S1 = S2).
Proof. solve_decision. Defined.

Instance focus_locks {Ti} : Locks (focus Ti) := λ φ,
  match φ with Stmt _ s => locks s | Expr e => locks e | _ => ∅ end.
Instance focus_gotos {Ti} : Gotos (focus Ti) := λ φ,
  match φ with Stmt _ s => gotos s | _ => ∅ end.
Instance focus_labels {Ti} : Labels (focus Ti) := λ φ,
  match φ with Stmt _ s => labels s | _ => ∅ end.
