(* Copyright (c) 2012-2015, Robbert Krebbers. *)
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
Inductive direction (K : iType) : iType :=
  | Down
  | Up
  | Top : val K → direction K
  | Goto : labelname → direction K
  | Throw : nat → direction K
  | Switch : option Z → direction K.
Arguments Down {_}.
Arguments Up {_}.
Arguments Top {_} _.
Arguments Goto {_} _.
Arguments Throw {_} _.
Arguments Switch {_} _%Z.

Notation "↘" := Down : C_scope.
Notation "↗" := Up : C_scope.
Notation "⇈ v" := (Top v) (at level 20) : C_scope.
Notation "↷ l" := (Goto l) (at level 20) : C_scope.
Notation "↑ n" := (Throw n) (at level 20) : C_scope.
Notation "↓ mx" := (Switch mx) (at level 20) : C_scope.

#[global] Instance direction_eq_dec {K : iType} `{EqDecision K}: EqDecision (direction K).
Proof. solve_decision. Defined.

Definition direction_in {K} (d : direction K) (s : stmt K) : Prop :=
  match d with
  | ↘ => True | ↷ l => l ∈ labels s | ↓ mx => mx ∈ cases s | _ => False
  end.
Definition direction_out {K} (d : direction K) (s : stmt K) : Prop :=
  match d with
  | ↗ | ⇈ _ => True | ↷ l => l ∉ labels s | ↑ _ => True | _ => False
  end.
Arguments direction_in _ _ _ : simpl nomatch.
Arguments direction_out _ _ _ : simpl nomatch.
Global Hint Unfold direction_in direction_out: core.

Lemma direction_in_out {K} (d : direction K) s :
  direction_in d s → direction_out d s → False.
Proof. by destruct d. Qed.

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
Inductive undef_state (K : iType) : iType :=
  | UndefExpr : ectx K → expr K → undef_state K
  | UndefBranch : esctx_item K → lockset → val K → undef_state K.
Inductive focus (K : iType) : iType :=
  | Stmt : direction K → stmt K → focus K
  | Expr : expr K → focus K
  | Call : funname → list (val K) → focus K
  | Return : funname → val K → focus K
  | Undef : undef_state K → focus K.
Record state (K : iType) : iType :=
  State { SCtx : ctx K; SFoc : focus K; SMem : mem K }.
Add Printing Constructor state.

Arguments UndefExpr {_} _ _.
Arguments UndefBranch {_} _ _ _.
Arguments Stmt {_} _ _.
Arguments Expr {_} _.
Arguments Call {_} _ _.
Arguments Return {_} _ _.
Arguments Undef {_} _.
Arguments State {_} _ _ _.
Arguments SCtx {_} _.
Arguments SFoc {_} _.
Arguments SMem {_} _.

#[global] Instance undef_state_eq_dec {K : iType} `{EqDecision K}: EqDecision (undef_state K).
Proof. solve_decision. Defined.
#[global] Instance focus_eq_dec {K : iType} `{EqDecision K}: EqDecision (focus K).
Proof. solve_decision. Defined.
#[global] Instance state_eq_dec `{Env K}: EqDecision (state K).
Proof. solve_decision. Defined.

#[global] Instance maybe_Call {K} : Maybe2 (@Call K) := λ S,
  match S with Call f vs => Some (f,vs) | _ => None end.
#[global] Instance maybe_Return {K} : Maybe2 (@Return K) := λ S,
  match S with Return f v => Some (f,v) | _ => None end.
#[global] Instance maybe_Undef {K} : Maybe (@Undef K) := λ S,
  match S with Undef Su => Some Su | _ => None end.

Definition initial_state {K} (m : mem K)
  (f : funname) (vs : list (val K)) : state K := State [] (Call f vs) m.
Definition is_final_state {K}
    (f : funname) (v : val K) (S : state K) : Prop :=
  maybe2 Return (SFoc S) = Some (f,v) ∧ SCtx S = [].
Arguments is_final_state _ _ _ !_ /.
Definition is_undef_state {K} (S : state K) : Prop :=
  is_Some (maybe Undef (SFoc S)).
Arguments is_undef_state _ !_ /.
