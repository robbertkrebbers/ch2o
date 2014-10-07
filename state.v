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
  Down | Up | Top (v : val Ti) | Goto (l : labelname) | Throw (n : nat).
Arguments Down {_}.
Arguments Up {_}.
Arguments Top {_} _.
Arguments Goto {_} _.
Arguments Throw {_} _.

Notation "↘" := Down : C_scope.
Notation "↗" := Up : C_scope.
Notation "⇈ v" := (Top v) (at level 20) : C_scope.
Notation "↷ l" := (Goto l) (at level 20) : C_scope.
Notation "↑ n" := (Throw n) (at level 20) : C_scope.

Instance direction_eq_dec {Ti : Set} `{∀ k1 k2 : Ti, Decision (k1 = k2)}
  (d1 d2 : direction Ti) : Decision (d1 = d2).
Proof. solve_decision. Defined.

Definition direction_in {Ti} (d : direction Ti) (s : stmt Ti) : Prop :=
  match d with ↘ => True | ↷ l => l ∈ labels s | _ => False end.
Definition direction_out {Ti} (d : direction Ti) (s : stmt Ti) : Prop :=
  match d with
  | ↗ | ⇈ _ => True | ↷ l => l ∉ labels s | ↑ _ => True | _ => False
  end.
Arguments direction_in _ _ _ : simpl nomatch.
Arguments direction_out _ _ _ : simpl nomatch.
Hint Unfold direction_in direction_out.

Definition direction_in_out_dec {Ti} (d : direction Ti) s :
  { direction_in d s ∧ ¬direction_out d s } +
  { ¬direction_in d s ∧ direction_out d s }.
Proof.
 refine
  match d with
  | ↘ => left _ | ↷ l => cast_if (decide (l ∈ labels s)) | _ => right _
  end; abstract naive_solver.
Defined.
Lemma direction_in_out {Ti} (d : direction Ti) s :
  direction_in d s → direction_out d s → False.
Proof. destruct (direction_in_out_dec d s); naive_solver. Qed.

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
Inductive undef_state (Ti : Set) : Set :=
  | UndefExpr : ectx Ti → expr Ti → undef_state Ti
  | UndefBranch : esctx_item Ti → lockset → val Ti → undef_state Ti.
Inductive focus (Ti : Set) : Set :=
  | Stmt : direction Ti → stmt Ti → focus Ti
  | Expr : expr Ti → focus Ti
  | Call : funname → list (val Ti) → focus Ti
  | Return : funname → val Ti → focus Ti
  | Undef : undef_state Ti → focus Ti.
Record state (Ti : Set) : Set :=
  State { SCtx : ctx Ti; SFoc : focus Ti; SMem : mem Ti }.
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

Instance undef_state_eq_dec {Ti : Set} `{∀ k1 k2 : Ti, Decision (k1 = k2)}
  (S1 S2 : undef_state Ti) : Decision (S1 = S2).
Proof. solve_decision. Defined.
Instance focus_eq_dec {Ti : Set} `{∀ k1 k2 : Ti, Decision (k1 = k2)}
  (φ1 φ2 : focus Ti) : Decision (φ1 = φ2).
Proof. solve_decision. Defined.
Instance state_eq_dec {Ti : Set} `{∀ k1 k2 : Ti, Decision (k1 = k2)}
  (S1 S2 : state Ti) : Decision (S1 = S2).
Proof. solve_decision. Defined.
Instance focus_locks {Ti} : Locks (focus Ti) := λ φ,
  match φ with Stmt _ s => locks s | Expr e => locks e | _ => ∅ end.

Definition initial_state {Ti} (m : mem Ti)
  (f : funname) (vs : list (val Ti)) : state Ti := State [] (Call f vs) m.
Inductive is_final_state {Ti} (v : val Ti) : state Ti → Prop :=
  | Return_final f m : is_final_state v (State [] (Return f v) m).
Inductive is_undef_state {Ti} : state Ti → Prop :=
  | Undef_undef k Su m : is_undef_state (State k (Undef Su) m).

Instance is_final_state_dec {Ti : Set} `{∀ k1 k2 : Ti, Decision (k1 = k2)}
  (v : val Ti) S : Decision (is_final_state v S).
Proof.
 refine
  match S with
  | State [] (Return _ v') _ => cast_if (decide (v = v'))
  | _ => right _
  end; abstract first [subst; constructor|by inversion 1].
Defined.
Instance is_undef_state_dec {Ti} (S : state Ti) : Decision (is_undef_state S).
Proof.
 refine match S with State _ (Undef _) _ => left _ | _ => right _ end;
    abstract first [constructor|by inversion 1].
Defined.
 
