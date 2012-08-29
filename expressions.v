(* Copyright (c) 2012, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file defines the syntax and semantics of expressions. Currently we
consider a rather simple expression language without side effects. We give
the semantics by an evaluation function in Coq. Notations for expressions are
defined in the scope [expr_scope]. *)
Require Export memory.

(** * Operations *)
(** We define a data type of binary operations and give an interpretation of
these binary operations as Coq functions. *)
Inductive binop := PlusOp | MultOp | MinusOp | LeOp | EqOp.

Instance binop_eq_dec (o1 o2 : binop) : Decision (o1 = o2).
Proof. solve_decision. Defined.

Definition value_eval_binop (op : binop) (v1 v2 : value) : option value :=
  match op, v1, v2 with
  | PlusOp, int x1, int x2 => Some (int (x1 + x2))
  | MultOp, int x1, int x2 => Some (int (x1 * x2))
  | MinusOp, int x1, int x2 => Some (int (x1 - x2))
  | LeOp, int x1, int x2 => Some (int (Z_decide_rel (≤)%Z x1 x2))
  | EqOp, int x1, int x2 => Some (int (Z_decide_rel (=) x1 x2))
  | EqOp, ptr b1, ptr b2 => Some (int (Z_decide_rel (=) b1 b2))
  | EqOp, null, null => Some (int 1)
  | EqOp, int _, null => Some (int 0)
  | EqOp, null, int _ => Some (int 0)
  | _, _, _ => None
  end%V.

(** * Syntax *)
(** We treat variables as De Bruijn indexes, i.e. the variable [var i]
refers to the [i]th element on the stack. The stack contains indexes to memory
rather than values itself so as to easily enable pointers to local variables.
We use De Bruijn style naming to having to deal with shadowing of variable
names due to block scoped local variables. Especially in the axiomatic semantics
this is a great advantage, as it allows an assertion to refer to both the
shadowed and the original variable without having to do any renaming. *)
Inductive expr : Type :=
  | EVar : nat → expr
  | EVal : value → expr
  | ELoad : expr → expr
  | EBinOp : binop → expr → expr → expr.
Notation stack := (list index) (only parsing).

Instance expr_eq_dec (e1 e2 : expr) : Decision (e1 = e2).
Proof. solve_decision. Defined.

(** We define notations for expressions in the scope [expr_scope]. We overload
some notations already in [value_scope], and define both general and specific
notations for operations, allowing us to to write [int 10 + int 20] instead of
the much longer [val (int 10) @op{PlusOp} val (int 20)]. *)
Delimit Scope expr_scope with E.
Bind Scope expr_scope with expr.
Arguments ELoad _%expr_scope.
Arguments EBinOp _ _%expr_scope _%expr_scope.

Notation "'var' x" := (EVar x) (at level 10) : expr_scope.
Notation "'val' v" := (EVal v) (at level 10) : expr_scope.
Notation "'int' x" := (EVal (int x%Z)) : expr_scope.
Notation "'ptr' b" := (EVal (ptr b%N)) : expr_scope.
Notation "'null'" := (EVal null) : expr_scope.
Notation "'load' e" := (ELoad e) (at level 10) : expr_scope.
Notation "e1 @{ op } e2" := (EBinOp op e1 e2)
  (at level 50, next at level 50) : expr_scope.

Infix "+" := (EBinOp PlusOp) : expr_scope.
Infix "*" := (EBinOp MultOp) : expr_scope.
Infix "-" := (EBinOp MinusOp) : expr_scope.
Infix "≤" := (EBinOp LeOp) : expr_scope.
Infix "=" := (EBinOp EqOp) : expr_scope.

(** * Semantics *)
(** We define the semantics of expressions by structural recursion. *)
Reserved Notation "⟦ e ⟧" (at level 2, format "⟦  e  ⟧").
Fixpoint expr_eval (e : expr) (ρ : stack) (m : mem) : option value :=
  match e with
  | var x =>
    b ← ρ !! x;
    Some (ptr b)%V
  | val v => Some v
  | load e =>
    v ← ⟦ e ⟧ ρ m;
    match v with
    | ptr b => m !! b
    | _ => None
    end%V
  | e1 @{op} e2 =>
    v1 ← ⟦ e1 ⟧ ρ m;
    v2 ← ⟦ e2 ⟧ ρ m;
    value_eval_binop op v1 v2
  end%E
where "⟦ e ⟧" := (expr_eval e).

(** * Theorems *)
(** Evaluation of expressions is preserved under extending the memory and the
stack. *)
Lemma expr_eval_weaken_mem e ρ m1 m2 v :
  m1 ⊆ m2 →
  ⟦ e ⟧ ρ m1 = Some v →
  ⟦ e ⟧ ρ m2 = Some v.
Proof.
  revert v.
  induction e; simpl; intros; simplify_option_bind; auto.
  match goal with
  | |- match ?v with _ => _ end = _ => destruct v as [|[]]; auto
  end.
Qed.

Lemma expr_eval_weaken_stack e ρ ρ' m v :
  ⟦ e ⟧ ρ m = Some v → ⟦ e ⟧ (ρ ++ ρ') m = Some v.
Proof.
  revert v.
  induction e; simpl; intros; simplify_option_bind; auto.
  erewrite list_lookup_weaken by eassumption.
  simplify_option_bind.
Qed.

Lemma expr_eval_subseteq_mem_eq e ρ m1 m2 v1 v2 :
  m1 ⊆ m2 →
  ⟦ e ⟧ ρ m1 = Some v1 →
  ⟦ e ⟧ ρ m2 = Some v2 →
  v1 = v2.
Proof.
  intros ? H1 H2.
  eapply expr_eval_weaken_mem in H1; eauto.
  congruence.
Qed.

Lemma Forall_expr_eval_subseteq_mem_eq es ρ m1 m2 vs1 vs2 :
  m1 ⊆ m2 →
  Forall2 (λ e v, ⟦ e ⟧ ρ m1 = Some v) es vs1 →
  Forall2 (λ e v, ⟦ e ⟧ ρ m2 = Some v) es vs2 →
  vs1 = vs2.
Proof.
  intros ? H1 H2.
  apply (Forall2_unique (λ e v, ⟦ e ⟧ ρ m2 = Some v) es);
    eauto using Forall2_impl, expr_eval_weaken_mem.
  congruence.
Qed.

(** * Tactics *)
(** The tactic [simplify_expr_eval] merges assumptions
[H1 : ⟦ e ⟧ ρ m1 = Some v1] and [H2 : ⟦ e ⟧ ρ m2 = Some v2]  by substituting
[v1] for [v2] and removing the assumption [H1] or [H2] that is on the largest
memory. The tactic may yield goals of the shape [m1 ⊆ m2] if these cannot be
solved automatically. *)
Ltac simplify_expr_eval := repeat
  match goal with
  | H1 : ⟦ ?e ⟧ ?ρ ?m1 = Some ?v1, H2 : ⟦ ?e ⟧ ?ρ ?m2 = Some ?v2 |- _ =>
    let H3 := fresh in
    feed pose proof (expr_eval_subseteq_mem_eq e ρ m1 m2 v1 v2) as H3;
      [ eauto with mem | assumption | assumption | ];
    clear H2; symmetry in H3
  | H1 : Forall2 (λ e v, ⟦ e ⟧ ?ρ ?m1 = Some v) ?es ?vs1,
     H2 : Forall2 (λ e v, ⟦ e ⟧ ?ρ ?m2 = Some v) ?es ?vs2 |- _ =>
    let H3 := fresh in
    feed pose proof (Forall_expr_eval_subseteq_mem_eq es ρ m1 m2 vs1 vs2) as H3;
      [ eauto with mem | assumption | assumption | ];
    clear H2; symmetry in H3
  | _ => progress simplify_equality
  end.
