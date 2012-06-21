Require Export memory.

Inductive binop := PlusOp | MultOp | LeOp | EqOp.

Instance binop_eq_dec (o1 o2 : binop) : Decision (o1 = o2).
Proof. solve_decision. Defined.

Definition val_true := (≠ 0).
Definition val_false := (= 0).

Lemma val_true_false_dec v : { val_true v } + { val_false v }.
Proof. destruct (decide (v = 0)); intuition. Defined.

Definition denoteBinOpN (op : binop) : N → N → N :=
  match op with
  | PlusOp => N.add
  | MultOp => N.mul
  | LeOp => λ x y, if decide_rel (≤) x y then 1 else 0
  | EqOp => λ x y, if decide_rel (=) x y then 1 else 0
  end.

Inductive expr : Type :=
  | EVar :> nat → expr
  | EVal :> N → expr
  | ELoad : expr → expr
  | EBinOp : binop → expr → expr → expr.

Instance expr_eq_dec (e1 e2 : expr) : Decision (e1 = e2).
Proof. solve_decision. Defined.

Delimit Scope expr_scope with E.
Bind Scope expr_scope with expr.
Notation "'var' x" := (EVar x) (at level 10) : expr_scope.
Notation "'val' v" := (EVal v) (at level 10) : expr_scope.
Notation "'load' e" := (ELoad e) (at level 10) : expr_scope.
Notation "e1 @{ op } e2" := (EBinOp op e1 e2) (at level 50, next at level 50) : expr_scope.

Infix "+" := (EBinOp PlusOp) : expr_scope.
Infix "*" := (EBinOp MultOp) : expr_scope.
Infix "≤" := (EBinOp LeOp) : expr_scope.
Infix "=" := (EBinOp EqOp) : expr_scope.

Notation stack := (list N).
Reserved Notation "⟦ e ⟧" (at level 2, format "⟦  e  ⟧").

Fixpoint expr_eval (e : expr) (ρ : stack) (m : mem) : option N :=
  match e with
  | var x => ρ !! x
  | val v => Some v
  | load e =>
    a ← ⟦ e ⟧ ρ m;
    m !! a
  | e1 @{op} e2 => 
    v1 ← ⟦ e1 ⟧ ρ m;
    v2 ← ⟦ e2 ⟧ ρ m;
    Some (denoteBinOpN op v1 v2)
  end%E
where "⟦ e ⟧" := (expr_eval e).

Lemma expr_eval_weaken_mem e ρ m1 m2 v :
  m1 ⊆ m2 → ⟦ e ⟧ ρ m1 = Some v → ⟦ e ⟧ ρ m2 = Some v.
Proof.
  revert v. induction e; simpl; intros; simplify_options;
    try destruct val_true_false_dec; simplify_options; auto.
Qed.

Lemma expr_eval_weaken_stack e ρ ρ' m v :
  ⟦ e ⟧ ρ m = Some v → ⟦ e ⟧ (ρ ++ ρ') m = Some v.
Proof.
  revert v. induction e; simpl; intros; simplify_options;
    try destruct val_true_false_dec; simplify_options; auto using list_lookup_weaken.
Qed.
