Require Export memory.

Inductive binOp := PlusOp | MultOp | LeOp | EqOp.

Instance binOp_eq_dec (o1 o2 : binOp) : Decision (o1 = o2).
Proof. solve_decision. Defined.

Definition val_true := (≠ 0).
Definition val_false := (= 0).

Lemma val_true_false_dec v : { val_true v } + { val_false v }.
Proof. destruct (decide (v = 0)); intuition. Defined.

Definition denoteBinOpN (op : binOp) : N → N → N :=
  match op with
  | PlusOp => N.add
  | MultOp => N.mul
  | LeOp => λ x y, if decide_rel (≤) x y then 1 else 0
  | EqOp => λ x y, if decide_rel (=) x y then 1 else 0
  end.

(*
Definition denoteBinOp (op : binOp) (v w : val) : option val :=
  match op, v, w with
  | PlusOp, VInt x, VInt y => Some $ VInt (Z.add x y)
  | MultOp, VInt x, VInt y => Some $ VInt (Z.mul x y)
  | LeOp, VInt x, VInt y => Some $ if decide_rel (≤) x y then VInt 1 else VInt 0
  | EqOp, VInt x, VInt y => Some $ if decide_rel (=) x y then VInt 1 else VInt 0
  | PlusOp, VPointer p, VInt y => VPointer <$> pointer_move y p
  | _,_,_ => None
  end.
*)

Inductive expr : Type :=
  | EVar :> nat → expr
  | EConst :> N → expr
  | ELoad : expr → expr
  | EBinOp : binOp → expr → expr → expr.

Instance expr_eq_dec (e1 e2 : expr) : Decision (e1 = e2).
Proof. solve_decision. Defined.

Delimit Scope expr_scope with E.
Bind Scope expr_scope with expr.
Infix "+" := (EBinOp PlusOp) : expr_scope.
Infix "*" := (EBinOp MultOp) : expr_scope.
Infix "≤" := (EBinOp LeOp) : expr_scope.
Infix "=" := (EBinOp EqOp) : expr_scope.
Notation "'load' e" := (ELoad e) (at level 20) : expr_scope.

Notation stack := (list N).
Reserved Notation "⟦ e ⟧" (at level 2, format "⟦  e  ⟧").

Fixpoint expr_eval (e : expr) (ρ : stack) (m : mem) : option N :=
  match e with
  | EVar x => ρ !! x
  | EConst v => Some v
  | load e =>
    b ← ⟦ e ⟧ ρ m;
    m !! b
  | EBinOp op e1 e2 => 
    v1 ← ⟦ e1 ⟧ ρ m;
    v2 ← ⟦ e2 ⟧ ρ m;
    Some (denoteBinOpN op v1 v2)
  end%E
where "⟦ e ⟧" := (expr_eval e).

Lemma expr_eval_weaken_mem e ρ m1 m2 v :
  m1 ⊆ m2 → ⟦ e ⟧ ρ m1 = Some v → ⟦ e ⟧ ρ m2 = Some v.
Proof.
  intros ?. revert v. induction e; simpl; repeat
    match goal with
    | |- context[ ⟦ ?e ⟧ ρ m1 ] =>destruct (⟦ e ⟧ ρ m1); try discriminate
    | H : context[ ⟦ _ ⟧ ρ m2 = Some _] |- _  => erewrite H; clear H
    end; eauto.
Qed.

Lemma expr_eval_weaken_stack e ρ ρ' m v :
  ⟦ e ⟧ ρ m = Some v → ⟦ e ⟧ (ρ ++ ρ') m = Some v.
Proof.
  revert v. induction e; simpl; simpl; repeat
    match goal with
    | |- context[ ⟦ ?e ⟧ ρ m ] =>destruct (⟦ e ⟧ ρ m); try discriminate
    | H : context[ ⟦ _ ⟧ (ρ ++ _) m = Some _] |- _  => erewrite H; clear H
    end; eauto using list_lookup_weaken.
Qed.
