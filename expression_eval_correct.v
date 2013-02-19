(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** We prove some correspondence results between the denotation semantics for
pure expressions and the small step operational semantics. *)
Require Export smallstep expression_eval.

Lemma ehstep_expr_eval_inv ρ m v e1 m1 e2 m2 :
  ρ ⊢ₕ e1, m1 ⇒ e2, m2 →
  ⟦ e1 ⟧ ρ m = Some v →
  m ⊆ m1 →
  m2 = m1 ∧ ⟦ e2 ⟧ ρ m = Some v.
Proof. by destruct 1; intros; simplify_expr_equality. Qed.

Lemma ehstep_expr_eval ρ e1 m v :
  ⟦ e1 ⟧ ρ m = Some v →
  is_redex e1 →
  ∃ e2, ρ ⊢ₕ e1, m ⇒ e2, m ∧ ⟦ e2 ⟧ ρ m = Some v.
Proof.
  destruct 2;
    repeat match goal with
    | H : is_value _ |- _ => inversion H; subst; clear H
    end;
    intros; simplify_expr_equality; eexists; by (split; [do_ehstep |]).
Qed.

Lemma ehstep_expr_eval_subst ρ (E : ectx) e1 m v :
  ⟦ subst E e1 ⟧ ρ m = Some v →
  is_redex e1 →
  ∃ e2, ρ ⊢ₕ e1, m ⇒ e2, m ∧ ⟦ subst E e2 ⟧ ρ m = Some v.
Proof.
  intros Heval ?.
  destruct (expr_eval_subst_inv _ _ _ _ _ Heval) as [v' [Heval' ?]].
  destruct (ehstep_expr_eval _ _ _ _ Heval') as [e2 [??]]; trivial.
  exists e2. split; [done |].
  rewrite (subst_preserves_expr_eval _ _ e1); congruence.
Qed.

Lemma ehsafe_expr_eval_subst ρ (E : ectx) e m v :
  ⟦ subst E e ⟧ ρ m = Some v →
  is_redex e →
  ρ ⊢ₕ safe e, m.
Proof.
  intros Heval ?.
  destruct (ehstep_expr_eval_subst _ _ _ _ _ Heval) as [? [??]];
    eauto using ehsafe_step.
Qed.

Lemma cred_expr_eval δ e k m v :
  ⟦ e ⟧ (get_stack k) m = Some v →
  ¬is_value e →
  red (cstep_in_ctx δ k) (State k (Expr e) m).
Proof.
  intros Heval He.
  destruct (is_value_is_redex _ He) as [E' [e' [??]]]; subst.
  destruct (expr_eval_subst_inv _ _ _ _ _ Heval) as [v' [??]].
  destruct (ehstep_expr_eval_subst _ _ _ _ _ Heval) as [? [??]]; trivial.
  solve_cred.
Qed.
