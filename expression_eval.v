(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file defines a denotational semantics [⟦ _ ⟧] for pure expressions as
an expression evaluator. *)
Require Export expressions abstract_memory.

Reserved Notation "⟦ e ⟧" (format "⟦  e  ⟧").

Section expression_eval.
Context `{Permissions P}.

(** * Definition of the semantics *)
Fixpoint expr_eval (e : expr) (ρ : stack) (m : amem P) : option value :=
  match e with
  | var x =>
     b ← ρ !! x;
     Some (ptr b)%V
  | load e =>
     v ← ⟦ e ⟧ ρ m;
     a ← maybe_ptr v;
     m !! a
  | val@{_} v => Some v
  | ⊙{op} e =>
     v ← ⟦ e ⟧ ρ m;
     eval_unop op v
  | el ⊙{op} er =>
     vl ← ⟦ el ⟧ ρ m;
     vr ← ⟦ er ⟧ ρ m;
     eval_binop op vl vr
  | _ => None
  end%E
where "⟦ e ⟧" := (expr_eval e) : C_scope.

(** * Theorems *)
(** We prove that we only give a semantics to pure expressions. The converse
of this property is not true, as pure expressions may still exhibit undefined
behavior. *)
Lemma expr_eval_is_pure ρ m e v :
  ⟦ e ⟧ ρ m = Some v → is_pure e.
Proof.
  revert v.
  induction e; intros; simplify_option_equality; constructor; eauto.
Qed.

(** Evaluation of expressions is preserved under extensions of the memory. *)
Lemma expr_eval_weaken_mem ρ m1 m2 e v :
  ⟦ e ⟧ ρ m1 = Some v →
  m1 ⊆ m2 →
  ⟦ e ⟧ ρ m2 = Some v.
Proof.
  revert v. induction e; intros; simplify_option_equality; eauto.
  eapply mem_lookup_weaken; eauto.
Qed.

Lemma expr_eval_weaken_inv ρ m1 m2 e v1 v2 :
  ⟦ e ⟧ ρ m1 = Some v1 →
  m1 ⊆ m2 →
  ⟦ e ⟧ ρ m2 = Some v2 →
  v1 = v2.
Proof.
  intros ? Hm1 Hm2.
  erewrite (expr_eval_weaken_mem _ m1 m2) in Hm2 by eauto.
  congruence.
Qed.

Lemma Forall_expr_eval_weaken_inv es ρ m1 m2 vs1 vs2 :
  Forall2 (λ e v, ⟦ e ⟧ ρ m1 = Some v) es vs1 →
  m1 ⊆ m2 →
  Forall2 (λ e v, ⟦ e ⟧ ρ m2 = Some v) es vs2 →
  vs1 = vs2.
Proof.
  intros ? Hm1 ?.
  apply (Forall2_unique (λ e v, ⟦ e ⟧ ρ m2 = Some v) es).
  * apply Forall2_impl with (λ e v, ⟦ e ⟧ ρ m1 = Some v);
      eauto using expr_eval_weaken_mem.
  * done.
  * congruence.
Qed.

(** Evaluation of expressions is preserved under unlocking. *)
Lemma expr_eval_unlock Ω ρ m e v :
  ⟦ e ⟧ ρ m = Some v →
  ⟦ e ⟧ ρ (mem_unlock Ω m) = Some v.
Proof.
  revert v. induction e; intros; simplify_option_equality; eauto.
  eapply mem_lookup_unlock; eauto.
Qed.

(** Evaluation of expressions is preserved under extensions of the stack. *)
Lemma expr_eval_weaken_stack ρ ρ' m e v :
  ⟦ e ⟧ ρ m = Some v →
  ⟦ e ⟧ (ρ ++ ρ') m = Some v.
Proof.
  revert v. induction e; intros; simplify_option_equality; intuition.
  rewrite lookup_app_l.
  * by simplify_option_equality.
  * eauto using lookup_lt_length_alt.
Qed.

(** Pure expressions without variables do not refer to the stack, so their
semantics is preserved under changes to the stack. *)
Lemma expr_var_free_stack_indep ρ1 ρ2 m e :
  expr_vars e ≡ ∅ →
  ⟦ e ⟧ ρ1 m = ⟦ e ⟧ ρ2 m.
Proof.
  induction e; simpl; intro; decompose_empty; repeat
    match goal with
    | H : expr_vars _ ≡ ∅ → ⟦ _ ⟧ _ _ = _ |- _ => rewrite H
    | _ => done
    | |- mbind (M:=option) _ ?o = mbind (M:=option) _ ?o =>
       destruct o; simpl
    | _ => destruct (value_true_false_dec _)
    end.
Qed.

(** Pure expressions without loads do not refer to the memory, so their
semantics is preserved under changes to the memory. *)
Lemma expr_load_free_mem_indep ρ m1 m2 e :
  load_free e →
  ⟦ e ⟧ ρ m1 = ⟦ e ⟧ ρ m2.
Proof.
  induction 1; simpl; repeat
    match goal with
    | H : ⟦ _ ⟧ _ _ = _ |- _ => rewrite H
    | _ => done
    | |- mbind (M:=option) _ ?o = mbind (M:=option) _ ?o =>
       destruct o; simpl
    | _ => destruct (value_true_false_dec _)
    end.
Qed.

(** Lifting DeBruijn indexes distributes over expression evaluation. *)
Lemma expr_eval_lift ρ e m :
  ⟦ e↑ ⟧ ρ m = ⟦ e ⟧ (tail ρ) m.
Proof.
  induction e; intros; simpl; repeat
    match goal with
    | H : ⟦ _↑ ⟧ _ _ = _ |- _ => rewrite H
    | |- _ ← ?o; ⟦ if _ then _ else _ ⟧ _ _ = _ =>
      destruct o; simpl; try destruct (value_true_false_dec _)
    end; auto.
  by rewrite <-lookup_tail.
Qed.

(** If an expression has a semantics, then each sub-expression has a semantics
as well. *)
Lemma expr_eval_subst_inv (E : ectx) e ρ m v :
  ⟦ subst E e ⟧ ρ m = Some v →
  ∃ v', ⟦ e ⟧ ρ m = Some v' ∧ ⟦ subst E (val v')%E ⟧ ρ m = Some v.
Proof.
  revert v. induction E as [|E' E IH] using rev_ind;
    simpl; intros v; [by eauto |].
  setoid_rewrite subst_snoc.
  intros; destruct E'; simplify_option_equality;
    naive_solver (by eauto || by simplify_option_equality).
Qed.

Lemma subst_preserves_expr_eval (E : ectx) e1 e2 ρ m :
  ⟦ e1 ⟧ ρ m = ⟦ e2 ⟧ ρ m →
  ⟦ subst E e1 ⟧ ρ m = ⟦ subst E e2 ⟧ ρ m.
Proof.
  intros. induction E as [|E' ? IH] using rev_ind; [done |].
  destruct E'; rewrite ?subst_snoc; simpl; rewrite ?IH; auto.
Qed.
End expression_eval.

Notation "⟦ e ⟧" := (expr_eval e) : C_scope.

(** * Tactics *)
Tactic Notation "simplify_expr_equality" "by" tactic3(tac) := repeat
  match goal with
  | _ => progress simplify_mem_equality by tac
  | _ => progress simplify_option_equality by tac
  | Ht : value_true ?v, Hf : value_false ?v |- _ =>
    destruct (value_true_false v Ht Hf)
  | H : maybe_ptr ?v = Some _ |- _ =>
    apply maybe_ptr_Some in H
  | H : context [ value_true_false_dec ?v ] |- _ =>
    destruct (value_true_false_dec v)
  | |- context [ value_true_false_dec ?v ] =>
    destruct (value_true_false_dec v)
  | H1 : ⟦ ?e ⟧ ?ρ ?m1 = Some ?v1, H2 : ⟦ ?e ⟧ ?ρ ?m2 = Some ?v2 |- _ =>
    let H3 := fresh in
    feed pose proof (expr_eval_weaken_inv e ρ m1 m2 v1 v2) as H3;
      [done | by tac | done | ];
    clear H2; symmetry in H3
  end.
Tactic Notation "simplify_expr_equality" :=
  simplify_expr_equality by eauto with simpl_mem.
