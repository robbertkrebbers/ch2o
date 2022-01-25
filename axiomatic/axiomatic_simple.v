(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export axiomatic_statements axiomatic_expressions.
Local Open Scope ctype_scope.

Definition const_assert `{EnvSpec K}
  (ν : lrval K) (P : assert K) : vassert K := λ ν', (⌜ ν' = ν ⌝ ★ P)%A.
Notation "ν '|' P" := (const_assert ν P) (at level 100) : assert_scope.
Arguments const_assert _ _ _ _ _ _/.

Section axiomatic_expressions_simple.
Context `{EnvSpec K}.
Implicit Types e : expr K.
Implicit Types p : ptr K.
Implicit Types v : val K.
Implicit Types ν : lrval K.

#[global] Instance:
  `{Proper ((≡{Γ,δ}) ==> pointwise_relation _ (≡{Γ,δ})) (const_assert ν)}.
Proof. by intros Γ δ ν P Q HPQ ν'; simpl; rewrite HPQ. Qed.

Lemma ax_expr_weaken_post' Γ δ A P Q Q' e ν :
  Q' ⊆{Γ,δ} Q →
  Γ\ δ\ A ⊨ₑ {{ P }} e {{ ν | Q' }} → Γ\ δ\ A ⊨ₑ {{ P }} e {{ ν | Q }}.
Proof. intros HQ. by apply ax_expr_weaken; simpl; intros; rewrite ?HQ. Qed.
Lemma ax_expr_frame_l' Γ δ A B P Q e ν :
  Γ\ δ\ B ⊨ₑ {{ P }} e {{ ν | Q }} →
  Γ\ δ\ B ⊨ₑ {{ A ★ P }} e {{ ν | A ★ Q }}.
Proof.
  intros; unfold const_assert.
  setoid_rewrite (assoc (R:=(≡{Γ,δ})) (★)%A).
  setoid_rewrite (comm (R:=(≡{Γ,δ})) (★)%A _ A).
  setoid_rewrite <-(assoc (R:=(≡{Γ,δ})) (★)%A).
  by apply ax_expr_frame_l.
Qed.
Lemma ax_expr_frame_r' Γ δ A B P Q e ν :
  Γ\ δ\ B ⊨ₑ {{ P }} e {{ ν | Q }} →
  Γ\ δ\ B ⊨ₑ {{ P ★ A }} e {{ ν | Q ★ A }}.
Proof. rewrite !(comm (★)%A _ A). apply ax_expr_frame_l'. Qed.
Lemma ax_expr_invariant_l' Γ δ A B P Q e ν :
  Γ\ δ\ A ★ B ⊨ₑ {{ P }} e {{ ν | Q }} →
  Γ\ δ\ B ⊨ₑ {{ A ★ P }} e {{ ν | A ★ Q }}.
Proof.
  intros; unfold const_assert.
  setoid_rewrite (assoc (R:=(≡{Γ,δ})) (★)%A).
  setoid_rewrite (comm (R:=(≡{Γ,δ})) (★)%A _ A).
  setoid_rewrite <-(assoc (R:=(≡{Γ,δ})) (★)%A).
  by apply ax_expr_invariant_l.
Qed.
Lemma ax_expr_invariant_r' Γ δ A B P Q e ν :
  Γ\ δ\ A ★ B ⊨ₑ {{ P }} e {{ ν | Q }} →
  Γ\ δ\ B ⊨ₑ {{ P ★ A }} e {{ ν | Q ★ A }}.
Proof. rewrite !(comm (★)%A _ A). apply ax_expr_invariant_l'. Qed.
Lemma ax_expr_invariant_emp' Γ δ A B e ν :
  Γ\ δ\ A ★ B ⊨ₑ {{ emp }} e {{ ν | emp }} →
  Γ\ δ\ B ⊨ₑ {{ A }} e {{ ν | A }}.
Proof.
  intros; rewrite <-(left_id _ (★)%A A); by apply ax_expr_invariant_r'.
Qed.
Lemma ax_var' Γ δ A P x p :
  (A ★ P)%A ⊆{Γ,δ} (var x ⇓ inl p)%A →
  Γ\ δ\ A ⊨ₑ {{ P }} var x {{ inl p | P }}.
Proof.
  rewrite (comm (★)%A); intros; eapply ax_var; eauto.
  simpl; apply assert_and_intro, assert_wand_intro; eauto.
  by rewrite assert_Prop_l by done.
Qed.
Lemma ax_rtol' Γ δ A P Q e v p :
  (A ★ Q)%A ⊆{Γ,δ} (.*(#v) ⇓ inl p)%A →
  Γ\ δ\ A ⊨ₑ {{ P }} e {{ inr v | Q }} →
  Γ\ δ\ A ⊨ₑ {{ P }} .* e {{ inl p | Q }}.
Proof.
  rewrite (comm (★)%A); intros; eapply ax_rtol; eauto.
  intros; apply assert_Prop_intro_l; intros; simplify_equality'.
  apply assert_exist_intro with p, assert_and_intro, assert_wand_intro; auto.
  by rewrite assert_Prop_l by done.
Qed.
Lemma ax_rofl' Γ δ A P Q e p :
  Γ\ δ\ A ⊨ₑ {{ P }} e {{ inl p | Q }} →
  Γ\ δ\ A ⊨ₑ {{ P }} & e {{ inr (ptrV p) | Q }}.
Proof.
  intros; eapply ax_rofl; eauto.
  intros; apply assert_Prop_intro_l; intros; simplify_equality'.
  by rewrite assert_Prop_l by done.
Qed.
Lemma ax_load' Γ δ A P Q e p v :
  Γ\ δ\ A ⊨ₑ {{ P }} e {{ inl p | Q }} →
  (A ★ Q)%A ⊆{Γ,δ} (load (%p) ⇓ inr v)%A →
  Γ\ δ\ A ⊨ₑ {{ P }} load e {{ inr v | Q }}.
Proof.
  rewrite (comm (★)%A); intros; eapply ax_load; eauto. intros; simpl.
  apply assert_Prop_intro_l; intros; simplify_equality'.
  apply assert_exist_intro with v, assert_and_intro, assert_wand_intro; eauto.
  by rewrite assert_Prop_l by done.
Qed.
Lemma ax_assign' Γ δ A P1 P2 Q1 Q2 Q ass e1 e2 μ γ τ p v va v' :
  Γ\ δ\ A ⊨ₑ {{ P1 }} e1 {{ inl p | Q1 }} →
  Γ\ δ\ A ⊨ₑ {{ P2 }} e2 {{ inr v | Q2 }} →
  (A ★ Q1 ★ Q2)%A ⊆{Γ,δ} (assert_assign p v ass τ va v')%A →
  (Q1 ★ Q2)%A ⊆{Γ,δ} (%p ↦{μ,γ} - : τ ★
    (%p ↦{μ,perm_lock γ} # (freeze true va) : τ -★ Q))%A →
  Some Writable ⊆ perm_kind γ →
  Γ\ δ\ A ⊨ₑ {{ P1 ★ P2 }} e1 ::={ass} e2 {{ inr v' | Q }}.
Proof.
  rewrite (comm (★)%A A); intros; eapply ax_assign; eauto.
  intros; simpl; rewrite <-!(assoc (★)%A).
  apply assert_Prop_intro_l; intros; simplify_equality'.
  rewrite (comm (★)%A _ Q2), (assoc (★)%A Q1).
  apply assert_Prop_intro_r; intros; simplify_equality'.
  apply assert_exist_intro with va, assert_exist_intro with v',
    assert_and_intro, assert_wand_intro; eauto.
  rewrite assert_Prop_l by done; eauto.
Qed.
Lemma ax_assign_r' Γ δ A P Q Q' ass e1 e2 μ γ τ p v va v' :
  Γ\ δ\ A ⊨ₑ {{ emp }} e1 {{ inl p | emp }} →
  Γ\ δ\ A ⊨ₑ {{ P }} e2 {{ inr v | Q }} →
  (A ★ Q)%A ⊆{Γ,δ} (assert_assign p v ass τ va v')%A →
  Q ⊆{Γ,δ} (%p ↦{μ,γ} - : τ ★
    (%p ↦{μ,perm_lock γ} # (freeze true va) : τ -★ Q'))%A →
  Some Writable ⊆ perm_kind γ →
  Γ\ δ\ A ⊨ₑ {{ P }} e1 ::={ass} e2 {{ inr v' | Q' }}.
Proof.
  intros. rewrite <-(left_id _ (★)%A P).
  eapply ax_assign'; rewrite ?(left_id _ (★)%A); eauto.
Qed.
Lemma ax_eltl' Γ δ A P Q e rs p p' :
  Γ\ δ\ A ⊨ₑ {{ P }} e {{ inl p | Q }} →
  (A ★ Q)%A ⊆{Γ,δ} (%p %> rs ⇓ inl p')%A →
  Γ\ δ\ A ⊨ₑ {{ P }} e %> rs {{ inl p' | Q }}.
Proof.
  rewrite (comm (★)%A); intros; eapply ax_eltl; eauto.
  intros; apply assert_Prop_intro_l; intros; simplify_equality'.
  apply assert_exist_intro with p', assert_and_intro, assert_wand_intro; auto.
  by rewrite assert_Prop_l by done.
Qed.
Lemma ax_eltr' Γ δ A P Q e rs v v' :
  Γ\ δ\ A ⊨ₑ {{ P }} e {{ inr v | Q }} →
  (A ★ Q)%A ⊆{Γ,δ} (#v #> rs ⇓ inr v')%A →
  Γ\ δ\ A ⊨ₑ {{ P }} e #> rs {{ inr v' | Q }}.
Proof.
  rewrite (comm (★)%A); intros; eapply ax_eltr; eauto.
  intros; apply assert_Prop_intro_l; intros; simplify_equality'.
  apply assert_exist_intro with v', assert_and_intro, assert_wand_intro; auto.
  by rewrite assert_Prop_l by done.
Qed.
Lemma ax_insert' Γ δ A P1 P2 Q1 Q2 e1 e2 r v1 v2 v :
  Γ\ δ\ A ⊨ₑ {{ P1 }} e1 {{ inr v1 | Q1 }} →
  Γ\ δ\ A ⊨ₑ {{ P2 }} e2 {{ inr v2 | Q2 }} →
  (A ★ Q1 ★ Q2)%A ⊆{Γ,δ} (#[r:=#v1] (#v2) ⇓ inr v)%A →
  Γ\ δ\ A ⊨ₑ {{ P1 ★ P2 }} #[r:=e1] e2 {{ inr v | Q1 ★ Q2 }}.
Proof.
  rewrite (comm (★)%A); intros; eapply ax_insert; eauto.
  intros; simpl; rewrite <-!(assoc (★)%A).
  apply assert_Prop_intro_l; intros; simplify_equality'.
  rewrite (comm (★)%A _ Q2), (assoc (★)%A Q1).
  apply assert_Prop_intro_r; intros; simplify_equality'.
  apply assert_exist_intro with v, assert_and_intro, assert_wand_intro; auto.
  by rewrite assert_Prop_l by done.
Qed.
Lemma ax_free' Γ δ A P Q e o τ n τp :
  Γ\ δ\ A ⊨ₑ {{ P }} e {{ inl (Ptr (Addr o [RArray 0 τ n] 0 (τ.[n]) τ τp)) |
    % Ptr (addr_top o (τ.[n])) ↦{true,perm_full} - : (τ.[n]) ★ Q }} →
  Γ\ δ\ A ⊨ₑ {{ P }} free e {{ inr voidV | Q }}.
Proof.
  intros; eapply ax_free with _ τ; eauto.
  intros; apply assert_Prop_intro_l; intros; simplify_equality'.
  apply assert_exist_intro with o, assert_exist_intro with n,
    assert_exist_intro with τp.
  by rewrite !(assert_Prop_l _ _ (_ = _)) by done.
Qed.
Lemma ax_unop' Γ δ A P Q op e v v' :
  Γ\ δ\ A ⊨ₑ {{ P }} e {{ inr v | Q }} →
  (A ★ Q)%A ⊆{Γ,δ} (.{op} #v ⇓ inr v')%A →
  Γ\ δ\ A ⊨ₑ {{ P }} .{op} e {{ inr v' | Q }}.
Proof.
  rewrite (comm (★)%A); intros; eapply ax_unop; eauto.
  intros; apply assert_Prop_intro_l; intros; simplify_equality'.
  apply assert_exist_intro with v', assert_and_intro, assert_wand_intro; auto.
  by rewrite assert_Prop_l by done.
Qed.
Lemma ax_binop' Γ δ A P1 P2 Q1 Q2 op e1 e2 v1 v2 v :
  Γ\ δ\ A ⊨ₑ {{ P1 }} e1 {{ inr v1 | Q1 }} →
  Γ\ δ\ A ⊨ₑ {{ P2 }} e2 {{ inr v2 | Q2 }} →
  (A ★ Q1 ★ Q2)%A ⊆{Γ,δ} (# v1 .{op} # v2 ⇓ inr v)%A →
  Γ\ δ\ A ⊨ₑ {{ P1 ★ P2 }} e1 .{op} e2 {{ inr v | Q1 ★ Q2 }}.
Proof.
  rewrite (comm (★)%A); intros; eapply ax_binop; eauto.
  intros; simpl; rewrite <-!(assoc (★)%A).
  apply assert_Prop_intro_l; intros; simplify_equality'.
  rewrite (comm (★)%A _ Q2), (assoc (★)%A Q1).
  apply assert_Prop_intro_r; intros; simplify_equality'.
  apply assert_exist_intro with v, assert_and_intro, assert_wand_intro; auto.
  by rewrite assert_Prop_l by done.
Qed.
Lemma ax_binop_r' Γ δ A P Q op e1 e2 v1 v2 v :
  Γ\ δ\ A ⊨ₑ {{ emp }} e1 {{ inr v1 | emp }} →
  Γ\ δ\ A ⊨ₑ {{ P }} e2 {{ inr v2 | Q }} →
  (A ★ Q)%A ⊆{Γ,δ} (# v1 .{op} # v2 ⇓ inr v)%A →
  Γ\ δ\ A ⊨ₑ {{ P }} e1 .{op} e2 {{ inr v | Q }}.
Proof.
  intros. rewrite <-(left_id _ (★)%A P), <-(left_id _ (★)%A Q).
  eapply ax_binop'; rewrite ?(left_id _ (★)%A); eauto.
Qed.
Lemma ax_cast' Γ δ A P Q σ e v v' :
  Γ\ δ\ A ⊨ₑ {{ P }} e {{ inr v | Q }} →
  (A ★ Q)%A ⊆{Γ,δ} (cast{σ} (#v) ⇓ inr v')%A →
  Γ\ δ\ A ⊨ₑ {{ P }} cast{σ} e {{ inr v' | Q }}.
Proof.
  rewrite (comm (★)%A); intros; eapply ax_cast; eauto.
  intros; apply assert_Prop_intro_l; intros; simplify_equality'.
  apply assert_exist_intro with v', assert_and_intro, assert_wand_intro; auto.
  by rewrite assert_Prop_l by done.
Qed.
Lemma ax_expr_if' Γ δ A P P' P'' Q e e1 e2 vb :
  Γ\ δ\ A ⊨ₑ {{ P }} e {{ inr (VBase vb) | P' }} →
  (A ★ P')%A ⊆{Γ,δ} (.{NotOp} #VBase vb ⇓ -)%A →
  P' ⊆{Γ,δ} (P''◊)%A →
  Γ\ δ\ A ⊨ₑ {{ ⌜ ¬base_val_is_0 vb ⌝ ★ P'' }} e1 {{ Q }} →
  Γ\ δ\ A ⊨ₑ {{ ⌜ base_val_is_0 vb ⌝ ★ P'' }} e2 {{ Q }} →
  Γ\ δ\ A ⊨ₑ {{ P }} if{e} e1 else e2 {{ Q }}.
Proof.
  rewrite (comm (★)%A); intros; eapply ax_expr_if; eauto.
  * intros; simpl. rewrite (comm (★)%A), <-(assoc (★)%A).
    by apply assert_Prop_intro_l; intros; simplify_equality'.
  * intros; apply assert_Prop_intro_l; intros; simplify_equality'.
    by rewrite assert_Prop_l by done.
  * intros; apply assert_Prop_intro_l; intros; simplify_equality'.
    by rewrite assert_Prop_l by done.
Qed.
Lemma ax_expr_comma' Γ δ A P P' Q e1 e2 ν :
  Γ\ δ\ A ⊨ₑ {{ P }} e1 {{ ν | P' ◊ }} →
  Γ\ δ\ A ⊨ₑ {{ P' }} e2 {{ Q }} →
  Γ\ δ\ A ⊨ₑ {{ P }} e1 ,, e2 {{ Q }}.
Proof.
  intros; eapply ax_expr_comma; eauto; eapply ax_expr_weaken_post; eauto.
  by intros; apply assert_Prop_intro_l.
Qed.
Lemma ax_do' Γ δ R J T C P Q Q' e ν :
  Γ\ δ\ emp ⊨ₑ {{ P }} e {{ ν | Q }} →
  Q ⊆{Γ,δ} (Q'◊)%A →
  Γ\ δ\ R\ J\ T\ C ⊨ₛ {{ P }} !e {{ Q' }}.
Proof.
  intros. eapply ax_do, ax_expr_weaken_post; eauto.
  by intros; apply assert_Prop_intro_l; intros; simplify_equality'.
Qed.
Lemma ax_if' Γ δ R J T C P P' P'' Q e s1 s2 vb :
  Γ\ δ\ emp ⊨ₑ {{ P }} e {{ inr (VBase vb) | P' }} →
  P' ⊆{Γ,δ} (.{NotOp} #VBase vb ⇓ -)%A →
  P' ⊆{Γ,δ} (P''◊)%A →
  Γ\ δ\ R\ J\ T\ C ⊨ₛ {{ ⌜ ¬base_val_is_0 vb ⌝ ★ P'' }} s1 {{ Q }} →
  Γ\ δ\ R\ J\ T\ C ⊨ₛ {{ ⌜ base_val_is_0 vb ⌝ ★ P'' }} s2 {{ Q }} →
  Γ\ δ\ R\ J\ T\ C ⊨ₛ {{ P }} if{e} s1 else s2 {{ Q }}.
Proof.
  intros; eapply ax_if; eauto.
  * by intros; apply assert_Prop_intro_l; intros; simplify_equality'.
  * intros; apply assert_Prop_intro_l; intros; simplify_equality'.
    by rewrite assert_Prop_l by done.
  * intros; apply assert_Prop_intro_l; intros; simplify_equality'.
    by rewrite assert_Prop_l by done.
Qed.
Lemma ax_if'' Γ δ R J T C P Q e s1 s2 vb :
  UnlockIndep P →
  Γ\ δ\ emp ⊨ₑ {{ P }} e {{ inr (VBase vb) | P }} →
  P ⊆{Γ,δ} (.{NotOp} #VBase vb ⇓ -)%A →
  Γ\ δ\ R\ J\ T\ C ⊨ₛ {{ ⌜ ¬base_val_is_0 vb ⌝ ★ P }} s1 {{ Q }} →
  Γ\ δ\ R\ J\ T\ C ⊨ₛ {{ ⌜ base_val_is_0 vb ⌝ ★ P }} s2 {{ Q }} →
  Γ\ δ\ R\ J\ T\ C ⊨ₛ {{ P }} if{e} s1 else s2 {{ Q }}.
Proof. intros ???; eapply ax_if'; eauto. Qed.
End axiomatic_expressions_simple.
