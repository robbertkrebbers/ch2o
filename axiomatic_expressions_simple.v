(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Import axiomatic_expressions.
Local Open Scope ctype_scope.

Definition const_assert `{EnvSpec K}
  (ν : lrval K) (P : assert K) : vassert K := λ ν', (⌜ ν' = ν ⌝ ★ P)%A.
Notation "ν '|' P" := (const_assert ν P) (at level 100).
Arguments const_assert _ _ _ _ _ _/.

Section axiomatic_expressions_simple.
Context `{EnvSpec K}.
Implicit Types e : expr K.
Implicit Types a : addr K.
Implicit Types v : val K.
Implicit Types ν : lrval K.

Global Instance:
  Proper ((≡{Γ}) ==> pointwise_relation _ (≡{Γ})) (const_assert ν).
Proof. by intros Γ ν P Q HPQ ν'; simpl; rewrite HPQ. Qed.

Lemma ax_expr_weaken_post' Γ δ A P Q Q' e ν :
  Q' ⊆{Γ} Q →
  Γ\ δ\ A ⊨ₑ {{ P }} e {{ ν | Q' }} → Γ\ δ\ A ⊨ₑ {{ P }} e {{ ν | Q }}.
Proof. intros HQ. by apply ax_expr_weaken; simpl; intros; rewrite ?HQ. Qed.
Lemma ax_expr_frame_l' Γ δ A B P Q e ν :
  Γ\ δ\ B ⊨ₑ {{ P }} e {{ ν | Q }} →
  Γ\ δ\ B ⊨ₑ {{ A ★ P }} e {{ ν | A ★ Q }}.
Proof.
  intros; unfold const_assert.
  setoid_rewrite (associative (R:=(≡{Γ})) (★)%A).
  setoid_rewrite (commutative (R:=(≡{Γ})) (★)%A _ A).
  setoid_rewrite <-(associative (R:=(≡{Γ})) (★)%A).
  by apply ax_expr_frame_l.
Qed.
Lemma ax_expr_frame_r' Γ δ A B P Q e ν :
  Γ\ δ\ B ⊨ₑ {{ P }} e {{ ν | Q }} →
  Γ\ δ\ B ⊨ₑ {{ P ★ A }} e {{ ν | Q ★ A }}.
Proof. rewrite !(commutative (★)%A _ A). apply ax_expr_frame_l'. Qed.
Lemma ax_expr_invariant_l' Γ δ A B P Q e ν :
  Γ\ δ\ A ★ B ⊨ₑ {{ P }} e {{ ν | Q }} →
  Γ\ δ\ B ⊨ₑ {{ A ★ P }} e {{ ν | A ★ Q }}.
Proof.
  intros; unfold const_assert.
  setoid_rewrite (associative (R:=(≡{Γ})) (★)%A).
  setoid_rewrite (commutative (R:=(≡{Γ})) (★)%A _ A).
  setoid_rewrite <-(associative (R:=(≡{Γ})) (★)%A).
  by apply ax_expr_invariant_l.
Qed.
Lemma ax_expr_invariant_r' Γ δ A B P Q e ν :
  Γ\ δ\ A ★ B ⊨ₑ {{ P }} e {{ ν | Q }} →
  Γ\ δ\ B ⊨ₑ {{ P ★ A }} e {{ ν | Q ★ A }}.
Proof. rewrite !(commutative (★)%A _ A). apply ax_expr_invariant_l'. Qed.
Lemma ax_expr_invariant_emp' Γ δ A B e ν :
  Γ\ δ\ A ★ B ⊨ₑ {{ emp }} e {{ ν | emp }} →
  Γ\ δ\ B ⊨ₑ {{ A }} e {{ ν | A }}.
Proof.
  intros; rewrite <-(left_id _ (★)%A A); by apply ax_expr_invariant_r'.
Qed.
Lemma ax_var' Γ δ A P x a :
  (A ★ P)%A ⊆{Γ} (var x ⇓ inl a)%A →
  Γ\ δ\ A ⊨ₑ {{ P }} var x {{ inl a | P }}.
Proof.
  rewrite (commutative (★)%A); intros; eapply ax_var; eauto.
  simpl; apply assert_and_intro, assert_wand_intro; eauto.
  by rewrite assert_Prop_l by done.
Qed.
Lemma ax_rtol' Γ δ A P Q e v a :
  (A ★ Q)%A ⊆{Γ} (.*(#v) ⇓ inl a)%A →
  Γ\ δ\ A ⊨ₑ {{ P }} e {{ inr v | Q }} →
  Γ\ δ\ A ⊨ₑ {{ P }} .* e {{ inl a | Q }}.
Proof.
  rewrite (commutative (★)%A); intros; eapply ax_rtol; eauto.
  intros; apply assert_Prop_intro_l; intros; simplify_equality'.
  apply assert_exist_intro with a, assert_and_intro, assert_wand_intro; auto.
  by rewrite assert_Prop_l by done.
Qed.
Lemma ax_rofl' Γ δ A P Q e a :
  Γ\ δ\ A ⊨ₑ {{ P }} e {{ inl a | Q }} →
  Γ\ δ\ A ⊨ₑ {{ P }} & e {{ inr (ptrV (Ptr a)) | Q }}.
Proof.
  intros; eapply ax_rofl; eauto.
  intros; apply assert_Prop_intro_l; intros; simplify_equality'.
  by rewrite assert_Prop_l by done.
Qed.
Lemma ax_load' Γ δ A P Q e a v :
  (A ★ Q)%A ⊆{Γ} (load (%a) ⇓ inr v)%A →
  Γ\ δ\ A ⊨ₑ {{ P }} e {{ inl a | Q }} →
  Γ\ δ\ A ⊨ₑ {{ P }} load e {{ inr v | Q }}.
Proof.
  rewrite (commutative (★)%A); intros; eapply ax_load; eauto.
  intros; apply assert_Prop_intro_l; intros; simplify_equality'.
  apply assert_exist_intro with v, assert_and_intro, assert_wand_intro; auto.
  by rewrite assert_Prop_l by done.
Qed.
Lemma ax_assign' Γ δ A P1 P2 Q1 Q2 Q ass e1 e2 μ x τ a v va v' :
  Some Writable ⊆ perm_kind x →
  (A ★ Q1 ★ Q2)%A ⊆{Γ} (assert_assign a v ass τ va v')%A →
  (Q1 ★ Q2)%A ⊆{Γ} (%a ↦{μ,x} - : τ ★
    (%a ↦{μ,perm_lock x} # (freeze true va) : τ -★ Q))%A →
  Γ\ δ\ A ⊨ₑ {{ P1 }} e1 {{ inl a | Q1 }} →
  Γ\ δ\ A ⊨ₑ {{ P2 }} e2 {{ inr v | Q2 }} →
  Γ\ δ\ A ⊨ₑ {{ P1 ★ P2 }} e1 ::={ass} e2 {{ inr v' | Q }}.
Proof.
  rewrite (commutative (★)%A A); intros; eapply ax_assign; eauto.
  intros; simpl; rewrite <-!(associative (★)%A).
  apply assert_Prop_intro_l; intros; simplify_equality'.
  rewrite (commutative (★)%A _ Q2), (associative (★)%A Q1).
  apply assert_Prop_intro_r; intros; simplify_equality'.
  apply assert_exist_intro with va, assert_exist_intro with v',
    assert_and_intro, assert_wand_intro; eauto.
  rewrite assert_Prop_l by done; eauto.
Qed.
Lemma ax_eltl' Γ δ A P Q e rs a a' :
  (A ★ Q)%A ⊆{Γ} (%a %> rs ⇓ inl a')%A →
  Γ\ δ\ A ⊨ₑ {{ P }} e {{ inl a | Q }} →
  Γ\ δ\ A ⊨ₑ {{ P }} e %> rs {{ inl a' | Q }}.
Proof.
  rewrite (commutative (★)%A); intros; eapply ax_eltl; eauto.
  intros; apply assert_Prop_intro_l; intros; simplify_equality'.
  apply assert_exist_intro with a', assert_and_intro, assert_wand_intro; auto.
  by rewrite assert_Prop_l by done.
Qed.
Lemma ax_eltr' Γ δ A P Q e rs v v' :
  (A ★ Q)%A ⊆{Γ} (#v #> rs ⇓ inr v')%A →
  Γ\ δ\ A ⊨ₑ {{ P }} e {{ inr v | Q }} →
  Γ\ δ\ A ⊨ₑ {{ P }} e #> rs {{ inr v' | Q }}.
Proof.
  rewrite (commutative (★)%A); intros; eapply ax_eltr; eauto.
  intros; apply assert_Prop_intro_l; intros; simplify_equality'.
  apply assert_exist_intro with v', assert_and_intro, assert_wand_intro; auto.
  by rewrite assert_Prop_l by done.
Qed.
Lemma ax_insert' Γ δ A P1 P2 Q1 Q2 e1 e2 r v1 v2 v :
  (A ★ Q1 ★ Q2)%A ⊆{Γ} (#[r:=#v1] (#v2) ⇓ inr v)%A →
  Γ\ δ\ A ⊨ₑ {{ P1 }} e1 {{ inr v1 | Q1 }} →
  Γ\ δ\ A ⊨ₑ {{ P2 }} e2 {{ inr v2 | Q2 }} →
  Γ\ δ\ A ⊨ₑ {{ P1 ★ P2 }} #[r:=e1] e2 {{ inr v | Q1 ★ Q2 }}.
Proof.
  rewrite (commutative (★)%A); intros; eapply ax_insert; eauto.
  intros; simpl; rewrite <-!(associative (★)%A).
  apply assert_Prop_intro_l; intros; simplify_equality'.
  rewrite (commutative (★)%A _ Q2), (associative (★)%A Q1).
  apply assert_Prop_intro_r; intros; simplify_equality'.
  apply assert_exist_intro with v, assert_and_intro, assert_wand_intro; auto.
  by rewrite assert_Prop_l by done.
Qed.
Lemma ax_unop' Γ δ A P Q op e v v' :
  (A ★ Q)%A ⊆{Γ} (@{op} #v ⇓ inr v')%A →
  Γ\ δ\ A ⊨ₑ {{ P }} e {{ inr v | Q }} →
  Γ\ δ\ A ⊨ₑ {{ P }} @{op} e {{ inr v' | Q }}.
Proof.
  rewrite (commutative (★)%A); intros; eapply ax_unop; eauto.
  intros; apply assert_Prop_intro_l; intros; simplify_equality'.
  apply assert_exist_intro with v', assert_and_intro, assert_wand_intro; auto.
  by rewrite assert_Prop_l by done.
Qed.
Lemma ax_binop' Γ δ A P1 P2 Q1 Q2 op e1 e2 v1 v2 v :
  (A ★ Q1 ★ Q2)%A ⊆{Γ} (# v1 @{op} # v2 ⇓ inr v)%A →
  Γ\ δ\ A ⊨ₑ {{ P1 }} e1 {{ inr v1 | Q1 }} →
  Γ\ δ\ A ⊨ₑ {{ P2 }} e2 {{ inr v2 | Q2 }} →
  Γ\ δ\ A ⊨ₑ {{ P1 ★ P2 }} e1 @{op} e2 {{ inr v | Q1 ★ Q2 }}.
Proof.
  rewrite (commutative (★)%A); intros; eapply ax_binop; eauto.
  intros; simpl; rewrite <-!(associative (★)%A).
  apply assert_Prop_intro_l; intros; simplify_equality'.
  rewrite (commutative (★)%A _ Q2), (associative (★)%A Q1).
  apply assert_Prop_intro_r; intros; simplify_equality'.
  apply assert_exist_intro with v, assert_and_intro, assert_wand_intro; auto.
  by rewrite assert_Prop_l by done.
Qed.
Lemma ax_cast' Γ δ A P Q σ e v v' :
  (A ★ Q)%A ⊆{Γ} (cast{σ} (#v) ⇓ inr v')%A →
  Γ\ δ\ A ⊨ₑ {{ P }} e {{ inr v | Q }} →
  Γ\ δ\ A ⊨ₑ {{ P }} cast{σ} e {{ inr v' | Q }}.
Proof.
  rewrite (commutative (★)%A); intros; eapply ax_cast; eauto.
  intros; apply assert_Prop_intro_l; intros; simplify_equality'.
  apply assert_exist_intro with v', assert_and_intro, assert_wand_intro; auto.
  by rewrite assert_Prop_l by done.
Qed.
Lemma ax_expr_if' Γ δ A P P' Q e e1 e2 vb :
  (A ★ P' ◊)%A ⊆{Γ} (@{NotOp} #VBase vb ⇓ -)%A →
  Γ\ δ\ A ⊨ₑ {{ P }} e {{ inr (VBase vb) | P' ◊ }} →
  Γ\ δ\ A ⊨ₑ {{ ⌜ ¬base_val_is_0 vb ⌝ ★ P' }} e1 {{ Q }} →
  Γ\ δ\ A ⊨ₑ {{ ⌜ base_val_is_0 vb ⌝ ★ P' }} e2 {{ Q }} →
  Γ\ δ\ A ⊨ₑ {{ P }} if{e} e1 else e2 {{ Q }}.
Proof.
  rewrite (commutative (★)%A); intros; eapply ax_expr_if; eauto.
  * intros; simpl. rewrite (commutative (★)%A), <-(associative (★)%A).
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
End axiomatic_expressions_simple.
