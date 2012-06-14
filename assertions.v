Require Export expressions subset.

(* Defining it as a record so we are required to use
  the projection assert_holds which we can register
  as a Proper for setoid rewriting *)
Record assert := Assert {
  assert_holds :> stack → mem → Prop
}.

(* Standard Hoare logic connectives *)
Coercion assert_as_Prop (P : assert) : Prop := ∀ ρ m, P ρ m.
Definition Prop_as_assert (P : Prop) : assert := Assert $ λ ρ m, P.

Delimit Scope assert_scope with A.
Bind Scope assert_scope with assert.
Arguments assert_holds _%A _ _.
Notation "⌜ P ⌝" := (Prop_as_assert P) : assert_scope.

Instance assert_subseteq: SubsetEq assert := λ P Q, ∀ ρ m, P ρ m → Q ρ m.
Instance: PreOrder assert_subseteq.
Proof. firstorder. Qed.
Instance: Proper ((⊆) ==> (=) ==> (=) ==> impl) assert_holds.
Proof. repeat intro; subst; firstorder. Qed.
Instance: Proper ((≡) ==> (=) ==> (=) ==> iff) assert_holds.
Proof. split; subst; firstorder. Qed.

Definition assert_imp (P Q : assert) : assert := Assert $ λ ρ m, P ρ m → Q ρ m.
Infix "→" := assert_imp : assert_scope.
Definition assert_and (P Q : assert) : assert := Assert $ λ ρ m, P ρ m ∧ Q ρ m.
Infix "∧" := assert_and : assert_scope.
Definition assert_or (P Q : assert) : assert := Assert $ λ ρ m, P ρ m ∨ Q ρ m.
Infix "∨" := assert_or : assert_scope.
Definition assert_not (P : assert) : assert := Assert $ λ ρ m, ¬P ρ m.
Notation "¬ P" := (assert_not P) : assert_scope.
Definition assert_forall {A} (P : A → assert) : assert := Assert $ λ ρ m, ∀ x, P x ρ m.
Notation "∀ x .. y , P" := (assert_forall (λ x, .. (assert_forall (λ y, P)) ..)) : assert_scope.
Definition assert_exist {A} (P : A → assert) : assert := Assert $ λ ρ m, ∃ x, P x ρ m.
Notation "∃ x .. y , P" := (assert_exist (λ x, .. (assert_exist (λ y, P)) ..)) : assert_scope.
Definition assert_iff (P Q : assert) : assert := ((P → Q) ∧ (Q → P))%A.
Infix "↔" := assert_iff : assert_scope.

Hint Unfold
  equiv preorder_equiv subseteq subseteq assert_subseteq
  assert_holds Prop_as_assert assert_imp assert_and assert_or 
  assert_not assert_exist assert_iff assert_as_Prop : assert.
Ltac destruct_asserts := repeat
  match goal with
  | x : assert |- _ => is_var x; destruct x
  end.
Ltac solve_assert :=
  repeat intro;
  destruct_asserts;
  repeat autounfold with assert in *; simpl in *;
  firstorder (eauto; congruence).

Lemma assert_subseteq_implies P Q : P ⊆ Q ↔ (P → Q)%A.
Proof. solve_assert. Qed.
Lemma assert_equiv_iff P Q : P ≡ Q ↔ (P ↔ Q)%A.
Proof. solve_assert. Qed.
Instance: Proper ((⊆) ==> impl) assert_as_Prop.
Proof. solve_assert. Qed. 
Instance: Proper ((≡) ==> iff) assert_as_Prop.
Proof. solve_assert. Qed.
Instance: Proper (flip (⊆) ==> (⊆) ==> (⊆)) assert_imp.
Proof. solve_assert. Qed.
Instance: Proper ((≡) ==> (≡) ==> (≡)) assert_imp.
Proof. solve_assert. Qed.
Instance: Proper ((≡) ==> (≡) ==> (≡)) assert_iff.
Proof. solve_assert. Qed.
Instance: Proper ((≡) ==> (≡) ==> (≡)) assert_and.
Proof. solve_assert. Qed.
Instance: Proper ((⊆) ==> (⊆) ==> (⊆)) assert_and.
Proof. solve_assert. Qed.
Instance: Proper ((≡) ==> (≡) ==> (≡)) assert_or.
Proof. solve_assert. Qed.
Instance: Proper ((⊆) ==> (⊆) ==> (⊆)) assert_or.
Proof. solve_assert. Qed.
Instance: Proper ((≡) ==> (≡)) assert_not.
Proof. solve_assert. Qed.
Instance: Proper (flip (⊆) ==> (⊆)) assert_not.
Proof. solve_assert. Qed.
Instance: Proper (pointwise_relation _ (≡) ==> (≡)) (@assert_forall A).
Proof. intros ??? H; split; intros ????; now apply H. Qed.
Instance: Proper (pointwise_relation _ (⊆) ==> (⊆)) (@assert_forall A).
Proof. intros ??? H ????; now apply H. Qed.
Instance: Proper (pointwise_relation _ (≡) ==> (≡)) (@assert_exist A).
Proof. solve_assert. Qed.
Instance: Proper (pointwise_relation _ (⊆) ==> (⊆)) (@assert_exist A).
Proof. solve_assert. Qed.

Instance: Commutative (≡) assert_iff.
Proof. solve_assert. Qed.
Instance: Commutative (≡) assert_and.
Proof. solve_assert. Qed.
Instance: Associative (≡) assert_and.
Proof. solve_assert. Qed.
Instance: Idempotent (≡) assert_and.
Proof. solve_assert. Qed.
Instance: Commutative (≡) assert_or.
Proof. solve_assert. Qed.
Instance: Associative (≡) assert_or.
Proof. solve_assert. Qed.
Instance: Idempotent (≡) assert_or.
Proof. solve_assert. Qed.

Lemma assert_and_left (P Q : assert) : (P ∧ Q)%A ⊆ P.
Proof. solve_assert. Qed.
Lemma assert_and_right (P Q : assert) : (P ∧ Q)%A ⊆ Q.
Proof. solve_assert. Qed.

Lemma assert_or_left (P Q : assert) : P ⊆ (P ∨ Q)%A.
Proof. solve_assert. Qed.
Lemma assert_or_right (P Q : assert) : P ⊆ (P ∨ Q)%A.
Proof. solve_assert. Qed.

Lemma assert_imp_distr (P Q : assert) : (P → Q)%A → P → Q.
Proof. solve_assert. Qed.
Lemma assert_imp_refl (P : assert) : (P → P)%A.
Proof. solve_assert. Qed.
Lemma assert_imp_trans (P P' Q : assert) : (P → P')%A → (P' → Q)%A → (P → Q)%A.
Proof. solve_assert. Qed.

Lemma assert_iff_distr (P Q : assert) : (P ↔ Q)%A → (P ↔ Q).
Proof. solve_assert. Qed.
Lemma assert_iff_make (P Q : assert) : (P → Q)%A → (Q → P)%A → (P ↔ Q)%A.
Proof. solve_assert. Qed.
Lemma assert_iff_proj1 (P Q : assert) : (P ↔ Q)%A → (P → Q)%A.
Proof. solve_assert. Qed.
Lemma assert_iff_proj2 (P Q : assert) : (P ↔ Q)%A → (Q → P)%A.
Proof. solve_assert. Qed.

Lemma assert_and_distr (P Q : assert) : (P ∧ Q)%A ↔ (P ∧ Q).
Proof. solve_assert. Qed.
Lemma assert_and_make (P Q : assert) : P → Q → (P ∧ Q)%A.
Proof. solve_assert. Qed.

Definition assert_expr (e : expr) (v : N) : assert := Assert $ λ ρ m, ⟦ e ⟧ ρ m = Some v.
Infix "⇓" := assert_expr (at level 60) : assert_scope.
Definition assert_expr_ (e : expr) : assert := Assert $ λ ρ m, ∃ v, ⟦ e ⟧ ρ m = Some v.
Notation "e ⇓ -" := (assert_expr_ e) (at level 60, format "e  '⇓'  '-'") : assert_scope.

Ltac simplify_assert_expr := repeat 
  match goal with
  | H : assert_holds (?e ⇓ ?v) ?ρ ?m |- _ => change (⟦ e ⟧ ρ m = Some v) in H
  | H1 : ⟦ ?e ⟧ ?ρ ?m1 = Some ?v1, H2 : ⟦ ?e ⟧ ?ρ ?m2 = Some ?v2 |- _ =>
    let H3 := fresh in
    assert (⟦ e ⟧ ρ m2 = Some v1) as H3 by
      (apply (expr_eval_weaken_mem _ _ m1); eauto with mem);
    assert (v1 = v2) by congruence; subst;
    clear H2 H3
  end.

(* Separation logic connectives *)
Definition assert_emp : assert := Assert $ λ ρ m, m = ∅.
Notation "'emp'" := assert_emp : assert_scope.

Definition assert_sep (P Q : assert) : assert := Assert $ λ ρ m, ∃ m1 m2,
  mem_disjoint m1 m2 ∧ m1 ∪ m2 = m ∧ P ρ m1 ∧ Q ρ m2.
Infix "*" := assert_sep : assert_scope.

Definition assert_wand (P Q : assert) : assert := Assert $ λ ρ m1, ∀ m2,
  mem_disjoint m1 m2 → P ρ m2 → Q ρ (m1 ∪ m2).
Infix "-*" := assert_wand (at level 90) : assert_scope.

Hint Unfold assert_emp assert_sep assert_wand : assert.

Instance: Proper ((⊆) ==> (⊆) ==> (⊆)) assert_sep.
Proof. solve_assert. Qed.
Instance: Proper ((≡) ==> (≡) ==> (≡)) assert_sep.
Proof. solve_assert. Qed.
Instance: Proper (flip (⊆) ==> (⊆) ==> (⊆)) assert_wand.
Proof. solve_assert. Qed.
Instance: Proper ((≡) ==> (≡) ==> (≡)) assert_wand.
Proof. solve_assert. Qed.

Lemma assert_sep_comm_1 P Q : (P * Q)%A ⊆ (Q * P)%A.
Proof.
  intros ? m [m1 [m2 [H [Hm1 Hm2]]]].
  exists m2 m1. rewrite mem_union_comm; intuition.
Qed.
Instance: Commutative (≡) assert_sep.
Proof. split; apply assert_sep_comm_1. Qed.

Lemma assert_sep_left_id_1 P : (emp * P)%A ⊆ P.
Proof.
  intros ? m [m1 [m2 [H [Hm1 [Hm2 Hm3]]]]].
  simpl in *. subst.
  red. simpl.
  unfold assert_holds.
  simpl. now rewrite (left_id ∅ (∪)).
Qed.
Lemma assert_sep_left_id_2 P : P ⊆ (emp * P)%A.
Proof.
  intros ? m ?. exists (∅ : mem) m. repeat split.
    auto with mem.
   apply (left_id _ _).
  easy.
Qed.
Instance: LeftId (≡) assert_emp assert_sep.
Proof. split. apply assert_sep_left_id_1. apply assert_sep_left_id_2. Qed.
Instance: RightId (≡) assert_emp assert_sep.
Proof. intros ?. rewrite (commutative _). apply (left_id _ _). Qed.

Lemma assert_sep_assoc_1 P Q R : ((P * Q) * R)%A ⊆ (P * (Q * R))%A.
Proof.
  intros ?? [? [mR [? [? [[mP [mQ ?]] ?]]]]]. intuition. subst.
  exists mP (mQ ∪ mR). repeat split.
  * solve_mem_disjoint.
  * apply (associative _).
  * easy.
  * exists mQ mR. solve_mem_disjoint. 
Qed.
Lemma assert_sep_assoc_2 P Q R : (P * (Q * R))%A ⊆ ((P * Q) * R)%A.
Proof.
  intros ?? [mP [? [? [? [? [mQ [mR ?]]]]]]]. intuition. subst.
  exists (mP ∪ mQ) mR. repeat split.
  * solve_mem_disjoint.
  * now rewrite (associative _).
  * exists mP mQ. solve_mem_disjoint.
  * easy.
Qed.
Instance: Associative (≡) assert_sep.
Proof. split. apply assert_sep_assoc_2. apply assert_sep_assoc_1. Qed.

Lemma assert_wand_1 (P Q R S : assert) : (P * Q → R)%A → (P → Q -* R)%A.
Proof. intros H ρ m ????. apply H. solve_assert. Qed.
Lemma assert_wand_2 (P Q : assert) : (P * (P -* Q))%A → Q.
Proof.
  rewrite (commutative assert_sep).
  intros H ρ m. destruct (H ρ m). solve_assert.
Qed.

Definition assert_inc_stack (P : assert) : assert := Assert $ λ ρ, P (tail ρ).
Notation "P ↑" := (assert_inc_stack P) (at level 20) : assert_scope.

Lemma assert_inc_stack_sep_distr P Q : ((P * Q)↑)%A ≡ (P↑ * Q↑)%A.
Proof. solve_assert. Qed.
Instance: Proper ((⊆) ==> (⊆)) assert_inc_stack.
Proof. solve_assert. Qed.
Instance: Proper ((≡) ==> (≡)) assert_inc_stack.
Proof. solve_assert. Qed.

Definition assert_singleton (e1 e2 : expr) : assert := Assert $ λ ρ m, ∃ a v,
  ⟦ e1 ⟧ ρ m = Some a ∧ ⟦ e2 ⟧ ρ m = Some v ∧ m = {{ (a, v) }}.
Infix "↦" := assert_singleton (at level 60) : assert_scope.
Definition assert_singleton_ (e : expr) : assert := Assert $ λ ρ m, ∃ a v,
  ⟦ e ⟧ ρ m = Some a ∧ m = {{ (a, v) }}.
Notation "e ↦ -" := (assert_singleton_ e) (at level 60, format "e  '↦'  '-'") : assert_scope.

Lemma assert_alloc (P : assert) (b : N) v (ρ : stack) m :
  is_free b m → P ρ m → (P↑ * (O ↦ -))%A (b :: ρ) (<[b:=v]> m).
Proof.
  intros ??. exists m ({{ (b, v) }} : mem). repeat split.
  * now auto with mem.
  * now rewrite mem_union_singleton_r.
  * easy.
  * exists b v. intuition.
Qed.

Lemma assert_free (P : assert) (b : N) (ρ : stack) m :
  (P↑ * (O ↦ -))%A (b :: ρ) m → P ρ (delete b m).
Proof.
  intros [m1 [m2 [? [? [? H]]]]].
  destruct H as [a [v [? ?]]]. simplify_eqs.
  rewrite <-mem_union_singleton_r.
   rewrite delete_insert.
    easy.
   eapply mem_disjoint_singleton_2; eauto.
  eapply mem_disjoint_singleton_2; eauto.
Qed.

Definition assert_subst (a : N) (v : N) (P : assert) := Assert $ λ ρ m, P ρ (<[a:=v]>m).
Notation "<[ a := v ]>" := (assert_subst a v) : assert_scope.

Arguments assert_holds _ _ _ : simpl never.
