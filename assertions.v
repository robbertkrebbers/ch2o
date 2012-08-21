Require Import SetoidList.
Require Export expressions subset.

(* We define assert as a record so we can register the projection
    [assert_holds] as [Proper] for setoid rewriting *)
Record assert := Assert {
  assert_holds :> stack → mem → Prop
}.

Delimit Scope assert_scope with A.
Bind Scope assert_scope with assert.
Arguments assert_holds _%A _ _.
Coercion assert_as_Prop (P : assert) : Prop := ∀ ρ m, P ρ m.

Instance assert_subseteq: SubsetEq assert := λ P Q, ∀ ρ m, P ρ m → Q ρ m.
Instance: PreOrder assert_subseteq.
Proof. firstorder. Qed.
Instance: Proper ((⊆) ==> (=) ==> (=) ==> impl) assert_holds.
Proof. repeat intro; subst; firstorder. Qed.
Instance: Proper ((≡) ==> (=) ==> (=) ==> iff) assert_holds.
Proof. split; subst; firstorder. Qed.

(* Useful properties of assertions *)
Class StackIndep (P : assert) : Prop :=
  stack_indep: ∀ ρ1 ρ2 m, P ρ1 m → P ρ2 m.
Class MemIndep (P : assert) : Prop :=
  mem_indep: ∀ ρ m1 m2, P ρ m1 → P ρ m2.
Class MemExt (P : assert) : Prop :=
  mem_ext: ∀ ρ m1 m2, m1 ⊆ m2 → P ρ m1 → P ρ m2.

Hint Extern 100 (StackIndep _) => apply _.
Hint Extern 100 (MemIndep _) => apply _.
Hint Extern 100 (MemExt _) => apply _.

Instance mem_indep_ext P : MemIndep P → MemExt P.
Proof. firstorder. Qed.

(* Standard Hoare logic connectives *)
Definition Prop_as_assert (P : Prop) : assert := Assert $ λ ρ m, P.
Notation "⌜ P ⌝" := (Prop_as_assert P) : assert_scope.
Notation "'True'" := (Prop_as_assert True) : assert_scope.
Notation "'False'" := (Prop_as_assert False) : assert_scope.
Definition assert_imp (P Q : assert) : assert := Assert $ λ ρ m, P ρ m → Q ρ m.
Infix "→" := assert_imp : assert_scope.
Definition assert_and (P Q : assert) : assert := Assert $ λ ρ m, P ρ m ∧ Q ρ m.
Infix "∧" := assert_and : assert_scope.
Definition assert_or (P Q : assert) : assert := Assert $ λ ρ m, P ρ m ∨ Q ρ m.
Infix "∨" := assert_or : assert_scope.
Definition assert_not (P : assert) : assert := Assert $ λ ρ m, ¬P ρ m.
Notation "¬ P" := (assert_not P) : assert_scope.
Definition assert_forall {A} (P : A → assert) : assert :=
  Assert $ λ ρ m, ∀ x, P x ρ m.
Notation "∀ x .. y , P" :=
  (assert_forall (λ x, .. (assert_forall (λ y, P)) ..)) : assert_scope.
Definition assert_exist {A} (P : A → assert) : assert :=
  Assert $ λ ρ m, ∃ x, P x ρ m.
Notation "∃ x .. y , P" :=
  (assert_exist (λ x, .. (assert_exist (λ y, P)) ..)) : assert_scope.
Definition assert_iff (P Q : assert) : assert := ((P → Q) ∧ (Q → P))%A.
Infix "↔" := assert_iff : assert_scope.

Hint Unfold
  StackIndep MemIndep MemExt
  equiv preorder_equiv subseteq subseteq assert_subseteq
  assert_as_Prop : assert.

Ltac solve_assert :=
  repeat intro;
  intuition auto;
  repeat autounfold with assert in *;
  simpl in *;
  firstorder (eauto; congruence).

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
Proof. solve_assert. Qed.
Instance: Proper (pointwise_relation _ (⊆) ==> (⊆)) (@assert_forall A).
Proof. solve_assert. Qed.
Instance: Proper (pointwise_relation _ (≡) ==> (≡)) (@assert_exist A).
Proof. solve_assert. Qed.
Instance: Proper (pointwise_relation _ (⊆) ==> (⊆)) (@assert_exist A).
Proof. solve_assert. Qed.

Instance Prop_as_assert_stack_indep P : StackIndep (⌜ P ⌝).
Proof. solve_assert. Qed.
Instance assert_imp_stack_indep :
  StackIndep P → StackIndep Q → StackIndep (P → Q).
Proof. solve_assert. Qed.
Instance assert_and_stack_indep :
  StackIndep P → StackIndep Q → StackIndep (P ∧ Q).
Proof. solve_assert. Qed.
Instance assert_or_stack_indep :
  StackIndep P → StackIndep Q → StackIndep (P ∨ Q).
Proof. solve_assert. Qed.
Instance assert_not_stack_indep :
  StackIndep P → StackIndep (¬P).
Proof. solve_assert. Qed.
Instance assert_forall_stack_indep A :
  (∀ x : A, StackIndep (P x)) → StackIndep (assert_forall P).
Proof. solve_assert. Qed.
Instance assert_exist_stack_indep A :
  (∀ x : A, StackIndep (P x)) → StackIndep (assert_exist P).
Proof. solve_assert. Qed.
Instance assert_iff_stack_indep :
  StackIndep P → StackIndep Q → StackIndep (P ↔ Q).
Proof. solve_assert. Qed.

Instance Prop_as_assert_mem_indep P : MemIndep (⌜ P ⌝).
Proof. solve_assert. Qed.
Instance assert_imp_mem_indep : MemIndep P → MemIndep Q → MemIndep (P → Q).
Proof. solve_assert. Qed.
Instance assert_and_mem_indep : MemIndep P → MemIndep Q → MemIndep (P ∧ Q).
Proof. solve_assert. Qed.
Instance assert_or_mem_indep : MemIndep P → MemIndep Q → MemIndep (P ∨ Q).
Proof. solve_assert. Qed.
Instance assert_not_mem_indep : MemIndep P → MemIndep (¬P).
Proof. solve_assert. Qed.
Instance assert_forall_mem_indep A :
  (∀ x : A, MemIndep (P x)) → MemIndep (assert_forall P).
Proof. solve_assert. Qed.
Instance assert_exist_mem_indep A :
  (∀ x : A, MemIndep (P x)) → MemIndep (assert_exist P).
Proof. solve_assert. Qed.
Instance assert_iff_mem_indep : MemIndep P → MemIndep Q → MemIndep (P ↔ Q).
Proof. solve_assert. Qed.

Instance assert_imp_mem_ext : MemIndep P → MemExt Q → MemExt (P → Q).
Proof. solve_assert. Qed.
Instance assert_and_mem_ext : MemExt P → MemExt Q → MemExt (P ∧ Q).
Proof. solve_assert. Qed.
Instance assert_or_mem_ext : MemExt P → MemExt Q → MemExt (P ∨ Q).
Proof. solve_assert. Qed.
Instance assert_forall_mem_ext A :
  (∀ x : A, MemExt (P x)) → MemExt (assert_forall P).
Proof. solve_assert. Qed.
Instance assert_exist_mem_ext A :
  (∀ x : A, MemExt (P x)) → MemExt (assert_exist P).
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

Lemma assert_subseteq_implies P Q : P ⊆ Q ↔ (P → Q)%A.
Proof. solve_assert. Qed.
Lemma assert_equiv_iff P Q : P ≡ Q ↔ (P ↔ Q)%A.
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

Definition assert_expr (e : expr) (v : N) : assert :=
  Assert $ λ ρ m, ⟦ e ⟧ ρ m = Some v.
Infix "⇓" := assert_expr (at level 60) : assert_scope.
Definition assert_expr_ (e : expr) : assert :=
  Assert $ λ ρ m, ∃ v, ⟦ e ⟧ ρ m = Some v.
Notation "e ⇓ -" := (assert_expr_ e)
  (at level 60, format "e  '⇓'  '-'") : assert_scope.

Ltac simplify_assert_expr := repeat
  match goal with
  | H : assert_holds (?e ⇓ ?v) ?ρ ?m |- _ => change (⟦ e ⟧ ρ m = Some v) in H
  | H1 : ⟦ ?e ⟧ ?ρ ?m1 = Some ?v1, H2 : ⟦ ?e ⟧ ?ρ ?m2 = Some ?v2 |- _ =>
    let H3 := fresh in
    assert (⟦ e ⟧ ρ m2 = Some v1) as H3 by
      (apply (expr_eval_weaken_mem _ _ m1); eauto with mem);
    assert (v2 = v1) by congruence; subst;
    clear H2 H3
  | H1 : Forall2 (λ e v, ⟦ e ⟧ ?ρ ?m1 = Some v) ?es ?vs1,
     H2 : Forall2 (λ e v, ⟦ e ⟧ ?ρ ?m2 = Some v) ?es ?vs2 |- _ =>
    let H3 := fresh in
    assert (Forall2 (λ e v, ⟦ e ⟧ ρ m2 = Some v) es vs1) as H3 by
      (apply (Forall2_impl _ _ _ _ H1);
        intros; apply (expr_eval_weaken_mem _ _ m1); eauto with mem);
    assert (vs2 = vs1) by (eapply (Forall2_unique _ _ _ _ H2 H3); congruence);
    subst; clear H2 H3
  end.

Instance assert_expr_mem_ext e v : MemExt (e ⇓ v).
Proof. intros ???. apply expr_eval_weaken_mem. Qed.
Instance assert_expr__mem_ext e : MemExt (e ⇓ -).
Proof. intros ??? ? [v ?]. exists v. eauto using expr_eval_weaken_mem. Qed.

(* Separation logic connectives *)
Definition assert_emp : assert := Assert $ λ ρ m, m = ∅.
Notation "'emp'" := assert_emp : assert_scope.

Definition assert_sep (P Q : assert) : assert := Assert $ λ ρ m, ∃ m1 m2,
  mem_disjoint m1 m2 ∧ m1 ∪ m2 = m ∧ P ρ m1 ∧ Q ρ m2.
Infix "*" := assert_sep : assert_scope.

Definition assert_wand (P Q : assert) : assert := Assert $ λ ρ m1, ∀ m2,
  mem_disjoint m1 m2 → P ρ m2 → Q ρ (m1 ∪ m2).
Infix "-*" := assert_wand (at level 90) : assert_scope.

Instance: Proper ((⊆) ==> (⊆) ==> (⊆)) assert_sep.
Proof. solve_assert. Qed.
Instance: Proper ((≡) ==> (≡) ==> (≡)) assert_sep.
Proof. solve_assert. Qed.
Instance: Proper (flip (⊆) ==> (⊆) ==> (⊆)) assert_wand.
Proof. solve_assert. Qed.
Instance: Proper ((≡) ==> (≡) ==> (≡)) assert_wand.
Proof. solve_assert. Qed.

Instance assert_emp_stack_indep : StackIndep emp.
Proof. solve_assert. Qed.

Lemma mem_ext_sep_true `{MemExt P} : P ≡ (P * True)%A.
Proof.
  split.
  * intros ? m ?. exists m (∅ : mem).
    repeat split; auto with mem. apply (right_id _ _).
  * intros ? ? [m1 [m2 [? [? [??]]]]]. subst.
    apply mem_ext with m1; auto with mem.
Qed.
Lemma assert_sep_true_mem_ext P : P ≡ (P * True)%A → MemExt P.
Proof.
  intros H ρ m1 m2 ??. rewrite H.
  exists m1 (m2 ∖ m1). repeat split; auto.
  * now apply mem_disjoint_difference_r.
  * rewrite <-mem_union_difference. now apply mem_subseteq_union.
Qed.
Lemma mem_ext_sep_true_off P : P ≡ (P * True)%A ↔ MemExt P.
Proof.
  split; intros. now apply assert_sep_true_mem_ext. now apply mem_ext_sep_true.
Qed.

Instance assert_sep_stack_indep :
  StackIndep P → StackIndep Q → StackIndep (P * Q).
Proof. solve_assert. Qed.
Instance assert_sep_mem_indep :
  MemIndep P → MemIndep Q → MemIndep (P * Q).
Proof.
  intros ???? ? m1 m2 [m2' [m2'' [? [??]]]]. subst.
  exists m2 (∅ : mem). intuition auto with mem.
  * now apply (right_id _ _).
  * solve_assert.
  * solve_assert.
Qed.
Instance assert_sep_mem_ext : MemExt P → MemExt Q → MemExt (P * Q).
Proof.
  intros ???? ? m1 m2 ? [m2' [m2'' [? [??]]]]. subst.
  exists m2' (m2'' ∪ m2 ∖ (m2' ∪ m2'')). intuition auto.
  * simplify_mem_disjoint. auto using mem_disjoint_difference_r with mem.
  * rewrite (associative _). rewrite <-mem_union_difference.
    now apply mem_subseteq_union.
  * apply mem_ext with m2''; auto with mem.
Qed.

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
  intros ? m ?. exists (∅ : mem) m.
  repeat split; auto with mem.
  apply (left_id _ _).
Qed.
Instance: LeftId (≡) assert_emp assert_sep.
Proof. split. apply assert_sep_left_id_1. apply assert_sep_left_id_2. Qed.
Instance: RightId (≡) assert_emp assert_sep.
Proof. intros ?. rewrite (commutative _). apply (left_id _ _). Qed.

Lemma assert_sep_assoc_1 P Q R : ((P * Q) * R)%A ⊆ (P * (Q * R))%A.
Proof.
  intros ?? [? [mR [? [? [[mP [mQ ?]] ?]]]]]. intuition. subst.
  exists mP (mQ ∪ mR). repeat split.
  * simplify_mem_disjoint.
  * apply (associative _).
  * easy.
  * exists mQ mR. simplify_mem_disjoint. 
Qed.
Lemma assert_sep_assoc_2 P Q R : (P * (Q * R))%A ⊆ ((P * Q) * R)%A.
Proof.
  intros ?? [mP [? [? [? [? [mQ [mR ?]]]]]]]. intuition. subst.
  exists (mP ∪ mQ) mR. repeat split.
  * simplify_mem_disjoint.
  * now rewrite (associative _).
  * exists mP mQ. simplify_mem_disjoint.
  * easy.
Qed.
Instance: Associative (≡) assert_sep.
Proof. split. apply assert_sep_assoc_2. apply assert_sep_assoc_1. Qed.

Definition assert_sep_list : list assert → assert := fold_right assert_sep emp%A.
Notation "'Π' Ps" := (assert_sep_list Ps)
  (at level 20, format "Π  Ps") : assert_scope.

Instance: Proper (eqlistA (≡) ==> (≡)) assert_sep_list.
Proof. induction 1; simpl; now f_equiv. Qed.

Lemma assert_wand_1 (P Q R S : assert) : (P * Q → R)%A → (P → Q -* R)%A.
Proof. intros H ρ m ????. apply H. solve_assert. Qed.
Lemma assert_wand_2 (P Q : assert) : (P * (P -* Q))%A → Q.
Proof.
  rewrite (commutative assert_sep).
  intros H ρ m. destruct (H ρ m). solve_assert.
Qed.

Definition assert_clear_stack (P : assert) : assert := Assert $ λ _ m, P [] m.
Notation "P ↡" := (assert_clear_stack P) (at level 20) : assert_scope.

Instance assert_clear_stack_clear_stack_indep: StackIndep (P↡).
Proof. solve_assert. Qed.
Lemma stack_indep_clear_stack `{StackIndep P} : (P↡)%A ≡ P.
Proof. solve_assert. Qed.

Lemma assert_clear_stack_imp_distr P Q : ((P → Q)↡)%A ≡ (P↡ → Q↡)%A.
Proof. solve_assert. Qed.
Lemma assert_clear_stack_not_distr P : ((¬P)↡)%A ≡ (¬P↡)%A.
Proof. solve_assert. Qed.
Lemma assert_clear_stack_and_distr P Q : ((P ∧ Q)↡)%A ≡ (P↡ ∧ Q↡)%A.
Proof. solve_assert. Qed.
Lemma assert_clear_stack_or_distr P Q : ((P ∨ Q)↡)%A ≡ (P↡ ∨ Q↡)%A.
Proof. solve_assert. Qed.
Lemma assert_clear_stack_sep_distr P Q : ((P * Q)↡)%A ≡ (P↡ * Q↡)%A.
Proof. solve_assert. Qed.

Instance: Proper ((⊆) ==> (⊆)) assert_clear_stack.
Proof. solve_assert. Qed.
Instance: Proper ((≡) ==> (≡)) assert_clear_stack.
Proof. solve_assert. Qed.

Definition assert_inc_stack (P : assert) : assert := Assert $ λ ρ, P (tail ρ).
Notation "P ↑" := (assert_inc_stack P) (at level 20) : assert_scope.

Lemma assert_inc_stack_imp_distr P Q : ((P → Q)↑)%A ≡ (P↑ → Q↑)%A.
Proof. solve_assert. Qed.
Lemma assert_inc_stack_not_distr P : ((¬P)↑)%A ≡ (¬P↑)%A.
Proof. solve_assert. Qed.
Lemma assert_inc_stack_and_distr P Q : ((P ∧ Q)↑)%A ≡ (P↑ ∧ Q↑)%A.
Proof. solve_assert. Qed.
Lemma assert_inc_stack_or_distr P Q : ((P ∨ Q)↑)%A ≡ (P↑ ∨ Q↑)%A.
Proof. solve_assert. Qed.
Lemma assert_inc_stack_sep_distr P Q : ((P * Q)↑)%A ≡ (P↑ * Q↑)%A.
Proof. solve_assert. Qed.

Instance: Proper ((⊆) ==> (⊆)) assert_inc_stack.
Proof. solve_assert. Qed.
Instance: Proper ((≡) ==> (≡)) assert_inc_stack.
Proof. solve_assert. Qed.

Instance assert_inc_stack_stack_indep: StackIndep P → StackIndep (P↑).
Proof. solve_assert. Qed.
Lemma stack_indep_inc `{StackIndep P} : (P↑)%A ≡ P.
Proof. solve_assert. Qed.

Definition assert_singleton (e1 e2 : expr) : assert := Assert $ λ ρ m, ∃ a v,
  ⟦ e1 ⟧ ρ m = Some a ∧ ⟦ e2 ⟧ ρ m = Some v ∧ m = {[(a, v)]}.
Infix "↦" := assert_singleton (at level 20) : assert_scope.
Definition assert_singleton_ (e : expr) : assert := Assert $ λ ρ m, ∃ a v,
  ⟦ e ⟧ ρ m = Some a ∧ m = {[(a, v)]}.
Notation "e ↦ -" := (assert_singleton_ e)
  (at level 20, format "e  '↦'  '-'") : assert_scope.

Fixpoint assert_call (P : list N → assert) (es : list expr) : assert :=
  match es with
  | [] => P []
  | e :: es => ∃ v, e ⇓ v ∧ assert_call (P ∘ (v ::)) es
  end%A.

Lemma assert_call_correct P es ρ m :
  assert_call P es ρ m → ∃ vs, Forall2 (λ e v, ⟦ e ⟧ ρ m = Some v) es vs
    ∧ P vs ρ m.
Proof.
  revert P. induction es; simpl.
   eexists []. intuition.
  intros P [v [? Hcall]]. destruct (IHes _ Hcall) as [vs [??]].
  exists (v :: vs). intuition.
Qed.

Lemma assert_alloc (P : assert) (b : N) v (ρ : stack) m :
  is_free m b → P ρ m → (var 0 ↦ - * P↑)%A (b :: ρ) (<[b:=v]>m).
Proof.
  intros ??. eexists {[(b, v)]}, m. repeat split.
  * simplify_mem_disjoint.
  * now rewrite mem_union_singleton_l.
  * now exists b v.
  * easy.
Qed.

Lemma assert_free (P : assert) (b : N) (ρ : stack) m :
  (var 0 ↦ - * P↑)%A (b :: ρ) m → P ρ (delete b m).
Proof.
  intros [m1 [m2 [? [? [[a [v [? ?]]] ?]]]]]; simplify_eqs.
  simplify_mem_disjoint.
  rewrite <-mem_union_singleton_l.
  now rewrite delete_insert.
Qed.

Arguments assert_holds _ _ _ : simpl never.

Lemma assert_alloc_params (P : assert) (ρ : stack) m1 bs vs m2 :
  StackIndep P →
  alloc_params m1 bs vs m2 →
  P ρ m1 →
  (Π imap (λ i v, var i ↦ val v) vs * P)%A (bs ++ ρ) m2.
Proof.
  intros ? Halloc ?. cut (∀ bs',
    (Π imap_go (λ i v, var i ↦ val v) (length bs') vs * P)%A
      (bs' ++ bs ++ ρ) m2).
   intros aux. now apply (aux []).
  induction Halloc as [| b bs v vs m2 ?? IH ]; intros bs'; simpl.
   rewrite (left_id emp%A assert_sep).
   now apply (stack_indep ρ).
  rewrite <-(associative assert_sep).
  eexists {[(b, v)]}, m2. repeat split.
  * simplify_mem_disjoint.
  * now rewrite mem_union_singleton_l.
  * exists b v. repeat split. apply list_lookup_app_length.
  * specialize (IH (bs' ++ [b])).
    rewrite app_length in IH. simpl in IH.
    now rewrite NPeano.Nat.add_1_r, <-app_assoc in IH.
Qed.

Lemma assert_alloc_params_alt (P : assert) (ρ : stack) m bs vs :
  StackIndep P →
  same_length bs vs →
  is_free_list m bs →
  P ρ m →
  (Π imap (λ i v, var i ↦ val v) vs * P)%A (bs ++ ρ)
    (insert_list (zip bs vs) m).
Proof. eauto using assert_alloc_params, alloc_params_insert_list_1. Qed.

Lemma assert_free_params (P : assert) (ρ : stack) m bs (vs : list N) :
  StackIndep P →
  same_length bs vs →
  NoDup bs → (* admissible *)
  (Π imap (λ i _, var i ↦ -) vs * P)%A (bs ++ ρ) m →
  P ρ (delete_list bs m).
Proof.
  intros ? Hlength. revert m. cut (∀ bs' m,
    NoDup bs →
    (Π imap_go (λ i _, var i ↦ -) (length bs') vs * P)%A
      (bs' ++ bs ++ ρ) m →
    P ρ (delete_list bs m)).
   intros aux. now apply (aux []).
  induction Hlength as [|b v bs vs ? IH];
    intros bs' m; simpl; inversion_clear 1.
   rewrite (left_id emp%A assert_sep).
   now apply (stack_indep _).
  rewrite <-(associative assert_sep).
  intros [m1 [m2 [? [? [[b' [v' [Heval ?]]] ?]]]]]; simpl in *.
  rewrite list_lookup_app_length in Heval. simplify_eqs.
  rewrite <-mem_union_singleton_l, delete_list_insert_comm by easy.
  rewrite delete_insert.
   apply (IH (bs' ++ [b'])). easy.
   rewrite app_length. simpl.
   now rewrite NPeano.Nat.add_1_r, <-app_assoc.
  rewrite lookup_delete_list_notin by easy.
  simplify_mem_disjoint.
Qed.

Definition assert_subst (a : N) (v : N) (P : assert) :=
  Assert $ λ ρ m, P ρ (<[a:=v]>m).
Notation "<[ a := v ]>" := (assert_subst a v) : assert_scope.
