(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** Judgments in a Hoare logic are triples [{{P}} s {{Q}}], where [s] is a
statement, and [P] and [Q] are assertions called the pre and postcondition of
[s], respectively. The intuitive reading of such a triple is:
if [P] holds for the state before execution of [s], and execution of [s]
terminates, then [Q] will hold afterwards. Like (Appel/Blazy, 2007), we define
assertions using a shallow embedding. That is, assertions are predicates over
the contents of the stack and memory. *)

(** This file defines the data type of assertions, the usual connectives of
Hoare logic ([∧], [∨], [¬], [↔], [∀] and [∃]), the connectives of separation
logic ([emp], [↦], [★], [-★]), and other connectives that are more specific to
our development. We overload the usual notations in [assert_scope] to obtain
nicely looking assertions. Furthermore, we prove various properties to make
reasoning about assertions easier. *)
Require Import SetoidList.
Require Export expression_eval memory.

(** * Definition of assertions *)
(** We pack assertions into a record so we can register the projection
[assert_holds] as [Proper] for the setoid rewriting mechanism. *)
Record assert := Assert {
  assert_holds :> stack → mem → Prop
}.

Delimit Scope assert_scope with A.
Bind Scope assert_scope with assert.
Arguments assert_holds _%A _ _.
Definition assert_as_Prop (P : assert) : Prop :=
  ∀ ρ m, P ρ m.
Coercion assert_as_Prop : assert >-> Sortclass.

(** By defining a pre-order on assertions we automatically obtain the desired
equality from the generic setoid equality on pre-orders. *)
Instance assert_subseteq: SubsetEq assert := λ P Q,
  ∀ ρ m, P ρ m → Q ρ m.
Instance: PreOrder assert_subseteq.
Proof.
  split.
  * by intros P ρ m.
  * intros P1 P2 P3 H1 H2 ρ m ?. by apply H2, H1.
Qed.
Instance: Proper ((⊆) ==> (=) ==> (=) ==> impl) assert_holds.
Proof. firstorder. Qed.
Instance: Proper ((≡) ==> (=) ==> (=) ==> iff) assert_holds.
Proof. firstorder. Qed.

(** * Subclasses of assertions *)
(** The following type classes collect important subclasses of assertions.
- [StackIndep] collects assertions that are independent of the stack.
- [MemIndep] collects assertions that are independent of the memory. In
  (Reynolds, 2002) these are called "pure".
- [MemExt] collects assertions that are preserved under extensions of the
  memory. In (Reynolds, 2002) these are called "intuitionistic".
- [UnlockIndep] collects assertions that are independent of unlocking the
  memory.

This file contains instances of these type classes for the various connectives.
We use instance resolution to automatically compose these instances to prove
the above properties for composite assertions. *)
Class StackIndep (P : assert) : Prop :=
  stack_indep: ∀ ρ1 ρ2 m, P ρ1 m → P ρ2 m.
Class MemIndep (P : assert) : Prop :=
  mem_indep: ∀ ρ m1 m2, P ρ m1 → P ρ m2.
Class MemExt (P : assert) : Prop :=
  mem_ext: ∀ ρ m1 m2, P ρ m1 → m1 ⊆ m2 → P ρ m2.
Class UnlockIndep (P : assert) : Prop :=
  unlock_indep: ∀ Ω ρ m, P ρ m ↔ P ρ (mem_unlock Ω m).

Instance mem_indep_ext P : MemIndep P → MemExt P.
Proof. firstorder auto. Qed.
Instance mem_indep_lock P : MemIndep P → UnlockIndep P.
Proof. intros H. split; apply H. Qed.

(** Invoke type class resolution when [auto] or [eauto] has to solve these
constraints. *)
Hint Extern 100 (StackIndep _) => apply _.
Hint Extern 100 (MemIndep _) => apply _.
Hint Extern 100 (MemExt _) => apply _.
Hint Extern 100 (UnlockIndep _) => apply _.

(** Allow it to solve more complex assertions automatically. *)
Hint Extern 1000 (MemIndep (match ?x with _ => _ end)) =>
  destruct x : typeclass_instances.
Hint Extern 1000 (MemExt (match ?x with _ => _ end)) =>
  destruct x : typeclass_instances.
Hint Extern 1000 (StackIndep (match ?x with _ => _ end)) =>
  destruct x : typeclass_instances.
Hint Extern 1000 (UnlockIndep (match ?x with _ => _ end)) =>
  destruct x : typeclass_instances.

(** * Tactics *)
(** The tactic [solve_assert] will be used to automatically prove simple
properties about assertions. It unfolds assertions using the unfold hint
database [assert] and uses the [naive_solver] tactic to finish the proof. *)
Hint Unfold
  assert_as_Prop
  StackIndep MemIndep MemExt UnlockIndep
  equiv preorder_equiv subseteq subseteq assert_subseteq : assert.

(** In most situations we do not want [simpl] to unfold assertions and expose
their internal definition. However, as the behavior of [simpl] cannot be
changed locally using Ltac we block unfolding of [assert_holds] by [simpl]
and define a custom tactic to perform this unfolding instead. Unfortunately,
it does not work properly for occurrences of [assert_hold] under binders. *)
Arguments assert_holds _ _ _ : simpl never.

Tactic Notation "unfold_assert" "in" hyp(H) :=
  repeat (progress (unfold assert_holds in H; simpl in H));
  repeat match type of H with
  | context C [let (x) := ?Q in x] =>
    let X := context C [assert_holds Q] in change X in H
  end.
Tactic Notation "unfold_assert" :=
  repeat (progress (unfold assert_holds; simpl));
  repeat match goal with
  | |- context C [let (x) := ?Q in x] =>
    let X := context C [assert_holds Q] in change X
  end.
Tactic Notation "unfold_assert" "in" "*" :=
  unfold_assert;
  repeat match goal with H : _ |- _ => progress unfold_assert in H end.

(* Hint Extern 100 (_ ⊥ _) => solve_mem_disjoint : assert. *)

Ltac solve_assert :=
  repeat intro;
  intuition;
  repeat autounfold with assert in *;
  unfold_assert in *;
  naive_solver (eauto with assert; congruence).

(** * Hoare logic connectives *)
(** Definitions and notations of the usual connectives of Hoare logic. *)
Definition Prop_as_assert (P : Prop) : assert := Assert $ λ _ _, P.
Notation "⌜ P ⌝" := (Prop_as_assert P) (format "⌜  P  ⌝") : assert_scope.
Notation "'True'" := (Prop_as_assert True) : assert_scope.
Notation "'False'" := (Prop_as_assert False) : assert_scope.
Definition assert_impl (P Q : assert) : assert :=
  Assert $ λ ρ m, P ρ m → Q ρ m.
Infix "→" := assert_impl : assert_scope.
Notation "(→)" := assert_impl (only parsing) : assert_scope.
Notation "( P →)" := (assert_impl P) (only parsing) : assert_scope.
Notation "(→ Q )" := (λ P, assert_impl P Q) (only parsing) : assert_scope.

Definition assert_and (P Q : assert) : assert :=
  Assert $ λ ρ m, P ρ m ∧ Q ρ m.
Infix "∧" := assert_and : assert_scope.
Notation "(∧)" := assert_and (only parsing) : assert_scope.
Notation "( P ∧)" := (assert_and P) (only parsing) : assert_scope.
Notation "(∧ Q )" := (λ P, assert_and P Q) (only parsing) : assert_scope.

Definition assert_or (P Q : assert) : assert :=
  Assert $ λ ρ m, P ρ m ∨ Q ρ m.
Infix "∨" := assert_or : assert_scope.
Notation "(∨)" := assert_or (only parsing) : assert_scope.
Notation "( P ∨)" := (assert_or P) (only parsing) : assert_scope.
Notation "(∨ Q )" := (λ P, assert_or P Q) (only parsing) : assert_scope.

Definition assert_iff (P Q : assert) : assert := ((P → Q) ∧ (Q → P))%A.
Infix "↔" := assert_iff : assert_scope.
Notation "(↔)" := assert_iff (only parsing) : assert_scope.
Notation "( P ↔)" := (assert_iff P) (only parsing) : assert_scope.
Notation "(↔ Q )" := (λ P, assert_iff P Q) (only parsing) : assert_scope.

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

(** Compatibility of the connectives with respect to order and setoid
equality. *)
Instance: Proper ((⊆) ==> impl) assert_as_Prop.
Proof. solve_assert. Qed.
Instance: Proper ((≡) ==> iff) assert_as_Prop.
Proof. solve_assert. Qed.
Instance: Proper (impl ==> (⊆)) Prop_as_assert.
Proof. solve_assert. Qed.
Instance: Proper (iff ==> (≡)) Prop_as_assert.
Proof. solve_assert. Qed.
Instance: Proper (flip (⊆) ==> (⊆) ==> (⊆)) (→)%A.
Proof. solve_assert. Qed.
Instance: Proper ((≡) ==> (≡) ==> (≡)) (→)%A.
Proof. solve_assert. Qed.
Instance: Proper ((≡) ==> (≡) ==> (≡)) (↔)%A.
Proof. solve_assert. Qed.
Instance: Proper ((≡) ==> (≡) ==> (≡)) (∧)%A.
Proof. solve_assert. Qed.
Instance: Proper ((⊆) ==> (⊆) ==> (⊆)) (∧)%A.
Proof. solve_assert. Qed.
Instance: Proper ((≡) ==> (≡) ==> (≡)) (∨)%A.
Proof. solve_assert. Qed.
Instance: Proper ((⊆) ==> (⊆) ==> (⊆)) (∨)%A.
Proof. solve_assert. Qed.
Instance: Proper ((≡) ==> (≡)) assert_not.
Proof. solve_assert. Qed.
Instance: Proper (flip (⊆) ==> (⊆)) assert_not.
Proof. solve_assert. Qed.
Instance: Proper (pointwise_relation _ (≡) ==> (≡)) (@assert_forall A).
Proof. unfold pointwise_relation. solve_assert. Qed.
Instance: Proper (pointwise_relation _ (⊆) ==> (⊆)) (@assert_forall A).
Proof. unfold pointwise_relation. solve_assert. Qed.
Instance: Proper (pointwise_relation _ (≡) ==> (≡)) (@assert_exist A).
Proof. unfold pointwise_relation. solve_assert. Qed.
Instance: Proper (pointwise_relation _ (⊆) ==> (⊆)) (@assert_exist A).
Proof. unfold pointwise_relation. solve_assert. Qed.

(** Instances of the type classes for stack independence, memory independence,
and memory extensibility.  *)
Instance Prop_as_assert_stack_indep P : StackIndep (⌜ P ⌝).
Proof. solve_assert. Qed.
Instance assert_impl_stack_indep :
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
Instance assert_impl_mem_indep : MemIndep P → MemIndep Q → MemIndep (P → Q).
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

Instance assert_impl_mem_ext : MemIndep P → MemExt Q → MemExt (P → Q).
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

(** Proofs of other useful properties. *)
Instance: Commutative (≡) (↔)%A.
Proof. solve_assert. Qed.
Instance: Commutative (≡) (∧)%A.
Proof. solve_assert. Qed.
Instance: Associative (≡) (∧)%A.
Proof. solve_assert. Qed.
Instance: Idempotent (≡) (∧)%A.
Proof. solve_assert. Qed.
Instance: Commutative (≡) (∨)%A.
Proof. solve_assert. Qed.
Instance: Associative (≡) (∨)%A.
Proof. solve_assert. Qed.
Instance: Idempotent (≡) (∨)%A.
Proof. solve_assert. Qed.

Instance: LeftId (≡) True%A (∧)%A.
Proof. solve_assert. Qed.
Instance: RightId (≡) True%A (∧)%A.
Proof. solve_assert. Qed.
Instance: LeftAbsorb (≡) False%A (∧)%A.
Proof. solve_assert. Qed.
Instance: RightAbsorb (≡) False%A (∧)%A.
Proof. solve_assert. Qed.
Instance: RightAbsorb (≡) True%A assert_impl.
Proof. intros ?. solve_assert. Qed.
Instance: LeftId (≡) False%A (∨)%A.
Proof. solve_assert. Qed.
Instance: RightId (≡) False%A (∨)%A.
Proof. solve_assert. Qed.
Instance: LeftAbsorb (≡) True%A (∨)%A.
Proof. solve_assert. Qed.
Instance: RightAbsorb (≡) True%A (∨)%A.
Proof. solve_assert. Qed.

Instance: LeftId (≡) True%A (→)%A.
Proof. solve_assert. Qed.
Instance: RightAbsorb (≡) True%A (→)%A.
Proof. intros ?. solve_assert. Qed.

Lemma Prop_as_assert_impl (P Q : Prop) : ⌜ P → Q ⌝%A ≡ (⌜P⌝ → ⌜Q⌝)%A.
Proof. solve_assert. Qed.
Lemma Prop_as_assert_not (P : Prop) : ⌜ ¬P ⌝%A ≡ (¬⌜P⌝)%A.
Proof. solve_assert. Qed.
Lemma Prop_as_assert_and (P Q : Prop) : ⌜ P ∧ Q ⌝%A ≡ (⌜P⌝ ∧ ⌜Q⌝)%A.
Proof. solve_assert. Qed.
Lemma Prop_as_assert_or (P Q : Prop) : ⌜ P ∨ Q ⌝%A ≡ (⌜P⌝ ∨ ⌜Q⌝)%A.
Proof. solve_assert. Qed.

Lemma assert_true_intro (P : assert) : P ⊆ True%A.
Proof. solve_assert. Qed.
Lemma assert_false_elim (P : assert) : False%A ⊆ P.
Proof. solve_assert. Qed.

Lemma assert_and_l (P Q : assert) : (P ∧ Q)%A ⊆ P.
Proof. solve_assert. Qed.
Lemma assert_and_r (P Q : assert) : (P ∧ Q)%A ⊆ Q.
Proof. solve_assert. Qed.
Lemma assert_and_intro P Q1 Q2 : P ⊆ Q1 → P ⊆ Q2 → P ⊆ (Q1 ∧ Q2)%A.
Proof. solve_assert. Qed.
Lemma assert_and_elim_l P1 P2 Q : P1 ⊆ Q → (P1 ∧ P2)%A ⊆ Q.
Proof. solve_assert. Qed.
Lemma assert_and_elim_r P1 P2 Q : P2 ⊆ Q → (P1 ∧ P2)%A ⊆ Q.
Proof. solve_assert. Qed.

Lemma assert_forall_intro {A} P (Q : A → assert) :
  (∀ x, P ⊆ Q x) → P ⊆ (∀ x, Q x)%A.
Proof. solve_assert. Qed.
Lemma assert_forall_specialize {A} (P : A → assert) Q x :
  (P x ⊆ Q) → (∀ x, P x)%A ⊆ Q.
Proof. solve_assert. Qed.

Lemma assert_exists_intro {A} P (Q : A → assert) x :
  P ⊆ Q x → P ⊆ (∃ x, Q x)%A.
Proof. solve_assert. Qed.
Lemma assert_exists_elim {A} (P : A → assert) Q :
  (∀ x, P x ⊆ Q) → (∃ x, P x)%A ⊆ Q.
Proof. solve_assert. Qed.

Lemma assert_or_l (P Q : assert) : P ⊆ (P ∨ Q)%A.
Proof. solve_assert. Qed.
Lemma assert_or_r (P Q : assert) : P ⊆ (P ∨ Q)%A.
Proof. solve_assert. Qed.
Lemma assert_or_elim (P Q R : assert) :
  P ⊆ R → Q ⊆ R → (P ∨ Q)%A ⊆ R.
Proof. solve_assert. Qed.

Lemma assert_and_exists {A} P (Q : A → assert) :
  (P ∧ ∃ x, Q x)%A ≡ (∃ x, P ∧ Q x)%A.
Proof. solve_assert. Qed.
Lemma assert_exists_and {A} (P : A → assert) Q :
  ((∃ x, P x) ∧ Q)%A ≡ (∃ x, P x ∧ Q)%A.
Proof. solve_assert. Qed.

Lemma assert_and_exists_l {A} P (Q : A → assert) :
  (P ∧ ∃ x, Q x)%A ≡ (∃ x, P ∧ Q x)%A.
Proof. solve_assert. Qed.
Lemma assert_and_exists_r {A} (P : A → assert) Q :
  ((∃ x, P x) ∧ Q)%A ≡ (∃ x, P x ∧ Q)%A.
Proof. solve_assert. Qed.

(** The assertion [e ⇓ v] asserts that the expression [e] evaluates to [v]
and [e ⇓ -] asserts that the expression [e] evaluates to an arbitrary value
(in other words, [e] does not impose undefined behavior). *)
Notation vassert := (value → assert).

Definition assert_expr (e : expr) : vassert := λ v,
  Assert $ λ ρ m, ⟦ e ⟧ ρ m = Some v.
Infix "⇓" := assert_expr (at level 60) : assert_scope.
Notation "(⇓)" := assert_expr (only parsing) : assert_scope.
Notation "( e ⇓)" := (assert_expr e) (only parsing) : assert_scope.
Notation "(⇓ v )" := (λ e, assert_expr e v) (only parsing) : assert_scope.

Notation "e ⇓ -" := (∃ v, e ⇓ v)%A
  (at level 60, format "e  '⇓'  '-'") : assert_scope.
Notation "(⇓ - )" := assert_expr (only parsing) : assert_scope.

Instance assert_expr_mem_ext e v : MemExt (e ⇓ v).
Proof.
  intros ρ m1 m2 ? Hm. unfold_assert in *.
  eauto using expr_eval_weaken_mem.
Qed.

Instance assert_expr_mem_indep e :
  load_free e →
  MemIndep (e ⇓ v).
Proof.
  intros ?? ρ m1 m2. unfold_assert.
  erewrite !(expr_load_free_mem_indep ρ m1 m2); eauto.
Qed.
Instance assert_expr_mem_indep_ e :
  load_free e →
  MemIndep (e ⇓ -).
Proof.
  intros ? ρ m1 m2 [v ?]. exists v. unfold_assert in *.
  erewrite !(expr_load_free_mem_indep ρ m2 m1); eauto.
Qed.

Instance assert_expr_stack_indep e v :
  expr_vars e ≡ ∅ →
  StackIndep (e ⇓ v).
Proof.
  intros ? ρ1 ρ2 m. unfold_assert.
  by rewrite !(expr_var_free_stack_indep ρ2 ρ1).
Qed.
Instance assert_expr_stack_indep_ e :
  expr_vars e ≡ ∅ →
  StackIndep (e ⇓ -).
Proof.
  intros ? ρ1 ρ2 m. unfold_assert.
  by rewrite !(expr_var_free_stack_indep ρ2 ρ1).
Qed.

Lemma assert_expr_load e p v :
  (load e ⇓ p ∧ load (val p) ⇓ v)%A ⊆ (load (load e) ⇓ v)%A.
Proof. intros ?? [He ?]. unfold_assert in *. by rewrite He. Qed.
Lemma assert_expr_forget e v : (e ⇓ v)%A ⊆ (e ⇓ -)%A.
Proof. solve_assert. Qed.

Notation "e ⇓ 'true'" := (∃ v, e⇓v ∧ ⌜ value_true v ⌝)%A
  (at level 60, format "e  '⇓'  'true'") : assert_scope.
Notation "e ⇓ 'false'" := (∃ v, e⇓v ∧ ⌜ value_false v ⌝)%A
  (at level 60, format "e  '⇓'  'false'") : assert_scope.

Definition assert_is_true (Pv : vassert) : assert :=
  (∃ v, Pv v ∧ ⌜ value_true v ⌝)%A.
Definition assert_is_false (Pv : vassert) : assert :=
  (∃ v, Pv v ∧ ⌜ value_false v ⌝)%A.

Definition assert_subst (a : index) (v : value) (P : assert) :=
  Assert $ λ ρ m, P ρ (<[a:=v]>m).
Notation "<[ a := v ]>" := (assert_subst a v) : assert_scope.

Instance: ∀ a v, Proper ((≡) ==> (≡)) (assert_subst a v).
Proof. solve_assert. Qed.

Lemma assert_subst_mem_indep P `{MemIndep P} a v:
  (<[a:=v]>P)%A ≡ P.
Proof. solve_assert. Qed.
Lemma assert_subst_impl P Q a v :
  (<[a:=v]>(P → Q))%A ≡ (<[a:=v]>P → <[a:=v]>Q)%A.
Proof. solve_assert. Qed.
Lemma assert_subst_not P a v : (<[a:=v]>(¬P))%A ≡ (¬<[a:=v]>P)%A.
Proof. solve_assert. Qed.
Lemma assert_subst_and P Q a v :
  (<[a:=v]>(P ∧ Q))%A ≡ (<[a:=v]>P ∧ <[a:=v]>Q)%A.
Proof. solve_assert. Qed.
Lemma assert_subst_or P Q a v :
  (<[a:=v]>(P ∨ Q))%A ≡ (<[a:=v]>P ∨ <[a:=v]>Q)%A.
Proof. solve_assert. Qed.
Lemma assert_subst_forall `(P : A → assert) a v :
  (<[a:=v]>(∀ x, P x))%A ≡ (∀ x, <[a:=v]>(P x))%A.
Proof. solve_assert. Qed.
Lemma assert_subst_exists `(P : A → assert) a v :
  (<[a:=v]>(∃ x, P x))%A ≡ (∃ x, <[a:=v]>(P x))%A.
Proof. solve_assert. Qed.

(** * Separation logic connectives *)
(** The assertion [emp] asserts that the memory is empty. The assertion [P ★ Q]
(called separating conjunction) asserts that the memory can be split into two
disjoint parts such that [P] holds in the one part, and [Q] in the other.
The assertion [P -★ Q] (called separating implication or magic wand) asserts
that if an arbitrary memory is extended with a disjoint part in which [P]
holds, then [Q] holds in the extended memory. *)
Definition assert_emp : assert := Assert $ λ ρ m, m = ∅.
Notation "'emp'" := assert_emp : assert_scope.

Definition assert_sep (P Q : assert) : assert :=
  Assert $ λ ρ m, ∃ m1 m2, m1 ∪ m2 = m ∧ m1 ⊥ m2 ∧ P ρ m1 ∧ Q ρ m2.
Infix "★" := assert_sep (at level 80, right associativity) : assert_scope.
Notation "(★)" := assert_sep (only parsing) : assert_scope.
Notation "( P ★)" := (assert_sep P) (only parsing) : assert_scope.
Notation "(★ Q )" := (λ P, assert_sep P Q) (only parsing) : assert_scope.

Definition assert_wand (P Q : assert) : assert :=
  Assert $ λ ρ m1, ∀ m2, m1 ⊥ m2 → P ρ m2 → Q ρ (m1 ∪ m2).
Infix "-★" := assert_wand (at level 90) : assert_scope.
Notation "(-★)" := assert_wand (only parsing) : assert_scope.
Notation "( P -★)" := (assert_wand P) (only parsing) : assert_scope.
Notation "(-★ Q )" := (λ P, assert_wand P Q) (only parsing) : assert_scope.

(** Compatibility of the separation logic connectives with respect to order and
equality. *)
Instance: Proper ((⊆) ==> (⊆) ==> (⊆)) (★)%A.
Proof. solve_assert. Qed.
Instance: Proper ((≡) ==> (≡) ==> (≡)) (★)%A.
Proof. solve_assert. Qed.
Instance: Proper (flip (⊆) ==> (⊆) ==> (⊆)) (-★)%A.
Proof. solve_assert. Qed.
Instance: Proper ((≡) ==> (≡) ==> (≡)) (-★)%A.
Proof. solve_assert. Qed.

(** Basic properties. *)
Lemma assert_sep_commutative_1 P Q : (P ★ Q)%A ⊆ (Q ★ P)%A.
Proof.
  intros ρ m (m1 & m2 & ? & ? & HP & HQ); simpl in *.
  exists m2 m1. by rewrite mem_union_commutative.
Qed.
Instance: Commutative (≡) (★)%A.
Proof. split; apply assert_sep_commutative_1. Qed.

Lemma assert_sep_left_id_1 P : (emp ★ P)%A ⊆ P.
Proof.
  intros ρ m (m1 & m2 & H & ? & ? & Hm2). simpl in *.
  unfold_assert in *. subst. by rewrite (left_id_eq ∅ (∪)).
Qed.
Lemma assert_sep_left_id_2 P : P ⊆ (emp ★ P)%A.
Proof.
  intros ? m ?. exists (∅ : mem) m. unfold_assert. split_ands; auto.
  * apply (left_id _ _).
  * apply mem_disjoint_empty_l.
Qed.
Instance: LeftId (≡) emp%A (★)%A.
Proof. split. apply assert_sep_left_id_1. apply assert_sep_left_id_2. Qed.
Instance: RightId (≡) emp%A (★)%A.
Proof. intros ?. by rewrite (commutative _), (left_id _ _). Qed.

Instance: LeftAbsorb (≡) False%A (★)%A.
Proof. solve_assert. Qed.
Instance: RightAbsorb (≡) False%A (★)%A.
Proof. solve_assert. Qed.

Lemma assert_sep_associative_1 P Q R : ((P ★ Q) ★ R)%A ⊆ (P ★ (Q ★ R))%A.
Proof.
  intros ?? (?&mR&?&?& (mP&mQ&?&?&?&?) &?); simpl in *; subst.
  exists mP (mQ ∪ mR). split_ands; auto.
  * apply (associative _).
  * by apply mem_disjoint_union_move_l.
  * exists mQ mR. eauto using mem_disjoint_union_lr.
Qed.

Lemma assert_sep_associative_2 P Q R : (P ★ (Q ★ R))%A ⊆ ((P ★ Q) ★ R)%A.
Proof.
  intros ?? (mP&?&?&?&?&mQ&mR&?&?&?&?); simpl in *; subst.
  exists (mP ∪ mQ) mR. split_ands; auto.
  * by rewrite (associative _).
  * by apply mem_disjoint_union_move_r.
  * exists mP mQ. eauto using mem_disjoint_union_rl.
Qed.
Instance: Associative (≡) (★)%A.
Proof.
  split. apply assert_sep_associative_2. apply assert_sep_associative_1.
Qed.

Lemma assert_wand_intro (P Q R S : assert) :
  (P ★ Q)%A ⊆ R →
  P ⊆ (Q -★ R)%A.
Proof. solve_assert. Qed.
Lemma assert_wand_elim (P Q : assert) :
  (P ★ (P -★ Q))%A ⊆ Q.
Proof. rewrite (commutative (★))%A. solve_assert. Qed.

Lemma assert_and_sep_associative (P Q R : assert) :
  MemIndep P →
  (P ∧ (Q ★ R))%A ≡ ((P ∧ Q) ★ R)%A.
Proof. solve_assert. Qed.
Lemma assert_sep_and_associative (P Q R : assert) :
  MemIndep R →
  ((P ★ Q) ∧ R)%A ≡ (P ★ (Q ∧ R))%A.
Proof. solve_assert. Qed.

(** The separation conjunction allows us to give an alternative formulation
of memory extensibility. *)
Lemma mem_ext_sep_true `{MemExt P} : P ≡ (P ★ True)%A.
Proof.
  split.
  * intros ? m ?. exists m (∅ : mem). unfold_assert. split_ands; auto.
    + apply (right_id _ _).
    + apply mem_disjoint_empty_r.
  * intros ?? (m1 & m2 & ? & ? & ? & ?). subst.
    apply mem_ext with m1; auto using mem_union_subseteq_l.
Qed.
Lemma assert_sep_true_mem_ext P : P ≡ (P ★ True)%A → MemExt P.
Proof.
  intros H ρ m1 m2 ??. rewrite H. exists m1 (m2 ∖ m1).
  unfold_assert. split_ands; auto.
  * by rewrite mem_difference_union.
  * by apply mem_difference_disjoint_r.
Qed.
Lemma mem_ext_sep_true_iff P : P ≡ (P ★ True)%A ↔ MemExt P.
Proof. split; auto using @mem_ext_sep_true, assert_sep_true_mem_ext. Qed.

(** Other type class instances for stack independence, memory independence, and
memory extensibility. *)
Instance assert_emp_stack_indep : StackIndep emp.
Proof. solve_assert. Qed.
Instance assert_sep_stack_indep :
  StackIndep P → StackIndep Q → StackIndep (P ★ Q).
Proof. solve_assert. Qed.
Instance assert_sep_mem_indep :
  MemIndep P → MemIndep Q → MemIndep (P ★ Q).
Proof.
  intros ???? ? m1 m2 (m2' & m2'' &?&?&?&?). subst.
  exists m2 (∅ : mem). split_ands.
  * by apply (right_id _ _).
  * apply mem_disjoint_empty_r.
  * solve_assert.
  * solve_assert.
Qed.
Instance assert_sep_mem_ext_2 : MemExt Q → MemExt (P ★ Q).
Proof.
  intros ??? ? m1 m2 (m2' & m2'' &?&?&?&?) ?. subst.
  exists m2' (m2'' ∪ m2 ∖ (m2' ∪ m2'')). split_ands; auto.
  * by rewrite (associative _), mem_difference_union.
  * apply mem_disjoint_union_move_l; auto using mem_difference_disjoint_r.
  * apply mem_ext with m2''; auto.
    apply mem_union_subseteq_l.
    apply mem_disjoint_union_lr with m2'; auto using mem_difference_disjoint_r.
Qed.
Instance assert_sep_mem_ext_l : MemExt P → MemExt (P ★ Q).
Proof.
  intros P Q ????. rewrite !(commutative (★) P)%A.
  by apply assert_sep_mem_ext_2.
Qed.

(** Proofs of other useful properties. *)
Lemma assert_and_sep_emp_l (P Q : assert) :
  MemIndep P →
  (P ∧ Q)%A ≡ ((P ∧ emp) ★ Q)%A.
Proof.
  intro. by rewrite <-assert_and_sep_associative, (left_id emp (★))%A.
Qed.
Lemma assert_and_sep_emp_r (P Q : assert) :
  MemIndep Q →
  (P ∧ Q)%A ≡ (P ★ (Q ∧ emp))%A.
Proof. intro. by rewrite !(commutative _ P), assert_and_sep_emp_l. Qed.

Lemma assert_sep_elim_l P1 P2 Q :
  MemExt Q →
  P1 ⊆ Q → (P1 ★ P2)%A ⊆ Q.
Proof. intros ? H. by rewrite mem_ext_sep_true, H, <-assert_true_intro. Qed.
Lemma assert_sep_elim_r P1 P2 Q :
  MemExt Q →
  P2 ⊆ Q → (P1 ★ P2)%A ⊆ Q.
Proof. rewrite (commutative (★))%A. apply assert_sep_elim_l. Qed.

(** The assertion [Π Ps] states that the memory can be split into disjoint
parts such that for each part the corresponding assertion in [Ps] holds. *)
Definition assert_sep_list : list assert → assert :=
  foldr (★)%A emp%A.
Notation "'Π' Ps" := (assert_sep_list Ps)
  (at level 20, format "Π  Ps") : assert_scope.

Instance: Proper (eqlistA (≡) ==> (≡)) assert_sep_list.
Proof. induction 1; simpl; by f_equiv. Qed.

Lemma assert_sep_list_alt_2 (Ps : list assert) ρ ms :
  list_disjoint ms →
  Forall2 (λ (P : assert) m, P ρ m) Ps ms →
  (Π Ps)%A ρ (⋃ ms).
Proof.
  intros Hms HPs. revert Hms.
  induction HPs as [|P m Ps ms IH]; inversion_clear 1.
  + done.
  + exists m (⋃ ms); simpl; auto.
Qed.
Lemma assert_sep_list_alt (Ps : list assert) ρ m :
  (Π Ps)%A ρ m ↔ ∃ ms,
    m = ⋃ ms
  ∧ list_disjoint ms
  ∧ Forall2 (λ (P : assert) m, P ρ m) Ps ms.
Proof.
  split.
  * revert m. induction Ps as [|P Ps IH].
    { eexists []. by repeat constructor. }
    intros ? (m1 & m2 & ? & ? & ? & ?); simpl in *; subst.
    destruct (IH m2) as (ms & ? & ? & ?); trivial; subst.
    exists (m1 :: ms). split_ands; trivial.
    + constructor; eauto using mem_disjoint_union_list_r.
    + constructor; auto.
  * naive_solver auto using assert_sep_list_alt_2.
Qed.

Lemma assert_sep_list_alt_vec {n} (Ps : vec assert n) ρ m :
  (Π Ps)%A ρ m ↔ ∃ ms : vec mem n,
    m = ⋃ ms
  ∧ list_disjoint ms
  ∧ ∀ i, (Ps !!! i) ρ (ms !!! i).
Proof.
  rewrite assert_sep_list_alt. split.
  * intros (ms & ? & ? & Hms).
    assert (n = length ms); subst.
    { by erewrite <-Forall2_length, vec_to_list_length by eauto. }
    exists (list_to_vec ms).
    rewrite ?vec_to_list_of_list.
    by rewrite <-(vec_to_list_of_list ms), Forall2_vlookup in Hms.
  * intros [ms ?]. exists ms. by rewrite Forall2_vlookup.
Qed.
Lemma assert_sep_list_alt_vec_2 {n} (Ps : vec assert n) ρ (ms : vec mem n) :
  list_disjoint ms →
  (∀ i, (Ps !!! i) ρ (ms !!! i)) →
  (Π Ps)%A ρ (⋃ ms).
Proof. intros. apply assert_sep_list_alt_vec. eauto. Qed.

(** The assertion [e1 ↦{γ} e2] asserts that the memory consists of exactly one
cell at address [e1] with permission [γ] and contents [e2]. The assertion
[e1 ↦{γ} -] asserts that the memory consists of exactly one cell at address [e1]
with permission [γ] and arbitrary contents. *)
Definition assert_singleton (e1 e2 : expr) (γ : memperm) : assert :=
  Assert $ λ ρ m, ∃ a v,
    ⟦ e1 ⟧ ρ m = Some (ptr a)%V ∧ ⟦ e2 ⟧ ρ m = Some v ∧ m = {[(a,v,γ)]}.
Notation "e1 ↦{ γ } e2" := (assert_singleton e1 e2 γ)%A
  (at level 20, format "e1  ↦{ γ }  e2") : assert_scope.
Definition assert_singleton_ (e : expr) (γ : memperm) : assert :=
  Assert $ λ ρ m, ∃ a v,
    ⟦ e ⟧ ρ m = Some (ptr a)%V ∧ m = {[(a,v,γ)]}.
Notation "e ↦{ γ } -" := (assert_singleton_ e γ)%A
  (at level 20, format "e  ↦{ γ }  -") : assert_scope.

Lemma assert_singleton_forget e1 e2 γ : (e1 ↦{γ} e2)%A ⊆ (e1 ↦{γ} -)%A.
Proof. solve_assert. Qed.

Instance assert_singleton_stack_indep e1 e2 γ :
  expr_vars e1 ≡ ∅ →
  expr_vars e2 ≡ ∅ →
  StackIndep (e1 ↦{γ} e2).
Proof.
  intros ?? ρ1 ρ2 m (a & v & ?). exists a v.
  by rewrite !(expr_var_free_stack_indep ρ2 ρ1).
Qed.
Instance assert_singleton_stack_indep_ e γ :
  expr_vars e ≡ ∅ →
  StackIndep (e ↦{γ} -).
Proof.
  intros ? ρ1 ρ2 m (a&v&?). exists a v.
  by rewrite !(expr_var_free_stack_indep ρ2 ρ1).
Qed.

Lemma assert_singleton_eval_l e1 v1 e2 γ :
  (e1 ⇓ v1 ∧ val v1 ↦{γ} e2)%A ⊆ (e1 ↦{γ} e2)%A.
Proof. solve_assert. Qed.
Lemma assert_singleton_eval_r e1 v2 e2 γ :
  (e1 ↦{γ} val v2 ∧ e2 ⇓ v2)%A ⊆ (e1 ↦{γ} e2)%A.
Proof. solve_assert. Qed.
Lemma assert_singleton_eval_ e v γ :
  (e ⇓ v ∧ val v ↦{γ} -)%A ⊆ (e ↦{γ} -)%A.
Proof. solve_assert. Qed.

(** The assertion [e1 ↪{γ} e2] asserts that the memory contains at least one
cell at address [e1] with permission [γ] and contents [e2]. The assertion
[e1 ↪{γ} -] asserts that the memory contains at least one cell at address
[e1] with permission [γ] and arbitrary contents. *)
Definition assert_assign (e1 e2 : expr) (γ : memperm) : assert :=
  Assert $ λ ρ m, ∃ a v,
    ⟦ e1 ⟧ ρ m = Some (ptr a)%V ∧
    ⟦ e2 ⟧ ρ m = Some v ∧
    {[(a,v,γ)]} ⊆ m.
Notation "e1 ↪{ γ } e2" := (assert_assign e1 e2 γ)%A
  (at level 20, format "e1  ↪{ γ }  e2") : assert_scope.
Definition assert_assign_ (e : expr) (γ : memperm) : assert :=
  Assert $ λ ρ m, ∃ a v,
    ⟦ e ⟧ ρ m = Some (ptr a)%V ∧
    {[(a,v,γ)]} ⊆ m.
Notation "e ↪{ γ } -" := (assert_assign_ e γ)%A
  (at level 20, format "e  ↪{ γ }  -") : assert_scope.

Lemma assert_assign_forget e1 e2 γ : (e1 ↪{γ} e2)%A ⊆ (e1 ↪{γ} -)%A.
Proof. solve_assert. Qed.
Lemma assert_singleton_assign e1 e2 γ : (e1 ↦{γ} e2)%A ⊆ (e1 ↪{γ} e2)%A.
Proof. solve_assert. Qed.
Lemma assert_singleton_assign_ e γ : (e ↦{γ} -)%A ⊆ (e ↪{γ} -)%A.
Proof. solve_assert. Qed.

Lemma assert_assign_eval_l e1 v1 e2 γ :
  (e1 ⇓ v1 ∧ val v1 ↪{γ} e2)%A ⊆ (e1 ↪{γ} e2)%A.
Proof. solve_assert. Qed.
Lemma assert_assign_eval_r e1 v2 e2 γ :
  (e1 ↪{γ} val v2 ∧ e2 ⇓ v2)%A ⊆ (e1 ↪{γ} e2)%A.
Proof. solve_assert. Qed.
Lemma assert_assign_eval_ e v γ :
  (e ⇓ v ∧ val v ↪{γ} -)%A ⊆ (e ↪{γ} -)%A.
Proof. solve_assert. Qed.

Instance assert_assign_stack_indep e1 e2 γ :
  expr_vars e1 ≡ ∅ →
  expr_vars e2 ≡ ∅ →
  StackIndep (e1 ↪{γ} e2).
Proof.
  intros ?? ρ1 ρ2 m (a&v&γ'&?). exists a v.
  by rewrite !(expr_var_free_stack_indep ρ2 ρ1).
Qed.
Instance assert_assign_stack_indep_ e γ :
  expr_vars e ≡ ∅ →
  StackIndep (e ↪{γ} -).
Proof.
  intros ? ρ1 ρ2 m (a&v&γ'&?). exists a v.
  by rewrite !(expr_var_free_stack_indep ρ2 ρ1).
Qed.

Instance assert_assign_mem_ext e1 e2 γ :
  MemExt (e1 ↪{γ} e2).
Proof.
  intros ρ m1 m2 (a&v&γ2&?&?) Hm12.
  exists a v. split_ands; eauto using expr_eval_weaken_mem.
  by transitivity m1.
Qed.
Instance assert_assign_mem_ext_ e γ :
  MemExt (e ↪{γ} -).
Proof.
  intros ρ m1 m2 (a&v&γ2&?) Hm12.
  exists a v. split_ands; eauto using expr_eval_weaken_mem.
  by transitivity m1.
Qed.

Lemma assign_assign_alt e1 e2 γ :
  load_free e1 → load_free e2 →
  (e1 ↪{γ} e2)%A ≡ (e1 ↦{γ} e2 ★ True)%A.
Proof.
  split.
  * intros ρ m (a&v&γ'&?&?).
    eexists {[ (a,v,γ) ]}, (m ∖ {[ (a,v,γ) ]}). split_ands.
    + by apply mem_difference_union.
    + by apply mem_difference_disjoint_r.
    + exists a v.
      erewrite !(expr_load_free_mem_indep _ {[(a,v,γ)]} m); eauto.
    + done.
  * rewrite assert_singleton_assign. apply mem_ext_sep_true.
Qed.
Lemma assert_assign_assign_alt_ e γ :
  load_free e →
  (e ↪{γ} -)%A ≡ (e ↦{γ} - ★ True)%A.
Proof.
  split.
  * intros ρ m (a&v&γ'&?).
    eexists {[ (a,v,γ) ]}, (m ∖ {[ (a,v,γ) ]}). split_ands.
    + by apply mem_difference_union.
    + by apply mem_difference_disjoint_r.
    + exists a v. simpl.
      erewrite !(expr_load_free_mem_indep _ {[(a,v,γ)]} m); eauto.
    + done.
  * rewrite assert_singleton_assign_. apply mem_ext_sep_true.
Qed.

Lemma assert_assign_load e v γ :
  perm_kind γ ≠ Locked →
  (e ↪{γ} val v)%A ⊆ (load e ⇓ v)%A.
Proof.
  intros ? ρ m (a&v'&Ha&?&?).
  unfold_assert. rewrite Ha. simplify_option_equality.
  apply mem_lookup_weaken with {[(a, v', γ)]}; [|done].
  by apply mem_lookup_singleton.
Qed.
Lemma assert_assign_load_ e γ :
  perm_kind γ ≠ Locked →
  (e ↪{γ} -)%A ⊆ (load e ⇓ -)%A.
Proof.
  intros ? ρ m (a&v'&Ha&?).
  unfold_assert. rewrite Ha. simplify_option_equality.
  exists v'. apply mem_lookup_weaken with {[(a, v', γ)]}; [|done].
  by apply mem_lookup_singleton.
Qed.

Lemma assert_singleton_load e v γ :
  perm_kind γ ≠ Locked →
  (e ↦{γ} val v)%A ⊆ (load e ⇓ v)%A.
Proof.
  intros. rewrite assert_singleton_assign. by apply assert_assign_load.
Qed.
Lemma assert_singleton_load_ e γ :
  perm_kind γ ≠ Locked →
  (e ↦{γ} -)%A ⊆ (load e ⇓ -)%A.
Proof.
  intros. by rewrite <-assert_assign_load_, assert_singleton_assign_.
Qed.

Definition assert_unlock (P : assert) : assert :=
  Assert $ λ ρ m, P ρ (mem_unlock (locks m) m).
Notation "P ▷" := (assert_unlock P) (at level 20) : assert_scope.

Instance: Proper ((⊆) ==> (⊆)) assert_unlock.
Proof. solve_assert. Qed.
Instance: Proper ((≡) ==> (≡)) assert_unlock.
Proof. solve_assert. Qed.

Lemma assert_unlock_unlock_indep `{UnlockIndep P} : (P ▷)%A ≡ P.
Proof. solve_assert. Qed.
Lemma assert_unlock_impl P Q : ((P → Q) ▷)%A ≡ (P ▷ → Q ▷)%A.
Proof. solve_assert. Qed.
Lemma assert_unlock_not P : ((¬P)▷)%A ≡ (¬P ▷)%A.
Proof. solve_assert. Qed.
Lemma assert_unlock_and P Q : ((P ∧ Q) ▷)%A ≡ (P ▷ ∧ Q ▷)%A.
Proof. solve_assert. Qed.
Lemma assert_unlock_or P Q : ((P ∨ Q) ▷)%A ≡ (P ▷ ∨ Q ▷)%A.
Proof. solve_assert. Qed.
Lemma assert_unlock_sep P Q : (P ▷ ★ Q ▷)%A ⊆ ((P ★ Q) ▷)%A.
Proof.
  intros ?? (m1&m2&?&?&?&?).
  exists (mem_unlock (locks m1) m1) (mem_unlock (locks m2) m2).
  split_ands; trivial.
  * subst. by rewrite mem_unlock_all_union.
  * by apply mem_disjoint_unlock_l, mem_disjoint_unlock_r.
Qed.
Lemma assert_unlock_sep_alt P P' Q Q' :
  P ⊆ (P' ▷)%A →
  Q ⊆ (Q' ▷)%A →
  (P ★ Q)%A ⊆ ((P' ★ Q') ▷)%A.
Proof. intros HP HQ. rewrite HP, HQ. apply assert_unlock_sep. Qed.

Lemma assert_unlock_forall `(P : A → assert) :
  ((∀ x, P x)▷)%A ≡ (∀ x, (P x)▷)%A.
Proof. solve_assert. Qed.
Lemma assert_unlock_exists `(P : A → assert) :
  ((∃ x, P x) ▷)%A ≡ (∃ x, (P x)▷)%A.
Proof. solve_assert. Qed.

Lemma assert_unlock_singleton_ e1 γ :
  (e1 ↦{γ} -)%A ⊆ ((e1 ↦{perm_unlock γ} -) ▷)%A.
Proof.
  intros ρ m (a&v&?&?). exists a v. split.
  * unfold_assert. eauto using expr_eval_unlock.
  * subst. apply mem_unlock_all_singleton.
Qed.

(** The assertion [P↡] asserts that [P] holds if the stack is cleared. This
connective allows us to specify stack independence in an alternative way. *)
Definition assert_clear_stack (P : assert) : assert := Assert $ λ _ m, P [] m.
Notation "P ↡" := (assert_clear_stack P) (at level 20) : assert_scope.

Instance assert_clear_stack_clear_stack_indep: StackIndep (P↡).
Proof. solve_assert. Qed.
Lemma stack_indep_clear_stack `{StackIndep P} : (P↡)%A ≡ P.
Proof. solve_assert. Qed.
Lemma stack_indep_clear_stack_iff P : StackIndep P ↔ (P↡)%A ≡ P.
Proof. solve_assert. Qed.

Lemma assert_clear_stack_impl P Q : ((P → Q)↡)%A ≡ (P↡ → Q↡)%A.
Proof. solve_assert. Qed.
Lemma assert_clear_stack_not P : ((¬P)↡)%A ≡ (¬P↡)%A.
Proof. solve_assert. Qed.
Lemma assert_clear_stack_and P Q : ((P ∧ Q)↡)%A ≡ (P↡ ∧ Q↡)%A.
Proof. solve_assert. Qed.
Lemma assert_clear_stack_or P Q : ((P ∨ Q)↡)%A ≡ (P↡ ∨ Q↡)%A.
Proof. solve_assert. Qed.
Lemma assert_clear_stack_sep P Q : ((P ★ Q)↡)%A ≡ (P↡ ★ Q↡)%A.
Proof. solve_assert. Qed.

Instance: Proper ((⊆) ==> (⊆)) assert_clear_stack.
Proof. solve_assert. Qed.
Instance: Proper ((≡) ==> (≡)) assert_clear_stack.
Proof. solve_assert. Qed.

(** To deal with block scope variables we need to lift an assertion such that
the De Bruijn indexes of its variables are increased. We define the lifting
[P↑] of an assertion [P] semantically, and prove that it indeed behaves as
expected. *)
Definition assert_lift (P : assert) : assert :=
  Assert $ λ ρ m, P (tail ρ) m.
Notation "P ↑" := (assert_lift P) (at level 20) : assert_scope.

Lemma assert_lift_expr e v : ((e ⇓ v)↑)%A ≡ ((e↑) ⇓ v)%A.
Proof. by split; intros ??; unfold_assert; rewrite expr_eval_lift. Qed.
Lemma assert_lift_expr_ e : ((e ⇓ -)↑)%A ≡ ((e↑) ⇓ -)%A.
Proof. by split; intros ??; unfold_assert; rewrite expr_eval_lift. Qed.
Lemma assert_lift_singleton e1 e2 γ :
  ((e1 ↦{γ} e2)↑)%A ≡ ((e1↑) ↦{γ} (e2↑))%A.
Proof.
  split; intros ??; unfold_assert; intros H.
  * by rewrite !expr_eval_lift.
  * by rewrite !expr_eval_lift in H.
Qed.
Lemma assert_lift_singleton_ e γ : ((e ↦{γ} -)↑)%A ≡ ((e↑) ↦{γ} -)%A.
Proof.
  split; intros ??; unfold_assert; intros H.
  * by rewrite !expr_eval_lift.
  * by rewrite !expr_eval_lift in H.
Qed.
Lemma assert_lift_impl P Q : ((P → Q)↑)%A ≡ (P↑ → Q↑)%A.
Proof. solve_assert. Qed.
Lemma assert_lift_not P : ((¬P)↑)%A ≡ (¬P↑)%A.
Proof. solve_assert. Qed.
Lemma assert_lift_and P Q : ((P ∧ Q)↑)%A ≡ (P↑ ∧ Q↑)%A.
Proof. solve_assert. Qed.
Lemma assert_lift_or P Q : ((P ∨ Q)↑)%A ≡ (P↑ ∨ Q↑)%A.
Proof. solve_assert. Qed.
Lemma assert_lift_sep P Q : ((P ★ Q)↑)%A ≡ (P↑ ★ Q↑)%A.
Proof. solve_assert. Qed.
Lemma assert_lift_forall `(P : A → assert) : ((∀ x, P x)↑)%A ≡ (∀ x, P x↑)%A.
Proof. solve_assert. Qed.
Lemma assert_lift_exists `(P : A → assert) : ((∃ x, P x)↑)%A ≡ (∃ x, P x↑)%A.
Proof. solve_assert. Qed.

Instance: Proper ((⊆) ==> (⊆)) assert_lift.
Proof. solve_assert. Qed.
Instance: Proper ((≡) ==> (≡)) assert_lift.
Proof. solve_assert. Qed.

Instance assert_lift_stack_indep: StackIndep P → StackIndep (P↑).
Proof. solve_assert. Qed.
Lemma stack_indep_lift `{StackIndep P} : (P↑)%A ≡ P.
Proof. solve_assert. Qed.

(** The assertion [assert_forall2 P xs ys] asserts that [P x y] holds for each
corresponding pair [x] and [y] of elements of [xs] and [ys]. *)
Definition assert_forall2 `(P : A → B → assert) : list A → list B → assert :=
  fix go xs ys :=
  match xs, ys with
  | [], [] => True
  | x :: xs, y :: ys => P x y ∧ go xs ys
  | _, _ => False
  end%A.

(** An alternative semantic formulation of the above assertion. *)
Lemma assert_forall2_correct `(P : A → B → assert) xs ys ρ m :
  assert_forall2 P xs ys ρ m ↔ Forall2 (λ x y, P x y ρ m) xs ys.
Proof.
  split.
  * revert ys. induction xs; intros [|??]; solve_assert.
  * induction 1; solve_assert.
Qed.

(** The rule for blocks is of the shape [{ var 0 ↦ - * P↑ } blk s
{ var 0 ↦ - * Q↑ }] implies [{P} s {Q}]. We prove that this pre and
postcondition is correct with respect to allocation of a local variable when
entering a block and freeing a local variable when leaving a block. *)
Lemma assert_alloc (P : assert) b v γ ρ m :
  is_free m b →
  P ρ m →
  (var 0 ↦{γ} - ★ P↑)%A (b :: ρ) (mem_alloc b v γ m).
Proof.
  intros ??. eexists {[(b,v,γ)]}, m. split_ands.
  * by rewrite mem_alloc_singleton_l.
  * by apply mem_disjoint_singleton_l.
  * by exists b v.
  * done.
Qed.

Lemma assert_free (P : assert) b γ ρ m :
  ¬perm_fragment γ →
  (var 0 ↦{γ} - ★ P↑)%A (b :: ρ) m →
  P ρ (delete b m) ∧ mem_perm b m = Some γ.
Proof.
  intros ? (m1 & m2 &?&?& (a&v&?&?) &?); simplify_equality. split.
  * rewrite mem_delete_union, mem_delete_singleton, (left_id ∅ _),
      mem_delete_free; eauto using mem_disjoint_singleton_l_inv.
  * apply mem_perm_union_Some_l.
    + apply mem_perm_singleton.
    + by apply mem_disjoint_singleton_l_inv with γ v. 
Qed.

(** We prove some properties related to allocation of local variables when
calling a function, and to freeing these when returning from the function
call. *)
Lemma assert_alloc_params (P : assert) ρ m1 γ bs vs m2 :
  StackIndep P →
  alloc_params γ m1 bs vs m2 →
  P ρ m1 →
  (Π imap (λ i v, var i ↦{γ} val v) vs ★ P)%A (bs ++ ρ) m2.
Proof.
  intros ? Halloc ?. cut (∀ bs',
    (Π imap_go (λ i v, var i ↦{γ} val v) (length bs') vs ★ P)%A
      (bs' ++ bs ++ ρ) m2).
  { intros aux. by apply (aux []). }
  induction Halloc as [| b bs v vs m2 ?? IH ]; intros bs'; simpl.
  * rewrite (left_id emp (★))%A. by apply (stack_indep ρ).
  * rewrite <-(associative (★))%A. eexists {[(b,v,γ)]}, m2. split_ands.
    + by rewrite mem_alloc_singleton_l.
    + by apply mem_disjoint_singleton_l.
    + exists b v. split_ands; trivial. simpl. by rewrite list_lookup_middle.
    + specialize (IH (bs' ++ [b])). rewrite app_length in IH. simpl in IH.
      by rewrite NPeano.Nat.add_1_r, <-(associative (++)) in IH.
Qed.

Lemma assert_alloc_params_alt (P : assert) ρ m γ bs vs :
  StackIndep P →
  same_length bs vs →
  is_free_list m bs →
  P ρ m →
  (Π imap (λ i v, var i ↦{γ} val v) vs ★ P)%A (bs ++ ρ)
    (mem_alloc_list γ (zip bs vs) m).
Proof. eauto using assert_alloc_params, alloc_params_alloc_list_2. Qed.

Lemma assert_free_params (P : assert) ρ m γ bs (vs : list value) :
  StackIndep P →
  ¬perm_fragment γ →
  same_length bs vs →
  NoDup bs → (* admissible *)
  (Π imap (λ i _, var i ↦{γ} -) vs ★ P)%A (bs ++ ρ) m →
  P ρ (delete_list bs m) ∧ Forall (λ b, mem_perm b m = Some γ) bs.
Proof.
  intros ?? Hlength. revert m. cut (∀ bs' m,
    NoDup bs →
    (Π imap_go (λ i _, var i ↦{γ} -) (length bs') vs ★ P)%A (bs'++bs++ρ) m →
    P ρ (delete_list bs m) ∧ Forall (λ b, mem_perm b m = Some γ) bs).
  { intros aux. by apply (aux []). }
  induction Hlength as [|b v bs vs ? IH];
    intros bs' m; simpl; inversion_clear 1.
  * rewrite (left_id emp (★))%A. split; [|done].
    by apply (stack_indep (bs' ++ ρ)).
  * rewrite <-(associative (★))%A.
    intros (m1 & m2 & ? & ? & (b' & v' & Heval & ?) & ?).
    simplify_equality. simpl in Heval.
    rewrite list_lookup_middle in Heval. simplify_equality.
    rewrite <-mem_alloc_singleton_l
      by eauto using mem_disjoint_singleton_l_inv.
    feed destruct (IH (bs' ++ [b']) m2) as [??]; trivial.
    { by rewrite app_length, NPeano.Nat.add_1_r, <-(associative (++)). }
    split.
    + rewrite mem_delete_list_alloc_ne, mem_delete_alloc; auto.
      apply is_free_subseteq with m2;
        eauto using mem_delete_list_subseteq, mem_disjoint_singleton_l_inv.
    + constructor; [by rewrite mem_perm_alloc |].
      eapply Forall_impl; eauto. intros b ?. by destruct (decide (b = b'));
        subst; rewrite ?mem_perm_alloc, ?mem_perm_alloc_ne.
Qed.
