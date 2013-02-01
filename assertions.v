(* Copyright (c) 2012, Robbert Krebbers. *)
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
Require Export expressions.

(** * Definition of assertions *)
(** We pack assertions into a record so we can register the projection
[assert_holds] as [Proper] for the setoid rewriting mechanism. *)
Record assert := Assert {
  assert_holds :> stack → mem → Prop
}.

Delimit Scope assert_scope with A.
Bind Scope assert_scope with assert.
Arguments assert_holds _%A _ _.
Definition assert_as_Prop (P : assert) : Prop := ∀ ρ m, P ρ m.
Coercion assert_as_Prop : assert >-> Sortclass.

(** By defining a pre-order on assertions we automatically obtain the desired
equality from the generic setoid equality on pre-orders. *)
Instance assert_subseteq: SubsetEq assert := λ P Q, ∀ ρ m, P ρ m → Q ρ m.
Instance: PreOrder assert_subseteq.
Proof. firstorder. Qed.
Instance: Proper ((⊆) ==> (=) ==> (=) ==> impl) assert_holds.
Proof. repeat intro; subst; firstorder. Qed.
Instance: Proper ((≡) ==> (=) ==> (=) ==> iff) assert_holds.
Proof. split; subst; firstorder. Qed.

(** * Subclasses of assertions *)
(** The following type classes collect important subclasses of assertions.
- [StackIndep] collects assertions that are independent of the stack.
- [MemIndep] collects assertions that are independent of the memory. In
  (Reynolds, 2002) these are called "pure".
- [MemExt] collects assertions that are preserved under extensions of the
  memory. In (Reynolds, 2002) these are called "intuitionistic".

This file contains instances of these type classes for the various connectives.
We use instance resolution to automatically compose these instances to prove
the above properties for composite assertions. *)
Class StackIndep (P : assert) : Prop :=
  stack_indep: ∀ ρ1 ρ2 m, P ρ1 m → P ρ2 m.
Class MemIndep (P : assert) : Prop :=
  mem_indep: ∀ ρ m1 m2, P ρ m1 → P ρ m2.
Class MemExt (P : assert) : Prop :=
  mem_ext: ∀ ρ m1 m2, P ρ m1 → m1 ⊆ m2 → P ρ m2.

Instance mem_indep_ext P : MemIndep P → MemExt P.
Proof. firstorder. Qed.

(** Invoke type class resolution when [auto] or [eauto] has to solve these
constraints. *)
Hint Extern 100 (StackIndep _) => apply _.
Hint Extern 100 (MemIndep _) => apply _.
Hint Extern 100 (MemExt _) => apply _.

(** Allow it to solve more complex assertions automatically. *)
Hint Extern 1000 (MemIndep (match ?x with _ => _ end)) =>
  destruct x : typeclass_instances.
Hint Extern 1000 (MemExt (match ?x with _ => _ end)) =>
  destruct x : typeclass_instances.
Hint Extern 1000 (StackIndep (match ?x with _ => _ end)) =>
  destruct x : typeclass_instances.

(** * Tactics *)
(** The tactic [solve_assert] will be used to automatically prove simple
properties about assertions. It unfolds assertions using the unfold hint
database [assert] and uses the [naive_solver] tactic to finish the proof. *)
Hint Unfold
  assert_as_Prop
  StackIndep MemIndep MemExt
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

Hint Extern 100 (_ ⊥ _) => solve_mem_disjoint : assert.

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
Definition assert_impl (P Q : assert) : assert := Assert $ λ ρ m, P ρ m → Q ρ m.
Infix "→" := assert_impl : assert_scope.
Notation "(→)" := assert_impl (only parsing) : assert_scope.
Notation "( P →)" := (assert_impl P) (only parsing) : assert_scope.
Notation "(→ Q )" := (λ P, assert_impl P Q) (only parsing) : assert_scope.

Definition assert_and (P Q : assert) : assert := Assert $ λ ρ m, P ρ m ∧ Q ρ m.
Infix "∧" := assert_and : assert_scope.
Notation "(∧)" := assert_and (only parsing) : assert_scope.
Notation "( P ∧)" := (assert_and P) (only parsing) : assert_scope.
Notation "(∧ Q )" := (λ P, assert_and P Q) (only parsing) : assert_scope.

Definition assert_or (P Q : assert) : assert := Assert $ λ ρ m, P ρ m ∨ Q ρ m.
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
Proof. red. unfold_assert. eauto using expr_eval_weaken_mem. Qed.

Instance assert_expr_mem_indep e :
  load_free e →
  MemIndep (e ⇓ v).
Proof.
  intros ?? ρ m1 m2. unfold_assert.
  by rewrite !(expr_load_free_mem_indep ρ m1 m2).
Qed.
Instance assert_expr_mem_indep_ e :
  load_free e →
  MemIndep (e ⇓ -).
Proof.
  intros ? ρ m1 m2 [v ?]. exists v. unfold_assert in *.
  by rewrite !(expr_load_free_mem_indep ρ m2 m1).
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
Proof. intros ρ m [He ?]. unfold_assert in *. by rewrite He. Qed.
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

Definition assert_sep (P Q : assert) : assert := Assert $ λ ρ m, ∃ m1 m2,
  m1 ∪ m2 = m ∧ m1 ⊥ m2 ∧ P ρ m1 ∧ Q ρ m2.
Infix "★" := assert_sep (at level 80, right associativity) : assert_scope.
Notation "(★)" := assert_sep (only parsing) : assert_scope.
Notation "( P ★)" := (assert_sep P) (only parsing) : assert_scope.
Notation "(★ Q )" := (λ P, assert_sep P Q) (only parsing) : assert_scope.

Definition assert_wand (P Q : assert) : assert := Assert $ λ ρ m1, ∀ m2,
  m1 ⊥ m2 → P ρ m2 → Q ρ (m1 ∪ m2).
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
Lemma assert_sep_comm_1 P Q : (P ★ Q)%A ⊆ (Q ★ P)%A.
Proof.
  intros ? m (m1 & m2 & ? & ? & HP & HQ).
  exists m2 m1. by rewrite finmap_union_comm.
Qed.
Instance: Commutative (≡) (★)%A.
Proof. split; apply assert_sep_comm_1. Qed.

Lemma assert_sep_left_id_1 P : (emp ★ P)%A ⊆ P.
Proof.
  intros ? m (m1 & m2 & H & Hm1 & Hm2 & Hm3).
  unfold_assert in *. subst.
  by rewrite (left_id ∅ (∪)).
Qed.
Lemma assert_sep_left_id_2 P : P ⊆ (emp ★ P)%A.
Proof.
  intros ? m ?. exists (∅ : mem) m. repeat split.
  * apply (left_id _ _).
  * solve_mem_disjoint.
  * done.
Qed.
Instance: LeftId (≡) emp%A (★)%A.
Proof. split. apply assert_sep_left_id_1. apply assert_sep_left_id_2. Qed.
Instance: RightId (≡) emp%A (★)%A.
Proof. intros ?. rewrite (commutative _). apply (left_id _ _). Qed.

Instance: LeftAbsorb (≡) False%A (★)%A.
Proof. solve_assert. Qed.
Instance: RightAbsorb (≡) False%A (★)%A.
Proof. solve_assert. Qed.

Lemma assert_sep_assoc_1 P Q R : ((P ★ Q) ★ R)%A ⊆ (P ★ (Q ★ R))%A.
Proof.
  intros ?? (? & mR & ? & ? & (mP & mQ & ?) & ?). intuition. subst.
  exists mP (mQ ∪ mR). repeat split.
  * apply (associative _).
  * solve_mem_disjoint.
  * done.
  * exists mQ mR. solve_mem_disjoint.
Qed.
Lemma assert_sep_assoc_2 P Q R : (P ★ (Q ★ R))%A ⊆ ((P ★ Q) ★ R)%A.
Proof.
  intros ?? (mP & ? & ? & ? & ? & mQ & mR & ?). intuition. subst.
  exists (mP ∪ mQ) mR. repeat split.
  * by rewrite (associative _).
  * solve_mem_disjoint.
  * exists mP mQ. solve_mem_disjoint.
  * done.
Qed.
Instance: Associative (≡) (★)%A.
Proof. split. apply assert_sep_assoc_2. apply assert_sep_assoc_1. Qed.

Lemma assert_wand_intro (P Q R S : assert) :
  (P ★ Q)%A ⊆ R →
  P ⊆ (Q -★ R)%A.
Proof. solve_assert. Qed.
Lemma assert_wand_elim (P Q : assert) :
  (P ★ (P -★ Q))%A ⊆ Q.
Proof. rewrite (commutative (★))%A. solve_assert. Qed.

Lemma assert_and_sep_assoc (P Q R : assert) :
  MemIndep P →
  (P ∧ (Q ★ R))%A ≡ ((P ∧ Q) ★ R)%A.
Proof. solve_assert. Qed.
Lemma assert_sep_and_assoc (P Q R : assert) :
  MemIndep R →
  ((P ★ Q) ∧ R)%A ≡ (P ★ (Q ∧ R))%A.
Proof. solve_assert. Qed.

(** The separation conjunction allows us to give an alternative formulation
of memory extensibility. *)
Lemma mem_ext_sep_true `{MemExt P} : P ≡ (P ★ True)%A.
Proof.
  split.
  * intros ? m ?. exists m (∅ : mem).
    repeat split. apply (right_id _ _). solve_mem_disjoint. done.
  * intros ? ? (m1 & m2 & ? & ? & ? & ?). subst.
    eauto using mem_ext, finmap_subseteq_union_l.
Qed.
Lemma assert_sep_true_mem_ext P : P ≡ (P ★ True)%A → MemExt P.
Proof.
  intros H ρ m1 m2 ??. rewrite H.
  exists m1 (m2 ∖ m1). repeat split; auto.
  * by rewrite <-finmap_union_difference.
  * by apply finmap_disjoint_difference_r.
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
  intros ???? ? m1 m2 (m2' & m2'' & ? & ? & ?). subst.
  exists m2 (∅ : mem). repeat split.
  * by apply (right_id _ _).
  * solve_mem_disjoint.
  * solve_assert.
  * solve_assert.
Qed.
Instance assert_sep_mem_ext_2 : MemExt Q → MemExt (P ★ Q).
Proof.
  intros ??? ? m1 m2 (m2' & m2'' & ? & ? & ? & ?) ?; subst.
  exists m2' (m2'' ∪ m2 ∖ (m2' ∪ m2'')). repeat split.
  * by rewrite (associative _), <-finmap_union_difference.
  * solve_mem_disjoint.
  * done.
  * apply mem_ext with m2''; auto with mem.
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
Proof. intro. by rewrite <-assert_and_sep_assoc, (left_id emp (★))%A. Qed.
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

Lemma assert_sep_list_alt (Ps : list assert) ρ m :
  (Π Ps)%A ρ m ↔ ∃ ms,
    m = ⋃ ms
  ∧ list_disjoint ms
  ∧ Forall2 (λ (P : assert) m, P ρ m) Ps ms.
Proof.
  split.
  * revert m. induction Ps as [|P Ps IH].
    + eexists []. by repeat constructor.
    + intros ? (m1 & m2 & ? & ? & ? & ?); subst.
      destruct (IH m2) as (ms & ? & ? & ?); trivial; subst.
      exists (m1 :: ms). repeat constructor; trivial.
      by apply finmap_disjoint_union_list_r.
  * intros (m2 & ? & Hdisjoint & Hassert); subst.
    revert Hdisjoint.
    induction Hassert as [|P m Ps ms IH]; inversion_clear 1.
    + done.
    + exists m (⋃ ms). rewrite finmap_disjoint_union_list_r.
      intuition.
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
Proof. intros. apply assert_sep_list_alt_vec. by exists ms. Qed.

Instance: Proper (eqlistA (≡) ==> (≡)) assert_sep_list.
Proof. induction 1; simpl; by f_equiv. Qed.

(** The assertion [e1 ↦ e2] asserts that the memory consists of exactly one cell
at address [e1] with contents [e2] and the assertion [e1 ↦ -] asserts that the
memory consists of exactly one cell at address [e1] with arbitrary contents. *)
Definition assert_singleton (e1 e2 : expr) : assert := Assert $ λ ρ m, ∃ a v,
  ⟦ e1 ⟧ ρ m = Some (ptr a)%V ∧ ⟦ e2 ⟧ ρ m = Some v ∧ m = {[(a, v)]}.
Notation "e1 ↦ e2" := (assert_singleton e1 e2)%A (at level 20) : assert_scope.
Definition assert_singleton_ (e : expr) : assert := Assert $ λ ρ m, ∃ a v,
  ⟦ e ⟧ ρ m = Some (ptr a)%V ∧ m = {[(a, v)]}.
Notation "e ↦ -" := (assert_singleton_ e)%A
  (at level 20, format "e  '↦'  '-'") : assert_scope.

Lemma assert_singleton_forget e1 e2 : (e1 ↦ e2)%A ⊆ (e1 ↦ -)%A.
Proof. solve_assert. Qed.

Instance assert_singleton_stack_indep e1 e2 :
  expr_vars e1 ≡ ∅ →
  expr_vars e2 ≡ ∅ →
  StackIndep (e1 ↦ e2).
Proof.
  intros ?? ρ1 ρ2 m (a & v & ?). exists a v.
  by rewrite !(expr_var_free_stack_indep ρ2 ρ1).
Qed.
Instance assert_singleton_stack_indep_ e :
  expr_vars e ≡ ∅ →
  StackIndep (e ↦ -).
Proof.
  intros ? ρ1 ρ2 m (a & v & ?). exists a v.
  by rewrite !(expr_var_free_stack_indep ρ2 ρ1).
Qed.

Lemma assert_singleton_eval_l e1 v1 e2 :
  (e1 ⇓ v1 ∧ val v1 ↦ e2)%A ⊆ (e1 ↦ e2)%A.
Proof. solve_assert. Qed.
Lemma assert_singleton_eval_r e1 v2 e2 :
  (e1 ↦ val v2 ∧ e2 ⇓ v2)%A ⊆ (e1 ↦ e2)%A.
Proof. solve_assert. Qed.
Lemma assert_singleton_eval_ e v :
  (e ⇓ v ∧ val v ↦ -)%A ⊆ (e ↦ -)%A.
Proof. solve_assert. Qed.

Definition assert_assign (e1 e2 : expr) : assert := Assert $ λ ρ m, ∃ a v,
  ⟦ e1 ⟧ ρ m = Some (ptr a)%V ∧ ⟦ e2 ⟧ ρ m = Some v ∧ m !! a = Some v.
Notation "e ↪ v" := (assert_assign e v)%A (at level 20) : assert_scope.
Definition assert_assign_ (e : expr) : assert := Assert $ λ ρ m, ∃ a v,
  ⟦ e ⟧ ρ m = Some (ptr a)%V ∧ m !! a = Some v.
Notation "e ↪ -" := (assert_assign_ e)%A
  (at level 20, format "e  '↪'  '-'") : assert_scope.

Lemma assert_assign_forget e1 e2 : (e1 ↪ e2)%A ⊆ (e1 ↪ -)%A.
Proof. solve_assert. Qed.
Lemma assert_singleton_assign e1 e2 : (e1 ↦ e2)%A ⊆ (e1 ↪ e2)%A.
Proof.
  intros ρ ? (a&v&?&?&?); subst.
  exists a v. by rewrite lookup_singleton.
Qed.
Lemma assert_singleton_assign_ e : (e ↦ -)%A ⊆ (e ↪ -)%A.
Proof.
  intros ρ ? (a&v&?&?); subst.
  exists a v. by rewrite lookup_singleton.
Qed.

Lemma assert_assign_eval_l e1 v1 e2 :
  (e1 ⇓ v1 ∧ val v1 ↪ e2)%A ⊆ (e1 ↪ e2)%A.
Proof. solve_assert. Qed.
Lemma assert_assign_eval_r e1 v2 e2 :
  (e1 ↪ val v2 ∧ e2 ⇓ v2)%A ⊆ (e1 ↪ e2)%A.
Proof. solve_assert. Qed.
Lemma assert_assign_eval_ e v :
  (e ⇓ v ∧ val v ↪ -)%A ⊆ (e ↪ -)%A.
Proof. solve_assert. Qed.

Instance assert_assign_stack_indep e1 e2 :
  expr_vars e1 ≡ ∅ →
  expr_vars e2 ≡ ∅ →
  StackIndep (e1 ↪ e2).
Proof.
  intros ?? ρ1 ρ2 m (a & v & ?). exists a v.
  by rewrite !(expr_var_free_stack_indep ρ2 ρ1).
Qed.
Instance assert_assign_stack_indep_ e :
  expr_vars e ≡ ∅ →
  StackIndep (e ↪ -).
Proof.
  intros ? ρ1 ρ2 m (a & v & ?). exists a v.
  by rewrite !(expr_var_free_stack_indep ρ2 ρ1).
Qed.
Instance assert_assign_mem_ext e1 e2 :
  MemExt (e1 ↪ e2).
Proof.
  intros ρ m1 m2 (a & v & ? &?&?) ?. exists a v.
  repeat split; eauto using expr_eval_weaken_mem, lookup_weaken.
Qed.
Instance assert_assign_mem_ext_ e :
  MemExt (e ↪ -).
Proof.
  intros ρ m1 m2 (a & v & ? &?) ?. exists a v.
  repeat split; eauto using expr_eval_weaken_mem, lookup_weaken.
Qed.

Lemma assign_assign_alt e1 e2 :
  load_free e1 → load_free e2 →
  (e1 ↪ e2)%A ≡ (e1 ↦ e2 ★ True)%A.
Proof.
  split.
  * intros ρ m (a & v &?&?&?). eexists {[ (a,v) ]}, (delete a m).
    repeat split.
    + by rewrite <-insert_union_singleton_l, insert_delete.
    + by apply finmap_disjoint_singleton_l, lookup_delete.
    + exists a v. by rewrite !(expr_load_free_mem_indep _ {[(a, v)]} m).
  * rewrite assert_singleton_assign. apply mem_ext_sep_true.
Qed.
Lemma assert_assign_assign_alt_ e :
  load_free e →
  (e ↪ -)%A ≡ (e ↦ - ★ True)%A.
Proof.
  split.
  * intros ρ m (a & v &?&?). eexists {[ (a,v) ]}, (delete a m).
    repeat split.
    + by rewrite <-insert_union_singleton_l, insert_delete.
    + by apply finmap_disjoint_singleton_l, lookup_delete.
    + exists a v. by rewrite !(expr_load_free_mem_indep _ {[(a, v)]} m).
  * rewrite assert_singleton_assign_. apply mem_ext_sep_true.
Qed.

Lemma assert_assign_load e v :
  (e ↪ val v)%A ≡ (load e ⇓ v)%A.
Proof.
  split.
  * intros ρ m (a&v'&Ha&?&?). simplify_equality.
    unfold_assert. by rewrite Ha.
  * intros ρ m ?. unfold_assert in *.
    by destruct (⟦ e ⟧ ρ m) as [[| |[|]]|]; simpl in *; eauto.
Qed.
Lemma assert_assign_load_ e :
  (e ↪ -)%A ≡ (load e ⇓ -)%A.
Proof.
  split.
  * intros ρ m (a&v'&Ha&?). simplify_equality.
    unfold_assert. exists v'. by rewrite Ha.
  * intros ρ m [v ?]. unfold_assert in *.
    by destruct (⟦ e ⟧ ρ m) as [[| |[|]]|]; simpl in *; eauto.
Qed.

Lemma assert_singleton_load e v :
  (e ↦ val v)%A ⊆ (load e ⇓ v)%A.
Proof. rewrite <-assert_assign_load. apply assert_singleton_assign. Qed.
Lemma assert_singleton_load_ e :
  (e ↦ -)%A ⊆ (load e ⇓ -)%A.
Proof. rewrite <-assert_assign_load_. apply assert_singleton_assign_. Qed.

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
Definition assert_lift (P : assert) : assert := Assert $ λ ρ, P (tail ρ).
Notation "P ↑" := (assert_lift P) (at level 20) : assert_scope.

Lemma assert_lift_expr e v : ((e ⇓ v)↑)%A ≡ ((e↑) ⇓ v)%A.
Proof. by split; intros ??; unfold_assert; rewrite expr_eval_lift. Qed.
Lemma assert_lift_expr_ e : ((e ⇓ -)↑)%A ≡ ((e↑) ⇓ -)%A.
Proof. by split; intros ??; unfold_assert; rewrite expr_eval_lift. Qed.
Lemma assert_lift_singleton e1 e2 : ((e1 ↦ e2)↑)%A ≡ ((e1↑) ↦ (e2↑))%A.
Proof. by split; intros ??; unfold_assert; setoid_rewrite expr_eval_lift. Qed.
Lemma assert_lift_singleton_ e : ((e ↦ -)↑)%A ≡ ((e↑) ↦ -)%A.
Proof. by split; intros ??; unfold_assert; setoid_rewrite expr_eval_lift. Qed.
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
Lemma assert_alloc (P : assert) (b : index) (v : value) (ρ : stack) m :
  is_free m b →
  P ρ m →
  (var 0 ↦ - ★ P↑)%A (b :: ρ) (<[b:=v]>m).
Proof.
  intros ??. eexists {[(b, v)]}, m. repeat split.
  * by rewrite insert_union_singleton_l.
  * solve_mem_disjoint.
  * by exists b v.
  * done.
Qed.

Lemma assert_free (P : assert) (b : index) (ρ : stack) m :
  (var 0 ↦ - ★ P↑)%A (b :: ρ) m →
  P ρ (delete b m) ∧ ∃ v, m !! b = Some v.
Proof.
  intros (m1 & m2 & ? & ? & (a & v & ? & ?) & ?); simplify_equality.
  rewrite <-insert_union_singleton_l, delete_insert by solve_mem_disjoint.
  simplify_map_equality; eauto.
Qed.

(** We prove some properties related to allocation of local variables when
calling a function, and to freeing these when returning from the function
call. *)
Lemma assert_alloc_params (P : assert) (ρ : stack) m1 bs vs m2 :
  StackIndep P →
  alloc_params m1 bs vs m2 →
  P ρ m1 →
  (Π imap (λ i v, var i ↦ val v) vs ★ P)%A (bs ++ ρ) m2.
Proof.
  intros ? Halloc ?. cut (∀ bs',
    (Π imap_go (λ i v, var i ↦ val v) (length bs') vs ★ P)%A
      (bs' ++ bs ++ ρ) m2).
  { intros aux. by apply (aux []). }
  induction Halloc as [| b bs v vs m2 ?? IH ]; intros bs'; simpl.
  * rewrite (left_id emp (★))%A. by apply (stack_indep ρ).
  * rewrite <-(associative (★))%A. eexists {[(b, v)]}, m2. repeat split.
    + by rewrite insert_union_singleton_l.
    + solve_mem_disjoint.
    + exists b v. repeat split. simpl.
      by rewrite list_lookup_middle.
    + specialize (IH (bs' ++ [b])).
      rewrite app_length in IH. simpl in IH.
      by rewrite NPeano.Nat.add_1_r, <-(associative (++)) in IH.
Qed.

Lemma assert_alloc_params_alt (P : assert) (ρ : stack) m bs vs :
  StackIndep P →
  same_length bs vs →
  is_free_list m bs →
  P ρ m →
  (Π imap (λ i v, var i ↦ val v) vs ★ P)%A (bs ++ ρ)
    (insert_list (zip bs vs) m).
Proof. eauto using assert_alloc_params, alloc_params_insert_list_2. Qed.

Lemma assert_free_params (P : assert) (ρ : stack) m (bs : list index)
    (vs : list value) :
  StackIndep P →
  same_length bs vs →
  NoDup bs → (* admissible *)
  (Π imap (λ i _, var i ↦ -) vs ★ P)%A (bs ++ ρ) m →
  P ρ (delete_list bs m) ∧ Forall (λ b, ∃ v, m !! b = Some v) bs.
Proof.
  intros ? Hlength. revert m. cut (∀ bs' m,
    NoDup bs →
    (Π imap_go (λ i _, var i ↦ -) (length bs') vs ★ P)%A
      (bs' ++ bs ++ ρ) m →
    P ρ (delete_list bs m) ∧ Forall (λ b, ∃ v, m !! b = Some v) bs).
  { intros aux. by apply (aux []). }
  induction Hlength as [|b v bs vs ? IH];
    intros bs' m; simpl; inversion_clear 1.
  * rewrite (left_id emp (★))%A. split.
    + by apply (stack_indep (bs' ++ ρ)).
    + done.
  * rewrite <-(associative (★))%A.
    intros (m1 & m2 & ? & ? & (b' & v' & Heval & ?) & ?).
    simplify_equality. simpl in Heval.
    rewrite list_lookup_middle in Heval. simplify_equality.
    rewrite <-insert_union_singleton_l, delete_list_insert_comm by done.
    feed destruct (IH (bs' ++ [b']) m2) as [??]; trivial.
    { by rewrite app_length, NPeano.Nat.add_1_r, <-(associative (++)). }
    split.
    + rewrite delete_insert; [done |].
      rewrite lookup_delete_list_not_elem_of by done.
      solve_mem_disjoint.
    + constructor; simplify_mem_equality; eauto.
      apply Forall_impl with (λ b, ∃ v, m2 !! b = Some v); trivial.
      intros b [??].
      destruct (decide (b = b')); simplify_mem_equality; eauto.
Qed.
