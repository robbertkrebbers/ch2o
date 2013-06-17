(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** Judgments in a Hoare logic are triples [{{P}} s {{Q}}], where [s] is a
statement, and [P] and [Q] are assertions called the pre and postcondition of
[s], respectively. The intuitive reading of such a triple is:
if [P] holds for the state before execution of [s], and execution of [s]
terminates, then [Q] will hold afterwards. Like (Appel/Blazy, 2007), we define
assertions using a shallow embedding. That is, assertions are predicates over
the contents of the stack and memory. To support dealing with pure functions,
assertions also range over environments of pure functions. *)

(** This file defines the data type of assertions, the usual connectives of
Hoare logic ([∧], [∨], [¬], [↔], [∀] and [∃]), the connectives of separation
logic ([emp], [↦], [★], [-★]), and other connectives that are more specific to
our development. We overload the usual notations in [assert_scope] to obtain
nicely looking assertions. Furthermore, we prove various properties to make
reasoning about assertions easier. *)
Require Export expression_eval memory.

(** * Definition of assertions *)
(** We pack assertions into an inductive type so we can register the projection
[assert_holds] as [Proper] for the setoid rewriting mechanism. *)
Inductive assert := Assert: (purefuns → stack → mem → Prop) → assert.
Definition assert_holds δ (P : assert) : stack → mem → Prop :=
  let (P') := P in P' δ.

Delimit Scope assert_scope with A.
Bind Scope assert_scope with assert.
Arguments assert_holds _ _%A _ _.

(** The relation [P ⊆@{δ} Q] states that the assertion [Q] is a logical
consenquence of [P] in the environment of pure functions [δ]. The relation
[P ≡@{δ} Q] states that [P] and [Q] are logically equivalent in the environment
of pure functions [δ]. *)
Instance assert_subseteq: SubsetEqEnv purefuns assert := λ δ P Q,
  ∀ ρ m, assert_holds δ P ρ m → assert_holds δ Q ρ m.
Instance assert_equiv: EquivEnv purefuns assert := λ δ P Q,
  P ⊑@{δ} Q ∧ Q ⊑@{δ} P.
Instance: PreOrder (assert_subseteq δ).
Proof. firstorder. Qed.
Instance: Equivalence (assert_equiv δ).
Proof. firstorder. Qed.
Instance: Proper ((≡@{δ}) ==> (≡@{δ}) ==> iff) (assert_subseteq δ).
Proof. firstorder auto. Qed.

Instance: Proper ((⊑@{δ}) ==> (=) ==> (=) ==> impl) (assert_holds δ).
Proof. firstorder. Qed.
Instance: Proper ((≡@{δ}) ==> (=) ==> (=) ==> iff) (assert_holds δ).
Proof. firstorder. Qed.

(** * Subclasses of assertions *)
(** The following type classes collect important subclasses of assertions.
- [StackIndep] collects assertions that are independent of the stack.
- [MemIndep] collects assertions that are independent of the memory. In
  (Reynolds, 2002) these are called "pure".
- [MemExt] collects assertions that are preserved under extensions of the
  memory. In (Reynolds, 2002) these are called "intuitionistic".
- [UnlockIndep] collects assertions that are independent of unlocking
  sequenced locations in the memory.
- [FunIndep fs] collections assertions that are independent of the denotations
  of the pure functions [fs].

This file contains instances of these type classes for the various connectives.
We use instance resolution to automatically compose these instances to prove
the above properties for composite assertions. *)
Class StackIndep (P : assert) : Prop :=
  stack_indep: ∀ δ ρ1 ρ2 m, assert_holds δ P ρ1 m → assert_holds δ P ρ2 m.
Class MemIndep (P : assert) : Prop :=
  mem_indep: ∀ δ ρ m1 m2, assert_holds δ P ρ m1 → assert_holds δ P ρ m2.
Class MemExt (P : assert) : Prop :=
  mem_ext: ∀ δ ρ m1 m2,
    assert_holds δ P ρ m1 → m1 ⊆ m2 → assert_holds δ P ρ m2.
Class UnlockIndep (P : assert) : Prop :=
  unlock_indep: ∀ δ Ω ρ m,
    assert_holds δ P ρ m → assert_holds δ P ρ (mem_unlock Ω m).
Class FunIndep (fs : funset) (P : assert) : Prop :=
  fun_indep: ∀ δ1 δ2 ρ m,
    (∀ f, f ∉ fs → δ1 !! f = δ2 !! f) →
    assert_holds δ1 P ρ m ↔ assert_holds δ2 P ρ m.

Instance mem_indep_ext P : MemIndep P → MemExt P.
Proof. firstorder auto. Qed.
Instance mem_indep_lock P : MemIndep P → UnlockIndep P.
Proof. intros H ????. apply H. Qed.

Lemma fun_indep_union_l P δ1 δ2 ρ m :
  FunIndep (dom _ δ1) P →
  assert_holds (δ1 ∪ δ2) P ρ m ↔ assert_holds δ2 P ρ m.
Proof.
  intros. apply fun_indep. intros f Hf. apply option_eq. intros F.
  rewrite lookup_union_Some_raw. rewrite not_elem_of_dom in Hf.
  intuition congruence.
Qed.
Lemma fun_indep_union_r P δ1 δ2 ρ m :
  FunIndep (dom _ δ2) P →
  assert_holds (δ1 ∪ δ2) P ρ m ↔ assert_holds δ1 P ρ m.
Proof.
  intros. apply fun_indep. intros f Hf. apply option_eq. intros F.
  rewrite lookup_union_Some_raw. rewrite not_elem_of_dom in Hf.
  intuition congruence.
Qed.

(** Invoke type class resolution when [auto] or [eauto] has to solve these
constraints. *)
Hint Extern 100 (StackIndep _) => apply _.
Hint Extern 100 (MemIndep _) => apply _.
Hint Extern 100 (MemExt _) => apply _.
Hint Extern 100 (UnlockIndep _) => apply _.
Hint Extern 100 (FunIndep _ _) => apply _.

(** Allow it to solve more complex assertions automatically. *)
Hint Extern 1000 (MemIndep (match ?x with _ => _ end)) =>
  destruct x : typeclass_instances.
Hint Extern 1000 (MemExt (match ?x with _ => _ end)) =>
  destruct x : typeclass_instances.
Hint Extern 1000 (StackIndep (match ?x with _ => _ end)) =>
  destruct x : typeclass_instances.
Hint Extern 1000 (UnlockIndep (match ?x with _ => _ end)) =>
  destruct x : typeclass_instances.
Hint Extern 1000 (FunIndep _ (match ?x with _ => _ end)) =>
  destruct x : typeclass_instances.

(** * Tactics *)
(** The tactic [solve_assert] will be used to automatically prove simple
properties about assertions. It unfolds assertions using the unfold hint
database [assert] and uses the [naive_solver] tactic to finish the proof. *)
Hint Unfold
  StackIndep MemIndep MemExt UnlockIndep FunIndep assert_holds
  equiv_env assert_equiv subseteq_env assert_subseteq : assert.

(** In most situations we do not want [simpl] to unfold assertions and expose
their internal definition. However, as the behavior of [simpl] cannot be
changed locally using Ltac we block unfolding of [assert_holds] by [simpl].
Instead, to unfold assertions, we first unfold [assert_holds] everywhere,
and then fold the projections back. This way of folding back is horrific,
especialially the way of dealing with foldings under a fixed number of forall
quantifiers. Since Ltac's support for dealing with open terms is limited, I
am unaware how to do this better. *)
Arguments assert_holds _ _ _ _ : simpl never.

Tactic Notation "fold_assert" "in" hyp(H) :=
  repeat match type of H with
  | context C [let (x) := ?Q in x ?δ] =>
    let X := context C [assert_holds δ Q] in change X in H
  | ∀ (x1 : ?A1) (x2 : ?A2) (x3 : ?A3), @?P' x1 x2 x3 =>
    let H' := fresh in
    let Q := fresh in evar (Q:A1 → A2 → A3 → Prop);
    let Q' := eval unfold Q in Q in clear Q;
    assert (∀ x1 x2 x3, P' x1 x2 x3 → Q' x1 x2 x3) as H' by
     (intros ???; lazy beta;
      progress repeat match goal with
      | |- context C [let (x) := ?Q in x ?δ] =>
        let X := context C [assert_holds δ Q] in change X
    end; apply id);
    specialize (λ x1 x2 x3, (H' x1 x2 x3) (H x1 x2 x3));
    lazy beta in H'; clear H; rename H' into H
  | ∀ (x1 : ?A1) (x2 : ?A2), @?P' x1 x2 =>
    let H' := fresh in
    let Q := fresh in evar (Q:A1 → A2 → Prop);
    let Q' := eval unfold Q in Q in clear Q;
    assert (∀ x1 x2, P' x1 x2 → Q' x1 x2) as H' by (intros ??; lazy beta;
      progress repeat match goal with
      | |- context C [let (x) := ?Q in x ?δ] =>
        let X := context C [assert_holds δ Q] in change X
    end; apply id);
    specialize (λ x1 x2, (H' x1 x2) (H x1 x2));
    lazy beta in H'; clear H; rename H' into H
  | ∀ x1 : ?A1, @?P' x1 =>
    let H' := fresh in
    let Q := fresh in evar (Q:A1 → Prop);
    let Q' := eval unfold Q in Q in clear Q;
    assert (∀ x1, P' x1 → Q' x1) as H' by (intro; lazy beta;
      progress repeat match goal with
      | |- context C [let (x) := ?Q in x ?δ] =>
        let X := context C [assert_holds δ Q] in change X
    end; apply id);
    specialize (λ x1, (H' x1) (H x1));
    lazy beta in H'; clear H; rename H' into H
  end.
Tactic Notation "fold_assert" :=
  let rec go :=
  lazymatch goal with
  | |- ∀ x, _ => intro x; fold_assert in x; go; revert x
  | |- ∀ _, _ => let H := fresh in intro H; fold_assert in H; go; revert H
  | |- _ =>
    repeat match goal with
    | |- context C [let (x) := ?Q in x ?δ] =>
    let X := context C [assert_holds δ Q] in change X
    end
  end in go.
Tactic Notation "fold_assert" "in" "*" :=
  fold_assert;
  repeat match goal with H : _ |- _ => progress fold_assert in H end.

Tactic Notation "unfold_assert" :=
  repeat (autounfold with assert; simpl); fold_assert.
Tactic Notation "unfold_assert" "in" "*" :=
  repeat (autounfold with assert in *; simpl in *); fold_assert in *.
Tactic Notation "unfold_assert" "in" hyp(H) :=
  repeat (autounfold with assert in H; simpl in H); fold_assert in H.

Create HintDb solve_assert.
Hint Extern 1000 (⊥ _) => solve_mem_disjoint : solve_assert.

Tactic Notation "solve_assert" tactic3(tac) :=
  repeat intro;
  intuition;
  unfold_assert in *;
  naive_solver tac.
Tactic Notation "solve_assert" := solve_assert auto with solve_assert.

(** * Hoare logic connectives *)
(** Definitions and notations of the usual connectives of Hoare logic. *)
Definition Prop_as_assert (P : Prop) : assert := Assert $ λ _ _ _, P.
Notation "⌜ P ⌝" := (Prop_as_assert P) (format "⌜  P  ⌝") : assert_scope.
Notation "'True'" := (Prop_as_assert True) : assert_scope.
Notation "'False'" := (Prop_as_assert False) : assert_scope.
Definition assert_impl (P Q : assert) : assert :=
  Assert $ λ δ ρ m, assert_holds δ P ρ m → assert_holds δ Q ρ m.
Infix "→" := assert_impl : assert_scope.
Notation "(→)" := assert_impl (only parsing) : assert_scope.
Notation "( P →)" := (assert_impl P) (only parsing) : assert_scope.
Notation "(→ Q )" := (λ P, assert_impl P Q) (only parsing) : assert_scope.

Definition assert_and (P Q : assert) : assert :=
  Assert $ λ δ ρ m, assert_holds δ P ρ m ∧ assert_holds δ Q ρ m.
Infix "∧" := assert_and : assert_scope.
Notation "(∧)" := assert_and (only parsing) : assert_scope.
Notation "( P ∧)" := (assert_and P) (only parsing) : assert_scope.
Notation "(∧ Q )" := (λ P, assert_and P Q) (only parsing) : assert_scope.

Definition assert_or (P Q : assert) : assert :=
  Assert $ λ δ ρ m, assert_holds δ P ρ m ∨ assert_holds δ Q ρ m.
Infix "∨" := assert_or : assert_scope.
Notation "(∨)" := assert_or (only parsing) : assert_scope.
Notation "( P ∨)" := (assert_or P) (only parsing) : assert_scope.
Notation "(∨ Q )" := (λ P, assert_or P Q) (only parsing) : assert_scope.

Definition assert_iff (P Q : assert) : assert := ((P → Q) ∧ (Q → P))%A.
Infix "↔" := assert_iff : assert_scope.
Notation "(↔)" := assert_iff (only parsing) : assert_scope.
Notation "( P ↔)" := (assert_iff P) (only parsing) : assert_scope.
Notation "(↔ Q )" := (λ P, assert_iff P Q) (only parsing) : assert_scope.

Definition assert_not (P : assert) : assert :=
  Assert $ λ δ ρ m, ¬assert_holds δ P ρ m.
Notation "¬ P" := (assert_not P) : assert_scope.

Definition assert_forall {A} (P : A → assert) : assert :=
  Assert $ λ δ ρ m, ∀ x, assert_holds δ (P x) ρ m.
Notation "∀ x .. y , P" :=
  (assert_forall (λ x, .. (assert_forall (λ y, P)) ..)) : assert_scope.
Definition assert_exist {A} (P : A → assert) : assert :=
  Assert $ λ δ ρ m, ∃ x, assert_holds δ (P x) ρ m.
Notation "∃ x .. y , P" :=
  (assert_exist (λ x, .. (assert_exist (λ y, P)) ..)) : assert_scope.

(** Compatibility of the connectives with respect to order and setoid
equality. *)
Instance: Proper (impl ==> (⊑@{δ})) Prop_as_assert.
Proof. solve_assert. Qed.
Instance: Proper (iff ==> (≡@{δ})) Prop_as_assert.
Proof. solve_assert. Qed.
Instance: Proper (flip (⊑@{δ}) ==> (⊑@{δ}) ==> (⊑@{δ})) (→)%A.
Proof. solve_assert. Qed.
Instance: Proper ((≡@{δ}) ==> (≡@{δ}) ==> (≡@{δ})) (→)%A.
Proof. solve_assert. Qed.
Instance: Proper ((≡@{δ}) ==> (≡@{δ}) ==> (≡@{δ})) (↔)%A.
Proof. solve_assert. Qed.
Instance: Proper ((≡@{δ}) ==> (≡@{δ}) ==> (≡@{δ})) (∧)%A.
Proof. solve_assert. Qed.
Instance: Proper ((⊑@{δ}) ==> (⊑@{δ}) ==> (⊑@{δ})) (∧)%A.
Proof. solve_assert. Qed.
Instance: Proper ((≡@{δ}) ==> (≡@{δ}) ==> (≡@{δ})) (∨)%A.
Proof. solve_assert. Qed.
Instance: Proper ((⊑@{δ}) ==> (⊑@{δ}) ==> (⊑@{δ})) (∨)%A.
Proof. solve_assert. Qed.
Instance: Proper ((≡@{δ}) ==> (≡@{δ})) assert_not.
Proof. solve_assert. Qed.
Instance: Proper (flip (⊑@{δ}) ==> (⊑@{δ})) assert_not.
Proof. solve_assert. Qed.
Instance:
  Proper (pointwise_relation _ (≡@{δ}) ==> (≡@{δ})) (@assert_forall A).
Proof. unfold pointwise_relation. solve_assert. Qed.
Instance:
  Proper (pointwise_relation _ (⊑@{δ}) ==> (⊑@{δ})) (@assert_forall A).
Proof. unfold pointwise_relation. solve_assert. Qed.
Instance:
  Proper (pointwise_relation _ (≡@{δ}) ==> (≡@{δ})) (@assert_exist A).
Proof. unfold pointwise_relation. solve_assert. Qed.
Instance:
  Proper (pointwise_relation _ (⊑@{δ}) ==> (⊑@{δ})) (@assert_exist A).
Proof. unfold pointwise_relation. solve_assert. Qed.

(** Instances of the type classes for stack independence, memory independence,
memory extensibility, unlock independence, and function independence.  *)
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
Instance assert_not_stack_indep : StackIndep P → StackIndep (¬P).
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

Instance Prop_as_assert_unlock_indep P : UnlockIndep (⌜ P ⌝).
Proof. solve_assert. Qed.
Instance assert_impl_unlock_indep :
  MemIndep P → UnlockIndep Q → UnlockIndep (P → Q).
Proof. solve_assert. Qed.
Instance assert_and_unlock_indep :
  UnlockIndep P → UnlockIndep Q → UnlockIndep (P ∧ Q).
Proof. solve_assert. Qed.
Instance assert_or_unlock_indep :
  UnlockIndep P → UnlockIndep Q → UnlockIndep (P ∨ Q).
Proof. solve_assert eauto. Qed.
Instance assert_forall_unlock_indep A :
  (∀ x : A, UnlockIndep (P x)) → UnlockIndep (assert_forall P).
Proof. solve_assert. Qed.
Instance assert_exist_unlock_indep A :
  (∀ x : A, UnlockIndep (P x)) → UnlockIndep (assert_exist P).
Proof. solve_assert. Qed.

Instance Prop_as_assert_fun_indep P : FunIndep fs (⌜ P ⌝).
Proof. solve_assert. Qed.
Instance assert_impl_fun_indep :
  FunIndep fs P → FunIndep fs Q → FunIndep fs (P → Q).
Proof. solve_assert eauto. Qed.
Instance assert_and_fun_indep :
  FunIndep fs P → FunIndep fs Q → FunIndep fs (P ∧ Q).
Proof. solve_assert eauto. Qed.
Instance assert_or_fun_indep :
  FunIndep fs P → FunIndep fs Q → FunIndep fs (P ∨ Q).
Proof. solve_assert eauto. Qed.
Instance assert_not_fun_indep :
  FunIndep fs P → FunIndep fs (¬P).
Proof. solve_assert eauto. Qed.
Instance assert_forall_fun_indep A :
  (∀ x : A, FunIndep fs (P x)) → FunIndep fs (assert_forall P).
Proof. solve_assert eauto. Qed.
Instance assert_exist_fun_indep A :
  (∀ x : A, FunIndep fs (P x)) → FunIndep fs (assert_exist P).
Proof. solve_assert eauto. Qed.
Instance assert_iff_fun_indep :
  FunIndep fs P → FunIndep fs Q → FunIndep fs (P ↔ Q).
Proof. unfold assert_iff. apply _. Qed.

(** Proofs of other useful properties. *)
Instance: Commutative (≡@{δ}) (↔)%A.
Proof. solve_assert. Qed.
Instance: Commutative (≡@{δ}) (∧)%A.
Proof. solve_assert. Qed.
Instance: Associative (≡@{δ}) (∧)%A.
Proof. solve_assert. Qed.
Instance: Idempotent (≡@{δ}) (∧)%A.
Proof. solve_assert. Qed.
Instance: Commutative (≡@{δ}) (∨)%A.
Proof. solve_assert. Qed.
Instance: Associative (≡@{δ}) (∨)%A.
Proof. solve_assert. Qed.
Instance: Idempotent (≡@{δ}) (∨)%A.
Proof. solve_assert. Qed.

Instance: LeftId (≡@{δ}) True%A (∧)%A.
Proof. solve_assert. Qed.
Instance: RightId (≡@{δ}) True%A (∧)%A.
Proof. solve_assert. Qed.
Instance: LeftAbsorb (≡@{δ}) False%A (∧)%A.
Proof. solve_assert. Qed.
Instance: RightAbsorb (≡@{δ}) False%A (∧)%A.
Proof. solve_assert. Qed.
Instance: RightAbsorb (≡@{δ}) True%A assert_impl.
Proof. intros ?. solve_assert. Qed.
Instance: LeftId (≡@{δ}) False%A (∨)%A.
Proof. solve_assert. Qed.
Instance: RightId (≡@{δ}) False%A (∨)%A.
Proof. solve_assert. Qed.
Instance: LeftAbsorb (≡@{δ}) True%A (∨)%A.
Proof. solve_assert. Qed.
Instance: RightAbsorb (≡@{δ}) True%A (∨)%A.
Proof. solve_assert. Qed.

Instance: LeftId (≡@{δ}) True%A (→)%A.
Proof. solve_assert. Qed.
Instance: RightAbsorb (≡@{δ}) True%A (→)%A.
Proof. intros ?. solve_assert. Qed.

Lemma Prop_as_assert_impl (P Q : Prop) δ : ⌜ P → Q ⌝%A ≡@{δ} (⌜P⌝ → ⌜Q⌝)%A.
Proof. solve_assert. Qed.
Lemma Prop_as_assert_not (P : Prop) δ : ⌜ ¬P ⌝%A ≡@{δ} (¬⌜P⌝)%A.
Proof. solve_assert. Qed.
Lemma Prop_as_assert_and (P Q : Prop) δ : ⌜ P ∧ Q ⌝%A ≡@{δ} (⌜P⌝ ∧ ⌜Q⌝)%A.
Proof. solve_assert. Qed.
Lemma Prop_as_assert_or (P Q : Prop) δ : ⌜ P ∨ Q ⌝%A ≡@{δ} (⌜P⌝ ∨ ⌜Q⌝)%A.
Proof. solve_assert. Qed.

Lemma assert_true_intro P δ : P ⊑@{δ} True%A.
Proof. solve_assert. Qed.
Lemma assert_false_elim P δ : False%A ⊑@{δ} P.
Proof. solve_assert. Qed.

Lemma assert_and_l P Q δ : (P ∧ Q)%A ⊑@{δ} P.
Proof. solve_assert. Qed.
Lemma assert_and_r P Q δ : (P ∧ Q)%A ⊑@{δ} Q.
Proof. solve_assert. Qed.
Lemma assert_and_intro P Q1 Q2 δ : P ⊑@{δ} Q1 → P ⊑@{δ} Q2 → P ⊑@{δ} (Q1 ∧ Q2)%A.
Proof. solve_assert. Qed.
Lemma assert_and_elim_l P1 P2 Q δ : P1 ⊑@{δ} Q → (P1 ∧ P2)%A ⊑@{δ} Q.
Proof. solve_assert. Qed.
Lemma assert_and_elim_r P1 P2 Q δ : P2 ⊑@{δ} Q → (P1 ∧ P2)%A ⊑@{δ} Q.
Proof. solve_assert. Qed.

Lemma assert_forall_intro {A} P (Q : A → assert) δ :
  (∀ x, P ⊑@{δ} Q x) → P ⊑@{δ} (∀ x, Q x)%A.
Proof. solve_assert. Qed.
Lemma assert_forall_specialize {A} (P : A → assert) Q δ x :
  (P x ⊑@{δ} Q) → (∀ x, P x)%A ⊑@{δ} Q.
Proof. solve_assert. Qed.

Lemma assert_exist_intro {A} P (Q : A → assert) δ x :
  P ⊑@{δ} Q x → P ⊑@{δ} (∃ x, Q x)%A.
Proof. solve_assert. Qed.
Lemma assert_exist_elim {A} (P : A → assert) Q δ :
  (∀ x, P x ⊑@{δ} Q) → (∃ x, P x)%A ⊑@{δ} Q.
Proof. solve_assert. Qed.

Lemma assert_or_l P Q δ : P ⊑@{δ} (P ∨ Q)%A.
Proof. solve_assert. Qed.
Lemma assert_or_r P Q δ : P ⊑@{δ} (P ∨ Q)%A.
Proof. solve_assert. Qed.
Lemma assert_or_elim P Q R δ : P ⊑@{δ} R → Q ⊑@{δ} R → (P ∨ Q)%A ⊑@{δ} R.
Proof. solve_assert. Qed.

Lemma assert_and_exist {A} P (Q : A → assert) δ :
  (P ∧ ∃ x, Q x)%A ≡@{δ} (∃ x, P ∧ Q x)%A.
Proof. solve_assert. Qed.
Lemma assert_exist_and {A} (P : A → assert) Q δ :
  ((∃ x, P x) ∧ Q)%A ≡@{δ} (∃ x, P x ∧ Q)%A.
Proof. solve_assert. Qed.

Lemma assert_Prop_intro_l (P : Prop) Q R δ :
  (P → Q ⊑@{δ} R) → (⌜ P ⌝ ∧ Q)%A ⊑@{δ} R.
Proof. solve_assert. Qed.
Lemma assert_Prop_intro_r (P : Prop) Q R δ :
  (P → Q ⊑@{δ} R) → (Q ∧ ⌜ P ⌝)%A ⊑@{δ} R.
Proof. solve_assert. Qed.

Lemma assert_Prop_and_elim (P : Prop) Q R δ :
  (P → Q ⊑@{δ} R) → (⌜ P ⌝ ∧ Q)%A ⊑@{δ} R.
Proof. solve_assert. Qed.
Lemma assert_and_Prop_elim (P : Prop) Q R δ :
  (P → Q ⊑@{δ} R) → (Q ∧ ⌜ P ⌝)%A ⊑@{δ} R.
Proof. solve_assert. Qed.
Lemma assert_Prop_and_intro (P : Prop) Q R δ :
  P → Q ⊑@{δ} R → Q ⊑@{δ} (⌜ P ⌝ ∧ R)%A.
Proof. solve_assert. Qed.
Lemma assert_and_Prop_intro (P : Prop) Q R δ :
  P → Q ⊑@{δ} R → Q ⊑@{δ} (R ∧ ⌜ P ⌝)%A.
Proof. solve_assert. Qed.

(** The assertion [e ⇓ v] asserts that the expression [e] evaluates to [v]
and [e ⇓ -] asserts that the expression [e] evaluates to an arbitrary value
(in other words, [e] does not impose undefined behavior). *)
Notation vassert := (val → assert).

Definition assert_expr (e : expr) : vassert := λ v,
  Assert $ λ δ ρ m, ⟦ e ⟧ δ ρ m = Some v.
Infix "⇓" := assert_expr (at level 60) : assert_scope.
Notation "(⇓)" := assert_expr (only parsing) : assert_scope.
Notation "( e ⇓)" := (assert_expr e) (only parsing) : assert_scope.
Notation "(⇓ v )" := (λ e, assert_expr e v) (only parsing) : assert_scope.

Notation "e ⇓ -" := (∃ v, e ⇓ v)%A
  (at level 60, format "e  '⇓'  '-'") : assert_scope.
Notation "(⇓ - )" := assert_expr (only parsing) : assert_scope.

Instance assert_expr_mem_ext e v : MemExt (e ⇓ v).
Proof.
  intros ρ m1 m2 ? Hm. unfold_assert in *. eauto using expr_eval_weaken_mem.
Qed.

Instance assert_expr_mem_indep e : load_free e → MemIndep (e ⇓ v).
Proof.
  intros ?? δ ρ m1 m2. unfold_assert.
  erewrite !(expr_load_free_mem_indep δ ρ m1 m2); eauto.
Qed.
Instance assert_expr_mem_indep_ e : load_free e → MemIndep (e ⇓ -).
Proof.
  intros ? δ ρ m1 m2 [v ?]. exists v. unfold_assert in *.
  erewrite !(expr_load_free_mem_indep δ ρ m2 m1); eauto.
Qed.

Instance assert_expr_stack_indep e v : vars e ≡ ∅ → StackIndep (e ⇓ v).
Proof.
  intros ? δ ρ1 ρ2 m. unfold_assert.
  by rewrite !(expr_var_free_stack_indep δ ρ2 ρ1).
Qed.
Instance assert_expr_stack_indep_ e : vars e ≡ ∅ → StackIndep (e ⇓ -).
Proof.
  intros ? δ ρ1 ρ2 m. unfold_assert.
  by rewrite !(expr_var_free_stack_indep δ ρ2 ρ1).
Qed.
Instance assert_expr_unlock_indep e v :
  UnlockIndep (e ⇓ v).
Proof. solve_assert eauto using expr_eval_unlock. Qed.
Instance assert_expr_unlock_indep_ e :
  UnlockIndep (e ⇓ -).
Proof. solve_assert eauto using expr_eval_unlock. Qed.

Lemma assert_expr_load e p v δ :
  (load e ⇓ p ∧ load (valc p) ⇓ v)%A ⊑@{δ} (load (load e) ⇓ v)%A.
Proof.
  intros ?? [He ?]. unfold_assert in *. rewrite He.
  by simplify_option_equality.
Qed.
Lemma assert_expr_forget e v δ : (e ⇓ v)%A ⊑@{δ} (e ⇓ -)%A.
Proof. solve_assert. Qed.

Notation "e ⇓ 'true'" := (∃ v, e⇓v ∧ ⌜ val_true v ⌝)%A
  (at level 60, format "e  '⇓'  'true'") : assert_scope.
Notation "e ⇓ 'false'" := (∃ v, e⇓v ∧ ⌜ val_false v ⌝)%A
  (at level 60, format "e  '⇓'  'false'") : assert_scope.

Definition assert_is_true (Pv : vassert) : assert :=
  (∃ v, Pv v ∧ ⌜ val_true v ⌝)%A.
Definition assert_is_false (Pv : vassert) : assert :=
  (∃ v, Pv v ∧ ⌜ val_false v ⌝)%A.

Definition assert_subst (a : index) (v : val) (P : assert) :=
  Assert $ λ δ ρ m, assert_holds δ P ρ (<[a:=v]>m).
Notation "<[ a := v ]>" := (assert_subst a v) : assert_scope.

Instance: ∀ a v, Proper ((≡@{δ}) ==> (≡@{δ})) (assert_subst a v).
Proof. solve_assert. Qed.

Lemma assert_subst_mem_indep P `{MemIndep P} δ a v: (<[a:=v]>P)%A ≡@{δ} P.
Proof. solve_assert. Qed.
Lemma assert_subst_impl P Q δ a v :
  (<[a:=v]>(P → Q))%A ≡@{δ} (<[a:=v]>P → <[a:=v]>Q)%A.
Proof. solve_assert. Qed.
Lemma assert_subst_not P δ a v : (<[a:=v]>(¬P))%A ≡@{δ} (¬<[a:=v]>P)%A.
Proof. solve_assert. Qed.
Lemma assert_subst_and P Q δ a v :
  (<[a:=v]>(P ∧ Q))%A ≡@{δ} (<[a:=v]>P ∧ <[a:=v]>Q)%A.
Proof. solve_assert. Qed.
Lemma assert_subst_or P Q δ a v :
  (<[a:=v]>(P ∨ Q))%A ≡@{δ} (<[a:=v]>P ∨ <[a:=v]>Q)%A.
Proof. solve_assert. Qed.
Lemma assert_subst_forall {A} (P : A → assert) δ a v :
  (<[a:=v]>(∀ x, P x))%A ≡@{δ} (∀ x, <[a:=v]>(P x))%A.
Proof. solve_assert. Qed.
Lemma assert_subst_exists {A} (P : A → assert) δ a v :
  (<[a:=v]>(∃ x, P x))%A ≡@{δ} (∃ x, <[a:=v]>(P x))%A.
Proof. solve_assert. Qed.

(** * Separation logic connectives *)
(** The assertion [emp] asserts that the memory is empty. The assertion [P ★ Q]
(called separating conjunction) asserts that the memory can be split into two
disjoint parts such that [P] holds in the one part, and [Q] in the other.
The assertion [P -★ Q] (called separating implication or magic wand) asserts
that if an arbitrary memory is extended with a disjoint part in which [P]
holds, then [Q] holds in the extended memory. *)
Definition assert_emp : assert := Assert $ λ δ ρ m, m = ∅.
Notation "'emp'" := assert_emp : assert_scope.

Definition assert_sep (P Q : assert) : assert :=
  Assert $ λ δ ρ m, ∃ m1 m2,
    m1 ∪ m2 = m ∧ ⊥[m1; m2] ∧ assert_holds δ P ρ m1 ∧ assert_holds δ Q ρ m2.
Infix "★" := assert_sep (at level 80, right associativity) : assert_scope.
Notation "(★)" := assert_sep (only parsing) : assert_scope.
Notation "( P ★)" := (assert_sep P) (only parsing) : assert_scope.
Notation "(★ Q )" := (λ P, assert_sep P Q) (only parsing) : assert_scope.

Definition assert_wand (P Q : assert) : assert :=
  Assert $ λ δ ρ m1, ∀ m2,
    ⊥[m1; m2] → assert_holds δ P ρ m2 → assert_holds δ Q ρ (m1 ∪ m2).
Infix "-★" := assert_wand (at level 90) : assert_scope.
Notation "(-★)" := assert_wand (only parsing) : assert_scope.
Notation "( P -★)" := (assert_wand P) (only parsing) : assert_scope.
Notation "(-★ Q )" := (λ P, assert_wand P Q) (only parsing) : assert_scope.

(** Compatibility of the separation logic connectives with respect to order and
equality. *)
Instance: Proper ((⊑@{δ}) ==> (⊑@{δ}) ==> (⊑@{δ})) (★)%A.
Proof. solve_assert. Qed.
Instance: Proper ((≡@{δ}) ==> (≡@{δ}) ==> (≡@{δ})) (★)%A.
Proof. solve_assert. Qed.
Instance: Proper (flip (⊑@{δ}) ==> (⊑@{δ}) ==> (⊑@{δ})) (-★)%A.
Proof. solve_assert. Qed.
Instance: Proper ((≡@{δ}) ==> (≡@{δ}) ==> (≡@{δ})) (-★)%A.
Proof. solve_assert. Qed.

(** Basic properties. *)
Lemma assert_sep_commutative_1 P Q δ : (P ★ Q)%A ⊑@{δ} (Q ★ P)%A.
Proof.
  intros ρ m (m1 & m2 & ? & ? & HP & HQ); simpl in *.
  exists m2 m1. rewrite mem_union_commutative; split_ands; auto with mem.
Qed.
Instance: Commutative (≡@{δ}) (★)%A.
Proof. split; apply assert_sep_commutative_1. Qed.

Lemma assert_sep_left_id_1 P δ : (emp ★ P)%A ⊑@{δ} P.
Proof.
  intros ρ m (m1 & m2 & H & ? & ? & Hm2). simpl in *.
  unfold_assert in *. subst. by rewrite (left_id_L ∅ (∪)).
Qed.
Lemma assert_sep_left_id_2 P δ : P ⊑@{δ} (emp ★ P)%A.
Proof.
  intros ? m ?. exists (∅ : mem) m. rewrite (left_id_L ∅ (∪)). solve_assert.
Qed.
Instance: LeftId (≡@{δ}) emp%A (★)%A.
Proof. split. apply assert_sep_left_id_1. apply assert_sep_left_id_2. Qed.
Instance: RightId (≡@{δ}) emp%A (★)%A.
Proof. intros ??. by rewrite (commutative _), (left_id _ _). Qed.

Instance: LeftAbsorb (≡@{δ}) False%A (★)%A.
Proof. solve_assert. Qed.
Instance: RightAbsorb (≡@{δ}) False%A (★)%A.
Proof. solve_assert. Qed.

Lemma assert_sep_associative_1 P Q R δ : ((P ★ Q) ★ R)%A ⊑@{δ} (P ★ (Q ★ R))%A.
Proof.
  intros ?? (?&mR&?&?& (mP&mQ&?&?&?&?) &?); simpl in *; subst.
  exists mP (mQ ∪ mR). split_ands; auto.
  * apply (associative_L (∪)).
  * solve_mem_disjoint.
  * exists mQ mR. split_ands; auto with mem.
Qed.

Lemma assert_sep_associative_2 P Q R δ : (P ★ (Q ★ R))%A ⊑@{δ} ((P ★ Q) ★ R)%A.
Proof.
  intros ?? (mP&?&?&?&?&mQ&mR&?&?&?&?); simpl in *; subst.
  exists (mP ∪ mQ) mR. split_ands; auto.
  * by rewrite (associative_L (∪)).
  * solve_mem_disjoint.
  * exists mP mQ. split_ands; auto with mem.
Qed.
Instance: Associative (≡@{δ}) (★)%A.
Proof.
  split. apply assert_sep_associative_2. apply assert_sep_associative_1.
Qed.

Lemma assert_wand_intro P Q R δ : (P ★ Q)%A ⊑@{δ} R → P ⊑@{δ} (Q -★ R)%A.
Proof. solve_assert. Qed.
Lemma assert_wand_elim δ P Q : (P ★ (P -★ Q))%A ⊑@{δ} Q.
Proof. rewrite (commutative (★))%A. solve_assert. Qed.

Lemma assert_and_sep_associative P Q R δ :
  MemIndep P → (P ∧ (Q ★ R))%A ≡@{δ} ((P ∧ Q) ★ R)%A.
Proof. solve_assert. Qed.
Lemma assert_sep_and_associative P Q R δ :
  MemIndep R → (P ★ (Q ∧ R))%A ≡@{δ} ((P ★ Q) ∧ R)%A.
Proof. solve_assert. Qed.
Lemma assert_sep_and_swap P Q R δ :
  MemIndep Q → (P ★ (Q ∧ R))%A ≡@{δ} ((P ∧ Q) ★ R)%A.
Proof. solve_assert. Qed.

Lemma assert_sep_exist {A} P (Q : A → assert) δ :
  (P ★ ∃ x, Q x)%A ≡@{δ} (∃ x, P ★ Q x)%A.
Proof. solve_assert. Qed.
Lemma assert_exist_sep {A} (P : A → assert) Q δ :
  ((∃ x, P x) ★ Q)%A ≡@{δ} (∃ x, P x ★ Q)%A.
Proof. solve_assert. Qed.

(** The separation conjunction allows us to give an alternative formulation
of memory extensibility. *)
Lemma mem_ext_sep_true P `{MemExt P} δ : P ≡@{δ} (P ★ True)%A.
Proof.
  split.
  * intros ? m ?. exists m (∅ : mem). rewrite (right_id_L ∅ (∪)). solve_assert.
  * intros ?? (m1&m2&?&?&?&?); subst. apply mem_ext with m1; auto with mem.
Qed.
Lemma assert_sep_true_mem_ext P : (∀ δ, P ≡@{δ} (P ★ True)%A) → MemExt P.
Proof.
  intros H δ ρ m1 m2 ??. rewrite H. exists m1 (m2 ∖ m1).
  unfold_assert. split_ands; auto.
  * by rewrite mem_union_difference.
  * rewrite <-mem_disjoint_difference by done. solve_mem_disjoint.
Qed.
Lemma mem_ext_sep_true_iff P : (∀ δ, P ≡@{δ} (P ★ True)%A) ↔ MemExt P.
Proof. split; auto using @mem_ext_sep_true, assert_sep_true_mem_ext. Qed.

(** Other type class instances for stack independence, memory independence, and
memory extensibility. *)
Instance assert_emp_stack_indep : StackIndep emp.
Proof. solve_assert. Qed.
Instance assert_emp_fun_indep fs : FunIndep fs emp.
Proof. solve_assert. Qed.
Instance assert_emp_unlock_indep : UnlockIndep emp.
Proof.
  intros δ ρ Ω m ?; unfold_assert in *; subst. by rewrite mem_unlock_empty.
Qed.

Instance assert_sep_stack_indep :
  StackIndep P → StackIndep Q → StackIndep (P ★ Q).
Proof. solve_assert. Qed.
Instance assert_sep_mem_indep : MemIndep P → MemIndep Q → MemIndep (P ★ Q).
Proof.
  intros ????? ? m1 m2 (m2' & m2'' &?&?&?&?). subst.
  exists m2 (∅ : mem). rewrite (right_id_L ∅ (∪)). solve_assert.
Qed.
Instance assert_sep_mem_ext_2 : MemExt Q → MemExt (P ★ Q).
Proof.
  intros ???? ? m1 m2 (m2' & m2'' &?&?&?&?) ?. subst.
  exists m2' (m2'' ∪ m2 ∖ (m2' ∪ m2'')). split_ands; auto.
  * by rewrite (associative_L (∪)), mem_union_difference.
  * rewrite <-mem_disjoint_union_le, <-(mem_disjoint_union m2') by done.
    by apply mem_disjoint_difference_alt.
  * apply mem_ext with m2''; auto. apply mem_union_subseteq_l.
    rewrite (mem_union_subseteq_r m2' m2'') at 1 by done.
    by apply mem_disjoint_difference_alt.
Qed.
Instance assert_sep_mem_ext_l : MemExt P → MemExt (P ★ Q).
Proof.
  intros P Q ?????. rewrite !(commutative (★) P)%A.
  by apply assert_sep_mem_ext_2.
Qed.
Instance assert_sep_fun_indep :
  FunIndep fs P → FunIndep fs Q → FunIndep fs (P ★ Q).
Proof. solve_assert eauto. Qed.
Instance assert_sep_unlock_indep P Q :
  UnlockIndep P → UnlockIndep Q → UnlockIndep (P ★ Q).
Proof.
  intros ?? δ Ω ρ m (m1 & m2 &?&?&?&?); subst.
  exists (mem_unlock Ω m1) (mem_unlock Ω m2). rewrite mem_unlock_union by done.
  split_ands; auto. by rewrite <-!mem_disjoint_unlock.
Qed.

(** Proofs of other useful properties. *)
Lemma assert_and_sep_emp_l P Q δ :
  MemIndep P → (P ∧ Q)%A ≡@{δ} ((P ∧ emp) ★ Q)%A.
Proof. intro. by rewrite <-assert_and_sep_associative, (left_id emp (★))%A. Qed.
Lemma assert_and_sep_emp_r P Q δ :
  MemIndep Q → (P ∧ Q)%A ≡@{δ} (P ★ (Q ∧ emp))%A.
Proof. intro. by rewrite !(commutative _ P), assert_and_sep_emp_l. Qed.

Lemma assert_sep_elim_l P1 P2 Q δ :
  MemExt Q → P1 ⊑@{δ} Q → (P1 ★ P2)%A ⊑@{δ} Q.
Proof. intros ? H. by rewrite (mem_ext_sep_true Q), H, <-assert_true_intro. Qed.
Lemma assert_sep_elim_r P1 P2 Q δ :
  MemExt Q → P2 ⊑@{δ} Q → (P1 ★ P2)%A ⊑@{δ} Q.
Proof. rewrite (commutative (★))%A. apply assert_sep_elim_l. Qed.

(** The assertion [Π Ps] states that the memory can be split into disjoint
parts such that for each part the corresponding assertion in [Ps] holds. *)
Definition assert_sep_list : list assert → assert := foldr (★)%A emp%A.
Notation "'Π' Ps" := (assert_sep_list Ps)
  (at level 20, format "Π  Ps") : assert_scope.
Instance: Proper (Forall2 (≡@{δ}) ==> (≡@{δ})) assert_sep_list.
Proof. induction 1; simpl; by f_equiv. Qed.

Lemma assert_sep_list_alt_2 (Ps : list assert) δ ρ ms :
  ⊥ ms → Forall2 (λ (P : assert) m, assert_holds δ P ρ m) Ps ms →
  assert_holds δ (Π Ps)%A ρ (⋃ ms).
Proof.
  intros Hms HPs. revert Hms. induction HPs as [|P m Ps ms IH].
  + done.
  + exists m (⋃ ms); simpl; auto. solve_assert.
Qed.
Lemma assert_sep_list_alt (Ps : list assert) δ ρ m :
  assert_holds δ (Π Ps)%A ρ m ↔ ∃ ms,
    m = ⋃ ms ∧ ⊥ ms ∧ Forall2 (λ (P : assert) m, assert_holds δ P ρ m) Ps ms.
Proof.
  split.
  * revert m. induction Ps as [|P Ps IH].
    { eexists []. by repeat constructor. }
    intros ? (m1 & m2 & ? & ? & ? & ?); simpl in *; subst.
    destruct (IH m2) as (ms & ? & ? & ?); trivial; subst.
    exists (m1 :: ms). split_ands; trivial.
    + solve_mem_disjoint.
    + constructor; auto.
  * naive_solver auto using assert_sep_list_alt_2.
Qed.

Lemma assert_sep_list_alt_vec {n} (Ps : vec assert n) δ ρ m :
  assert_holds δ (Π Ps)%A ρ m ↔ ∃ ms : vec mem n,
    m = ⋃ ms ∧ ⊥ ms ∧ ∀ i, assert_holds δ (Ps !!! i) ρ (ms !!! i).
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
Lemma assert_sep_list_alt_vec_2 {n} (Ps : vec assert n) δ ρ (ms : vec mem n) :
  ⊥ ms → (∀ i, assert_holds δ (Ps !!! i) ρ (ms !!! i)) →
  assert_holds δ (Π Ps)%A ρ (⋃ ms).
Proof. intros. apply assert_sep_list_alt_vec. eauto. Qed.

(** The assertion [e1 ↦{γ} e2] asserts that the memory consists of exactly one
cell at address [e1] with permission [γ] and contents [e2]. The assertion
[e1 ↦{γ} -] asserts that the memory consists of exactly one cell at address
[e1] with permission [γ] and arbitrary contents. *)
Definition assert_singleton (e1 e2 : expr) (γ : memperm) : assert :=
  Assert $ λ δ ρ m, ∃ a v,
    ⟦ e1 ⟧ δ ρ m = Some (ptrc a)%V ∧ ⟦ e2 ⟧ δ ρ m = Some v ∧ m = {[(a,v,γ)]}.
Notation "e1 ↦{ γ } e2" := (assert_singleton e1 e2 γ)%A
  (at level 20, format "e1  ↦{ γ }  e2") : assert_scope.
Notation "e ↦{ γ } -" := (∃ v, e ↦{ γ } valc v)%A
  (at level 20, format "e  ↦{ γ }  -") : assert_scope.

Lemma assert_singleton_forget δ e1 e2 γ : (e1 ↦{γ} e2)%A ⊑@{δ} (e1 ↦{γ} -)%A.
Proof. solve_assert. Qed.

Instance assert_singleton_stack_indep e1 e2 γ :
  vars e1 ≡ ∅ → vars e2 ≡ ∅ → StackIndep (e1 ↦{γ} e2).
Proof.
  intros ?? δ ρ1 ρ2 m (a & v & ?). exists a v.
  by rewrite !(expr_var_free_stack_indep δ ρ2 ρ1).
Qed.
Instance assert_singleton_stack_indep_ e γ : vars e ≡ ∅ → StackIndep (e ↦{γ} -).
Proof.
  intros; apply assert_exist_stack_indep.
  by intros; apply assert_singleton_stack_indep.
Qed.
Instance assert_singleton_unlock_indep e1 e2 γ :
  perm_kind γ ≠ Locked → UnlockIndep (e1 ↦{γ} e2).
Proof.
  intros ? δ Ω ρ m (a & v &?&?&?); subst. exists a v.
  split_ands; eauto using expr_eval_unlock. destruct (decide (a ∈ Ω)).
  * by rewrite mem_unlock_singleton, perm_unlock_other.
  * by rewrite mem_unlock_singleton_ne.
Qed.
Instance assert_singleton_unlock_indep_ e γ :
  perm_kind γ ≠ Locked → UnlockIndep (e ↦{γ} -).
Proof.
  intros; apply assert_exist_unlock_indep.
  by intros; apply assert_singleton_unlock_indep.
Qed.
Lemma assert_singleton_eval_l_1 δ e1 v1 e2 γ :
  (e1 ⇓ v1 ∧ valc v1 ↦{γ} e2)%A ⊑@{δ} (e1 ↦{γ} e2)%A.
Proof. solve_assert. Qed.
Lemma assert_singleton_eval_r_1 δ e1 e2 v2 γ :
  (e1 ↦{γ} valc v2 ∧ e2 ⇓ v2)%A ⊑@{δ} (e1 ↦{γ} e2)%A.
Proof. solve_assert. Qed.
Lemma assert_singleton_eval__1 δ e v γ :
  (e ⇓ v ∧ valc v ↦{γ} -)%A ⊑@{δ} (e ↦{γ} -)%A.
Proof. solve_assert. Qed.

Lemma assert_eval_singleton_l_1 δ e1 v1 e2 γ :
  (e1 ⇓ v1 ∧ e1 ↦{γ} e2)%A ⊑@{δ} (valc v1 ↦{γ} e2)%A.
Proof.
  intros ?? (?&?&?&?&?&?); unfold_assert in *;
    simplify_option_equality; naive_solver.
Qed.
Lemma assert_eval_singleton_r_1 δ e1 e2 v2 γ :
  (e1 ↦{γ} e2 ∧ e2 ⇓ v2)%A ⊑@{δ} (e1 ↦{γ} valc v2)%A.
Proof.
  intros ?? ((?&?&?&?&?)&?); unfold_assert in *;
    simplify_option_equality; naive_solver.
Qed.
Lemma assert_eval_singleton__1 δ e v γ :
  (e ⇓ v ∧ e ↦{γ} -)%A ⊑@{δ} (valc v ↦{γ} -)%A.
Proof.
  intros ?? (?&?&?&?&?&?&?); unfold_assert in *;
    simplify_option_equality; naive_solver.
Qed.

Lemma assert_singleton_eval_l δ e1 e2 γ :
  (∃ v1, e1 ⇓ v1 ∧ valc v1 ↦{γ} e2)%A ≡@{δ} (e1 ↦{γ} e2)%A.
Proof. solve_assert. Qed.
Lemma assert_singleton_eval_r δ e1 e2 γ :
  (∃ v2, e1 ↦{γ} valc v2 ∧ e2 ⇓ v2)%A ≡@{δ} (e1 ↦{γ} e2)%A.
Proof. solve_assert. Qed.
Lemma assert_singleton_eval_ δ e γ :
  (∃ v, e ⇓ v ∧ valc v ↦{γ} -)%A ≡@{δ} (e ↦{γ} -)%A.
Proof. solve_assert. Qed.

Lemma assert_singleton_eval_l_alt δ e1 e2 γ :
  (e1 ↦{γ} e2)%A ≡@{δ} (e1 ⇓ - ∧ e1 ↦{γ} e2)%A.
Proof. solve_assert. Qed.
Lemma assert_singleton_eval_alt δ e γ :
  (e ↦{γ} -)%A ≡@{δ} (e ⇓ - ∧ e ↦{γ} -)%A.
Proof. solve_assert. Qed.

(** The assertion [e1 ↪{γ} e2] asserts that the memory contains at least one
cell at address [e1] with permission [γ] and contents [e2]. The assertion
[e1 ↪{γ} -] asserts that the memory contains at least one cell at address
[e1] with permission [γ] and arbitrary contents. *)
Definition assert_assign (e1 e2 : expr) (γ : memperm) : assert :=
  Assert $ λ δ ρ m, ∃ a v,
    ⟦ e1 ⟧ δ ρ m = Some (ptrc a)%V ∧ ⟦ e2 ⟧ δ ρ m = Some v ∧ {[(a,v,γ)]} ⊆ m.
Notation "e1 ↪{ γ } e2" := (assert_assign e1 e2 γ)%A
  (at level 20, format "e1  ↪{ γ }  e2") : assert_scope.
Notation "e ↪{ γ } -" := (∃ v, e ↪{γ} valc v)%A
  (at level 20, format "e  ↪{ γ }  -") : assert_scope.

Lemma assert_assign_forget δ e1 e2 γ : (e1 ↪{γ} e2)%A ⊑@{δ} (e1 ↪{γ} -)%A.
Proof. solve_assert. Qed.
Lemma assert_singleton_assign δ e1 e2 γ : (e1 ↦{γ} e2)%A ⊑@{δ} (e1 ↪{γ} e2)%A.
Proof. solve_assert. Qed.
Lemma assert_singleton_assign_ δ e γ : (e ↦{γ} -)%A ⊑@{δ} (e ↪{γ} -)%A.
Proof. solve_assert. Qed.

Lemma assert_assign_eval_l δ e1 v1 e2 γ :
  (e1 ⇓ v1 ∧ valc v1 ↪{γ} e2)%A ⊑@{δ} (e1 ↪{γ} e2)%A.
Proof. solve_assert. Qed.
Lemma assert_assign_eval_r δ e1 v2 e2 γ :
  (e1 ↪{γ} valc v2 ∧ e2 ⇓ v2)%A ⊑@{δ} (e1 ↪{γ} e2)%A.
Proof. solve_assert. Qed.
Lemma assert_assign_eval_ δ e v γ :
  (e ⇓ v ∧ valc v ↪{γ} -)%A ⊑@{δ} (e ↪{γ} -)%A.
Proof. solve_assert. Qed.

Instance assert_assign_stack_indep e1 e2 γ :
  vars e1 ≡ ∅ → vars e2 ≡ ∅ → StackIndep (e1 ↪{γ} e2).
Proof.
  intros ?? δ ρ1 ρ2 m (a&v&γ'&?). exists a v.
  by rewrite !(expr_var_free_stack_indep δ ρ2 ρ1).
Qed.
Instance assert_assign_stack_indep_ e γ : vars e ≡ ∅ → StackIndep (e ↪{γ} -).
Proof.
  intros; apply assert_exist_stack_indep.
  by intros; apply assert_assign_stack_indep.
Qed.

Instance assert_assign_mem_ext e1 e2 γ : MemExt (e1 ↪{γ} e2).
Proof.
  intros δ ρ m1 m2 (a&v&γ2&?&?) Hm12. exists a v.
  split_ands; eauto using expr_eval_weaken_mem. by transitivity m1.
Qed.
Instance assert_assign_mem_ext_ e γ : MemExt (e ↪{γ} -).
Proof.
  apply assert_exist_mem_ext. by intros; apply assert_assign_mem_ext.
Qed.

Lemma assign_assign_alt δ e1 e2 γ :
  load_free e1 → load_free e2 → (e1 ↪{γ} e2)%A ≡@{δ} (e1 ↦{γ} e2 ★ True)%A.
Proof.
  split.
  * intros ρ m (a&v&γ'&?&?).
    eexists {[ (a,v,γ) ]}, (m ∖ {[ (a,v,γ) ]}). split_ands.
    + by apply mem_union_difference.
    + by apply mem_disjoint_difference_alt.
    + exists a v. erewrite !(expr_load_free_mem_indep _ _ {[(a,v,γ)]} m); eauto.
    + done.
  * rewrite assert_singleton_assign. apply (mem_ext_sep_true _).
Qed.
Lemma assert_assign_assign_alt_ δ e γ :
  load_free e → (e ↪{γ} -)%A ≡@{δ} (e ↦{γ} - ★ True)%A.
Proof.
  intros. rewrite !assert_exist_sep. f_equiv; intros v.
  by apply assign_assign_alt; repeat constructor.
Qed.

Lemma assert_assign_load δ e v γ :
  perm_kind γ ≠ Locked → (e ↪{γ} valc v)%A ⊑@{δ} (load e ⇓ v)%A.
Proof.
  intros ? ρ m (a&v'&Ha&?&?); unfold_assert.
  rewrite Ha. simplify_option_equality.
  by apply mem_lookup_weaken with {[(a, v', γ)]}; simpl_mem.
Qed.
Lemma assert_assign_load_ δ e γ :
  perm_kind γ ≠ Locked → (e ↪{γ} -)%A ⊑@{δ} (load e ⇓ -)%A.
Proof.
  intros. apply assert_exist_elim; intros v.
  by apply assert_exist_intro with v, assert_assign_load.
Qed.

Lemma assert_singleton_load δ e v γ :
  perm_kind γ ≠ Locked → (e ↦{γ} valc v)%A ⊑@{δ} (load e ⇓ v)%A.
Proof.
  intros. rewrite assert_singleton_assign. by apply assert_assign_load.
Qed.
Lemma assert_singleton_load_ δ e γ :
  perm_kind γ ≠ Locked → (e ↦{γ} -)%A ⊑@{δ} (load e ⇓ -)%A.
Proof.
  intros. by rewrite <-assert_assign_load_, assert_singleton_assign_.
Qed.

Lemma assert_singleton_half δ e1 e2 γ :
  perm_kind γ ≠ Locked → (e1 ↦{γ.½} e2 ★ e1 ↦{γ.½} e2)%A ≡@{δ} (e1 ↦{γ} e2)%A.
Proof.
  intros. split.
  * intros ?? (m1 & m2 & ?&?&(a1&v1&?&?&?)&(a2&v2&?&?&?)).
    simplify_expr_equality. exists a2 v2. split_ands.
    + eapply expr_eval_weaken_mem; eauto using mem_union_subseteq_r.
    + eapply expr_eval_weaken_mem; eauto using mem_union_subseteq_r.
    + by rewrite mem_union_double, perm_union_half.
  * intros ?? (a&v&?&?&?); subst. exists {[(a, v, γ.½)]} {[(a, v, γ.½)]}.
    split_ands; auto.
    + by rewrite mem_union_double, perm_union_half.
    + by apply mem_disjoint_double_same, perm_disjoint_half.
    + exists a v; split_ands; auto; eapply expr_eval_weaken_mem_lookup;
       eauto; by intros; simplify_mem_equality.
    + exists a v; split_ands; auto; eapply expr_eval_weaken_mem_lookup;
       eauto; by intros; simplify_mem_equality.
Qed.

(** The assertion [P▷] asserts that [P] holds if all sequenced locations
are unlocked. *)
Definition assert_unlock (P : assert) : assert :=
  Assert $ λ δ ρ m, assert_holds δ P ρ (mem_unlock (locks m) m).
Notation "P ▷" := (assert_unlock P) (at level 20) : assert_scope.

Instance: Proper ((⊑@{δ}) ==> (⊑@{δ})) assert_unlock.
Proof. solve_assert. Qed.
Instance: Proper ((≡@{δ}) ==> (≡@{δ})) assert_unlock.
Proof. solve_assert. Qed.

Lemma assert_unlock_unlock_indep P `{UnlockIndep P} δ : P ⊑@{δ} (P ▷)%A.
Proof. solve_assert. Qed.
Lemma assert_unlock_impl P Q δ : ((P → Q) ▷)%A ≡@{δ} (P ▷ → Q ▷)%A.
Proof. solve_assert. Qed.
Lemma assert_unlock_not P δ : ((¬P)▷)%A ≡@{δ} (¬P ▷)%A.
Proof. solve_assert. Qed.
Lemma assert_unlock_and P Q δ : ((P ∧ Q) ▷)%A ≡@{δ} (P ▷ ∧ Q ▷)%A.
Proof. solve_assert. Qed.
Lemma assert_unlock_or P Q δ : ((P ∨ Q) ▷)%A ≡@{δ} (P ▷ ∨ Q ▷)%A.
Proof. solve_assert. Qed.
Lemma assert_unlock_sep P Q δ : (P ▷ ★ Q ▷)%A ⊑@{δ} ((P ★ Q) ▷)%A.
Proof.
  intros ?? (m1&m2&?&?&?&?). exists (mem_unlock_all m1) (mem_unlock_all m2).
  split_ands; trivial.
  * subst. by rewrite <-mem_unlock_all_union.
  * by rewrite <-!mem_disjoint_unlock.
Qed.
Lemma assert_unlock_sep_alt P P' Q Q' δ :
  P ⊑@{δ} (P' ▷)%A → Q ⊑@{δ} (Q' ▷)%A → (P ★ Q)%A ⊑@{δ} ((P' ★ Q') ▷)%A.
Proof. intros HP HQ. rewrite HP, HQ. apply assert_unlock_sep. Qed.

Lemma assert_unlock_forall {A} (P : A → assert) δ :
  ((∀ x, P x)▷)%A ≡@{δ} (∀ x, (P x)▷)%A.
Proof. solve_assert. Qed.
Lemma assert_unlock_exists {A} (P : A → assert) δ :
  ((∃ x, P x) ▷)%A ≡@{δ} (∃ x, (P x)▷)%A.
Proof. solve_assert. Qed.

Lemma assert_unlock_expr δ e v : (e ⇓ v)%A ⊑@{δ} ((e ⇓ v) ▷)%A.
Proof. intros ρ m ?. by apply expr_eval_unlock. Qed.
Lemma assert_unlock_expr_ δ e : (e ⇓ -)%A ⊑@{δ} ((e ⇓ -) ▷)%A.
Proof. intros ρ m (v&?). exists v. by apply expr_eval_unlock. Qed.

Lemma assert_unlock_singleton δ e1 e2 γ :
  (e1 ↦{γ} e2)%A ⊑@{δ} ((e1 ↦{perm_unlock γ} e2)▷)%A.
Proof.
  intros ρ m (a&v&?&?&?). exists a v. split_ands.
  * unfold_assert. eauto using expr_eval_unlock.
  * unfold_assert. eauto using expr_eval_unlock.
  * subst. apply mem_unlock_all_singleton.
Qed.
Lemma assert_lock_singleton δ e1 e2 γ :
  Write ⊆ perm_kind γ → (e1 ↦{perm_lock γ} e2)%A ⊑@{δ} ((e1 ↦{γ} e2)▷)%A.
Proof.
  intros. etransitivity; [apply assert_unlock_singleton|].
  by rewrite perm_unlock_lock.
Qed.

Lemma assert_unlock_singleton_ δ e1 γ :
  (e1 ↦{γ} -)%A ⊑@{δ} ((e1 ↦{perm_unlock γ} -)▷)%A.
Proof.
  apply assert_exist_elim; intros v. rewrite assert_unlock_exists.
  apply assert_exist_intro with v, assert_unlock_singleton.
Qed.
Lemma assert_lock_singleton_ δ e1 γ :
  Write ⊆ perm_kind γ → (e1 ↦{perm_lock γ} -)%A ⊑@{δ} ((e1 ↦{γ} -)▷)%A.
Proof.
  intros. etransitivity; [apply assert_unlock_singleton_|].
  by rewrite perm_unlock_lock.
Qed.

Lemma assert_unlock_singleton_other δ e1 e2 γ :
  perm_kind γ ≠ Locked → (e1 ↦{γ} e2)%A ⊑@{δ} ((e1 ↦{γ} e2)▷)%A.
Proof.
  intros ? ρ m (a&v&?&?&?). exists a v. split_ands.
  * unfold_assert. eauto using expr_eval_unlock.
  * unfold_assert. eauto using expr_eval_unlock.
  * subst. by rewrite mem_unlock_all_singleton, perm_unlock_other.
Qed.
Lemma assert_unlock_singleton_other_ δ e γ :
  perm_kind γ ≠ Locked → (e ↦{γ} -)%A ⊑@{δ} ((e ↦{γ} -)▷)%A.
Proof.
  intros. apply assert_exist_elim; intros v. rewrite assert_unlock_exists.
  by apply assert_exist_intro with v, assert_unlock_singleton_other.
Qed.

(** The assertion [P↡] asserts that [P] holds if the stack is cleared. This
connective allows us to specify stack independence in an alternative way. *)
Definition assert_clear_stack (P : assert) : assert :=
  Assert $ λ δ _ m, assert_holds δ P [] m.
Notation "P ↡" := (assert_clear_stack P) (at level 20) : assert_scope.

Instance assert_clear_stack_clear_stack_indep: StackIndep (P↡).
Proof. solve_assert. Qed.
Lemma stack_indep_clear_stack P `{StackIndep P} δ : (P↡)%A ≡@{δ} P.
Proof. solve_assert. Qed.
Lemma stack_indep_clear_stack_iff P : StackIndep P ↔ (∀ δ, (P↡)%A ≡@{δ} P).
Proof. solve_assert. Qed.

Lemma assert_clear_stack_impl P Q δ : ((P → Q)↡)%A ≡@{δ} (P↡ → Q↡)%A.
Proof. solve_assert. Qed.
Lemma assert_clear_stack_not P δ : ((¬P)↡)%A ≡@{δ} (¬P↡)%A.
Proof. solve_assert. Qed.
Lemma assert_clear_stack_and P Q δ : ((P ∧ Q)↡)%A ≡@{δ} (P↡ ∧ Q↡)%A.
Proof. solve_assert. Qed.
Lemma assert_clear_stack_or P Q δ : ((P ∨ Q)↡)%A ≡@{δ} (P↡ ∨ Q↡)%A.
Proof. solve_assert. Qed.
Lemma assert_clear_stack_sep P Q δ : ((P ★ Q)↡)%A ≡@{δ} (P↡ ★ Q↡)%A.
Proof. solve_assert. Qed.

Instance: Proper ((⊑@{δ}) ==> (⊑@{δ})) assert_clear_stack.
Proof. solve_assert. Qed.
Instance: Proper ((≡@{δ}) ==> (≡@{δ})) assert_clear_stack.
Proof. solve_assert. Qed.

(** To deal with block scope variables we need to lift an assertion such that
the De Bruijn indexes of its variables are increased. We define the lifting
[P↑] of an assertion [P] semantically, and prove that it indeed behaves as
expected. *)
Definition assert_lift (P : assert) : assert :=
  Assert $ λ δ ρ m, assert_holds δ P (tail ρ) m.
Notation "P ↑" := (assert_lift P) (at level 20) : assert_scope.

Lemma assert_lift_expr δ e v : ((e ⇓ v)↑)%A ≡@{δ} ((e↑) ⇓ v)%A.
Proof. by split; intros ??; unfold_assert; rewrite expr_eval_lift. Qed.
Lemma assert_lift_expr_ δ e : ((e ⇓ -)↑)%A ≡@{δ} ((e↑) ⇓ -)%A.
Proof. by split; intros ??; unfold_assert; rewrite expr_eval_lift. Qed.
Lemma assert_lift_singleton δ e1 e2 γ :
  ((e1 ↦{γ} e2)↑)%A ≡@{δ} ((e1↑) ↦{γ} (e2↑))%A.
Proof.
  split; intros ??; unfold_assert; intros H.
  * by rewrite !expr_eval_lift.
  * by rewrite !expr_eval_lift in H.
Qed.
Lemma assert_lift_singleton_ δ e γ : ((e ↦{γ} -)↑)%A ≡@{δ} ((e↑) ↦{γ} -)%A.
Proof.
  split; intros ??; unfold_assert; intros H.
  * by rewrite !expr_eval_lift.
  * by rewrite !expr_eval_lift in H.
Qed.
Lemma assert_lift_impl P Q δ : ((P → Q)↑)%A ≡@{δ} (P↑ → Q↑)%A.
Proof. solve_assert. Qed.
Lemma assert_lift_not P δ : ((¬P)↑)%A ≡@{δ} (¬P↑)%A.
Proof. solve_assert. Qed.
Lemma assert_lift_and P Q δ : ((P ∧ Q)↑)%A ≡@{δ} (P↑ ∧ Q↑)%A.
Proof. solve_assert. Qed.
Lemma assert_lift_or P Q δ : ((P ∨ Q)↑)%A ≡@{δ} (P↑ ∨ Q↑)%A.
Proof. solve_assert. Qed.
Lemma assert_lift_sep P Q δ : ((P ★ Q)↑)%A ≡@{δ} (P↑ ★ Q↑)%A.
Proof. solve_assert. Qed.
Lemma assert_lift_forall {A} (P : A → assert) δ :
  ((∀ x, P x)↑)%A ≡@{δ} (∀ x, P x↑)%A.
Proof. solve_assert. Qed.
Lemma assert_lift_exists {A} (P : A → assert) δ :
  ((∃ x, P x)↑)%A ≡@{δ} (∃ x, P x↑)%A.
Proof. solve_assert. Qed.

Instance: Proper ((⊑@{δ}) ==> (⊑@{δ})) assert_lift.
Proof. solve_assert. Qed.
Instance: Proper ((≡@{δ}) ==> (≡@{δ})) assert_lift.
Proof. solve_assert. Qed.

Instance assert_lift_stack_indep: StackIndep P → StackIndep (P↑).
Proof. solve_assert. Qed.
Lemma stack_indep_lift P `{StackIndep P} δ : (P↑)%A ≡@{δ} P.
Proof. solve_assert. Qed.

(** The assertion [assert_forall2 P xs ys] asserts that [P x y] holds for each
corresponding pair [x] and [y] of elements of [xs] and [ys]. *)
Definition assert_Forall2 `(P : A → B → assert) : list A → list B → assert :=
  fix go xs ys :=
  match xs, ys with
  | [], [] => True
  | x :: xs, y :: ys => P x y ∧ go xs ys
  | _, _ => False
  end%A.

(** An alternative semantic formulation of the above assertion. *)
Lemma assert_Forall2_correct `(P : A → B → assert) δ ρ m xs ys :
  assert_holds δ (assert_Forall2 P xs ys) ρ m ↔
    Forall2 (λ x y, assert_holds δ (P x y) ρ m) xs ys.
Proof.
  split.
  * revert ys. induction xs; intros [|??]; solve_assert.
  * induction 1; solve_assert.
Qed.

(** The rule for blocks is of the shape [{ var 0 ↦ - * P↑ } blk s
{ var 0 ↦ - * Q↑ }] implies [{P} s {Q}]. We prove that this pre and
postcondition is correct with respect to allocation of a local variable when
entering a block and freeing a local variable when leaving a block. *)
Lemma assert_alloc (P : assert) δ ρ m b v γ :
  is_free m b → assert_holds δ P ρ m →
  assert_holds δ (var 0 ↦{γ} - ★ P↑)%A (b :: ρ) (mem_alloc b v γ m).
Proof.
  intros ??. eexists {[(b,v,γ)]}, m. split_ands.
  * by rewrite mem_alloc_singleton_l.
  * by apply mem_disjoint_singleton_l.
  * by exists v b v.
  * done.
Qed.

Lemma assert_free (P : assert) δ ρ m b γ :
  ¬perm_fragment γ → assert_holds δ (var 0 ↦{γ} - ★ P↑)%A (b :: ρ) m →
  assert_holds δ P ρ (delete b m) ∧ mem_perm b m = Some γ.
Proof.
  intros ? (m1 & m2 &?&?& (?&a&v&?&?&?)&?); simplify_equality. split.
  * rewrite mem_delete_union, mem_delete_singleton, (left_id_L ∅ (∪)),
      mem_delete_free; eauto using mem_disjoint_singleton_l_inv.
  * apply mem_perm_union_Some_l.
    + apply mem_perm_singleton.
    + by apply mem_disjoint_singleton_l_inv with γ v.
Qed.

(** We prove some properties related to allocation of local variables when
calling a function, and to freeing these when returning from the function
call. *)
Lemma assert_alloc_params (P : assert) δ ρ m1 γ bs vs m2 :
  StackIndep P → alloc_params γ m1 bs vs m2 → assert_holds δ P ρ m1 →
  assert_holds δ (Π imap (λ i v, var i ↦{γ} valc v) vs ★ P)%A (bs ++ ρ) m2.
Proof.
  intros ? Halloc ?. cut (∀ bs',
    assert_holds δ (Π imap_go (λ i v, var i ↦{γ} valc v) (length bs') vs ★ P)%A
      (bs' ++ bs ++ ρ) m2).
  { intros aux. by apply (aux []). }
  induction Halloc as [| b bs v vs m2 ?? IH ]; intros bs'; simpl.
  { rewrite (left_id emp (★))%A. by apply (stack_indep δ ρ). }
  rewrite <-(associative (★))%A. eexists {[(b,v,γ)]}, m2. split_ands.
  * by rewrite mem_alloc_singleton_l.
  * by apply mem_disjoint_singleton_l.
  * exists b v. split_ands; trivial; simpl. by rewrite list_lookup_middle.
  * specialize (IH (bs' ++ [b])). rewrite app_length in IH. simpl in IH.
    by rewrite Nat.add_1_r, <-(associative_L (++)) in IH.
Qed.

Lemma assert_alloc_params_alt (P : assert) δ ρ m γ bs vs :
  StackIndep P → bs `same_length` vs → is_free_list m bs →
  assert_holds δ P ρ m →
  assert_holds δ (Π imap (λ i v, var i ↦{γ} valc v) vs ★ P)%A (bs ++ ρ)
    (mem_alloc_list γ (zip bs vs) m).
Proof. eauto using assert_alloc_params, alloc_params_alloc_list_2. Qed.

Lemma assert_free_params (P : assert) δ ρ m γ bs (vs : list val) :
  StackIndep P → ¬perm_fragment γ → bs `same_length` vs →
  NoDup bs → (* admissible *)
  assert_holds δ (Π imap (λ i _, var i ↦{γ} -) vs ★ P)%A (bs ++ ρ) m →
  assert_holds δ P ρ (delete_list bs m) ∧
    Forall (λ b, mem_perm b m = Some γ) bs.
Proof.
  intros ?? Hlength. revert m. cut (∀ bs' m,
    NoDup bs →
    assert_holds δ (Π imap_go (λ i _, var i ↦{γ} -) (length bs') vs ★ P)%A
      (bs' ++ bs ++ ρ) m →
    assert_holds δ P ρ (delete_list bs m) ∧
      Forall (λ b, mem_perm b m = Some γ) bs).
  { intros aux. by apply (aux []). }
  induction Hlength as [|b v bs vs ? IH];
    intros bs' m; simpl; inversion_clear 1.
  * rewrite (left_id emp (★))%A. split; [|done].
    by apply (stack_indep δ (bs' ++ ρ)).
  * rewrite <-(associative (★))%A. intros (m1&m2&?&?&(?&b'&v'& Heval&?&?)&?).
    simplify_equality. simpl in Heval.
    rewrite list_lookup_middle in Heval. simplify_equality.
    rewrite <-mem_alloc_singleton_l
      by eauto using mem_disjoint_singleton_l_inv.
    feed destruct (IH (bs' ++ [b']) m2) as [??]; trivial.
    { by rewrite app_length, Nat.add_1_r, <-(associative_L (++)). }
    split.
    + rewrite mem_delete_list_alloc_ne, mem_delete_alloc; auto.
      apply is_free_subseteq with m2;
        eauto using mem_delete_list_subseteq, mem_disjoint_singleton_l_inv.
    + constructor; [by rewrite mem_perm_alloc |].
      eapply Forall_impl; eauto. intros b ?. by destruct (decide (b = b'));
        subst; rewrite ?mem_perm_alloc, ?mem_perm_alloc_ne.
Qed.
