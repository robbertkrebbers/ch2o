(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** We define assertions of Hoare logic using a shallow embedding. That is,
assertions are predicates over the contents of the stack and memory. *)

(** This file defines the data type of assertions, the usual connectives of
Hoare logic ([∧], [¬], [↔], [∀] and [∃]), the connectives of separation
logic ([emp], [↦], [★]), and other connectives that are more specific to
our development. We overload the usual notations in [assert_scope] to obtain
nicely looking assertions. *)
Require Export expression_eval_separation type_system memory_singleton.
Require Import type_system_decidable.
Local Obligation Tactic := idtac.

Local Hint Extern 1 (_ ⊆ _) => etransitivity; [eassumption|]: core.
Local Hint Extern 1 (_ ⊆ _) => etransitivity; [|eassumption]: core.
Local Hint Extern 1 (_ ⊆{_} _) => etransitivity; [eassumption|]: core.
Local Hint Extern 1 (_ ⊆{_} _) => etransitivity; [|eassumption]: core.

(** * Definition of assertions *)
Record assert (K : iType) `{Env K} := Assert {
  assert_holds : env K → memenv K → funenv K → stack K → nat → mem K → Prop;
  assert_weaken Γ1 Γ2 Δ1 Δ2 δ1 δ2 ρ n n' m :
    ✓ Γ1 → ✓{Γ1,Δ1} m → ✓{Δ1}* ρ →
    assert_holds Γ1 Δ1 δ1 ρ n m →
    Γ1 ⊆ Γ2 → Δ1 ⇒ₘ Δ2 → δ1 ⊆ δ2 → n' ≤ n →
    assert_holds Γ2 Δ2 δ2 ρ n' m
}.
Add Printing Constructor assert.

Declare Scope assert_scope.
Delimit Scope assert_scope with A.
Bind Scope assert_scope with assert.
Arguments Assert {_ _} _ _.
Arguments assert_holds {_ _} _%A _ _ _ _ _ _.
Arguments assert_weaken {_ _} _%A _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _.

(** The relation [P ⊆.{Γ} Q] states that the assertion [Q] is a logical
consequence of [P] in [Γ] and [P ≡.{Γ} Q] states that [P] and [Q] are logically
equivalent in [Γ]. *)
#[global] Instance assert_entails `{Env K} :
    SubsetEqE (env K * funenv K) (assert K) := λ Γδ P Q,
  ∀ Γ Δ δ ρ n m,
    Γδ.1 ⊆ Γ → ✓ Γ → Γδ.2 ⊆ δ → ✓{Γ,Δ} δ → ✓{Γ,Δ} m → ✓{Δ}* ρ →
    assert_holds P Γ Δ δ ρ n m → assert_holds Q Γ Δ δ ρ n m.
#[global] Instance assert_equiv `{Env K} :
    EquivE (env K * funenv K) (assert K) := λ Γδ P Q, P ⊆{Γδ} Q ∧ Q ⊆{Γδ} P.

(** * Hoare logic connectives *)
(** Definitions and notations of the usual connectives of Hoare logic. *)
Program Definition assert_False `{Env K} : assert K := {|
  assert_holds Γ Δ δ ρ n m := False
|}.
Next Obligation. naive_solver. Qed.
Notation "'False'" := assert_False : assert_scope.
Program Definition assert_True `{Env K} : assert K := {|
  assert_holds Γ Δ δ ρ n m := True
|}.
Next Obligation. naive_solver. Qed.
Notation "'True'" := assert_True : assert_scope.

Program Definition assert_impl `{Env K} (P Q : assert K) : assert K := {|
  assert_holds Γ Δ δ ρ n m := ∀ Γ' Δ' δ' n',
    Γ ⊆ Γ' → ✓ Γ' → Δ ⇒ₘ Δ' → δ ⊆ δ' → ✓{Γ',Δ'} δ' → ✓{Γ',Δ'} m → n' ≤ n →
    assert_holds P Γ' Δ' δ' ρ n' m → assert_holds Q Γ' Δ' δ' ρ n' m
|}.
Next Obligation.
  intros ?? P Q Γ1 Γ2 Δ1 Δ2 δ1 δ2 ρ n1 n2 m ??? HPQ ???? Γ3 Δ3 δ3 n3 ????????.
  apply HPQ; eauto; lia.
Qed.
Infix "→" := assert_impl : assert_scope.
Notation "(→)" := assert_impl (only parsing) : assert_scope.
Notation "( P →)" := (assert_impl P) (only parsing) : assert_scope.
Notation "(→ Q )" := (λ P, assert_impl P Q) (only parsing) : assert_scope.

Program Definition assert_and `{Env K} (P Q : assert K) : assert K := {|
  assert_holds Γ Δ δ ρ n m :=
    assert_holds P Γ Δ δ ρ n m ∧ assert_holds Q Γ Δ δ ρ n m
|}.
Next Obligation. naive_solver eauto using assert_weaken. Qed.
Infix "∧" := assert_and : assert_scope.
Notation "(∧)" := assert_and (only parsing) : assert_scope.
Notation "( P ∧)" := (assert_and P) (only parsing) : assert_scope.
Notation "(∧ Q )" := (λ P, assert_and P Q) (only parsing) : assert_scope.

Program Definition assert_or `{Env K} (P Q : assert K) : assert K := {|
  assert_holds Γ Δ δ ρ n m :=
    assert_holds P Γ Δ δ ρ n m ∨ assert_holds Q Γ Δ δ ρ n m
|}.
Next Obligation. naive_solver eauto using assert_weaken. Qed.
Infix "∨" := assert_or : assert_scope.
Notation "(∨)" := assert_or (only parsing) : assert_scope.
Notation "( P ∨)" := (assert_or P) (only parsing) : assert_scope.
Notation "(∨ Q )" := (λ P, assert_or P Q) (only parsing) : assert_scope.

Definition assert_not `{Env K} (P : assert K) : assert K := (P → False)%A.
Notation "¬ P" := (assert_not P) : assert_scope.
Definition assert_iff `{Env K} (P Q : assert K) : assert K :=
  ((P → Q) ∧ (Q → P))%A.
Infix "↔" := assert_iff : assert_scope.
Notation "(↔)" := assert_iff (only parsing) : assert_scope.
Notation "( P ↔)" := (assert_iff P) (only parsing) : assert_scope.
Notation "(↔ Q )" := (λ P, assert_iff P Q) (only parsing) : assert_scope.

Program Definition assert_forall `{Env K} `(P: A → assert K) : assert K := {|
  assert_holds := λ Γ Δ δ ρ n m, ∀ x, assert_holds (P x) Γ Δ δ ρ n m
|}.
Next Obligation. naive_solver eauto using assert_weaken. Qed.
Notation "∀ x .. y , P" :=
  (assert_forall (λ x, .. (assert_forall (λ y, P)) ..)) : assert_scope.

Program Definition assert_exist `{Env K} `(P : A → assert K): assert K := {|
  assert_holds := λ Γ Δ δ ρ n m, ∃ x, assert_holds (P x) Γ Δ δ ρ n m
|}.
Next Obligation. naive_solver eauto using assert_weaken. Qed.
Notation "∃ x .. y , P" :=
  (assert_exist (λ x, .. (assert_exist (λ y, P)) ..)) : assert_scope.

Program Definition assert_later `{Env K} (P : assert K) : assert K := {|
  assert_holds Γ Δ δ ρ n m := ∀ n', n' < n → assert_holds P Γ Δ δ ρ n' m
|}.
Next Obligation.
  intros ?? P Γ1 Γ2 Δ1 Δ2 δ1 δ2 ρ n1 n2 m ???????? n3 ?.
  eapply assert_weaken with _ _ _ n3; eauto with lia.
Qed.
Notation "▷ P" := (assert_later P) (at level 20) : assert_scope.

(** * Separation logic connectives *)
(** The assertion [emp] asserts that the memory is empty. The assertion [P ★ Q]
(called separating conjunction) asserts that the memory can be split into two
disjoint parts such that [P] holds in the one part, and [Q] in the other. *)
Program Definition assert_eq_mem `{Env K} (m : mem K) : assert K := {|
  assert_holds Γ Δ δ ρ n m' := m' = m
|}.
Next Obligation. naive_solver. Qed.
Program Definition assert_Prop `{Env K} (P : Prop) : assert K := {|
  assert_holds Γ Δ δ ρ n m := P ∧ m = ∅
|}.
Next Obligation. naive_solver. Qed.
Notation "⌜ P ⌝" := (assert_Prop P) (format "⌜  P  ⌝") : assert_scope.
Notation "'emp'" := (assert_Prop True) : assert_scope.

Program Definition assert_sep `{EnvSpec K} (P Q : assert K) : assert K := {|
  assert_holds Γ Δ δ ρ n m := ∃ m1 m2,
    m = m1 ∪ m2 ∧ ##[m1; m2] ∧
    assert_holds P Γ Δ δ ρ n m1 ∧ assert_holds Q Γ Δ δ ρ n m2
|}.
Next Obligation.
  intros ??? P Q Γ1 Γ2 Δ1 Δ2 δ1 δ2 ρ n m ???? (m1&m2&->&?&?&?) ????.
  eauto 15 using assert_weaken, cmap_valid_subseteq,
    @sep_union_subseteq_l, @sep_union_subseteq_r.
Qed.
Infix "★" := assert_sep (at level 80, right associativity) : assert_scope.
Notation "(★)" := assert_sep (only parsing) : assert_scope.
Notation "( P ★)" := (assert_sep P) (only parsing) : assert_scope.
Notation "(★ Q )" := (λ P, assert_sep P Q) (only parsing) : assert_scope.

Class MemExt `{EnvSpec K} (P : assert K) : Prop :=
  mem_ext Γ δ : (P ★ True)%A ⊆{Γ,δ} P.
Global Hint Extern 10 (MemExt _) => apply _: core.

Program Definition assert_wand `{Env K} (P Q : assert K) : assert K := {|
  assert_holds Γ Δ δ ρ n m2 := ∀ Γ' Δ' δ' n' m1,
    Γ ⊆ Γ' → ✓ Γ' → Δ ⇒ₘ Δ' → δ ⊆ δ' → ✓{Γ',Δ'} δ' → n' ≤ n →
    ✓{Γ',Δ'} m1 → ✓{Γ',Δ'} m2 → ##[m1; m2] →
    assert_holds P Γ' Δ' δ' ρ n' m1 → assert_holds Q Γ' Δ' δ' ρ n' (m1 ∪ m2)
|}.
Next Obligation.
  intros ?? P Q Γ Γ2 Δ Δ2 δ1 δ2 ρ n n2 m ??? HPQ ???? Γ3 Δ3 δ3 n3 ???????????.
  apply HPQ; eauto; lia.
Qed.
Infix "-★" := assert_wand (at level 90) : assert_scope.
Notation "(-★)" := assert_wand (only parsing) : assert_scope.
Notation "( P -★)" := (assert_wand P) (only parsing) : assert_scope.
Notation "(-★ Q )" := (λ P, assert_wand P Q) (only parsing) : assert_scope.

(** The assertion [Π Ps] states that the memory can be split into disjoint
parts such that for each part the corresponding assertion in [Ps] holds. *)
Definition assert_sep_list `{EnvSpec K} :
  list (assert K) → assert K := foldr (★)%A emp%A.
Notation "'Π' Ps" := (assert_sep_list Ps)
  (at level 20, format "Π  Ps") : assert_scope.

(** The assertion [e ⇓ v : τlr] asserts that the expression [e] evaluates to [v]
and [e ⇓ - : τlr] asserts that the expression [e] evaluates to an arbitrary
value (in other words, [e] does not impose undefined behavior). *)
Notation vassert K := ((ptr K + val K) → assert K)%type.
Program Definition assert_expr `{EnvSpec K} (e : expr K) : vassert K := λ ν, {|
  assert_holds Γ Δ δ ρ n m := ∃ τlr, (Γ,Δ,ρ.*2) ⊢ e : τlr ∧ ⟦ e ⟧ Γ ρ m = Some ν
|}.
Next Obligation.
  intros ??? e ν Γ1 Γ2 Δ1 Δ2 δ1 δ2 ρ n1 n2 m ??? (τlr&?&?) ??;
    exists τlr; split; eauto using expr_typed_weaken, expr_eval_weaken,
    mem_lookup_weaken, mem_forced_weaken.
Qed.
Notation "e ⇓ ν" := (assert_expr e ν)%A
  (at level 60, ν at next level, format "e  '⇓'  ν") : assert_scope.
Notation "e ⇓ -" := (∃ ν, e ⇓ ν)%A
  (at level 60, format "e  '⇓'  '-'") : assert_scope.

(** The assertion [e1 ↦{μ,γ} e2] asserts that the memory consists of
exactly one object at address [e1] with permission [x] and contents [e2]. The
assertion [e1 ↦{μ,γ} -] asserts that the memory consists of exactly one
object at address [e1] with permission [x] and arbitrary contents. The Boolean
[μ] denotes whether the object has been obtained via malloc. *)
Program Definition assert_singleton `{EnvSpec K}
    (e1 : expr K) (μ : bool) (γ : perm)
    (e2 : expr K) (τ : type K) : assert K := {|
  assert_holds Γ Δ δ ρ n m := ∃ a v,
    (Γ,Δ,ρ.*2) ⊢ e1 : inl (TType τ) ∧ ⟦ e1 ⟧ Γ ρ ∅ = Some (inl (Ptr a)) ∧
    (Γ,Δ,ρ.*2) ⊢ e2 : inr τ ∧ ⟦ e2 ⟧ Γ ρ ∅ = Some (inr v) ∧
    mem_singleton Γ Δ a μ γ v τ m
|}.
Next Obligation.
  intros ??? e1 e2 ml γ τ Γ1 Γ2 Δ1 Δ2 δ1 δ2 ρ n1 n2 m ??? (a&v&?&?&?&?&?) ??.
  exists a, v; split_and ?; eauto using expr_typed_weaken,
    expr_eval_weaken_empty, mem_singleton_weaken, cmap_valid_memenv_valid.
Qed.
Notation "e1 ↦{ μ , γ } e2 : τ" := (assert_singleton e1 μ γ e2 τ)%A
  (at level 20, μ at next level, γ at next level, e2 at next level,
   τ at next level, format "e1  ↦{ μ , γ }  e2  :  τ") : assert_scope.
Notation "e1 ↦{ μ , γ } - : τ" :=
  (∃ v, e1 ↦{μ,γ} (# v) : τ)%A
  (at level 20, μ at next level, γ at next level,
   τ at next level, format "e1  ↦{ μ , γ }  -  :  τ") : assert_scope.

(** The assertion [P ◊] asserts that [P] holds if all sequenced locations
are unlocked. *)
Program Definition assert_unlock `{EnvSpec K} (P : assert K) : assert K := {|
  assert_holds Γ Δ δ ρ n m := assert_holds P Γ Δ δ ρ n (mem_unlock_all m)
|}.
Next Obligation.
  naive_solver eauto using assert_weaken, mem_unlock_all_valid.
Qed.
Notation "P ◊" := (assert_unlock P) (at level 20) : assert_scope.
Class UnlockIndep `{EnvSpec K} (P : assert K) : Prop :=
  unlock_indep Γ δ : P ⊆{Γ,δ} (P ◊)%A.
Global Hint Extern 10 (UnlockIndep _) => apply _: core.

(** To deal with block scope variables we need to lift an assertion such that
the De Bruijn indexes of its variables are increased. We define the lifting
[P↑] of an assertion [P] semantically, and prove that it indeed behaves as
expected. *)
Program Definition assert_lift `{Env K} (P : assert K) : assert K := {|
  assert_holds Γ Δ δ ρ n m := assert_holds P Γ Δ δ (tail ρ) n m
|}.
Next Obligation. naive_solver eauto using assert_weaken, Forall_tail. Qed.
(* Notation "... ↑" was already reserved at level 20 in `expressions.v`. *)
Notation "P ↑" := (assert_lift P) : assert_scope.
Class StackIndep `{Env K} (P : assert K) : Prop :=
  stack_indep Γ δ : (P ↑)%A ≡{Γ,δ} P.
Global Hint Extern 10 (StackIndep _) => apply _: core.

Section assertions.
Context `{EnvSpec K}.
Implicit Types Γ : env K.

Hint Unfold Proper respectful pointwise_relation : assert.
Hint Unfold subseteqE assert_entails equivE assert_equiv : assert.
Hint Unfold StackIndep UnlockIndep : assert.
Hint Extern 100 (## _) => solve_sep_disjoint: core.
Hint Extern 100 (_ ## _) => solve_sep_disjoint: core.
Hint Extern 100 (sep_valid _) => solve_sep_disjoint: core.
Hint Immediate cmap_valid_sep_valid: core.
Hint Extern 0 (_ ⊢ _ : _ ↣ _) => typed_constructor; try lia: core.
Hint Extern 0 (_ ⊢ _ : _) => typed_constructor: core.

Ltac solve t :=
  repeat first
  [ progress simplify_equality'
  | progress autounfold with assert in *];
  naive_solver t.

Lemma assert_entails_spec P Q Γ Δ δ ρ n m :
  ✓ Γ → ✓{Γ,Δ} δ → ✓{Γ,Δ} m → ✓{Δ}* ρ →
  P ⊆{Γ,δ} Q → assert_holds P Γ Δ δ ρ n m → assert_holds Q Γ Δ δ ρ n m.
Proof. intros ???? HPQ; apply HPQ; auto. Qed.

(** Ordinary logic connections *)
#[global] Instance: `{PreOrder (⊆{Γ,δ})}.
Proof. split; solve eauto. Qed.
#[global] Instance: `{Equivalence (≡{Γ,δ})}.
Proof. split; red; solve eauto. Qed.
#[global] Instance: `{Proper ((≡{Γ,δ}) ==> (≡{Γ,δ}) ==> iff) (⊆{Γ,δ})}.
Proof. solve eauto. Qed.
#[global] Instance: `{Proper (flip (⊆{Γ,δ}) ==> (⊆{Γ,δ}) ==> (⊆{Γ,δ})) (→)%A}.
Proof.
  intros Γ1 δ1 P1 P2 HP Q1 Q2 HQ Γ2 Δ1 δ2 ρ n m ?????? HPQ Γ3 Δ2 δ3 n2 ????????.
  eapply HQ; eauto 8 using indexes_valid_weaken.
Qed.
#[global] Instance: `{Proper ((≡{Γ,δ}) ==> (≡{Γ,δ}) ==> (≡{Γ,δ})) (→)%A}.
Proof. by intros ???? [??] ?? [??]; split; f_equiv. Qed.
#[global] Instance: `{Proper ((≡{Γ,δ}) ==> (≡{Γ,δ}) ==> (≡{Γ,δ})) (∧)%A}.
Proof. solve eauto. Qed.
#[global] Instance: `{Proper ((⊆{Γ,δ}) ==> (⊆{Γ,δ}) ==> (⊆{Γ,δ})) (∧)%A}.
Proof. solve eauto. Qed.
#[global] Instance: `{Proper ((≡{Γ,δ}) ==> (≡{Γ,δ}) ==> (≡{Γ,δ})) (∨)%A}.
Proof. solve eauto. Qed.
#[global] Instance: `{Proper ((⊆{Γ,δ}) ==> (⊆{Γ,δ}) ==> (⊆{Γ,δ})) (∨)%A}.
Proof. solve eauto. Qed.
#[global] Instance: `{Proper ((≡{Γ,δ}) ==> (≡{Γ,δ}) ==> (≡{Γ,δ})) (↔)%A}.
Proof. by intros ????????; unfold assert_iff; do 2 f_equiv. Qed.
#[global] Instance: `{Proper ((≡{Γ,δ}) ==> (≡{Γ,δ})) assert_not}.
Proof. by intros ?????; unfold assert_not; f_equiv. Qed.
#[global] Instance: `{Proper (flip (⊆{Γ,δ}) ==> (⊆{Γ,δ})) assert_not}.
Proof. by intros ?????; unfold assert_not; f_equiv. Qed.
#[global] Instance:
  `{Proper (pointwise_relation _ (≡{Γ,δ}) ==> (≡{Γ,δ})) (@assert_forall _ _ A)}.
Proof. solve eauto. Qed.
#[global] Instance:
  `{Proper (pointwise_relation _ (⊆{Γ,δ}) ==> (⊆{Γ,δ})) (@assert_forall _ _ A)}.
Proof. solve eauto. Qed.
#[global] Instance:
  `{Proper (pointwise_relation _ (≡{Γ,δ}) ==> (≡{Γ,δ})) (@assert_exist _ _ A)}.
Proof. solve eauto. Qed.
#[global] Instance:
  `{Proper (pointwise_relation _ (⊆{Γ,δ}) ==> (⊆{Γ,δ})) (@assert_exist _ _ A)}.
Proof. solve eauto. Qed.
#[global] Instance:
  `{Proper (pointwise_relation _ (flip (⊆{Γ,δ})) ==> (flip (⊆{Γ,δ})))
  (@assert_exist _ _ A)}.
Proof. solve eauto. Qed.

#[global] Instance: `{Comm (≡{Γ,δ}) (↔)%A}.
Proof. red; solve eauto. Qed.
#[global] Instance: `{Comm (≡{Γ,δ}) (∧)%A}.
Proof. red; solve eauto. Qed.
#[global] Instance: `{Assoc (≡{Γ,δ}) (∧)%A}.
Proof. red; solve eauto. Qed.
#[global] Instance: `{IdemP (≡{Γ,δ}) (∧)%A}.
Proof. red; solve eauto. Qed.
#[global] Instance: `{LeftId (≡{Γ,δ}) True%A (∧)%A}.
Proof. red; solve eauto. Qed.
#[global] Instance: `{RightId (≡{Γ,δ}) True%A (∧)%A}.
Proof. red; solve eauto. Qed.
#[global] Instance: `{LeftAbsorb (≡{Γ,δ}) False%A (∧)%A}.
Proof. red; solve eauto. Qed.
#[global] Instance: `{RightAbsorb (≡{Γ,δ}) False%A (∧)%A}.
Proof. red; solve eauto. Qed.
#[global] Instance: `{Comm (≡{Γ,δ}) (∨)%A}.
Proof. red; solve eauto. Qed.
#[global] Instance: `{Assoc (≡{Γ,δ}) (∨)%A}.
Proof. red; solve eauto. Qed.
#[global] Instance: `{IdemP (≡{Γ,δ}) (∨)%A}.
Proof. red; solve eauto. Qed.
#[global] Instance: `{LeftId (≡{Γ,δ}) False%A (∨)%A}.
Proof. red; solve eauto. Qed.
#[global] Instance: `{RightId (≡{Γ,δ}) False%A (∨)%A}.
Proof. red; solve eauto. Qed.
#[global] Instance: `{LeftAbsorb (≡{Γ,δ}) True%A (∨)%A}.
Proof. red; solve eauto. Qed.
#[global] Instance: `{RightAbsorb (≡{Γ,δ}) True%A (∨)%A}.
Proof. red; solve eauto. Qed.
Lemma assert_False_elim Γ δ P : False%A ⊆{Γ,δ} P.
Proof. solve eauto. Qed.
Lemma assert_True_intro Γ δ P : P ⊆{Γ,δ} True%A.
Proof. solve eauto. Qed.
Lemma assert_and_l Γ δ P Q : (P ∧ Q)%A ⊆{Γ,δ} P.
Proof. solve eauto. Qed.
Lemma assert_and_r Γ δ P Q : (P ∧ Q)%A ⊆{Γ,δ} Q.
Proof. solve eauto. Qed.
Lemma assert_impl_and Γ δ P Q : P ⊆{Γ,δ} Q → P ≡{Γ,δ} (P ∧ Q)%A.
Proof. solve eauto. Qed.
Lemma assert_and_intro Γ δ P Q1 Q2 :
  P ⊆{Γ,δ} Q1 → P ⊆{Γ,δ} Q2 → P ⊆{Γ,δ} (Q1 ∧ Q2)%A.
Proof. solve eauto. Qed.
Lemma assert_and_elim_l Γ δ P1 P2 Q : P1 ⊆{Γ,δ} Q → (P1 ∧ P2)%A ⊆{Γ,δ} Q.
Proof. solve eauto. Qed.
Lemma assert_and_elim_r Γ δ P1 P2 Q : P2 ⊆{Γ,δ} Q → (P1 ∧ P2)%A ⊆{Γ,δ} Q.
Proof. solve eauto. Qed.
Lemma assert_or_l Γ δ P Q : P ⊆{Γ,δ} (P ∨ Q)%A.
Proof. solve eauto. Qed.
Lemma assert_or_r Γ δ P Q : Q ⊆{Γ,δ} (P ∨ Q)%A.
Proof. solve eauto. Qed.
Lemma assert_forall_intro {A} Γ δ P (Q : A → assert K) :
  (∀ x, P ⊆{Γ,δ} Q x) → P ⊆{Γ,δ} (∀ x, Q x)%A.
Proof. solve eauto. Qed.
Lemma assert_forall_elim {A} Γ δ (P : A → assert K) Q x :
  (P x ⊆{Γ,δ} Q) → (∀ x, P x)%A ⊆{Γ,δ} Q.
Proof. solve eauto. Qed.
Lemma assert_exist_intro {A} Γ δ P (Q : A → assert K) x :
  P ⊆{Γ,δ} Q x → P ⊆{Γ,δ} (∃ x, Q x)%A.
Proof. solve eauto. Qed.
Lemma assert_exist_elim {A} Γ δ (P : A → assert K) Q :
  (∀ x, P x ⊆{Γ,δ} Q) → (∃ x, P x)%A ⊆{Γ,δ} Q.
Proof. solve eauto. Qed.
Lemma assert_and_exist {A} Γ δ P (Q : A → assert K) :
  (P ∧ ∃ x, Q x)%A ≡{Γ,δ} (∃ x, P ∧ Q x)%A.
Proof. solve eauto. Qed.
Lemma assert_exist_and {A} Γ δ (P : A → assert K) Q :
  ((∃ x, P x) ∧ Q)%A ≡{Γ,δ} (∃ x, P x ∧ Q)%A.
Proof. solve eauto. Qed.
Lemma assert_exist_exist {A B} Γ δ (P : A → B → assert K) :
  (∃ x y, P x y)%A ≡{Γ,δ} (∃ y x, P x y)%A.
Proof. solve eauto. Qed.

(** Later *)
Lemma assert_later_lob Γ δ P : (▷P → P)%A ⊆{Γ,δ} P.
Proof.
  intros Γ1 Δ δ1 ρ n m ?????? HP; induction n as [|n IH].
  { apply HP; eauto. intros n'; lia. }
  eapply HP; eauto. intros n' ?.
  eapply assert_weaken with _ _ δ1 n; eauto with lia.
  eapply IH, assert_weaken with _ _ _ (S n); eauto with lia.
Qed.
Lemma assert_later_weaken Γ δ P : P ⊆{Γ,δ} (▷P)%A.
Proof.
  intros Γ1 Δ ρ δ1 n m ??????? n' ?.
  eapply assert_weaken with _ _ _ n; eauto with lia.
Qed.
Lemma assert_later_impl Γ δ P Q : (▷(P → Q))%A ⊆{Γ,δ} (▷P → ▷Q)%A.
Proof.
  intros Γ1 Δ1 δ1 ρ n1 m ?????? HPQ Γ2 Δ2 δ2 n2 ???????? n3 ?.
  eapply HPQ; eauto; lia.
Qed.
Lemma assert_later_and Γ δ P Q : (▷(P ∧ Q))%A ≡{Γ,δ} (▷P ∧ ▷Q)%A.
Proof. solve eauto. Qed.
Lemma assert_later_or Γ δ P Q : (▷P ∨ ▷Q)%A ⊆{Γ,δ} (▷(P ∨ Q))%A.
Proof. solve eauto. Qed.
Lemma assert_later_forall {A} Γ δ (P : A → assert K) :
  (▷(∀ x, P x))%A ≡{Γ,δ} (∀ x, ▷(P x))%A.
Proof. solve eauto. Qed.
Lemma assert_later_exists {A} Γ δ (P : A → assert K) :
  (∃ x, ▷(P x))%A ⊆{Γ,δ} (▷(∃ x, P x))%A.
Proof. solve eauto. Qed.

(** Separation logic connectives *)
#[global] Instance: `{Proper (impl ==> (⊆{Γ,δ})) assert_Prop}.
Proof. solve eauto. Qed.
#[global] Instance: `{Proper (iff ==> (≡{Γ,δ})) assert_Prop}.
Proof. solve eauto. Qed.
#[global] Instance: `{Proper ((⊆{Γ,δ}) ==> (⊆{Γ,δ}) ==> (⊆{Γ,δ})) (★)%A}.
Proof.
  solve ltac:(eauto 15 using cmap_valid_subseteq,
    @sep_union_subseteq_l, @sep_union_subseteq_r).
Qed.
#[global] Instance:
  `{Proper (flip (⊆{Γ,δ}) ==> flip (⊆{Γ,δ}) ==> flip (⊆{Γ,δ})) (★)%A}.
Proof.
  solve ltac:(eauto 15 using cmap_valid_subseteq,
    @sep_union_subseteq_l, @sep_union_subseteq_r).
Qed.
#[global] Instance: `{Proper ((≡{Γ,δ}) ==> (≡{Γ,δ}) ==> (≡{Γ,δ})) (★)%A}.
Proof.
  by intros ???? [??] ?? [??]; split;
    apply (_ : Proper ((⊆{Γ,δ}) ==> (⊆{Γ,δ}) ==> (⊆{Γ,δ})) (★)%A).
Qed.
#[global] Instance: `{Proper (Forall2 (≡{Γ,δ}) ==> (≡{Γ,δ})) assert_sep_list}.
Proof.
  induction 1; simpl; [done|];
    by apply (_ : Proper ((≡{Γ,δ}) ==> (≡{Γ,δ}) ==> (≡{Γ,δ})) (★)%A).
Qed.
#[global] Instance: `{Proper (flip (⊆{Γ,δ}) ==> (⊆{Γ,δ}) ==> (⊆{Γ,δ})) (-★)%A}.
Proof.
  intros Γ1 δ1 P1 P2 HP Q1 Q2 HQ Γ2 Δ1 δ2 ρ n1 m
    ?????? HPQ Γ3 Δ2 δ3 n2 ???????????.
  apply HQ; eauto 10 using indexes_valid_weaken, cmap_union_valid_2.
Qed.
#[global] Instance: `{Proper ((≡{Γ,δ}) ==> (≡{Γ,δ}) ==> (≡{Γ,δ})) (-★)%A}.
Proof.
  by intros ???? [??] ?? [??]; split;
    apply (_ : Proper (flip (⊆{Γ,δ}) ==> (⊆{Γ,δ}) ==> (⊆{Γ,δ})) (-★)%A).
Qed.

#[global] Instance: `{Comm (⊆{Γ,δ}) (★)%A}.
Proof.
  intros Γ δ P Q Γ1 Δ δ1 ρ n m ?????? (m1&m2&->&?&?&?).
  exists m2, m1. rewrite sep_commutative by auto; auto.
Qed.
#[global] Instance: `{Comm (≡{Γ,δ}) (★)%A}.
Proof. split; by rewrite (comm (★)%A). Qed.
#[global] Instance: `{LeftId (≡{Γ,δ}) emp%A (★)%A}.
Proof.
  intros δ Γ; intros P; split.
  * intros Γ1 Δ δ1 ρ n m ?????? (m1&m2&->&?&[_ ->]&?).
    rewrite sep_left_id by auto; auto.
  * intros Γ1 Δ δ1 ρ n m ???????. eexists ∅, m.
    rewrite sep_left_id, sep_disjoint_equiv_empty,
      sep_disjoint_list_singleton by eauto; solve eauto.
Qed.
#[global] Instance: `{RightId (≡{Γ,δ}) emp%A (★)%A}.
Proof. intros ???. by rewrite (comm _), (left_id _ _). Qed.
#[global] Instance: `{LeftAbsorb (≡{Γ,δ}) False%A (★)%A}.
Proof. red; solve eauto. Qed.
#[global] Instance: `{RightAbsorb (≡{Γ,δ}) False%A (★)%A}.
Proof. red; solve eauto. Qed.
#[global] Instance: `{Assoc (≡{Γ,δ}) (★)%A}.
Proof.
  intros Γ δ. assert (∀ P Q R, ((P ★ Q) ★ R)%A ⊆{Γ,δ} (P ★ (Q ★ R))%A).
  { intros P Q R Γ1 Δ δ1 ρ ? n ?????? (?&m3&->&?&(m1&m2&->&?&?&?)&?).
    exists m1, (m2 ∪ m3); rewrite sep_associative by auto; split_and ?; auto.
    exists m2, m3; auto. }
  assert (∀ P Q R, (P ★ (Q ★ R))%A ⊆{Γ,δ} ((P ★ Q) ★ R)%A).
  { intros P Q R Γ1 Δ δ1 ρ ? n ?????? (m1&?&->&?&?&(m2&m3&->&?&?&?)).
    exists (m1 ∪ m2), m3; rewrite sep_associative by auto; split_and ?; auto.
    exists m1, m2; auto. }
  split; auto.
Qed.

Lemma assert_Prop_impl Γ δ (P Q : Prop) : ⌜ P → Q ⌝%A ⊆{Γ,δ} (⌜P⌝ → ⌜Q⌝)%A.
Proof. solve eauto. Qed.
Lemma assert_Prop_not Γ δ (P : Prop) : ⌜ ¬P ⌝%A ⊆{Γ,δ} (¬⌜P⌝)%A.
Proof. solve eauto. Qed.
Lemma assert_Prop_and Γ δ (P Q : Prop) : ⌜ P ∧ Q ⌝%A ≡{Γ,δ} (⌜P⌝ ∧ ⌜Q⌝)%A.
Proof. solve eauto. Qed.
Lemma assert_Prop_or Γ δ (P Q : Prop) : ⌜ P ∨ Q ⌝%A ≡{Γ,δ} (⌜P⌝ ∨ ⌜Q⌝)%A.
Proof. solve eauto. Qed.
Lemma assert_Prop_l Γ δ (P : Prop) Q : P → (⌜ P ⌝ ★ Q)%A ≡{Γ,δ} Q.
Proof.
  intros. assert (P ↔ True) as -> by (by split; intros _).
  by rewrite (left_id emp%A _).
Qed.
Lemma assert_Prop_r Γ δ (P : Prop) Q : P → (Q ★ ⌜ P ⌝)%A ≡{Γ,δ} Q.
Proof. intros. by rewrite (comm (★))%A, assert_Prop_l. Qed.
Lemma assert_Prop_intro_l Γ δ (P : Prop) Q R :
  (P → Q ⊆{Γ,δ} R) → (⌜ P ⌝ ★ Q)%A ⊆{Γ,δ} R.
Proof.
  intros HQR Γ1 Δ δ1 ρ n ????? Hm ? (m1&m2&->&?&[? ->]&?).
  rewrite sep_left_id in Hm |- * by auto; by apply HQR.
Qed.
Lemma assert_Prop_intro_r Γ δ (P : Prop) Q R :
  (P → Q ⊆{Γ,δ} R) → (Q ★ ⌜ P ⌝)%A ⊆{Γ,δ} R.
Proof. rewrite (comm (★)%A). by apply assert_Prop_intro_l. Qed.
Lemma assert_Prop_True Γ δ P (Q : Prop) :
  P ⊆{Γ,δ} (⌜ Q ⌝ ★ True)%A → P ⊆{Γ,δ} (⌜ Q ⌝ ★ P)%A.
Proof.
  intros HPQ Γ1 Δ δ1 ρ n m ?????? HP.
  destruct (HPQ Γ1 Δ δ1 ρ n m) as (m1&m2&->&?&[? ->]&?); auto.
  rewrite sep_left_id in HP by auto; solve eauto.
Qed.

Lemma assert_sep_preserving Γ δ P P' Q Q' :
  P ⊆{Γ,δ} P' → Q ⊆{Γ,δ} Q' → (P ★ Q)%A ⊆{Γ,δ} (P' ★ Q')%A.
Proof. intros HP HQ. by rewrite HP, HQ. Qed.
Lemma assert_sep_exist {A} Γ δ P (Q : A → assert K) :
  (P ★ ∃ x, Q x)%A ≡{Γ,δ} (∃ x, P ★ Q x)%A.
Proof. solve eauto. Qed.
Lemma assert_exist_sep {A} Γ δ (P : A → assert K) Q :
  ((∃ x, P x) ★ Q)%A ≡{Γ,δ} (∃ x, P x ★ Q)%A.
Proof. solve eauto. Qed.
Lemma assert_wand_intro Γ δ P Q R : (P ★ Q)%A ⊆{Γ,δ} R → P ⊆{Γ,δ} (Q -★ R)%A.
Proof.
  intros HPQR Γ1 Δ1 ρ δ1 n1 m1 ?????? HP Γ2 Δ2 δ2 n2 m2 ????????? HQ.
  apply HPQR; eauto using indexes_valid_weaken, cmap_union_valid_2.
  exists m1, m2; split_and ?; eauto using assert_weaken, @sep_commutative.
Qed.
Lemma assert_wand_elim Γ δ P Q : ((P -★ Q) ★ P)%A ⊆{Γ,δ} Q.
Proof.
  intros Γ1 Δ1 ρ δ1 n ??????? (m1&m2&->&?&HQ&?).
  rewrite sep_commutative by auto; eapply HQ; eauto using
    cmap_valid_subseteq, @sep_union_subseteq_l, @sep_union_subseteq_r.
Qed.
#[global] Instance: `{LeftId (≡{Γ,δ}) emp%A (-★)%A}.
Proof.
  intros Γ P; split.
  * rewrite <-(right_id _ (★)%A); apply assert_wand_elim.
  * apply assert_wand_intro. by rewrite (right_id _ (★)%A).
Qed.

Lemma assert_Forall_holds_2 (Ps : list (assert K)) Γ Δ δ ρ ms n :
  ## ms → Forall2 (λ (P : assert K) m, assert_holds P Γ Δ δ ρ n m) Ps ms →
  assert_holds (Π Ps)%A Γ Δ δ ρ n (⋃ ms).
Proof. intros Hms HPs. revert Hms. induction HPs; solve eauto. Qed.
Lemma assert_Forall_holds (Ps : list (assert K)) Γ Δ δ ρ n m :
  assert_holds (Π Ps)%A Γ Δ δ ρ n m ↔ ∃ ms, m = ⋃ ms ∧ ## ms ∧
    Forall2 (λ (P : assert K) m, assert_holds P Γ Δ δ ρ n m) Ps ms.
Proof.
  split; [|naive_solver eauto using assert_Forall_holds_2].
  revert m. induction Ps as [|P Ps IH].
  { intros m [? ->]. eexists []. by repeat constructor. }
  intros ? (m1&m2&->&?&?&?); destruct (IH m2) as (ms&->&?&?); trivial.
  exists (m1 :: ms); auto.
Qed.
Lemma assert_Forall_holds_vec {vn} (Ps : vec (assert K) vn) Γ Δ δ ρ n m :
  assert_holds (Π Ps)%A Γ Δ δ ρ n m ↔ ∃ ms : vec _ vn, m = ⋃ ms ∧ ## ms ∧
    ∀ i, assert_holds (Ps !!! i) Γ Δ δ ρ n (ms !!! i).
Proof.
  rewrite assert_Forall_holds; split.
  * intros (ms&->&?&Hms). assert (vn = length ms); [|subst vn].
    { by erewrite <-Forall2_length, vec_to_list_length by eauto. }
    exists (list_to_vec ms); rewrite ?vec_to_list_to_vec.
    by rewrite <-(vec_to_list_to_vec ms), Forall2_vlookup in Hms.
  * intros [ms ?]; exists ms; by rewrite Forall2_vlookup.
Qed.
Lemma assert_memext_l Γ δ P Q : MemExt P → (P ★ Q)%A ⊆{Γ,δ} P.
Proof.
  intros; transitivity (P ★ True)%A;
    auto using assert_sep_preserving, assert_True_intro.
Qed.
Lemma assert_memext_r Γ δ P Q : MemExt P → (Q ★ P)%A ⊆{Γ,δ} P.
Proof. rewrite (comm (★)%A). apply assert_memext_l. Qed.
Lemma assert_memext_l' Γ δ P Q R : MemExt R → P ⊆{Γ,δ} R → (P ★ Q)%A ⊆{Γ,δ} R.
Proof.
  intros. rewrite <-(assert_memext_l _ _ R) by done.
  eauto using assert_sep_preserving.
Qed.
Lemma assert_memext_r' Γ δ P Q R : MemExt R → Q ⊆{Γ,δ} R → (P ★ Q)%A ⊆{Γ,δ} R.
Proof. rewrite (comm (★)%A). apply assert_memext_l'. Qed.

(* Evaluation and singleton connectives *)
#[global] Instance assert_eval_memext e ν : MemExt (e ⇓ ν)%A.
Proof.
  intros Γ δ Γ' Δ δ' ρ n m ???? Hm ? (m1&m2&->&?&(τlr&?&?)&?).
  exists τlr; split; auto.
  rewrite cmap_union_valid in Hm by auto; destruct Hm.
  eapply expr_eval_subseteq with _ m1 _; eauto using @sep_union_subseteq_l'.
Qed.
Lemma assert_int_typed_eval Γ δ P x τi :
  int_typed x τi → P ⊆{Γ,δ} (#intV{τi} x ⇓ inr (intV{τi} x))%A.
Proof.
  intros ? Γ' Δ ρ δ' n m ??????.
  eexists (inr (intT τi)%T); split; auto using lockset_empty_valid.
Qed.
Lemma assert_eval_int_typed Γ δ e x τi :
  (e ⇓ inr (intV{τi} x))%A ⊆{Γ,δ} (⌜ int_typed x τi ⌝ ★ True)%A.
Proof.
  intros Γ' Δ δ' ρ n m ?????? (τlr&?&?).
  assert ((Γ',Δ) ⊢ inr (intV{τi} x) : τlr) by eauto using expr_eval_typed.
  assert (sep_valid m) by eauto.
  typed_inversion_all; exists ∅, m; eauto 9 using @sep_left_id, eq_sym.
Qed.
Lemma assert_eval_int_typed' Γ δ e x τi :
  (e ⇓ inr (intV{τi} x))%A ⊆{Γ,δ} (⌜ int_typed x τi ⌝ ★ e ⇓ inr (intV{τi} x))%A.
Proof. eauto using assert_Prop_True, assert_eval_int_typed. Qed.
Hint Extern 1 (unop_typed _ _ _) => constructor: core.
Hint Extern 1 (base_unop_typed _ _ _) => constructor: core.
Lemma assert_eval_int_unop Γ δ op e x τi :
  int_unop_ok op x τi →
  (e ⇓ inr (intV{τi} x))%A
  ⊆{Γ,δ} (.{op} e ⇓ inr (intV{int_unop_type_of op τi} (int_unop op x τi)))%A.
Proof.
  intros ? Γ' Δ δ' ρ n m ?????? (τlr&?&?).
  assert ((Γ',Δ) ⊢ inr (intV{τi} x) : τlr) by eauto using expr_eval_typed.
  typed_inversion_all;
    simplify_option_eq; eauto 20 using lockset_empty_valid.
Qed.
Lemma assert_eval_int_unop' Γ δ P op e x y τi σi :
  P ⊆{Γ,δ} (e ⇓ inr (intV{τi} x))%A →
  int_unop_type_of op τi = σi → int_unop_ok op x τi → int_unop op x τi = y → 
  P ⊆{Γ,δ} (.{op} e ⇓ inr (intV{σi} y))%A.
Proof. intros; subst; rewrite <-assert_eval_int_unop by eauto; eauto. Qed.
Hint Extern 1 (binop_typed _ _ _ _) => constructor: core.
Hint Extern 1 (base_binop_typed _ _ _ _) => constructor: core.
Lemma assert_eval_int_binop Γ δ op e1 e2 x1 x2 τi1 τi2 :
  (int_binop_ok op x1 τi1 x2 τi2) →
  (e1 ⇓ inr (intV{τi1} x1) ∧ e2 ⇓ inr (intV{τi2} x2))%A ⊆{Γ,δ} (e1 .{op} e2 ⇓
       inr (intV{int_binop_type_of op τi1 τi2} (int_binop op x1 τi1 x2 τi2)))%A.
Proof.
  intros Hok Γ' Δ δ' ρ n m ?????? [(τlr1&?&?) (τlr2&?&?)].
  assert ((Γ',Δ) ⊢ inr (intV{τi1} x1) : τlr1) by eauto using expr_eval_typed.
  assert ((Γ',Δ) ⊢ inr (intV{τi2} x2) : τlr2) by eauto using expr_eval_typed.
  typed_inversion_all.
  simplify_option_eq; eauto 20 using lockset_empty_valid.
Qed.
Lemma assert_eval_int_binop' Γ δ P op e1 e2 x1 x2 y τi1 τi2 σi :
  P ⊆{Γ,δ} (e1 ⇓ inr (intV{τi1} x1))%A → P ⊆{Γ,δ} (e2 ⇓ inr (intV{τi2} x2))%A →
  σi = int_binop_type_of op τi1 τi2 →
  int_binop_ok op x1 τi1 x2 τi2 → int_binop op x1 τi1 x2 τi2 = y →
  P ⊆{Γ,δ} (e1 .{op} e2 ⇓ inr (intV{σi} y))%A.
Proof.
  intros; subst;
    rewrite <-assert_eval_int_binop by eauto; eauto using assert_and_intro.
Qed.
Lemma assert_eval_int_arithop' Γ δ P op e1 e2 x1 x2 y τi1 τi2 σi :
  P ⊆{Γ,δ} (e1 ⇓ inr (intV{τi1} x1))%A → P ⊆{Γ,δ} (e2 ⇓ inr (intV{τi2} x2))%A →
  σi = int_promote τi1 ∪ int_promote τi2 →
  int_pre_arithop_ok op (int_pre_cast σi x1) (int_pre_cast σi x2) σi →
  int_pre_arithop op (int_pre_cast σi x1) (int_pre_cast σi x2) σi = y →
  P ⊆{Γ,δ} (e1 .{ArithOp op} e2 ⇓ inr (intV{σi} y))%A.
Proof.
  intros ?? -> ??.
  rewrite assert_Prop_True by (rewrite <-(assert_eval_int_typed _ _ e1); auto).
  apply assert_Prop_intro_l; intros.
  rewrite assert_Prop_True by (rewrite <-(assert_eval_int_typed _ _ e2); auto).
  apply assert_Prop_intro_l; intros; eapply assert_eval_int_binop'; eauto.
  * by apply int_arithop_ok_more.
  * unfold int_binop. by rewrite int_arithop_spec by auto.
Qed.
Hint Extern 1 (cast_typed _ _) => constructor: core.
Hint Extern 1 (base_cast_typed _ _) => constructor: core.
Lemma assert_eval_int_cast Γ δ e x τi σi :
  int_cast_ok σi x → 
  (e ⇓ inr (intV{τi} x))%A
  ⊆{Γ,δ} (cast{(intT σi)%T} e ⇓ inr (intV{σi} (int_cast σi x)))%A.
Proof.
  intros ? Γ' Δ δ' ρ n m ?????? (τlr&?&?).
  assert ((Γ',Δ) ⊢ inr (intV{τi} x) : τlr) by eauto using expr_eval_typed.
  typed_inversion_all; simplify_option_eq.
  eauto 20 using lockset_empty_valid, TBase_valid, TInt_valid.
Qed.
Lemma assert_eval_int_cast' Γ δ P e x τi σi y :
  P ⊆{Γ,δ} (e ⇓ inr (intV{τi} x))%A →
  int_cast_ok σi x → int_cast σi x = y →
  P ⊆{Γ,δ} (cast{(intT σi)%T} e ⇓ inr (intV{σi} y))%A.
Proof. intros; subst; rewrite <-assert_eval_int_cast by eauto; eauto. Qed.
Lemma assert_eval_int_cast_self' Γ δ P e x τi :
  P ⊆{Γ,δ} (e ⇓ inr (intV{τi} x))%A →
  P ⊆{Γ,δ} (cast{(intT τi)%T} e ⇓ inr (intV{τi} x))%A.
Proof.
  intros HP. rewrite HP, assert_eval_int_typed'.
  eauto using assert_Prop_intro_l,
    assert_eval_int_cast', int_cast_ok_self, int_cast_self.
Qed.
Lemma assert_eval_singleton_l Γ δ a e μ γ τ :
  (%a ↦{μ,γ} e : τ)%A ⊆{Γ,δ} (%a ⇓ inl a)%A.
Proof.
  intros Γ' Δ δ' ρ n m ?????? (a'&v&?&?&?&?&?);
    eexists (inl (TType τ)); simplify_option_eq; eauto.
Qed.
Lemma assert_eval_singleton_r Γ δ e v μ γ τ :
  (e ↦{μ,γ} #v : τ)%A ⊆{Γ,δ} (#v ⇓ inr v)%A.
Proof.
  intros Γ' Δ δ' ρ n m ?????? (a&v'&?&?&?&?&?);
    eexists (inr τ); simplify_option_eq; eauto.
Qed.
Lemma assert_singleton_l Γ δ e1 e2 μ γ τ :
  (e1 ↦{μ,γ} e2 : τ)%A ≡{Γ,δ} (∃ a, (e1 ⇓ inl a ∧ emp) ★ %a ↦{μ,γ} e2 : τ)%A.
Proof.
  split.
  * intros Γ' Δ δ' ρ n m ?????? (a&v&?&?&?&?&?); exists (Ptr a).
    assert (sep_valid m) by eauto using cmap_valid_sep_valid.
    eexists ∅, m; split_and ?; simplify_option_eq; eauto 20 using
      @sep_left_id, eq_sym, lockset_empty_valid, mem_singleton_typed_addr_typed.
  * intros Γ' Δ δ' ρ n m_ ???? Hm ?
      (?&?&m&->&?&((τlr&?&?)&_&->)&(a&v&?&?&?&?&?)); simplify_option_eq.
    exists a, v; rewrite sep_left_id in Hm |- * by auto; split_and ?; auto.
    cut (τlr = inl (TType τ)); [intros ->; auto|typed_inversion_all].
    apply (typed_unique (Γ',Δ) (inl (Ptr a)));
      eauto using expr_eval_typed, cmap_empty_valid, cmap_valid_memenv_valid.
Qed.
Lemma assert_singleton_l_2 Γ δ e1 e2 μ γ a τ :
  ((e1 ⇓ inl a ∧ emp) ★ %a ↦{μ,γ} e2 : τ)%A ⊆{Γ,δ} (e1 ↦{μ,γ} e2 : τ)%A.
Proof. rewrite (assert_singleton_l _ _ e1); solve eauto. Qed.
Lemma assert_singleton_l_ Γ δ e μ γ τ :
  (e ↦{μ,γ} - : τ)%A ≡{Γ,δ} (∃ a, (e ⇓ inl a ∧ emp) ★ %a ↦{μ,γ} - : τ)%A.
Proof.
  setoid_rewrite (assert_singleton_l Γ δ e).
  by setoid_rewrite (assert_sep_exist Γ δ); rewrite assert_exist_exist.
Qed.
Lemma assert_singleton_l_2_ Γ δ e μ γ a τ :
  ((e ⇓ inl a ∧ emp) ★ %a ↦{μ,γ} - : τ)%A ⊆{Γ,δ} (e ↦{μ,γ} - : τ)%A.
Proof. rewrite (assert_singleton_l_ _ _ e); solve eauto. Qed.
Lemma assert_singleton_int_typed Γ δ e μ γ z τi :
  (e ↦{μ,γ} #intV{τi} z : intT τi)%A ⊆{Γ,δ} (⌜ int_typed z τi ⌝ ★ True)%A.
Proof. rewrite assert_eval_singleton_r; apply assert_eval_int_typed. Qed.
Lemma assert_singleton_int_typed' Γ δ e μ γ z τi :
  (e ↦{μ,γ} #intV{τi} z : intT τi)%A
  ⊆{Γ,δ} (⌜ int_typed z τi ⌝ ★ (e ↦{μ,γ} #intV{τi} z : intT τi))%A.
Proof. by apply assert_Prop_True, assert_singleton_int_typed. Qed.
Lemma assert_expr_lift Γ δ e ν : vars e = ∅ → (e↑ ⇓ ν)%A ≡{Γ,δ} (e ⇓ ν)%A.
Proof.
  split; intros Γ' Δ δ' ρ n m ?????? (τlr&?&?); exists τlr; split.
  * by apply expr_typed_var_free with (tail (ρ.*2)), expr_typed_lift.
  * erewrite expr_eval_var_free, <-expr_eval_lift; eauto.
  * eapply expr_typed_lift, expr_typed_var_free; eauto.
  * erewrite expr_eval_lift, <-expr_eval_var_free by done; eauto.
Qed.
Lemma assert_singleton_lift_l Γ δ e1 e2 μ γ τ :
  vars e1 = ∅ → (e1↑ ↦{μ,γ} e2 : τ)%A ≡{Γ,δ} (e1 ↦{μ,γ} e2 : τ)%A.
Proof.
  split; intros Γ' Δ δ' ρ n m ?????? (a&v&?&?&?&?&?);
    exists a, v; split_and ?; auto.
  * by apply expr_typed_var_free with (tail (ρ.*2)), expr_typed_lift.
  * erewrite expr_eval_var_free, <-expr_eval_lift; eauto.
  * eapply expr_typed_lift, expr_typed_var_free; eauto.
  * erewrite expr_eval_lift, <-expr_eval_var_free by done; eauto.
Qed.
Lemma assert_singleton_lift_r Γ δ e1 e2 μ γ τ :
  vars e2 = ∅ → (e1 ↦{μ,γ} (e2↑) : τ)%A ≡{Γ,δ} (e1 ↦{μ,γ} e2 : τ)%A.
Proof.
  split; intros Γ' Δ δ' ρ n m ?????? (a&v&?&?&?&?&?);
    exists a, v; split_and ?; auto.
  * by apply expr_typed_var_free with (tail (ρ.*2)), expr_typed_lift.
  * erewrite expr_eval_var_free, <-expr_eval_lift; eauto.
  * eapply expr_typed_lift, expr_typed_var_free; eauto.
  * erewrite expr_eval_lift, <-expr_eval_var_free by done; eauto.
Qed.
Lemma assert_singleton_eval Γ δ e v μ γ τ :
  Some Readable ⊆ perm_kind γ → (e ↦{μ,γ} #v : τ)%A ⊆{Γ,δ} (load e ⇓ inr v)%A.
Proof.
  intros ? Γ1 Δ δ' ρ n ??????? (a&v'&?&?&?&?&?); simplify_option_eq.
  assert (✓{Γ1} Δ) by eauto using cmap_valid_memenv_valid.
  eexists (inr τ); split_and ?; eauto using mem_singleton_typed_addr_typed,
    addr_typed_type_valid, type_valid_complete.
  erewrite (expr_eval_weaken _ _ _ _ _ ∅) by eauto using cmap_empty_valid,
    cmap_subseteq_index_alive, mem_lookup_subseteq, mem_forced_subseteq,
    @sep_subseteq_empty; simpl.
  by erewrite option_guard_True, mem_lookup_singleton
    by eauto using mem_singleton_forced.
Qed.
Lemma assert_singleton_union_lr Γ δ e1 e2 μ γ1 γ2 τ :
  ##[γ1;γ2] → ¬sep_unmapped γ1 → ¬sep_unmapped γ2 →
  (e1 ↦{μ,γ1 ∪ γ2} e2 : τ)%A ≡{Γ,δ} (e1 ↦{μ,γ1} e2 : τ ★ e1 ↦{μ,γ2} e2 : τ)%A.
Proof.
  intros; split.
  * intros Γ1 Δ δ' ρ n ??????? (a&v&?&?&?&?&?).
    destruct (mem_singleton_union_rev Γ1 Δ m a μ γ1 γ2 v τ)
      as (m1&m2&->&?&?&?); auto.
    exists m1, m2; split_and ?; solve ltac:(eauto).
  * intros Γ1 Δ δ' ρ n ??????? (?&?&->&?&(a1&v1&?&?&?&?&?)&(a2&v2&?&?&?&?&?));
      simplify_equality'; exists a1, v1; eauto 10 using mem_singleton_union.
Qed.
Lemma assert_singleton_union_l Γ δ e1 e2 μ γ1 γ2 τ :
  ##[γ1;γ2] → ¬sep_unmapped γ1 → γ2 ≠ ∅ →
  (e1 ↦{μ,γ1 ∪ γ2} e2 : τ)%A ≡{Γ,δ} (e1 ↦{μ,γ1} e2 : τ ★ e1 ↦{μ,γ2} - : τ)%A.
Proof.
  intros; split.
  * intros Γ1 Δ1 δ1 ρ n ??????? (a&v&?&?&?&?&?).
    destruct (decide (sep_unmapped γ2)).
    + destruct (mem_singleton_union_rev_unmapped Γ1 Δ1 m a μ γ1 γ2 v τ)
        as (m1&m2&->&?&?&?); auto using @sep_unmapped_empty_alt.
      assert ((Γ1,Δ1) ⊢ val_new Γ1 τ : τ).
      { eauto using val_new_typed,
          mem_singleton_typed_addr_typed, addr_typed_type_valid. }
      exists m1, m2; simplify_option_eq;
        eauto 20 using lockset_empty_valid.
    + destruct (mem_singleton_union_rev Γ1 Δ1 m a μ γ1 γ2 v τ)
        as (m1&m2&->&?&?&?); auto.
      exists m1, m2; solve ltac:(eauto using expr_eval_typed,
        lockset_empty_valid, cmap_empty_valid, cmap_valid_memenv_valid).
  * intros Γ1 Δ1 δ1 ρ n ???????
      (?&?&->&?&(a1&v1&?&?&?&?&?)&(?&a2&v2&?&?&?&?&?));
      simplify_option_eq; exists a1, v1; split_and ?; auto.
    by eapply (mem_singleton_union _ _ _ _ _ _ _ _ v1 v2); eauto.
Qed.
Lemma assert_singleton_union_r Γ δ e1 e2 μ γ1 γ2 τ :
  ##[γ1;γ2] → γ1 ≠ ∅ → ¬sep_unmapped γ2 →
  (e1 ↦{μ,γ1 ∪ γ2} e2 : τ)%A ≡{Γ,δ} (e1 ↦{μ,γ1} - : τ ★ e1 ↦{μ,γ2} e2 : τ)%A.
Proof.
  intros. rewrite (comm (★)%A), sep_commutative by auto.
  by rewrite assert_singleton_union_l by auto.
Qed.
Lemma assert_singleton_union Γ δ e1 μ γ1 γ2 τ :
  ##[γ1;γ2] → γ1 ≠ ∅ → γ2 ≠ ∅ →
  (e1 ↦{μ,γ1 ∪ γ2} - : τ)%A ≡{Γ,δ} (e1 ↦{μ,γ1} - : τ ★ e1 ↦{μ,γ2} - : τ)%A.
Proof.
  intros; split.
  * intros Γ1 Δ δ1 ρ n ??????? (?&a&v&?&?&?&?&?); simplify_option_eq;
      typed_inversion_all; destruct (decide (sep_unmapped γ2)).
    { destruct (mem_singleton_union_rev_unmapped Γ1 Δ m a μ γ1 γ2 v τ)
        as (m1&m2&->&?&?&?); auto using @sep_unmapped_empty_alt.
      assert ((Γ1,Δ) ⊢ val_new Γ1 τ : τ).
      { eauto using val_new_typed,
          mem_singleton_typed_addr_typed, addr_typed_type_valid. }
      exists m1, m2; split_and ?; eauto 10 using lockset_empty_valid. }
    destruct (decide (sep_unmapped γ1)).
    { destruct (mem_singleton_union_rev_unmapped Γ1 Δ m a μ γ2 γ1 v τ)
        as (m1&m2&->&?&?&?); auto using @sep_unmapped_empty_alt.
      { by rewrite sep_commutative by auto. }
      assert ((Γ1,Δ) ⊢ val_new Γ1 τ : τ).
      { eauto using val_new_typed,
          mem_singleton_typed_addr_typed, addr_typed_type_valid. }
      exists m2, m1; eauto 30 using @sep_commutative. }
    destruct (mem_singleton_union_rev Γ1 Δ m a μ γ1 γ2 v τ)
      as (m1&m2&->&?&?&?); eauto 40.
  * intros Γ1 Δ δ1 ρ n ???????
      (?&?&->&?&(?&a1&v1&?&?&?&?&?)&(?&a2&v2&?&?&?&?&?));
      simplify_option_eq; destruct (decide (sep_unmapped γ1)).
    + eexists v2, a1, v2; split_and ?; eauto.
      by eapply (mem_singleton_union _ _ _ _ _ _ _ _ v1 v2); eauto.
    + eexists v1, a1, v1; split_and ?; eauto.
      by eapply (mem_singleton_union _ _ _ _ _ _ _ _ v1 v2); eauto.
Qed.
Lemma assert_singleton_array Γ δ e μ γ vs τ n :
  length vs = n → n ≠ 0 →
  (e ↦{μ,γ} #(VArray τ vs) : (τ.[n]))%A
  ≡{Γ,δ} (Π imap_go (λ i v, (e %> RArray i τ n) ↦{μ,γ} #v : τ) 0 vs)%A.
Proof.
  intros Hn Hn'. split.
  * intros Γ1 Δ δ1 ρ n' ????? Hm ? (a&v&?&?&_&Hvs&w&->&->&Hw&Hw'&Ha&_&?&?).
    apply cmap_valid_memenv_valid in Hm; clear Hn Hn'.
    assert (∃ ws, w = MArray τ ws ∧ length ws = n ∧
      vs = to_val Γ1 <$> ws ∧ (Γ1,Δ) ⊢* ws : τ) as (ws&->&Hn&->&Hws).
    { destruct w; simplify_option_eq; typed_inversion_all; eauto. }
    assert (Forall (not ∘ Forall (∅ =.) ∘ ctree_flatten) ws) as Hemp.
    { clear Hn Hw Hvs.
      induction Hws as [|w ws]; constructor; decompose_Forall_hyps; eauto.
      eapply ctree_Forall_not, Forall_impl; naive_solver. }
    erewrite cmap_singleton_array_union by eauto.
    apply assert_Forall_holds_2; eauto using cmap_singleton_array_disjoint.
    cut (0 + length ws ≤ n); [|lia]; unfold imap_go; generalize 0 as j.
    clear Hemp Hn Hvs Hw; induction Hws as [|w ws]; intros j ?;
      decompose_Forall_hyps; constructor; eauto with lia.
    exists (addr_elt Γ1 (RArray j τ n) a), (to_val Γ1 w); split_and ?; eauto.
    + by simplify_option_eq.
    + typed_constructor; eauto using to_val_typed, lockset_empty_valid.
    + exists w; eauto 12 using addr_elt_is_obj, addr_elt_strict, addr_elt_typed.
  * intros Γ1 Δ δ1 ρ n' m _ ??? Hm ?.
    rewrite assert_Forall_holds; intros (ms&->&_&Hms).
    apply cmap_valid_memenv_valid in Hm.
    assert (∃ a, (Γ1,Δ,ρ.*2) ⊢ e : inl (TType (τ.[n]))%T ∧
      ⟦ e ⟧ Γ1 ρ ∅ = Some (inl (Ptr a)) ∧ addr_strict Γ1 a ∧
      γ ≠ ∅) as (a&He&?&?&?).
    { unfold imap_go in *; destruct vs; decompose_Forall_hyps.
      match goal with
      | H : ∃ a, _ |- _ => destruct H as (?&?&?&?&_&_&?&_&_&_&_&_&_&_&?)
      end; simplify_option_eq; typed_inversion_all; eauto. }
    assert (∃ ws,
      ms = imap_go (λ i, cmap_singleton Γ1 (addr_elt Γ1 (RArray i τ n) a) μ) 0 ws ∧
      vs = to_val Γ1 <$> ws ∧ (Γ1,Δ) ⊢* ws : τ ∧
      Forall (λ γb, tagged_perm γb = γ) (ws ≫= ctree_flatten))
      as (ws&->&->&Hws&Hws').
    { cut (0 + length vs ≤ n); [|lia]; unfold imap_go in *.
      clear Hn Hn' He; revert Hms; generalize 0 as j; revert vs.
      induction ms as [|m ms IH]; intros [|v vs] j ??; decompose_Forall_hyps.
      { eexists []; simpl; eauto. }
      match goal with
      | H : ∃ a, _ |- _ => destruct H as (?&?&_&?&_&?&w&->&->&Hw&?&_)
      end; simplify_option_eq.
      destruct (IH vs (S j)) as (ws&->&->&?&?); clear IH; auto with lia.
      exists (w :: ws); split_and ?; csimpl; eauto using Forall_app_2. }
    assert (Forall (not ∘ Forall (∅ =.) ∘ ctree_flatten) ws) as Hemp.
    { clear Hn Hms.
      induction Hws as [|w ws]; constructor; decompose_Forall_hyps; eauto.
      eapply ctree_Forall_not, Forall_impl; naive_solver. }
    assert ((Γ1,Δ) ⊢* to_val Γ1 <$> ws : τ).
    { eapply Forall_fmap; eauto using Forall_impl, to_val_typed. }
    assert ((Γ1,Δ) ⊢ a : TType (τ.[n])) by eauto 10
      using lval_typed_inv, Ptr_typed_inv, expr_eval_typed, cmap_empty_valid.
    exists a, (VArray τ (to_val Γ1 <$> ws));
      split_and ?; eauto using lockset_empty_valid.
    rewrite fmap_length in Hn.
    erewrite <-cmap_singleton_array_union by eauto.
    exists (MArray τ ws); eauto 10 using lval_typed_inv, expr_eval_typed,
      cmap_empty_valid, (addr_ref_byte_is_obj_parent _ _ (RArray 0 τ n)).
Qed.

(* Lifting De Bruijn indexes *)
#[global] Instance: `{Proper ((⊆{Γ,δ}) ==> (⊆{Γ,δ})) assert_lift}.
Proof. solve ltac:(eauto using Forall_tail). Qed.
#[global] Instance: `{Proper ((≡{Γ,δ}) ==> (≡{Γ,δ})) assert_lift}.
Proof. solve ltac:(eauto using Forall_tail). Qed.

Lemma assert_lift_impl Γ δ P Q : ((P → Q)↑)%A ≡{Γ,δ} (P↑ → Q↑)%A.
Proof. solve eauto. Qed.
Lemma assert_lift_and Γ δ P Q : ((P ∧ Q)↑)%A ≡{Γ,δ} (P↑ ∧ Q↑)%A.
Proof. solve eauto. Qed.
Lemma assert_lift_or Γ δ P Q : ((P ∨ Q)↑)%A ≡{Γ,δ} (P↑ ∨ Q↑)%A.
Proof. solve eauto. Qed.
Lemma assert_lift_not Γ δ P : ((¬P)↑)%A ≡{Γ,δ} (¬P↑)%A.
Proof. solve eauto. Qed.
Lemma assert_lift_forall Γ δ {A} (P : A → assert K) :
  ((∀ x, P x)↑)%A ≡{Γ,δ} (∀ x, P x↑)%A.
Proof. solve eauto. Qed.
Lemma assert_lift_exists Γ δ {A} (P : A → assert K) :
  ((∃ x, P x)↑)%A ≡{Γ,δ} (∃ x, P x↑)%A.
Proof. solve eauto. Qed.
Lemma assert_lift_sep Γ δ P Q : ((P ★ Q)↑)%A ≡{Γ,δ} (P↑ ★ Q↑)%A.
Proof. solve eauto. Qed.
Lemma assert_lift_wand Γ δ P Q : ((P -★ Q)↑)%A ≡{Γ,δ} (P↑ -★ Q↑)%A.
Proof. solve eauto. Qed.
Lemma assert_lift_expr Γ δ e v : ((e ⇓ v)↑)%A ≡{Γ,δ} (e↑ ⇓ v)%A.
Proof.
  split.
  * intros Γ' Δ δ' ρ n m ?????? (τlr&?&?); exists τlr.
    by rewrite expr_eval_lift, expr_typed_lift, <-fmap_tail.
  * intros Γ' Δ δ' ρ n m ?????? (τlr&?&?); exists τlr.
    by rewrite fmap_tail, <-expr_eval_lift, <-expr_typed_lift.
Qed.
Lemma assert_lift_expr_ Γ δ e : ((e ⇓ -)↑)%A ≡{Γ,δ} (e↑ ⇓ -)%A.
Proof.
  by rewrite assert_lift_exists; setoid_rewrite (assert_lift_expr Γ δ).
Qed.
Lemma assert_lift_singleton Γ δ e1 e2 μ γ τ :
  ((e1 ↦{μ,γ} e2 : τ)↑)%A ≡{Γ,δ} ((e1↑) ↦{μ,γ} (e2↑) : τ)%A.
Proof.
  split; repeat intro.
  * do 2 red. by setoid_rewrite expr_eval_lift;
      setoid_rewrite expr_typed_lift; rewrite <-fmap_tail.
  * do 4 red. by rewrite fmap_tail; setoid_rewrite <-expr_eval_lift;
      setoid_rewrite <-expr_typed_lift.
Qed.
Lemma assert_lift_singleton_ Γ δ e1 μ γ τ :
  ((e1 ↦{μ,γ} - : τ)↑)%A ≡{Γ,δ} ((e1↑) ↦{μ,γ} - : τ)%A.
Proof.
  by rewrite assert_lift_exists; setoid_rewrite (assert_lift_singleton Γ δ).
Qed.

#[global] Instance assert_lift_stack_indep: `{StackIndep P → StackIndep (P↑)}.
Proof. intros P ? Γ δ; by rewrite !stack_indep. Qed.
#[global] Instance assert_True_stack_indep : StackIndep True.
Proof. solve eauto. Qed.
#[global] Instance assert_False_stack_indep : StackIndep False.
Proof. solve eauto. Qed.
#[global] Instance assert_Prop_stack_indep P : StackIndep (⌜ P ⌝).
Proof. solve eauto. Qed.
#[global] Instance assert_impl_stack_indep :
  `{StackIndep P → StackIndep Q → StackIndep (P → Q)}.
Proof. by intros P Q ?? Γ δ; rewrite assert_lift_impl, !stack_indep. Qed.
#[global] Instance assert_and_stack_indep :
  `{StackIndep P → StackIndep Q → StackIndep (P ∧ Q)}.
Proof. solve eauto. Qed.
#[global] Instance assert_or_stack_indep :
  `{StackIndep P → StackIndep Q → StackIndep (P ∨ Q)}.
Proof. solve eauto. Qed.
#[global] Instance assert_forall_stack_indep A :
  `{(∀ x : A, StackIndep (P x)) → StackIndep (assert_forall P)}.
Proof. solve eauto. Qed.
#[global] Instance assert_exist_stack_indep A :
  `{(∀ x : A, StackIndep (P x)) → StackIndep (assert_exist P)}.
Proof. solve eauto. Qed.
#[global] Instance assert_sep_stack_indep :
  `{StackIndep P → StackIndep Q → StackIndep (P ★ Q)}.
Proof. by intros P Q HP HQ Γ δ; rewrite assert_lift_sep, !stack_indep. Qed.
#[global] Instance assert_wand_stack_indep :
  `{StackIndep P → StackIndep Q → StackIndep (P -★ Q)}.
Proof. by intros P Q ?? Γ δ; rewrite assert_lift_wand, !stack_indep. Qed.
#[global] Instance assert_expr_stack_indep e v : vars e = ∅ → StackIndep (e ⇓ v).
Proof. intros ? Γ δ. by rewrite assert_lift_expr, assert_expr_lift. Qed.
#[global] Instance assert_singleton_stack_indep e1 e2 μ γ τ :
  vars e1 = ∅ → vars e2 = ∅ → StackIndep (e1 ↦{μ,γ} e2 : τ).
Proof.
  by intros ?? Γ δ; rewrite assert_lift_singleton,
    assert_singleton_lift_l, assert_singleton_lift_r by done.
Qed.
Lemma stack_indep_spec P Γ Δ δ ρ1 ρ2 n m :
  StackIndep P → ✓ Γ → ✓{Γ,Δ} δ → ✓{Γ,Δ} m → ✓{Δ}* ρ1 → ✓{Δ}* ρ2 →
  assert_holds P Γ Δ δ ρ1 n m → assert_holds P Γ Δ δ ρ2 n m.
Proof.
  intros HP ??? Hρ1 Hρ2 ?; assert (assert_holds P Γ Δ δ [] n m).
  * induction Hρ1 as [|[o τ] ρ ?? IH]; auto.
    eapply IH, (proj2 (HP _ _) Γ Δ δ (_ :: _)); simpl; eauto.
  * induction Hρ2 as [|[o τ] ρ ?? IH]; auto.
    eapply (proj1 (HP _ _)), IH; simpl; eauto.
Qed.

(* Unlocking *)
Lemma assert_unlock_spec P Γ Δ δ ρ n m :
  assert_holds (P ◊) Γ Δ δ ρ n m = assert_holds P Γ Δ δ ρ n (mem_unlock_all m).
Proof. done. Qed.
#[global] Instance: `{Proper ((⊆{Γ,δ}) ==> (⊆{Γ,δ})) assert_unlock}.
Proof. solve ltac:(eauto using mem_unlock_all_valid). Qed.
#[global] Instance: `{Proper ((≡{Γ,δ}) ==> (≡{Γ,δ})) assert_unlock}.
Proof. solve ltac:(eauto using mem_unlock_all_valid). Qed.

Lemma assert_unlock_unlock Γ δ P : (P ◊ ◊)%A ≡{Γ,δ} (P ◊)%A.
Proof.
  split; intros Γ' Δ ρ m ????; simpl;
    by rewrite (mem_unlock_all_spec (mem_unlock_all _)),
    !mem_locks_unlock_all, mem_unlock_empty.
Qed.
Lemma assert_unlock_impl Γ δ P Q : ((P → Q) ◊)%A ≡{Γ,δ} (P ◊ → Q ◊)%A.
Proof.
  split; [solve ltac:(eauto using mem_unlock_all_valid)|].
  solve ltac:(eauto using cmap_valid_weaken_squeeze, mem_unlock_memenv_of).
Qed.
Lemma assert_unlock_and Γ δ P Q : ((P ∧ Q) ◊)%A ≡{Γ,δ} (P ◊ ∧ Q ◊)%A.
Proof. solve eauto. Qed.
Lemma assert_unlock_or Γ δ P Q : ((P ∨ Q) ◊)%A ≡{Γ,δ} (P ◊ ∨ Q ◊)%A.
Proof. solve eauto. Qed.
Lemma assert_unlock_forall Γ δ {A} (P : A → assert K) :
  ((∀ x, P x) ◊)%A ≡{Γ,δ} (∀ x, (P x) ◊)%A.
Proof. solve eauto. Qed.
Lemma assert_unlock_exists Γ δ {A} (P : A → assert K) :
  ((∃ x, P x) ◊)%A ≡{Γ,δ} (∃ x, (P x) ◊)%A.
Proof. solve eauto. Qed.
Lemma assert_unlock_sep Γ δ P Q : (P ◊ ★ Q ◊)%A ⊆{Γ,δ} ((P ★ Q) ◊)%A.
Proof.
  intros Γ1 Δ δ1 ρ n m ?????? (m1&m2&->&?&?&?).
  exists (mem_unlock_all m1), (mem_unlock_all m2); split_and ?; auto.
  * by rewrite mem_unlock_all_union by solve_sep_disjoint.
  * by rewrite <-!mem_unlock_all_disjoint_le.
Qed.
Lemma assert_unlock_sep_alt Γ δ P P' Q Q' :
  P ⊆{Γ,δ} (P' ◊)%A → Q ⊆{Γ,δ} (Q' ◊)%A → (P ★ Q)%A ⊆{Γ,δ} ((P' ★ Q') ◊)%A.
Proof. intros HP HQ. by rewrite HP, HQ, assert_unlock_sep. Qed.
Lemma assert_unlock_singleton Γ δ e1 e2 μ γ τ :
  perm_locked γ = true →
  (e1 ↦{μ,γ} e2 : τ)%A ⊆{Γ,δ} ((e1 ↦{μ,perm_unlock γ} e2 : τ) ◊)%A.
Proof.
  intros ? Γ1 Δ δ1 ρ n m ?????? (a&v&?&?&?&?&?).
  exists a, v; split_and ?; eauto using mem_unlock_all_singleton.
Qed.
Lemma assert_unlock_singleton_ Γ δ e1 μ γ τ :
  perm_locked γ = true →
  (e1 ↦{μ,γ} - : τ)%A ⊆{Γ,δ} ((e1 ↦{μ,perm_unlock γ} - : τ) ◊)%A.
Proof.
  intros Hγ. rewrite assert_unlock_exists.
  by setoid_rewrite (λ e2, assert_unlock_singleton Γ δ e1 e2 μ γ τ Hγ).
Qed.
Lemma assert_lock_singleton Γ δ e1 e2 μ γ τ :
  sep_valid γ → Some Writable ⊆ perm_kind γ →
  (e1 ↦{μ,perm_lock γ} e2 : τ)%A ⊆{Γ,δ} ((e1 ↦{μ,γ} e2 : τ) ◊)%A.
Proof.
  intros. by rewrite assert_unlock_singleton,
    perm_unlock_lock by auto using perm_locked_lock.
Qed.
Lemma assert_lock_singleton_ Γ δ e1 μ γ τ :
  sep_valid γ → Some Writable ⊆ perm_kind γ →
  (e1 ↦{μ,perm_lock γ} - : τ)%A ⊆{Γ,δ} ((e1 ↦{μ,γ} - : τ) ◊)%A.
Proof.
  intros. by rewrite assert_unlock_singleton_,
    perm_unlock_lock by auto using perm_locked_lock.
Qed.

#[global] Instance assert_unlock_unlock_indep P : UnlockIndep (P ◊).
Proof. intros Γ δ. by rewrite assert_unlock_unlock. Qed.
#[global] Instance assert_True_unlock_indep : UnlockIndep True.
Proof. solve ltac:(eauto using mem_unlock_all_empty). Qed.
#[global] Instance assert_False_unlock_indep : UnlockIndep False.
Proof. solve ltac:(eauto using mem_unlock_all_empty). Qed.
#[global] Instance assert_Prop_unlock_indep : `{UnlockIndep ⌜ P ⌝}.
Proof. solve ltac:(eauto using mem_unlock_all_empty). Qed.
#[global] Instance assert_and_unlock_indep :
  `{UnlockIndep P → UnlockIndep Q → UnlockIndep (P ∧ Q)}.
Proof. solve eauto. Qed.
#[global] Instance assert_or_unlock_indep :
  `{UnlockIndep P → UnlockIndep Q → UnlockIndep (P ∨ Q)}.
Proof. solve eauto. Qed.
#[global] Instance assert_forall_unlock_indep A :
  `{(∀ x : A, UnlockIndep (P x)) → UnlockIndep (assert_forall P)}.
Proof. solve eauto. Qed.
#[global] Instance assert_exist_unlock_indep A :
  `{(∀ x : A, UnlockIndep (P x)) → UnlockIndep (assert_exist P)}.
Proof. solve eauto. Qed.
#[global] Instance assert_lift_unlock_indep : `{UnlockIndep P → UnlockIndep (P↑)}.
Proof. solve ltac:(eauto using Forall_tail). Qed.
#[global] Instance assert_sep_unlock_indep P Q :
  UnlockIndep P → UnlockIndep Q → UnlockIndep (P ★ Q).
Proof. intros ?? [Γ δ]; auto using assert_unlock_sep_alt. Qed.
#[global] Instance assert_singleton_unlock_indep e1 e2 μ γ τ :
  perm_locked γ = false → UnlockIndep (e1 ↦{μ,γ} e2 : τ).
Proof.
  intros ? Γ δ Γ' Δ δ' ρ n m ?????? (a&v&?&?&?&?&?).
  exists a, v; split_and ?; eauto using mem_unlock_all_singleton_unlocked.
Qed.
End assertions.
