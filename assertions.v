(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** We define assertions of Hoare logic using a shallow embedding. That is,
assertions are predicates over the contents of the stack and memory. *)

(** This file defines the data type of assertions, the usual connectives of
Hoare logic ([∧], [¬], [↔], [∀] and [∃]), the connectives of separation
logic ([emp], [↦], [★]), and other connectives that are more specific to
our development. We overload the usual notations in [assert_scope] to obtain
nicely looking assertions. *)
Require Export expression_eval type_system memory_singleton.
Local Obligation Tactic := idtac.

Local Hint Extern 1 (_ ⊆ _) => etransitivity; [eassumption|].
Local Hint Extern 1 (_ ⊆ _) => etransitivity; [|eassumption].
Local Hint Extern 1 (_ ⊆{_} _) => etransitivity; [eassumption|].
Local Hint Extern 1 (_ ⊆{_} _) => etransitivity; [|eassumption].

(** * Definition of assertions *)
Record assert (K : Set) `{Env K} := Assert {
  assert_holds : env K → memenv K → stack K → mem K → Prop;
  assert_weaken Γ1 Γ2 Δ1 Δ2 ρ m :
    ✓ Γ1 → ✓{Γ1,Δ1} m → ✓{Δ1}* ρ →
    assert_holds Γ1 Δ1 ρ m →
    Γ1 ⊆ Γ2 → Δ1 ⇒ₘ Δ2 →
    assert_holds Γ2 Δ2 ρ m
}.
Add Printing Constructor assert.

Delimit Scope assert_scope with A.
Bind Scope assert_scope with assert.
Arguments Assert {_ _} _ _.
Arguments assert_holds {_ _} _%A _ _ _ _.
Arguments assert_weaken {_ _} _%A _ _ _ _ _ _ _ _ _ _ _ _.

(** The relation [P ⊆@{Γ} Q] states that the assertion [Q] is a logical
consequence of [P] in [Γ] and [P ≡@{Γ} Q] states that [P] and [Q] are logically
equivalent in [Γ]. *)
Instance assert_entails `{Env K} : SubsetEqE (env K) (assert K) := λ Γ P Q,
  ∀ Γ' Δ ρ m,
    Γ ⊆ Γ' → ✓ Γ' → ✓{Γ',Δ} m → ✓{Δ}* ρ →
    assert_holds P Γ' Δ ρ m → assert_holds Q Γ' Δ ρ m.
Instance assert_equiv `{Env K} : EquivE (env K) (assert K) := λ Γ P Q,
  P ⊆{Γ} Q ∧ Q ⊆{Γ} P.

(** * Hoare logic connectives *)
(** Definitions and notations of the usual connectives of Hoare logic. *)
Program Definition assert_Prop `{Env K} (P : Prop) : assert K := {|
  assert_holds Γ Δ ρ m := P ∧ m = ∅
|}.
Next Obligation. naive_solver. Qed.
Notation "⌜ P ⌝" := (assert_Prop P) (format "⌜  P  ⌝") : assert_scope.
Notation "'False'" := (assert_Prop False) : assert_scope.

Program Definition assert_impl `{Env K} (P Q : assert K) : assert K := {|
  assert_holds Γ Δ ρ m := ∀ Γ' Δ',
    Γ ⊆ Γ' → ✓ Γ' → Δ ⇒ₘ Δ' → ✓{Γ',Δ'} m →
    assert_holds P Γ' Δ' ρ m → assert_holds Q Γ' Δ' ρ m
|}.
Next Obligation.
  intros ?? P Q Γ1 Γ2 Δ1 Δ2 ρ m ??? HPQ ?? Γ3 Δ3 ?????.
  apply HPQ; eauto.
Qed.
Infix "→" := assert_impl : assert_scope.
Notation "(→)" := assert_impl (only parsing) : assert_scope.
Notation "( P →)" := (assert_impl P) (only parsing) : assert_scope.
Notation "(→ Q )" := (λ P, assert_impl P Q) (only parsing) : assert_scope.

Program Definition assert_and `{Env K} (P Q : assert K) : assert K := {|
  assert_holds Γ Δ ρ m :=
    assert_holds P Γ Δ ρ m ∧ assert_holds Q Γ Δ ρ m
|}.
Next Obligation. naive_solver eauto using assert_weaken. Qed.
Infix "∧" := assert_and : assert_scope.
Notation "(∧)" := assert_and (only parsing) : assert_scope.
Notation "( P ∧)" := (assert_and P) (only parsing) : assert_scope.
Notation "(∧ Q )" := (λ P, assert_and P Q) (only parsing) : assert_scope.

Definition assert_not `{Env K} (P : assert K) : assert K := (P → False)%A.
Notation "¬ P" := (assert_not P) : assert_scope.
Definition assert_iff `{Env K} (P Q : assert K) : assert K :=
  ((P → Q) ∧ (Q → P))%A.
Infix "↔" := assert_iff : assert_scope.
Notation "(↔)" := assert_iff (only parsing) : assert_scope.
Notation "( P ↔)" := (assert_iff P) (only parsing) : assert_scope.
Notation "(↔ Q )" := (λ P, assert_iff P Q) (only parsing) : assert_scope.

Program Definition assert_forall `{Env K} `(P: A → assert K) : assert K := {|
  assert_holds := λ Γ Δ ρ m, ∀ x, assert_holds (P x) Γ Δ ρ m
|}.
Next Obligation. naive_solver eauto using assert_weaken. Qed.
Notation "∀ x .. y , P" :=
  (assert_forall (λ x, .. (assert_forall (λ y, P)) ..)) : assert_scope.

Program Definition assert_exist `{Env K} `(P : A → assert K): assert K := {|
  assert_holds := λ Γ Δ ρ m, ∃ x, assert_holds (P x) Γ Δ ρ m
|}.
Next Obligation. naive_solver eauto using assert_weaken. Qed.
Notation "∃ x .. y , P" :=
  (assert_exist (λ x, .. (assert_exist (λ y, P)) ..)) : assert_scope.

(** * Separation logic connectives *)
(** The assertion [emp] asserts that the memory is empty. The assertion [P ★ Q]
(called separating conjunction) asserts that the memory can be split into two
disjoint parts such that [P] holds in the one part, and [Q] in the other. *)
Notation "'emp'" := (assert_Prop True) : assert_scope.

Program Definition assert_sep `{EnvSpec K} (P Q : assert K) : assert K := {|
  assert_holds Γ Δ ρ m := ∃ m1 m2,
    m = m1 ∪ m2 ∧ ⊥[m1; m2] ∧
    assert_holds P Γ Δ ρ m1 ∧ assert_holds Q Γ Δ ρ m2
|}.
Next Obligation.
  intros ??? P Q Γ1 Γ2 Δ1 Δ2 ρ m ??? (m1&m2&->&?&?&?) ??.
  eauto 15 using assert_weaken, cmap_valid_subseteq,
    @sep_union_subseteq_l, @sep_union_subseteq_r.
Qed.
Infix "★" := assert_sep (at level 80, right associativity) : assert_scope.
Notation "(★)" := assert_sep (only parsing) : assert_scope.
Notation "( P ★)" := (assert_sep P) (only parsing) : assert_scope.
Notation "(★ Q )" := (λ P, assert_sep P Q) (only parsing) : assert_scope.

Program Definition assert_wand `{Env K} (P Q : assert K) : assert K := {|
  assert_holds Γ Δ ρ m2 := ∀ Γ' Δ' m1,
    Γ ⊆ Γ' → ✓ Γ' → Δ ⇒ₘ Δ' → ✓{Γ',Δ'} m1 → ✓{Γ',Δ'} m2 →
    ⊥[m1; m2] → assert_holds P Γ' Δ' ρ m1 → assert_holds Q Γ' Δ' ρ (m1 ∪ m2)
|}.
Next Obligation.
  intros ?? P Q Γ1 Γ2 Δ1 Δ2 ρ m ??? HPQ ?? Γ3 Δ3 ????????; apply HPQ; eauto.
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
Notation vassert K := (lrval K → assert K).
Program Definition assert_expr `{EnvSpec K} (e : expr K) : vassert K := λ ν, {|
  assert_holds Γ Δ ρ m := ∃ τlr, (Γ,Δ,ρ.*2) ⊢ e : τlr ∧ ⟦ e ⟧ Γ ρ m = Some ν
|}.
Next Obligation.
  intros ??? e ν Γ1 Γ2 Δ1 Δ2 ρ m ??? (τlr&?&?) ??; exists τlr; split;
    eauto using expr_typed_weaken, expr_eval_weaken,
    mem_lookup_weaken, mem_forced_weaken.
Qed.
Notation "e ⇓ ν" := (assert_expr e ν)%A
  (at level 60, ν at next level, format "e  '⇓'  ν") : assert_scope.
Notation "e ⇓ -" := (∃ ν, e ⇓ ν)%A
  (at level 60, format "e  '⇓'  '-'") : assert_scope.

(** The assertion [e1 ↦{μ,x} e2] asserts that the memory consists of
exactly one object at address [e1] with permission [x] and contents [e2]. The
assertion [e1 ↦{μ,x} -] asserts that the memory consists of exactly one
object at address [e1] with permission [x] and arbitrary contents. The Boolean
[μ] denotes whether the object has been obtained via malloc. *)
Program Definition assert_singleton `{EnvSpec K}
    (e1 : expr K) (μ : bool) (x : perm)
    (e2 : expr K) (τ : type K) : assert K := {|
  assert_holds Γ Δ ρ m := ∃ a v,
    (Γ,Δ,ρ.*2) ⊢ e1 : inl τ ∧ ⟦ e1 ⟧ Γ ρ ∅ = Some (inl a) ∧
    (Γ,Δ,ρ.*2) ⊢ e2 : inr τ ∧ ⟦ e2 ⟧ Γ ρ ∅ = Some (inr v) ∧
    mem_singleton Γ Δ a μ x v τ m
|}.
Next Obligation.
  intros ??? e1 e2 ml x τ Γ1 Γ2 Δ1 Δ2 ρ m ??? (a&v&?&?&?&?&?) ??.
  exists a v; split_ands; eauto using expr_typed_weaken,
    expr_eval_weaken_empty, mem_singleton_weaken, cmap_valid_memenv_valid.
Qed.
Notation "e1 ↦{ μ , x } e2 : τ" := (assert_singleton e1 μ x e2 τ)%A
  (at level 20, μ at next level, x at next level, e2 at next level,
   τ at next level, format "e1  ↦{ μ , x }  e2  :  τ") : assert_scope.
Notation "e1 ↦{ μ , x } - : τ" :=
  (∃ ν, e1 ↦{μ,x} (%# ν) : τ)%A
  (at level 20, μ at next level, x at next level,
   τ at next level, format "e1  ↦{ μ , x }  -  :  τ") : assert_scope.

(** The assertion [P ◊] asserts that [P] holds if all sequenced locations
are unlocked. *)
Program Definition assert_unlock `{EnvSpec K} (P : assert K) : assert K := {|
  assert_holds := λ Γ Δ ρ m, assert_holds P Γ Δ ρ (mem_unlock_all m)
|}.
Next Obligation.
  naive_solver eauto using assert_weaken, mem_unlock_all_valid.
Qed.
Notation "P ◊" := (assert_unlock P) (at level 20) : assert_scope.

(** The assertion [P↡] asserts that [P] holds if the stack is cleared. This
connective allows us to specify stack independence in an alternative way. *)
Program Definition assert_clear_stack `{Env K} (P : assert K) : assert K := {|
  assert_holds := λ Γ Δ ρ m, assert_holds P Γ Δ [] m
|}.
Next Obligation. naive_solver eauto using assert_weaken, Forall2_nil. Qed.
Notation "P ↡" := (assert_clear_stack P) (at level 20) : assert_scope.

(** To deal with block scope variables we need to lift an assertion such that
the De Bruijn indexes of its variables are increased. We define the lifting
[P↑] of an assertion [P] semantically, and prove that it indeed behaves as
expected. *)
Program Definition assert_lift `{Env K} (P : assert K) : assert K := {|
  assert_holds := λ Γ Δ ρ m, assert_holds P Γ Δ (tail ρ) m
|}.
Next Obligation. naive_solver eauto using assert_weaken, Forall_tail. Qed.
Notation "P ↑" := (assert_lift P) (at level 20) : assert_scope.

(** * Subclasses of assertions *)
(** The following type classes collect important subclasses of assertions.
- [StackIndep] collects assertions that are independent of the stack.
- [UnlockIndep] collects assertions that are independent of unlocking
  sequenced locations in the memory.

This file contains instances of these type classes for the various connectives.
We use instance resolution to automatically compose these instances to prove
the above properties for composite assertions. *)
Class StackIndep `{Env K} (P : assert K) : Prop :=
  stack_indep Γ Δ ρ1 ρ2 m :
    ✓ Γ → ✓{Γ,Δ} m → ✓{Δ}* ρ1 → ✓{Δ}* ρ2 →
    assert_holds P Γ Δ ρ1 m → assert_holds P Γ Δ ρ2 m.
Class UnlockIndep `{Env K} (P : assert K) : Prop :=
  unlock_indep Γ Δ ρ m :
    ✓ Γ → ✓{Γ,Δ} m → ✓{Δ}* ρ →
    assert_holds P Γ Δ ρ m → assert_holds P Γ Δ ρ (mem_unlock_all m).

Hint Extern 10 (StackIndep _) => apply _.
Hint Extern 10 (UnlockIndep _) => apply _.

Section assertions.
Context `{EnvSpec K}.
Implicit Types Γ : env K.

Hint Unfold Proper respectful pointwise_relation : assert.
Hint Unfold subseteqE assert_entails equivE assert_equiv : assert.
Hint Unfold StackIndep UnlockIndep : assert.
Hint Extern 100 (⊥ _) => solve_sep_disjoint.
Hint Extern 100 (_ ⊥ _) => solve_sep_disjoint.
Hint Extern 100 (sep_valid _) => solve_sep_disjoint.
Hint Immediate cmap_valid_sep_valid.
Hint Extern 0 (_ ⊢ _ : _ ↣ _) => typed_constructor; try omega.
Hint Extern 0 (_ ⊢ _ : _) => typed_constructor.

Ltac solve t :=
  repeat first
  [ progress simplify_equality'
  | progress autounfold with assert in *];
  naive_solver t.

(** Ordinary logic connections *)
Global Instance: PreOrder (⊆{Γ}).
Proof. split; solve eauto. Qed.
Global Instance: Equivalence (≡{Γ}).
Proof. split; red; solve eauto. Qed.
Global Instance: Proper ((≡{Γ}) ==> (≡{Γ}) ==> iff) (⊆{Γ}).
Proof. solve eauto. Qed.
Global Instance: Proper (impl ==> (⊆{Γ})) assert_Prop.
Proof. solve eauto. Qed.
Global Instance: Proper (iff ==> (≡{Γ})) assert_Prop.
Proof. solve eauto. Qed.
Global Instance: Proper (flip (⊆{Γ}) ==> (⊆{Γ}) ==> (⊆{Γ})) (→)%A.
Proof.
  intros Γ1 P1 P2 HP Q1 Q2 HQ Γ2 Δ ρ m ???? HPQ Γ3 Δ2 ???? HP2.
  eapply HQ; eauto using indexes_valid_weaken.
Qed.
Global Instance: Proper ((≡{Γ}) ==> (≡{Γ}) ==> (≡{Γ})) (→)%A.
Proof. by intros ??? [??] ?? [??]; split; f_equiv. Qed.
Global Instance: Proper ((≡{Γ}) ==> (≡{Γ}) ==> (≡{Γ})) (∧)%A.
Proof. solve eauto. Qed.
Global Instance: Proper ((⊆{Γ}) ==> (⊆{Γ}) ==> (⊆{Γ})) (∧)%A.
Proof. solve eauto. Qed.
Global Instance: Proper ((≡{Γ}) ==> (≡{Γ}) ==> (≡{Γ})) (↔)%A.
Proof. by intros ???????; unfold assert_iff; do 2 f_equiv. Qed.
Global Instance: Proper ((≡{Γ}) ==> (≡{Γ})) assert_not.
Proof. by intros ????; unfold assert_not; f_equiv. Qed.
Global Instance: Proper (flip (⊆{Γ}) ==> (⊆{Γ})) assert_not.
Proof. by intros ????; unfold assert_not; f_equiv. Qed.
Global Instance:
  Proper (pointwise_relation _ (≡{Γ}) ==> (≡{Γ})) (@assert_forall _ _ A).
Proof. solve eauto. Qed.
Global Instance:
  Proper (pointwise_relation _ (⊆{Γ}) ==> (⊆{Γ})) (@assert_forall _ _ A).
Proof. solve eauto. Qed.
Global Instance:
  Proper (pointwise_relation _ (≡{Γ}) ==> (≡{Γ})) (@assert_exist _ _ A).
Proof. solve eauto. Qed.
Global Instance:
  Proper (pointwise_relation _ (⊆{Γ}) ==> (⊆{Γ})) (@assert_exist _ _ A).
Proof. solve eauto. Qed.
Global Instance:
  Proper (pointwise_relation _ (flip (⊆{Γ})) ==> (flip (⊆{Γ})))
  (@assert_exist _ _ A).
Proof. solve eauto. Qed.

Global Instance assert_Prop_stack_indep P : StackIndep (⌜ P ⌝).
Proof. solve eauto. Qed.
Global Instance assert_impl_stack_indep :
  StackIndep P → StackIndep Q → StackIndep (P → Q).
Proof.
  intros P Q HP HQ Γ Δ ρ1 ρ2 m ???? HPQ Γ2 Δ2 ???? HP'.
  eapply HQ, HPQ, HP with ρ2; eauto using indexes_valid_weaken.
Qed.
Global Instance assert_and_stack_indep :
  StackIndep P → StackIndep Q → StackIndep (P ∧ Q).
Proof. solve eauto. Qed.
Global Instance assert_forall_stack_indep A :
  (∀ x : A, StackIndep (P x)) → StackIndep (assert_forall P).
Proof. solve eauto. Qed.
Global Instance assert_exist_stack_indep A :
  (∀ x : A, StackIndep (P x)) → StackIndep (assert_exist P).
Proof. solve eauto. Qed.

Global Instance assert_Prop_unlock_indep P : UnlockIndep (⌜ P ⌝).
Proof. solve ltac:(eauto using mem_unlock_all_empty). Qed.
Global Instance assert_and_unlock_indep :
  UnlockIndep P → UnlockIndep Q → UnlockIndep (P ∧ Q).
Proof. solve eauto. Qed.
Global Instance assert_forall_unlock_indep A :
  (∀ x : A, UnlockIndep (P x)) → UnlockIndep (assert_forall P).
Proof. solve eauto. Qed.
Global Instance assert_exist_unlock_indep A :
  (∀ x : A, UnlockIndep (P x)) → UnlockIndep (assert_exist P).
Proof. solve eauto. Qed.

Global Instance: Commutative (≡{Γ}) (↔)%A.
Proof. red; solve eauto. Qed.
Global Instance: Commutative (≡{Γ}) (∧)%A.
Proof. red; solve eauto. Qed.
Global Instance: Associative (≡{Γ}) (∧)%A.
Proof. red; solve eauto. Qed.
Global Instance: Idempotent (≡{Γ}) (∧)%A.
Proof. red; solve eauto. Qed.
Global Instance: LeftAbsorb (≡{Γ}) False%A (∧)%A.
Proof. red; solve eauto. Qed.
Global Instance: RightAbsorb (≡{Γ}) False%A (∧)%A.
Proof. red; solve eauto. Qed.
Lemma assert_Prop_impl Γ (P Q : Prop) : ⌜ P → Q ⌝%A ⊆{Γ} (⌜P⌝ → ⌜Q⌝)%A.
Proof. solve eauto. Qed.
Lemma assert_Prop_not Γ (P : Prop) : ⌜ ¬P ⌝%A ⊆{Γ} (¬⌜P⌝)%A.
Proof. apply assert_Prop_impl. Qed.
Lemma assert_Prop_and Γ (P Q : Prop) : ⌜ P ∧ Q ⌝%A ≡{Γ} (⌜P⌝ ∧ ⌜Q⌝)%A.
Proof. solve eauto. Qed.
Lemma assert_false_elim Γ P : False%A ⊆{Γ} P.
Proof. solve eauto. Qed.
Lemma assert_and_l Γ P Q : (P ∧ Q)%A ⊆{Γ} P.
Proof. solve eauto. Qed.
Lemma assert_and_r Γ P Q : (P ∧ Q)%A ⊆{Γ} Q.
Proof. solve eauto. Qed.
Lemma assert_and_intro Γ P Q1 Q2 : P ⊆{Γ} Q1 → P ⊆{Γ} Q2 → P ⊆{Γ} (Q1 ∧ Q2)%A.
Proof. solve eauto. Qed.
Lemma assert_and_elim_l Γ P1 P2 Q : P1 ⊆{Γ} Q → (P1 ∧ P2)%A ⊆{Γ} Q.
Proof. solve eauto. Qed.
Lemma assert_and_elim_r Γ P1 P2 Q : P2 ⊆{Γ} Q → (P1 ∧ P2)%A ⊆{Γ} Q.
Proof. solve eauto. Qed.
Lemma assert_forall_intro {A} Γ P (Q : A → assert K) :
  (∀ x, P ⊆{Γ} Q x) → P ⊆{Γ} (∀ x, Q x)%A.
Proof. solve eauto. Qed.
Lemma assert_forall_elim {A} Γ (P : A → assert K) Q x :
  (P x ⊆{Γ} Q) → (∀ x, P x)%A ⊆{Γ} Q.
Proof. solve eauto. Qed.
Lemma assert_exist_intro {A} Γ P (Q : A → assert K) x :
  P ⊆{Γ} Q x → P ⊆{Γ} (∃ x, Q x)%A.
Proof. solve eauto. Qed.
Lemma assert_exist_elim {A} Γ (P : A → assert K) Q :
  (∀ x, P x ⊆{Γ} Q) → (∃ x, P x)%A ⊆{Γ} Q.
Proof. solve eauto. Qed.
Lemma assert_and_exist {A} Γ P (Q : A → assert K) :
  (P ∧ ∃ x, Q x)%A ≡{Γ} (∃ x, P ∧ Q x)%A.
Proof. solve eauto. Qed.
Lemma assert_exist_and {A} Γ (P : A → assert K) Q :
  ((∃ x, P x) ∧ Q)%A ≡{Γ} (∃ x, P x ∧ Q)%A.
Proof. solve eauto. Qed.
Lemma assert_Prop_intro_l Γ (P : Prop) Q R :
  (P → Q ⊆{Γ} R) → (⌜ P ⌝ ∧ Q)%A ⊆{Γ} R.
Proof. solve eauto. Qed.
Lemma assert_Prop_intro_r Γ (P : Prop) Q R :
  (P → Q ⊆{Γ} R) → (Q ∧ ⌜ P ⌝)%A ⊆{Γ} R.
Proof. solve eauto. Qed.
Lemma assert_Prop_and_elim Γ (P : Prop) Q R :
  (P → Q ⊆{Γ} R) → (⌜ P ⌝ ∧ Q)%A ⊆{Γ} R.
Proof. solve eauto. Qed.
Lemma assert_and_Prop_elim Γ (P : Prop) Q R :
  (P → Q ⊆{Γ} R) → (Q ∧ ⌜ P ⌝)%A ⊆{Γ} R.
Proof. solve eauto. Qed.

(** Separation logic connectives *)
Global Instance: Proper ((⊆{Γ}) ==> (⊆{Γ}) ==> (⊆{Γ})) (★)%A.
Proof.
  solve ltac:(eauto 15 using cmap_valid_subseteq,
    @sep_union_subseteq_l, @sep_union_subseteq_r).
Qed.
Global Instance: Proper ((≡{Γ}) ==> (≡{Γ}) ==> (≡{Γ})) (★)%A.
Proof.
  by intros ??? [??] ?? [??]; split;
    apply (_ : Proper ((⊆{Γ}) ==> (⊆{Γ}) ==> (⊆{Γ})) (★)%A).
Qed.
Global Instance: Proper (Forall2 (≡{Γ}) ==> (≡{Γ})) assert_sep_list.
Proof.
  induction 1; simpl; [done|];
    by apply (_ : Proper ((≡{Γ}) ==> (≡{Γ}) ==> (≡{Γ})) (★)%A).
Qed.
Global Instance: Proper (flip (⊆{Γ}) ==> (⊆{Γ}) ==> (⊆{Γ})) (-★)%A.
Proof.
  intros Γ1 P1 P2 HP Q1 Q2 HQ Γ2 Δ ρ m ???? HPQ Γ3 Δ2 m2 ?????? HP2.
  apply HQ; eauto using indexes_valid_weaken, cmap_union_valid_2.
Qed.
Global Instance: Proper ((≡{Γ}) ==> (≡{Γ}) ==> (≡{Γ})) (-★)%A.
Proof.
  by intros ??? [??] ?? [??]; split;
    apply (_ : Proper (flip (⊆{Γ}) ==> (⊆{Γ}) ==> (⊆{Γ})) (-★)%A).
Qed.

Global Instance assert_sep_unlock_indep P Q :
  UnlockIndep P → UnlockIndep Q → UnlockIndep (P ★ Q).
Proof.
  intros HP HQ Γ Δ δ m ??? (m1&m2&->&?&?&?).
  rewrite mem_unlock_all_union by solve_sep_disjoint.
  exists (mem_unlock_all m1) (mem_unlock_all m2); split_ands;
    rewrite <-?mem_unlock_all_disjoint_le; eauto using
    cmap_valid_subseteq, @sep_union_subseteq_l, @sep_union_subseteq_r.
Qed.
Global Instance assert_sep_stack_indep :
  StackIndep P → StackIndep Q → StackIndep (P ★ Q).
Proof.
  solve ltac:(eauto 15 using cmap_valid_subseteq,
    @sep_union_subseteq_l, @sep_union_subseteq_r).
Qed.
Global Instance assert_wand_stack_indep :
  StackIndep P → StackIndep Q → StackIndep (P -★ Q).
Proof.
  intros P Q HP HQ Γ Δ ρ1 ρ2 m2 ???? HPQ Γ2 Δ2 m1 ?????? HP'.
  eapply HQ, HPQ, HP with ρ2;
    eauto using indexes_valid_weaken, cmap_union_valid_2.
Qed.

Global Instance: Commutative (⊆{Γ}) (★)%A.
Proof.
  intros Γ P Q Γ1 Δ1 ρ m ???? (m1&m2&->&?&?&?).
  exists m2 m1. rewrite sep_commutative by auto; auto.
Qed.
Global Instance: Commutative (≡{Γ}) (★)%A.
Proof. split; by rewrite (commutative (★)%A). Qed.
Global Instance: LeftId (≡{Γ}) emp%A (★)%A.
Proof.
  intros Γ; intros P; split.
  * intros Γ1 Δ1 ρ m ???? (m1&m2&->&?&[_ ->]&?).
    rewrite sep_left_id by auto; auto.
  * intros Γ1 Δ1 ρ m ?????. eexists ∅, m.
    rewrite sep_left_id, sep_disjoint_equiv_empty,
      sep_disjoint_list_singleton by eauto; solve eauto.
Qed.
Global Instance: RightId (≡{Γ}) emp%A (★)%A.
Proof. intros ??. by rewrite (commutative _), (left_id _ _). Qed.
Global Instance: LeftAbsorb (≡{Γ}) False%A (★)%A.
Proof. red; solve eauto. Qed.
Global Instance: RightAbsorb (≡{Γ}) False%A (★)%A.
Proof. red; solve eauto. Qed.
Global Instance: Associative (≡{Γ}) (★)%A.
Proof.
  intros Γ. assert (∀ P Q R, ((P ★ Q) ★ R)%A ⊆{Γ} (P ★ (Q ★ R))%A).
  { intros P Q R Γ1 Δ1 ρ ????? (?&m3&->&?&(m1&m2&->&?&?&?)&?).
    exists m1 (m2 ∪ m3); rewrite sep_associative by auto; split_ands; auto.
    exists m2 m3; auto. }
  assert (∀ P Q R, (P ★ (Q ★ R))%A ⊆{Γ} ((P ★ Q) ★ R)%A).
  { intros P Q R Γ1 Δ1 ρ ????? (m1&?&->&?&?&(m2&m3&->&?&?&?)).
    exists (m1 ∪ m2) m3; rewrite sep_associative by auto; split_ands; auto.
    exists m1 m2; auto. }
  split; auto.
Qed.
Lemma assert_Prop_and_intro Γ (P : Prop) Q R :
  P → Q ⊆{Γ} R → Q ⊆{Γ} (⌜ P ⌝ ★ R)%A.
Proof.
  intros ?? Γ1 Δ1 ρ ??????. eexists ∅, m.
  rewrite sep_left_id, sep_disjoint_equiv_empty,
    sep_disjoint_list_singleton by eauto; solve eauto.
Qed.
Lemma assert_and_Prop_intro Γ (P : Prop) Q R :
  P → Q ⊆{Γ} R → Q ⊆{Γ} (R ★ ⌜ P ⌝)%A.
Proof. rewrite (commutative (★)%A). apply assert_Prop_and_intro. Qed. 
Lemma assert_sep_exist {A} Γ P (Q : A → assert K) :
  (P ★ ∃ x, Q x)%A ≡{Γ} (∃ x, P ★ Q x)%A.
Proof. solve eauto. Qed.
Lemma assert_exist_sep {A} Γ (P : A → assert K) Q :
  ((∃ x, P x) ★ Q)%A ≡{Γ} (∃ x, P x ★ Q)%A.
Proof. solve eauto. Qed.
Lemma assert_wand_intro Γ P Q R : (P ★ Q)%A ⊆{Γ} R → P ⊆{Γ} (Q -★ R)%A.
Proof.
  intros HPQR Γ1 Δ1 ρ m1 ???? HP Γ2 Δ2 m2 ?????? HQ.
  apply HPQR; eauto using indexes_valid_weaken, cmap_union_valid_2.
  exists m1 m2; split_ands; eauto using assert_weaken, @sep_commutative.
Qed.
Lemma assert_wand_elim Γ P Q : ((P -★ Q) ★ P)%A ⊆{Γ} Q.
Proof.
  intros Γ1 Δ1 ρ ????? (m1&m2&->&?&HQ&?).
  rewrite sep_commutative by auto; eapply HQ; eauto using
    cmap_valid_subseteq, @sep_union_subseteq_l, @sep_union_subseteq_r.
Qed.

Lemma assert_Forall_holds_2 (Ps : list (assert K)) Γ Δ ρ ms :
  ⊥ ms → Forall2 (λ (P : assert K) m, assert_holds P Γ Δ ρ m) Ps ms →
  assert_holds (Π Ps)%A Γ Δ ρ (⋃ ms).
Proof. intros Hms HPs. revert Hms. induction HPs; solve eauto. Qed.
Lemma assert_Forall_holds (Ps : list (assert K)) Γ Δ ρ m :
  assert_holds (Π Ps)%A Γ Δ ρ m ↔ ∃ ms, m = ⋃ ms ∧ ⊥ ms ∧
    Forall2 (λ (P : assert K) m, assert_holds P Γ Δ ρ m) Ps ms.
Proof.
  split; [|naive_solver eauto using assert_Forall_holds_2].
  revert m. induction Ps as [|P Ps IH].
  { intros m [? ->]. eexists []. by repeat constructor. }
  intros ? (m1&m2&->&?&?&?); destruct (IH m2) as (ms&->&?&?); trivial.
  exists (m1 :: ms); auto.
Qed.

(* Evaluation and singleton connectives *)
Global Instance assert_expr_stack_indep e v : vars e = ∅ → StackIndep (e ⇓ v).
Proof.
  intros ? Γ Δ ρ1 ρ2 m ???? (τlr&?&?); exists τlr; split;
    erewrite 1?expr_eval_var_free by eauto; eauto using expr_typed_var_free.
Qed.
Global Instance assert_singleton_stack_indep e1 e2 μ x τ :
  vars e1 = ∅ → vars e2 = ∅ → StackIndep (e1 ↦{μ,x} e2 : τ).
Proof.
  intros ?? Γ Δ ρ1 ρ2 m ???? (a&v&?&?&?&?&?);
    exists a v; erewrite !(expr_eval_var_free _ ρ2 ρ1) by eauto;
    split_ands; eauto using expr_typed_var_free.
Qed.
Global Instance assert_singleton_unlock_indep Γ e1 e2 μ x τ :
  perm_locked x = false → UnlockIndep (e1 ↦{μ,x} e2 : τ).
Proof.
  intros ? Γ1 Δ1 ρ m ??? (a&v&?&?&?&?&?).
  exists a v; split_ands; eauto using mem_unlock_all_singleton_unlocked.
Qed.

Lemma assert_singleton_union_lr Γ e1 e2 μ x y τ :
  ⊥[x; y] → ¬sep_unmapped x → ¬sep_unmapped y →
  (e1 ↦{μ,x ∪ y} e2 : τ)%A ≡{Γ} (e1 ↦{μ,x} e2 : τ ★ e1 ↦{μ,y} e2 : τ)%A.
Proof.
  intros; split.
  * intros Γ1 Δ1 ρ ????? (a&v&?&?&?&?&?).
    destruct (mem_singleton_union_rev Γ1 Δ1 m a μ x y v τ)
      as (m1&m2&->&?&?&?); auto.
    exists m1 m2; split_ands; solve ltac:eauto.
  * intros Γ1 Δ1 ρ ????? (?&?&->&?&(a1&v1&?&?&?&?&?)&(a2&v2&?&?&?&?&?));
      simplify_equality'; exists a1 v1; eauto 10 using mem_singleton_union.
Qed.
Lemma assert_singleton_union_l Γ e1 e2 μ x y τ :
  ⊥[x; y] → ¬sep_unmapped x → y ≠ ∅ →
  (e1 ↦{μ,x ∪ y} e2 : τ)%A ≡{Γ} (e1 ↦{μ,x} e2 : τ ★ e1 ↦{μ,y} - : τ)%A.
Proof.
  intros; split.
  * intros Γ1 Δ1 ρ ????? (a&v&?&?&?&?&?); destruct (decide (sep_unmapped y)).
    + destruct (mem_singleton_union_rev_unmapped Γ1 Δ1 m a μ x y v τ)
        as (m1&m2&->&?&?&?); auto using @sep_unmapped_empty_alt.
      assert ((Γ1,Δ1) ⊢ val_new Γ1 τ : τ).
      { eauto using val_new_typed,
          mem_singleton_typed_addr_typed, addr_typed_type_valid. }
      exists m1 m2; simplify_option_equality;
        eauto 20 using lockset_empty_valid.
    + destruct (mem_singleton_union_rev Γ1 Δ1 m a μ x y v τ)
        as (m1&m2&->&?&?&?); auto.
      exists m1 m2; solve ltac:(eauto using expr_eval_typed,
        lockset_empty_valid, cmap_empty_valid, cmap_valid_memenv_valid).
  * intros Γ1 Δ1 ρ ????? (?&?&->&?&(a1&v1&?&?&?&?&?)&(?&a2&v2&?&?&?&?&?));
      simplify_option_equality; exists a1 v1; split_ands; auto.
    by eapply (mem_singleton_union _ _ _ _ _ _ _ _ v1 v2); eauto.
Qed.
Lemma assert_singleton_union_r Γ e1 e2 μ x y τ :
  ⊥[x; y] → x ≠ ∅ → ¬sep_unmapped y →
  (e1 ↦{μ,x ∪ y} e2 : τ)%A ≡{Γ} (e1 ↦{μ,x} - : τ ★ e1 ↦{μ,y} e2 : τ)%A.
Proof.
  intros. rewrite (commutative (★)%A), sep_commutative by auto.
  by rewrite assert_singleton_union_l by auto.
Qed.
Lemma assert_singleton_union Γ e1 μ x y τ :
  ⊥[x; y] → x ≠ ∅ → y ≠ ∅ →
  (e1 ↦{μ,x ∪ y} - : τ)%A ≡{Γ} (e1 ↦{μ,x} - : τ ★ e1 ↦{μ,y} - : τ)%A.
Proof.
  intros; split.
  * intros Γ1 Δ1 ρ ????? (?&a&v&?&?&?&?&?); simplify_option_equality;
      typed_inversion_all; destruct (decide (sep_unmapped y)).
    { destruct (mem_singleton_union_rev_unmapped Γ1 Δ1 m a μ x y v τ)
        as (m1&m2&->&?&?&?); auto using @sep_unmapped_empty_alt.
      assert ((Γ1,Δ1) ⊢ val_new Γ1 τ : τ).
      { eauto using val_new_typed,
          mem_singleton_typed_addr_typed, addr_typed_type_valid. }
      exists m1 m2; split_ands; eauto 10 using lockset_empty_valid. }
    destruct (decide (sep_unmapped x)).
    { destruct (mem_singleton_union_rev_unmapped Γ1 Δ1 m a μ y x v τ)
        as (m1&m2&->&?&?&?); auto using @sep_unmapped_empty_alt.
      { by rewrite sep_commutative by auto. }
      assert ((Γ1,Δ1) ⊢ val_new Γ1 τ : τ).
      { eauto using val_new_typed,
          mem_singleton_typed_addr_typed, addr_typed_type_valid. }
      exists m2 m1; eauto 30 using @sep_commutative. }
    destruct (mem_singleton_union_rev Γ1 Δ1 m a μ x y v τ)
      as (m1&m2&->&?&?&?); eauto 40.
  * intros Γ1 Δ1 ρ ????? (?&?&->&?&(?&a1&v1&?&?&?&?&?)&(?&a2&v2&?&?&?&?&?));
      simplify_option_equality; destruct (decide (sep_unmapped x)).
    + eexists (inr v2), a1, v2; split_ands; eauto.
      by eapply (mem_singleton_union _ _ _ _ _ _ _ _ v1 v2); eauto.
    + eexists (inr v1), a1, v1; split_ands; eauto.
      by eapply (mem_singleton_union _ _ _ _ _ _ _ _ v1 v2); eauto.
Qed.
Lemma assert_singleton_array Γ e μ x vs τ n :
  length vs = n → n ≠ 0 →
  (e ↦{μ,x} #(VArray τ vs) : (τ.[n]))%A
  ≡{Γ} (Π imap (λ i v, (e %> RArray i τ n) ↦{μ,x} #v : τ) vs)%A.
Proof.
  intros Hn Hn'. split.
  * intros Γ1 Δ1 ρ ??? Hm ? (a&v&?&?&_&Hvs&w&->&->&Hw&Hw'&Ha&_&?&?).
    apply cmap_valid_memenv_valid in Hm; clear Hn Hn'.
    assert (∃ ws, w = MArray τ ws ∧ length ws = n ∧
      vs = to_val Γ1 <$> ws ∧ (Γ1,Δ1) ⊢* ws : τ) as (ws&->&Hn&->&Hws).
    { destruct w; simplify_option_equality; typed_inversion_all; eauto. }
    assert (Forall (not ∘ Forall (∅ =) ∘ ctree_flatten) ws) as Hemp.
    { clear Hn Hw Hvs.
      induction Hws as [|w ws]; constructor; decompose_Forall_hyps; eauto.
      eapply ctree_Forall_not, Forall_impl; naive_solver. }
    erewrite cmap_singleton_array_union by eauto.
    apply assert_Forall_holds_2; eauto using cmap_singleton_array_disjoint.
    cut (0 + length ws ≤ n); [|lia]; unfold imap; generalize 0 as j.
    clear Hemp Hn Hvs Hw; induction Hws as [|w ws]; intros j ?;
      decompose_Forall_hyps; constructor; eauto with lia.
    exists (addr_elt Γ1 (RArray j τ n) a) (to_val Γ1 w); split_ands; eauto.
    + by simplify_option_equality.
    + typed_constructor; eauto using to_val_typed, lockset_empty_valid.
    + exists w; eauto 12 using addr_elt_is_obj, addr_elt_strict, addr_elt_typed.
  * intros Γ1 Δ1 ρ m _ ? Hm ?; rewrite assert_Forall_holds; intros (ms&->&_&Hms).
    apply cmap_valid_memenv_valid in Hm.
    assert (∃ a, (Γ1,Δ1,ρ.*2) ⊢ e : inl (τ.[n])%T ∧
      ⟦ e ⟧ Γ1 ρ ∅ = Some (inl a) ∧ addr_strict Γ1 a ∧ x ≠ ∅) as (a&He&?&?&?).
    { unfold imap in *; destruct vs; decompose_Forall_hyps.
      match goal with
      | H : ∃ a, _ |- _ => destruct H as (?&?&?&?&_&_&?&_&_&_&_&_&_&_&?)
      end; simplify_option_equality; typed_inversion_all; eauto. }
    assert (∃ ws,
      ms = imap (λ i, cmap_singleton Γ1 (addr_elt Γ1 (RArray i τ n) a) μ) ws ∧
      vs = to_val Γ1 <$> ws ∧ (Γ1,Δ1) ⊢* ws : τ ∧
      Forall (λ xb, tagged_perm xb = x) (ws ≫= ctree_flatten))
      as (ws&->&->&Hws&Hws').
    { cut (0 + length vs ≤ n); [|lia]; unfold imap in *.
      clear Hn Hn' He; revert Hms; generalize 0 as j; revert vs.
      induction ms as [|m ms IH]; intros [|v vs] j ??; decompose_Forall_hyps.
      { eexists []; simpl; eauto. }
      match goal with
      | H : ∃ a, _ |- _ => destruct H as (?&?&_&?&_&?&w&->&->&Hw&?&_)
      end; simplify_option_equality.
      destruct (IH vs (S j)) as (ws&->&->&?&?); clear IH; auto with lia.
      exists (w :: ws); split_ands; csimpl; eauto using Forall_app_2. }
    assert (Forall (not ∘ Forall (∅ =) ∘ ctree_flatten) ws) as Hemp.
    { clear Hn Hms.
      induction Hws as [|w ws]; constructor; decompose_Forall_hyps; eauto.
      eapply ctree_Forall_not, Forall_impl; naive_solver. }
    assert ((Γ1,Δ1) ⊢* to_val Γ1 <$> ws : τ).
    { eapply Forall_fmap; eauto using Forall_impl, to_val_typed. }
    assert ((Γ1,Δ1) ⊢ a : TType (τ.[n])) by eauto 10
      using lval_typed_inv, expr_eval_typed, cmap_empty_valid.
    exists a (VArray τ (to_val Γ1 <$> ws));
      split_ands; eauto using lockset_empty_valid.
    rewrite fmap_length in Hn.
    erewrite <-cmap_singleton_array_union by eauto.
    exists (MArray τ ws); eauto 10 using lval_typed_inv, expr_eval_typed,
      cmap_empty_valid, (addr_ref_byte_is_obj_parent _ _ (RArray 0 τ n)).
Qed.
Lemma assert_singleton_eval Γ e v μ x τ :
  Some Readable ⊆ perm_kind x → (e ↦{μ,x} #v : τ)%A ⊆{Γ} (load e ⇓ inr v)%A.
Proof.
  intros ? Γ1 Δ1 ρ ????? (a&v'&?&?&?&?&?); simplify_option_equality.
  assert (✓{Γ1} Δ1) by eauto using cmap_valid_memenv_valid.
  eexists (inr τ); split_ands; auto.
  erewrite (expr_eval_weaken _ _ _ _ _ ∅) by eauto using cmap_empty_valid,
    cmap_subseteq_index_alive, mem_lookup_subseteq, mem_forced_subseteq,
    @sep_subseteq_empty; simpl.
  by erewrite option_guard_True, mem_lookup_singleton
    by eauto using mem_singleton_forced.
Qed.

(* Lifting De Bruijn indexes *)
Global Instance: Proper ((⊆{Γ}) ==> (⊆{Γ})) assert_lift.
Proof. solve ltac:(eauto using Forall_tail). Qed.
Global Instance: Proper ((≡{Γ}) ==> (≡{Γ})) assert_lift.
Proof. solve ltac:(eauto using Forall_tail). Qed.

Global Instance assert_lift_stack_indep: StackIndep P → StackIndep (P↑).
Proof. solve ltac:(eauto using Forall_tail). Qed.
Global Instance assert_lift_unlock_indep: UnlockIndep P → UnlockIndep (P↑).
Proof. solve ltac:(eauto using Forall_tail). Qed.

Lemma stack_indep_lift Γ P `{!StackIndep P} : (P↑)%A ≡{Γ} P.
Proof. solve ltac:(eauto using Forall_tail). Qed.
Lemma assert_lift_impl Γ P Q : ((P → Q)↑)%A ≡{Γ} (P↑ → Q↑)%A.
Proof. solve eauto. Qed.
Lemma assert_lift_and Γ P Q : ((P ∧ Q)↑)%A ≡{Γ} (P↑ ∧ Q↑)%A.
Proof. solve eauto. Qed.
Lemma assert_lift_not Γ P : ((¬P)↑)%A ≡{Γ} (¬P↑)%A.
Proof. solve eauto. Qed.
Lemma assert_lift_forall Γ {A} (P : A → assert K) :
  ((∀ x, P x)↑)%A ≡{Γ} (∀ x, P x↑)%A.
Proof. solve eauto. Qed.
Lemma assert_lift_exists Γ {A} (P : A → assert K) :
  ((∃ x, P x)↑)%A ≡{Γ} (∃ x, P x↑)%A.
Proof. solve eauto. Qed.
Lemma assert_lift_sep Γ P Q : ((P ★ Q)↑)%A ≡{Γ} (P↑ ★ Q↑)%A.
Proof. solve eauto. Qed.
Lemma assert_lift_expr Γ e v : ((e ⇓ v)↑)%A ≡{Γ} (e↑ ⇓ v)%A.
Proof.
  split.
  * intros Γ' Δ ρ m ???? (τlr&?&?); exists τlr.
    by rewrite expr_eval_lift, expr_typed_lift, <-fmap_tail.
  * intros Γ' Δ ρ m ???? (τlr&?&?); exists τlr.
    by rewrite fmap_tail, <-expr_eval_lift, <-expr_typed_lift.
Qed.
Lemma assert_lift_expr_ Γ e : ((e ⇓ -)↑)%A ≡{Γ} (e↑ ⇓ -)%A.
Proof. by rewrite assert_lift_exists; setoid_rewrite (assert_lift_expr Γ). Qed.
Lemma assert_lift_singleton Γ e1 e2 μ x τ :
  ((e1 ↦{μ,x} e2 : τ)↑)%A ≡{Γ} ((e1↑) ↦{μ,x} (e2↑) : τ)%A.
Proof.
  split; repeat intro.
  * do 2 red. by setoid_rewrite expr_eval_lift;
      setoid_rewrite expr_typed_lift; rewrite <-fmap_tail.
  * do 4 red. by rewrite fmap_tail; setoid_rewrite <-expr_eval_lift;
      setoid_rewrite <-expr_typed_lift.
Qed.
Lemma assert_lift_singleton_ Γ e1 μ x τ :
  ((e1 ↦{μ,x} - : τ)↑)%A ≡{Γ} ((e1↑) ↦{μ,x} - : τ)%A.
Proof.
  by rewrite assert_lift_exists; setoid_rewrite (assert_lift_singleton Γ).
Qed.

(* Unlocking *)
Global Instance: Proper ((⊆{Γ}) ==> (⊆{Γ})) assert_unlock.
Proof. solve ltac:(eauto using mem_unlock_all_valid). Qed.
Global Instance: Proper ((≡{Γ}) ==> (≡{Γ})) assert_unlock.
Proof. solve ltac:(eauto using mem_unlock_all_valid). Qed.

Lemma assert_unlock_unlock_indep Γ P `{!UnlockIndep P} : P ⊆{Γ} (P ◊)%A.
Proof. solve eauto. Qed.
Lemma assert_unlock_impl Γ P Q : ((P → Q) ◊)%A ≡{Γ} (P ◊ → Q ◊)%A.
Proof.
  split; [solve ltac:(eauto using mem_unlock_all_valid)|].
  solve ltac:(eauto using cmap_valid_weaken_squeeze, mem_unlock_memenv_of).
Qed.
Lemma assert_unlock_and Γ P Q : ((P ∧ Q) ◊)%A ≡{Γ} (P ◊ ∧ Q ◊)%A.
Proof. solve eauto. Qed.
Lemma assert_unlock_forall Γ {A} (P : A → assert K) :
  ((∀ x, P x) ◊)%A ≡{Γ} (∀ x, (P x) ◊)%A.
Proof. solve eauto. Qed.
Lemma assert_unlock_exists Γ {A} (P : A → assert K) :
  ((∃ x, P x) ◊)%A ≡{Γ} (∃ x, (P x) ◊)%A.
Proof. solve eauto. Qed.
Lemma assert_unlock_sep Γ P Q : (P ◊ ★ Q ◊)%A ⊆{Γ} ((P ★ Q) ◊)%A.
Proof.
  intros Γ1 Δ1 ρ m ???? (m1&m2&->&?&?&?).
  exists (mem_unlock_all m1) (mem_unlock_all m2); split_ands; auto.
  * by rewrite mem_unlock_all_union by solve_sep_disjoint.
  * by rewrite <-!mem_unlock_all_disjoint_le.
Qed.
Lemma assert_unlock_sep_alt Γ P P' Q Q' :
  P ⊆{Γ} (P' ◊)%A → Q ⊆{Γ} (Q' ◊)%A → (P ★ Q)%A ⊆{Γ} ((P' ★ Q') ◊)%A.
Proof. intros HP HQ. by rewrite HP, HQ, assert_unlock_sep. Qed.

Lemma assert_unlock_singleton Γ e1 e2 μ x τ :
  perm_locked x = true →
  (e1 ↦{μ,x} e2 : τ)%A ⊆{Γ} ((e1 ↦{μ,perm_unlock x} e2 : τ) ◊)%A.
Proof.
  intros ? Γ1 Δ1 ρ m ???? (a&v&?&?&?&?&?).
  exists a v; split_ands; eauto using mem_unlock_all_singleton.
Qed.
Lemma assert_unlock_singleton_ Γ e1 μ x τ :
  perm_locked x = true →
  (e1 ↦{μ,x} - : τ)%A ⊆{Γ} ((e1 ↦{μ,perm_unlock x} - : τ) ◊)%A.
Proof.
  intros Hx. rewrite assert_unlock_exists.
  by setoid_rewrite (λ e2, assert_unlock_singleton Γ e1 e2 μ x τ Hx).
Qed.
Lemma assert_lock_singleton Γ e1 e2 μ x τlr :
  sep_valid x → Some Writable ⊆ perm_kind x →
  (e1 ↦{μ,perm_lock x} e2 : τlr)%A ⊆{Γ} ((e1 ↦{μ,x} e2 : τlr) ◊)%A.
Proof.
  intros. by rewrite assert_unlock_singleton,
    perm_unlock_lock by auto using perm_locked_lock.
Qed.
Lemma assert_lock_singleton_ Γ e1 μ x τlr :
  sep_valid x → Some Writable ⊆ perm_kind x →
  (e1 ↦{μ,perm_lock x} - : τlr)%A ⊆{Γ} ((e1 ↦{μ,x} - : τlr) ◊)%A.
Proof.
  intros. by rewrite assert_unlock_singleton_,
    perm_unlock_lock by auto using perm_locked_lock.
Qed.
End assertions.
