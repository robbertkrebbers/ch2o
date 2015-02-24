(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** We define assertions of Hoare logic using a shallow embedding. That is,
assertions are predicates over the contents of the stack and memory. *)

(** This file defines the data type of assertions, the usual connectives of
Hoare logic ([∧], [¬], [↔], [∀] and [∃]), the connectives of separation
logic ([emp], [↦], [★]), and other connectives that are more specific to
our development. We overload the usual notations in [assert_scope] to obtain
nicely looking assertions. *)
Require Export expression_eval type_system memory_separation.
Local Obligation Tactic := idtac.

Local Hint Extern 1 (_ ⊆ _) => etransitivity; [eassumption|].
Local Hint Extern 1 (_ ⊆ _) => etransitivity; [|eassumption].
Local Hint Extern 1 (_ ⇒ₘ _) => etransitivity; [|eassumption].
Local Hint Extern 1 (_ ⇒ₘ _) => etransitivity; [|eassumption].
Local Hint Extern 1 (_ ⊆{_} _) => etransitivity; [eassumption|].
Local Hint Extern 1 (_ ⊆{_} _) => etransitivity; [|eassumption].

(** * Definition of assertions *)
Record assert (K : Set) `{Env K} := Assert {
  assert_holds : env K → memenv K → stack → list (type K) → mem K → Prop;
  assert_weaken Γ1 Γ2 Δ1 Δ2 ρ τs m :
    ✓ Γ1 → ✓{Γ1,Δ1} m → Δ1 ⊢* ρ :* τs →
    assert_holds Γ1 Δ1 ρ τs m →
    Γ1 ⊆ Γ2 → Δ1 ⇒ₘ Δ2 →
    assert_holds Γ2 Δ2 ρ τs m
}.
Add Printing Constructor assert.

Delimit Scope assert_scope with A.
Bind Scope assert_scope with assert.
Arguments Assert {_ _} _ _.
Arguments assert_holds {_ _} _%A _ _ _ _ _.
Arguments assert_weaken {_ _} _%A _ _ _ _ _ _ _ _ _ _ _ _ _.

(** The relation [P ⊆@{Γ} Q] states that the assertion [Q] is a logical
consequence of [P] in [Γ] and [P ≡@{Γ} Q] states that [P] and [Q] are logically
equivalent in [Γ]. *)
Instance assert_entails `{Env K} : SubsetEqE (env K) (assert K) := λ Γ P Q,
  ∀ Γ' Δ ρ τs m,
    Γ ⊆ Γ' → ✓ Γ' → ✓{Γ',Δ} m → Δ ⊢* ρ :* τs →
    assert_holds P Γ' Δ ρ τs m → assert_holds Q Γ' Δ ρ τs m.
Instance assert_equiv `{Env K} : EquivE (env K) (assert K) := λ Γ P Q,
  P ⊆{Γ} Q ∧ Q ⊆{Γ} P.

(** * Hoare logic connectives *)
(** Definitions and notations of the usual connectives of Hoare logic. *)
Program Definition assert_Prop `{Env K} (P : Prop) : assert K := {|
  assert_holds := λ _ _ _ _ m, P ∧ m = ∅
|}.
Next Obligation. naive_solver. Qed.
Notation "⌜ P ⌝" := (assert_Prop P) (format "⌜  P  ⌝") : assert_scope.
Notation "'False'" := (assert_Prop False) : assert_scope.

Program Definition assert_impl `{Env K} (P Q : assert K) : assert K := {|
  assert_holds := λ Γ Δ ρ τs m, ∀ Γ' Δ',
    Γ ⊆ Γ' → ✓ Γ' → Δ ⇒ₘ Δ' → ✓{Γ',Δ'} m →
    assert_holds P Γ' Δ' ρ τs m → assert_holds Q Γ' Δ' ρ τs m
|}.
Next Obligation.
  intros ?? P Q Γ1 Γ2 Δ1 Δ2 ρ τs m ??? HPQ ?? Γ3 Δ3 ?????.
  apply HPQ; eauto.
Qed.
Infix "→" := assert_impl : assert_scope.
Notation "(→)" := assert_impl (only parsing) : assert_scope.
Notation "( P →)" := (assert_impl P) (only parsing) : assert_scope.
Notation "(→ Q )" := (λ P, assert_impl P Q) (only parsing) : assert_scope.

Program Definition assert_and `{Env K} (P Q : assert K) : assert K := {|
  assert_holds := λ Γ Δ ρ τs m,
    assert_holds P Γ Δ ρ τs m ∧ assert_holds Q Γ Δ ρ τs m
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
  assert_holds := λ Γ Δ ρ τs m, ∀ x, assert_holds (P x) Γ Δ ρ τs m
|}.
Next Obligation. naive_solver eauto using assert_weaken. Qed.
Notation "∀ x .. y , P" :=
  (assert_forall (λ x, .. (assert_forall (λ y, P)) ..)) : assert_scope.

Program Definition assert_exist `{Env K} `(P : A → assert K): assert K := {|
  assert_holds := λ Γ Δ ρ τs m, ∃ x, assert_holds (P x) Γ Δ ρ τs m
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
  assert_holds := λ Γ Δ ρ τs m, ∃ m1 m2,
    m = m1 ∪ m2 ∧ ⊥[m1; m2] ∧
    assert_holds P Γ Δ ρ τs m1 ∧ assert_holds Q Γ Δ ρ τs m2
|}.
Next Obligation.
  intros ??? P Q Γ1 Γ2 Δ1 Δ2 ρ τs m ??? (m1&m2&->&?&?&?) ??.
  eauto 15 using assert_weaken, cmap_valid_subseteq,
    (@sep_union_subseteq_l (mem K) _ _), (@sep_union_subseteq_r (mem K) _ _).
Qed.
Infix "★" := assert_sep (at level 80, right associativity) : assert_scope.
Notation "(★)" := assert_sep (only parsing) : assert_scope.
Notation "( P ★)" := (assert_sep P) (only parsing) : assert_scope.
Notation "(★ Q )" := (λ P, assert_sep P Q) (only parsing) : assert_scope.

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
Program Definition assert_expr `{EnvSpec K}
    (e : expr K) (τlr : lrtype K) : vassert K := λ ν, {|
  assert_holds := λ Γ Δ ρ τs m, (Γ,Δ,τs) ⊢ e : τlr ∧ ⟦ e ⟧ Γ ∅ ρ m = Some ν
|}.
Next Obligation.
  intros ??? e τlr ν Γ1 Γ2 Δ1 Δ2 ρ τs m ??? [??] ??; split;
    eauto using expr_typed_weaken, expr_eval_weaken, purefuns_empty_valid,
    mem_lookup_weaken, mem_forced_weaken.
Qed.
Notation "e ⇓ ν : τlr" := (assert_expr e τlr ν)%A
  (at level 60, ν at next level, τlr at next level,
   format "e  '⇓'  ν  :  τlr") : assert_scope.
Notation "e ⇓ - : τlr" := (∃ ν, e ⇓ ν : τlr)%A
  (at level 60, τlr at next level,
   format "e  '⇓'  '-'  :  τlr") : assert_scope.

(** The assertion [e1 ↦{malloc,x} e2] asserts that the memory consists of
exactly one object at address [e1] with permission [x] and contents [e2]. The
assertion [e1 ↦{malloc,x} -] asserts that the memory consists of exactly one
object at address [e1] with permission [x] and arbitrary contents. The Boolean
[malloc] denotes whether the object has been obtained via malloc. *)
Program Definition assert_singleton `{EnvSpec K}
    (e1 e2 : expr K) (malloc : bool) (x : perm) (τ : type K) : assert K := {|
  assert_holds := λ Γ Δ ρ τs m, ∃ a v,
    (Γ,Δ,τs) ⊢ e1 : inl τ ∧ ⟦ e1 ⟧ Γ ∅ ρ ∅ = Some (inl a) ∧
    (Γ,Δ,τs) ⊢ e2 : inr τ ∧ ⟦ e2 ⟧ Γ ∅ ρ ∅ = Some (inr v) ∧
    addr_is_obj a ∧ sep_valid x ∧ ¬sep_unmapped x ∧ 
    m = mem_singleton Γ a malloc x v
|}.
Next Obligation.
  intros ??? e1 e2 ml x τ Γ1 Γ2 Δ1 Δ2 ρ τs m ??? (a&v&?&?&?&?&?&?&?&->) ??.
  exists a v; split_ands;
    eauto 15 using expr_typed_weaken, expr_eval_weaken_empty,
    purefuns_empty_valid, mem_singleton_weaken, cmap_valid_memenv_valid,
    lval_typed_inv, lval_typed_strict, rval_typed_inv, expr_eval_typed,
    cmap_empty_valid.
Qed.
Notation "e1 ↦{ malloc , x } e2 : τ" := (assert_singleton e1 e2 malloc x τ)%A
  (at level 20, malloc at next level, x at next level, e2 at next level,
   τ at next level, format "e1  ↦{ malloc , x }  e2  :  τ") : assert_scope.
Notation "e1 ↦{ malloc , x } - : τ" :=
  (∃ ν, e1 ↦{malloc,x} (%# ν) : τ)%A
  (at level 20, malloc at next level, x at next level,
   τ at next level, format "e1  ↦{ malloc , x }  -  :  τ") : assert_scope.

(** The assertion [P ○] asserts that [P] holds if all sequenced locations
are unlocked. *)
Program Definition assert_unlock `{EnvSpec K} (P : assert K) : assert K := {|
  assert_holds := λ Γ Δ ρ τs m, assert_holds P Γ Δ ρ τs (mem_unlock_all m)
|}.
Next Obligation.
  naive_solver eauto using assert_weaken, mem_unlock_all_valid.
Qed.
Notation "P ○" := (assert_unlock P) (at level 20) : assert_scope.

(** The assertion [P↡] asserts that [P] holds if the stack is cleared. This
connective allows us to specify stack independence in an alternative way. *)
Program Definition assert_clear_stack `{Env K} (P : assert K) : assert K := {|
  assert_holds := λ Γ Δ ρ τs m, assert_holds P Γ Δ [] [] m
|}.
Next Obligation. naive_solver eauto using assert_weaken. Qed.
Notation "P ↡" := (assert_clear_stack P) (at level 20) : assert_scope.

(** To deal with block scope variables we need to lift an assertion such that
the De Bruijn indexes of its variables are increased. We define the lifting
[P↑] of an assertion [P] semantically, and prove that it indeed behaves as
expected. *)
Program Definition assert_lift `{Env K} (P : assert K) : assert K := {|
  assert_holds := λ Γ Δ ρ τs m, assert_holds P Γ Δ (tail ρ) (tail τs) m
|}.
Next Obligation. naive_solver eauto using assert_weaken, Forall2_tail. Qed.
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
  stack_indep Γ Δ ρ1 τs1 ρ2 τs2 m :
    ✓ Γ → ✓{Γ,Δ} m → Δ ⊢* ρ1 :* τs1 → Δ ⊢* ρ2 :* τs2 →
    assert_holds P Γ Δ ρ1 τs1 m →
    assert_holds P Γ Δ ρ2 τs2 m.
Class UnlockIndep `{Env K} (P : assert K) : Prop :=
  unlock_indep Γ Δ ρ τs m :
    ✓ Γ → ✓{Γ,Δ} m → Δ ⊢* ρ :* τs →
    assert_holds P Γ Δ ρ τs m →
    assert_holds P Γ Δ ρ τs (mem_unlock_all m).

Hint Extern 10 (StackIndep _) => apply _.
Hint Extern 10 (UnlockIndep _) => apply _.

Section assertions.
Context `{EnvSpec K}.
Implicit Types Γ : env K.

Hint Unfold Proper respectful pointwise_relation : assert.
Hint Unfold subseteqE assert_entails equivE assert_equiv : assert.
Hint Unfold StackIndep UnlockIndep : assert.
Hint Extern 100 (⊥ _) => solve_sep_disjoint.
Hint Extern 100 (sep_valid _) =>
  apply sep_disjoint_list_singleton; solve_sep_disjoint.
Hint Immediate cmap_valid_sep_valid.
Hint Immediate purefuns_empty_valid.
Hint Extern 0 (Separation _) => apply (_ : Separation (mem K)).
Hint Extern 0 (Separation _) => apply (_ : Separation perm).
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
  intros Γ1 P1 P2 HP Q1 Q2 HQ Γ2 Δ ρ τs m ???? HPQ Γ3 Δ2 ???? HP2.
  eapply HQ; eauto using Forall2_impl, memenv_forward_typed.
  eapply HPQ; eauto.
  eapply HP; eauto using Forall2_impl, memenv_forward_typed.
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
  intros P Q HP HQ Γ Δ ρ1 τs1 ρ2 τs2 m ???? HPQ Γ2 Δ2 ???? HP'.
  eapply HQ, HPQ, HP with ρ2 τs2; eauto using Forall2_impl,memenv_forward_typed.
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

Global Instance assert_sep_unlock_indep P Q :
  UnlockIndep P → UnlockIndep Q → UnlockIndep (P ★ Q).
Proof.
  intros HP HQ Γ Δ δ τs m ??? (m1&m2&->&?&?&?).
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

Global Instance: Commutative (⊆{Γ}) (★)%A.
Proof.
  intros Γ P Q Γ1 Δ1 ρ τs m ???? (m1&m2&->&?&?&?).
  exists m2 m1. rewrite sep_commutative by auto; auto.
Qed.
Global Instance: Commutative (≡{Γ}) (★)%A.
Proof. split; by rewrite (commutative (★)%A). Qed.
Global Instance: LeftId (≡{Γ}) emp%A (★)%A.
Proof.
  intros Γ; intros P; split.
  * intros Γ1 Δ1 ρ τs m ???? (m1&m2&->&?&[_ ->]&?).
    rewrite sep_left_id by auto; auto.
  * intros Γ1 Δ1 ρ τs m ?????. eexists ∅, m.
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
  { intros P Q R Γ1 Δ1 ρ τs ????? (?&m3&->&?&(m1&m2&->&?&?&?)&?).
    exists m1 (m2 ∪ m3); rewrite sep_associative by auto; split_ands; auto.
    exists m2 m3; auto. }
  assert (∀ P Q R, (P ★ (Q ★ R))%A ⊆{Γ} ((P ★ Q) ★ R)%A).
  { intros P Q R Γ1 Δ1 ρ τs ????? (m1&?&->&?&?&(m2&m3&->&?&?&?)).
    exists (m1 ∪ m2) m3; rewrite sep_associative by auto; split_ands; auto.
    exists m1 m2; auto. }
  split; auto.
Qed.
Lemma assert_Prop_and_intro Γ (P : Prop) Q R :
  P → Q ⊆{Γ} R → Q ⊆{Γ} (⌜ P ⌝ ★ R)%A.
Proof.
  intros ?? Γ1 Δ1 ρ τs ??????. eexists ∅, m.
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

Lemma assert_Forall_holds_2 (Ps : list (assert K)) Γ Δ ρ τs ms :
  ⊥ ms → Forall2 (λ (P : assert K) m, assert_holds P Γ Δ ρ τs m) Ps ms →
  assert_holds (Π Ps)%A Γ Δ ρ τs (⋃ ms).
Proof. intros Hms HPs. revert Hms. induction HPs; solve eauto. Qed.
Lemma assert_Forall_holds (Ps : list (assert K)) Γ Δ ρ τs m :
  assert_holds (Π Ps)%A Γ Δ ρ τs m ↔ ∃ ms, m = ⋃ ms ∧ ⊥ ms ∧
    Forall2 (λ (P : assert K) m, assert_holds P Γ Δ ρ τs m) Ps ms.
Proof.
  split; [|naive_solver eauto using assert_Forall_holds_2].
  revert m. induction Ps as [|P Ps IH].
  { intros m [? ->]. eexists []. by repeat constructor. }
  intros ? (m1&m2&->&?&?&?); destruct (IH m2) as (ms&->&?&?); trivial.
  exists (m1 :: ms); auto.
Qed.

(* Evaluation and singleton connectives *)
Global Instance assert_expr_stack_indep e v τlr :
  vars e = ∅ → StackIndep (e ⇓ v : τlr).
Proof.
  intros ? Γ Δ ρ1 τs1 ρ2 τs2 m ???? [??]; split;
    erewrite 1?expr_eval_var_free by eauto; eauto using expr_typed_var_free.
Qed.
Global Instance assert_singleton_stack_indep e1 e2 malloc x τ :
  vars e1 = ∅ → vars e2 = ∅ → StackIndep (e1 ↦{malloc,x} e2 : τ).
Proof.
  intros ?? Γ Δ ρ1 τs1 ρ2 τs2 m ???? (a&v&?&?&?&?&?&?&?&->);
    exists a v; erewrite !(expr_eval_var_free _ _ ρ2 ρ1) by eauto;
    eauto 10 using expr_typed_var_free.
Qed.
Global Instance assert_singleton_unlock_indep Γ e1 e2 malloc x τ :
  perm_locked x = false → UnlockIndep (e1 ↦{malloc,x} e2 : τ).
Proof.
  intros ? Γ1 Δ1 ρ τs m ??? (a&v&?&?&?&?&?&?&?&->).
  assert ((Γ1,Δ1) ⊢ v : τ ∧ (Γ1,Δ1) ⊢ a : TType τ ∧ addr_strict Γ1 a)
    as (?&?&?) by eauto 15 using cmap_valid_memenv_valid, lval_typed_inv,
    lval_typed_strict, rval_typed_inv, expr_eval_typed, cmap_empty_valid.
  exists a v; split_ands; eauto using mem_unlock_all_singleton_unlocked.
Qed.

Lemma assert_singleton_union Γ e1 e2 malloc x y τ :
  ⊥[x; y] → ¬sep_unmapped x → ¬sep_unmapped y →
  (e1 ↦{malloc,x} e2 : τ ★ e1 ↦{malloc,y} e2 : τ)%A
  ≡{Γ} (e1 ↦{malloc,x ∪ y} e2 : τ)%A.
Proof.
  intros; split.
  * intros Γ1 Δ1 ρ τs ????? (?&?&->&?&(a1&v1&?&?&?&?&?&?&?&->)&
      (a2&v2&?&?&?&?&?&?&?&->)); simplify_equality'.
    assert ((Γ1,Δ1) ⊢ v1 : τ ∧ (Γ1,Δ1) ⊢ a1 : TType τ ∧ addr_strict Γ1 a1)
      as (?&?&?) by eauto 15 using cmap_valid_memenv_valid, lval_typed_inv,
      lval_typed_strict, rval_typed_inv, expr_eval_typed, cmap_empty_valid.
    exists a1 v1; split_ands;
      eauto 13 using mem_singleton_union, eq_sym, @sep_unmapped_union_l.
  * intros Γ1 Δ1 ρ τs ????? (a&v&?&He1&?&?&He2&?&?&->).
    assert (x ⊥ y) by solve_sep_disjoint.
    assert ((Γ1,Δ1) ⊢ v : τ ∧ (Γ1,Δ1) ⊢ a : TType τ ∧ addr_strict Γ1 a)
      as (?&?&?) by eauto 15 using cmap_valid_memenv_valid, lval_typed_inv,
      lval_typed_strict, rval_typed_inv, expr_eval_typed, cmap_empty_valid.
    exists (mem_singleton Γ1 a malloc x v) (mem_singleton Γ1 a malloc y v).
    split_ands; rewrite ?sep_disjoint_list_double; solve
      ltac:(eauto using mem_singleton_union, eq_sym, mem_singleton_disjoint).
Qed.
Lemma assert_singleton_array Γ e malloc x vs τ n :
  length vs = n → n ≠ 0 →
  (e ↦{malloc,x} #(VArray τ vs) : (τ.[n]))%A
  ≡{Γ} (Π imap (λ i v, (e %> RArray i τ n) ↦{malloc,x} #v : τ) vs)%A.
Proof.
  intros Hn Hn'. split.
  * intros Γ1 Δ1 ρ τs ????? (a&v&?&?&Hvs&Hvs'&?&?&?&->).
    assert ((Γ1,Δ1) ⊢ a : TType (τ.[n]) ∧ addr_strict Γ1 a)
      as [] by eauto 10 using cmap_valid_memenv_valid, lval_typed_inv,
      lval_typed_strict, expr_eval_typed, cmap_empty_valid.
    assert (∀ j, j + length vs ≤ n → (Γ1,Δ1) ⊢* vs : τ →
      Forall2 (λ (P : assert K) m, assert_holds P Γ1 Δ1 ρ τs m)
        (imap_go (λ i v,((e %> RArray i τ n) ↦{malloc,x} #v : τ)%A) j vs)
        (imap_go (λ i,
          mem_singleton Γ1 (addr_elt Γ1 (RArray i τ n) a) malloc x) j vs)).
    { clear Hn Hvs Hvs'. intros j Hj Hvs; revert j Hj.
      induction Hvs as [|v' vs ?? IH]; csimpl; intros j ?; auto.
      constructor; [|eauto with lia].
      eexists (addr_elt Γ1 (RArray j τ n) a), v'; simplify_option_equality;
        eauto 15 using addr_elt_is_obj, lockset_empty_valid. }
    simplify_option_equality; typed_inversion_all.
    erewrite mem_singleton_array_union by eauto.
    apply assert_Forall_holds_2;
      eauto using mem_singleton_array_disjoint with lia.
  * intros Γ1 Δ1 ρ τs m _ ? Hm ?; rewrite assert_Forall_holds; intros (ms&->&_&Hms).
    apply cmap_valid_memenv_valid in Hm.
    assert (∃ a, (Γ1,Δ1,τs) ⊢ e : inl (τ.[n])%T ∧ ⟦ e ⟧ Γ1 ∅ ρ ∅ = Some (inl a) ∧
      sep_valid x ∧ ¬sep_unmapped x) as (a&?&?&?&?).
    { unfold imap in *. destruct vs; decompose_Forall_hyps.
      naive_solver (simplify_option_equality; typed_inversion_all; eauto). }
    assert ((Γ1,Δ1) ⊢* vs : τ).
    { clear Hn Hn'. revert ms Hms. unfold imap. generalize 0.
      induction vs; intros ? [|??] ?; decompose_Forall_hyps;
        try match goal with
        | H : ∃ a, _ |- _ => destruct H as (?&?&?&?&?&?&?&?&?&?)
        end; simplify_option_equality; typed_inversion_all; eauto. }
    assert (ms = imap (λ i,
      mem_singleton Γ1 (addr_elt Γ1 (RArray i τ n) a) malloc x) vs) as ->.
    { clear Hn Hn'. revert ms Hms. unfold imap. generalize 0.
      induction vs; intros ? [|??] ?; decompose_Forall_hyps;
        try match goal with
        | H : ∃ a, _ |- _ => destruct H as (?&?&?&?&?&?&?&?&?&?)
        end; simplify_option_equality; typed_inversion_all; f_equal; auto. }
    assert ((Γ1,Δ1) ⊢ a : TType (τ.[n]) ∧ addr_strict Γ1 a) as [] by eauto 10
      using lval_typed_inv, lval_typed_strict, expr_eval_typed, cmap_empty_valid.
    exists a (VArray τ vs); split_ands; eauto using lockset_empty_valid,
      (addr_ref_byte_is_obj_parent _ _ (RArray 0 τ n)),
      mem_singleton_array_union, eq_sym.
Qed.

(* Lifting De Bruijn indexes *)
Global Instance: Proper ((⊆{Γ}) ==> (⊆{Γ})) assert_lift.
Proof. solve ltac:(eauto using Forall2_tail). Qed.
Global Instance: Proper ((≡{Γ}) ==> (≡{Γ})) assert_lift.
Proof. solve ltac:(eauto using Forall2_tail). Qed.

Global Instance assert_lift_stack_indep: StackIndep P → StackIndep (P↑).
Proof. solve ltac:(eauto using Forall2_tail). Qed.
Global Instance assert_lift_unlock_indep: UnlockIndep P → UnlockIndep (P↑).
Proof. solve ltac:(eauto using Forall2_tail). Qed.

Lemma stack_indep_lift Γ P `{!StackIndep P} : (P↑)%A ≡{Γ} P.
Proof. solve ltac:(eauto using Forall2_tail). Qed.
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
Lemma assert_lift_expr Γ e v τ : ((e ⇓ v : τ)↑)%A ≡{Γ} (e↑ ⇓ v : τ)%A.
Proof.
  split; repeat intro.
  * do 2 red; by rewrite expr_eval_lift, expr_typed_lift.
  * do 4 red; by rewrite <-expr_eval_lift, <-expr_typed_lift.
Qed.
Lemma assert_lift_expr_ Γ e τ : ((e ⇓ - : τ)↑)%A ≡{Γ} (e↑ ⇓ - : τ)%A.
Proof. by rewrite assert_lift_exists; setoid_rewrite (assert_lift_expr Γ). Qed.
Lemma assert_lift_singleton Γ e1 e2 malloc x τ :
  ((e1 ↦{malloc,x} e2 : τ)↑)%A ≡{Γ} ((e1↑) ↦{malloc,x} (e2↑) : τ)%A.
Proof.
  split; repeat intro.
  * do 2 red. by setoid_rewrite expr_eval_lift; setoid_rewrite expr_typed_lift.
  * do 4 red; by setoid_rewrite <-expr_eval_lift;
      setoid_rewrite <-expr_typed_lift.
Qed.
Lemma assert_lift_singleton_ Γ e1 malloc x τ :
  ((e1 ↦{malloc,x} - : τ)↑)%A ≡{Γ} ((e1↑) ↦{malloc,x} - : τ)%A.
Proof.
  by rewrite assert_lift_exists; setoid_rewrite (assert_lift_singleton Γ).
Qed.

(* Unlocking *)
Global Instance: Proper ((⊆{Γ}) ==> (⊆{Γ})) assert_unlock.
Proof. solve ltac:(eauto using mem_unlock_all_valid). Qed.
Global Instance: Proper ((≡{Γ}) ==> (≡{Γ})) assert_unlock.
Proof. solve ltac:(eauto using mem_unlock_all_valid). Qed.

Lemma assert_unlock_unlock_indep Γ P `{!UnlockIndep P} : P ⊆{Γ} (P ○)%A.
Proof. solve eauto. Qed.
Lemma assert_unlock_impl Γ P Q : ((P → Q) ○)%A ≡{Γ} (P ○ → Q ○)%A.
Proof.
  split; [solve ltac:(eauto using mem_unlock_all_valid)|].
  solve ltac:(eauto using cmap_valid_weaken_squeeze, mem_unlock_memenv_of).
Qed.
Lemma assert_unlock_and Γ P Q : ((P ∧ Q) ○)%A ≡{Γ} (P ○ ∧ Q ○)%A.
Proof. solve eauto. Qed.
Lemma assert_unlock_forall Γ {A} (P : A → assert K) :
  ((∀ x, P x) ○)%A ≡{Γ} (∀ x, (P x) ○)%A.
Proof. solve eauto. Qed.
Lemma assert_unlock_exists Γ {A} (P : A → assert K) :
  ((∃ x, P x) ○)%A ≡{Γ} (∃ x, (P x) ○)%A.
Proof. solve eauto. Qed.
Lemma assert_unlock_sep Γ P Q : (P ○ ★ Q ○)%A ⊆{Γ} ((P ★ Q) ○)%A.
Proof.
  intros Γ1 Δ1 ρ τs m ???? (m1&m2&->&?&?&?).
  exists (mem_unlock_all m1) (mem_unlock_all m2); split_ands; auto.
  * by rewrite mem_unlock_all_union by solve_sep_disjoint.
  * by rewrite <-!mem_unlock_all_disjoint_le.
Qed.
Lemma assert_unlock_sep_alt Γ P P' Q Q' :
  P ⊆{Γ} (P' ○)%A → Q ⊆{Γ} (Q' ○)%A → (P ★ Q)%A ⊆{Γ} ((P' ★ Q') ○)%A.
Proof. intros HP HQ. by rewrite HP, HQ, assert_unlock_sep. Qed.

Lemma assert_unlock_singleton Γ e1 e2 malloc x τ :
  perm_locked x = true →
  (e1 ↦{malloc,x} e2 : τ)%A ⊆{Γ} ((e1 ↦{malloc,perm_unlock x} e2 : τ) ○)%A.
Proof.
  intros ? Γ1 Δ1 ρ τs m ???? (a&v&?&?&?&?&?&?&?&->).
  exists a v; split_ands; eauto using perm_unlock_valid, perm_unlock_mapped.
  assert ((Γ1,Δ1) ⊢ v : τ ∧ (Γ1,Δ1) ⊢ a : TType τ ∧ addr_strict Γ1 a)
    as (?&?&?) by eauto 15 using cmap_valid_memenv_valid, lval_typed_inv,
    lval_typed_strict, rval_typed_inv, expr_eval_typed, cmap_empty_valid.
  by erewrite mem_unlock_all_singleton by eauto.
Qed.
Lemma assert_unlock_singleton_ Γ e1 malloc x τ :
  perm_locked x = true →
  (e1 ↦{malloc,x} - : τ)%A ⊆{Γ} ((e1 ↦{malloc,perm_unlock x} - : τ) ○)%A.
Proof.
  intros Hx. rewrite assert_unlock_exists.
  by setoid_rewrite (λ e2, assert_unlock_singleton Γ e1 e2 malloc x τ Hx).
Qed.
Lemma assert_lock_singleton Γ e1 e2 malloc x τlr :
  sep_valid x → Some Writable ⊆ perm_kind x →
  (e1 ↦{malloc,perm_lock x} e2 : τlr)%A ⊆{Γ} ((e1 ↦{malloc,x} e2 : τlr) ○)%A.
Proof.
  intros. by rewrite assert_unlock_singleton,
    perm_unlock_lock by auto using perm_locked_lock.
Qed.
Lemma assert_lock_singleton_ Γ e1 malloc x τlr :
  sep_valid x → Some Writable ⊆ perm_kind x →
  (e1 ↦{malloc,perm_lock x} - : τlr)%A ⊆{Γ} ((e1 ↦{malloc,x} - : τlr) ○)%A.
Proof.
  intros. by rewrite assert_unlock_singleton_,
    perm_unlock_lock by auto using perm_locked_lock.
Qed.
End assertions.
